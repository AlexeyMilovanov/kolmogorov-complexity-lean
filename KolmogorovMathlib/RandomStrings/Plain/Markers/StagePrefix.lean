/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Markers.LastProgram

/-!
# Stage prefix complexity and the post-marker tail

This module proves the quantitative properties of the marker `w_n = lastProgram B n` that rest on
replaying the canonical enumeration of `B` up to the marker tick.

* `last_program_conditional_complexity_deficit` is the final arithmetic of the conditional
  incompressibility of the marker (`lem:marker-incompressible`): a logarithmic literal cost plus a
  fixed overhead eventually stays below its value.
* `last_program_tail_bound` and `last_program_tail_bound_advice` bound the number `rest B n u` of
  simple strings at scale `u` that are not yet emitted at the marker tick, by `2 ^ (u - n + c)`,
  for an upper scale `u` computed from `n` by a fixed partial computable map, or described by a
  bounded-length conditional program (`lem:tail`).  The proof charges the raw bits of a dyadic
  count threshold to an auxiliary decoder that replays the enumeration.
* `exponential_tail_budget` specialises the tail bound to the scale `u = 2 ^ n`
  (`cor:tail-budget`).
* `marker_stage_prefix_complexity_exact` and its variants show that, for short arguments, the
  prefix complexity computed at the marker tick equals the true prefix complexity `KP B.D`
  (`lem:short-prefix-exact`); `marker_stage_prefix_complexity_exact_common` collects all marker
  assertions under one threshold `n₀`.

These statements are the inputs of the later modules that bound the size of the enumeration after
the marker tick and that pad the marker to a random string.
-/

namespace Kolmogorov.Milovanov

private lemma add_two_le_two_pow_div_four (n : ℕ) (hn : 64 ≤ n) : n + 2 ≤ 2 ^ (n / 4) := by
  have h1 : 16 ≤ n / 4 := by omega
  have h2 : n + 2 ≤ 4 * (n / 4) + 5 := by omega
  have h3 : 4 * (n / 4) + 5 ≤ 2 ^ (n / 4) := four_mul_add_five_le_two_pow (n / 4) h1
  omega

private lemma clog_two_add_two_le_div_four (n : ℕ) (hn : 64 ≤ n) :
    Nat.clog 2 (n + 2) ≤ n / 4 := by
  apply Nat.clog_le_iff_le_pow (by decide) |>.mpr
  exact add_two_le_two_pow_div_four n hn

/-- A logarithmic integer literal cost plus any fixed decoder overhead eventually beats its value.
Blueprint node `lem:marker-incompressible`. This is the deficit arithmetic in its proof. -/
theorem last_program_conditional_complexity_deficit (c b : ℕ) :
    ∃ c₀ : ℕ, ∀ t > c₀, integerLiteralBound c t + b < t := by
  use max 64 (2 * (c + b) + 1)
  intro t ht
  have ht_ge : 64 ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht)
  have ht_lt : 2 * (c + b) + 1 < t := lt_of_le_of_lt (le_max_right _ _) ht
  have h3 : Nat.clog 2 (t + 2) ≤ t / 4 :=
    clog_two_add_two_le_div_four t ht_ge
  unfold integerLiteralBound
  calc
    2 * Nat.clog 2 (t + 2) + c + b = 2 * Nat.clog 2 (t + 2) + (c + b) := by ring
    _ ≤ 2 * (t / 4) + (c + b) := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left 2 h3
    _ ≤ t / 2 + (c + b) := by
      apply Nat.add_le_add_right
      omega
    _ < t := by omega

/-- The distinct outputs emitted by the marker tick and the remaining distinct outputs partition
all simple outputs at scale `u`. -/
private lemma stageCount_add_rest_eq_simpleCount (B : Base) (n u : ℕ) :
    stageCount B u (markerTick B n) + rest B n u = simpleCount B.V u := by
  have hd : (stageOutputs B u (markerTick B n) : Set BitString) ⊆ {x | Simple B.V x u} := by
    intro x hx
    exact (canonical_enumeration_spec_union B u x).mpr ⟨markerTick B n, hx⟩
  have hf : {x | Simple B.V x u}.Finite := (simple_finite_card_lt B.V u).1
  have hd2 : {x : BitString | Simple B.V x u ∧ x ∉ stageOutputs B u (markerTick B n)} =
      {x | Simple B.V x u} \ (stageOutputs B u (markerTick B n) : Set BitString) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe]
  dsimp [rest, simpleCount, stageCount]
  rw [hd2]
  have hd4 := Set.ncard_sdiff_add_ncard_of_subset hd hf
  have hd3 : (stageOutputs B u (markerTick B n)).card =
      (stageOutputs B u (markerTick B n) : Set BitString).ncard := by
    exact Set.ncard_coe_finset _ |>.symm
  rw [hd3]
  omega

/-- A number `R ≥ 2 ^ (u - n)` lies in some dyadic bracket
`[2 ^ (u - n + j), 2 ^ (u - n + j + 1))`. -/
private lemma exists_dyadic_gap_of_le (u n R : ℕ) (hR2 : 2 ^ (u - n) ≤ R) :
    ∃ j : ℕ, 2 ^ (u - n + j) ≤ R ∧ R < 2 ^ (u - n + j + 1) := by
  have hd : ∃ k, 2 ^ k ≤ R ∧ R < 2 ^ (k + 1) := by
    use Nat.log2 R
    have h1 : R ≠ 0 := by
      intro h
      rw [h] at hR2
      have h2 : 0 < 2 ^ (u - n) := by positivity
      omega
    constructor
    · exact (Nat.le_log2 h1).mp (le_refl _)
    · exact (Nat.log2_lt h1).mp (Nat.lt_succ_self _)
  obtain ⟨k, hk1, hk2⟩ := hd
  have h_le : u - n ≤ k := by
    by_contra h
    push Not at h
    have h1 : u - n ≥ k + 1 := by omega
    have h2 : 2 ^ (k + 1) ≤ 2 ^ (u - n) := Nat.pow_le_pow_right (by decide) h1
    have h3 : R < 2 ^ (u - n) := lt_of_lt_of_le hk2 h2
    omega
  use k - (u - n)
  have h_eq : u - n + (k - (u - n)) = k := by omega
  rw [h_eq]
  exact ⟨hk1, hk2⟩

/-- A dyadic count threshold `a * 2 ^ (u - n + j)` lies beyond `T - R` but at most `T`, where
`2 ^ (u - n + j)` is the dyadic bracket of `R`, and `a` is encodable in `n - j + 1` raw bits. -/
private lemma exists_count_threshold (n u R T : ℕ) (hlt : n < u) (hR : R ≤ T)
    (hT : T < 2 ^ (u + 1)) (hR2 : 2 ^ (u - n) ≤ R) :
    ∃ j a : ℕ, j ≤ n ∧ a < 2 ^ (n - j + 1) ∧ 2 ^ (u - n + j) ≤ R ∧
      R < 2 ^ (u - n + j + 1) ∧ T - R < a * 2 ^ (u - n + j) ∧
      a * 2 ^ (u - n + j) ≤ T := by
  obtain ⟨j, hj1, hj2⟩ := exists_dyadic_gap_of_le u n R hR2
  have hT2 : 2 ^ (u - n + j) ≤ T := le_trans hj1 hR
  have h_j_le_n : j ≤ n := by
    by_contra h
    push Not at h
    have h1 : u + 1 ≤ u - n + j := by omega
    have h2 : 2 ^ (u + 1) ≤ 2 ^ (u - n + j) := Nat.pow_le_pow_right (by decide) h1
    have h3 : 2 ^ (u + 1) ≤ R := le_trans h2 hj1
    have h4 : 2 ^ (u + 1) ≤ T := le_trans h3 hR
    omega
  set a := (T - R) / 2 ^ (u - n + j) + 1
  have ha1 : a * 2 ^ (u - n + j) > T - R := by
    have h6 : 0 < 2 ^ (u - n + j) := by positivity
    have h7 : 2 ^ (u - n + j) * ((T - R) / 2 ^ (u - n + j)) +
        (T - R) % 2 ^ (u - n + j) = T - R :=
      Nat.div_add_mod (T - R) (2 ^ (u - n + j))
    have h8 : (T - R) % 2 ^ (u - n + j) < 2 ^ (u - n + j) := Nat.mod_lt (T - R) h6
    calc
      T - R = 2 ^ (u - n + j) * ((T - R) / 2 ^ (u - n + j)) +
          (T - R) % 2 ^ (u - n + j) := h7.symm
      _ = ((T - R) / 2 ^ (u - n + j)) * 2 ^ (u - n + j) +
          (T - R) % 2 ^ (u - n + j) := by ring
      _ < ((T - R) / 2 ^ (u - n + j)) * 2 ^ (u - n + j) + 2 ^ (u - n + j) :=
        Nat.add_lt_add_left h8 _
      _ = ((T - R) / 2 ^ (u - n + j) + 1) * 2 ^ (u - n + j) := by ring
  have ha2 : a * 2 ^ (u - n + j) ≤ T := by
    have h9 : ((T - R) / 2 ^ (u - n + j)) * 2 ^ (u - n + j) ≤ T - R :=
      Nat.div_mul_le_self (T - R) (2 ^ (u - n + j))
    have h10 : a * 2 ^ (u - n + j) =
        ((T - R) / 2 ^ (u - n + j)) * 2 ^ (u - n + j) + 2 ^ (u - n + j) := by ring
    calc
      a * 2 ^ (u - n + j) =
          ((T - R) / 2 ^ (u - n + j)) * 2 ^ (u - n + j) + 2 ^ (u - n + j) := h10
      _ ≤ T - R + 2 ^ (u - n + j) := Nat.add_le_add_right (by omega) _
      _ ≤ T - R + R := Nat.add_le_add_left hj1 _
      _ = T := by omega
  have ha3 : a < 2 ^ (n - j + 1) := by
    have h14 : a * 2 ^ (u - n + j) < 2 ^ (n - j + 1) * 2 ^ (u - n + j) := by
      calc
        a * 2 ^ (u - n + j) < 2 ^ (u + 1) := lt_of_le_of_lt ha2 hT
        _ = 2 ^ (n - j + 1 + (u - n + j)) := by
          congr 1
          omega
        _ = 2 ^ (n - j + 1) * 2 ^ (u - n + j) := by rw [Nat.pow_add]
    exact Nat.lt_of_mul_lt_mul_right h14
  exact ⟨j, a, h_j_le_n, ha3, hj1, hj2, ha1, ha2⟩

/-- Replay all program emissions up to a finite tick, retaining the latest program of length
at most `n`. -/
private def lastProgramReplay (B : Base) (n : ℕ) : ℕ → BitString
  | 0 => []
  | t + 1 => (eventAt B (t + 1)).elim
      (lastProgramReplay B n t)
      (fun e => if e.2.2.1.length ≤ n then e.2.2.1
        else lastProgramReplay B n t)

/-- The finite replay of program events is computable uniformly in the length budget and the
tick. -/
private lemma lastProgramReplay_computable (B : Base) :
    Computable₂ (lastProgramReplay B) := by
  have hselect : Primrec (fun p : (ℕ × BitString) × Option TimedEvent =>
      p.2.elim p.1.2 (fun e => if e.2.2.1.length ≤ p.1.1 then e.2.2.1 else p.1.2)) := by
    have h : Primrec (fun p : (ℕ × BitString) × Option TimedEvent =>
        Option.casesOn (motive := fun _ => BitString) p.2 p.1.2
          (fun e => if e.2.2.1.length ≤ p.1.1 then e.2.2.1 else p.1.2)) := by
      apply Primrec.option_casesOn Primrec.snd (Primrec.snd.comp Primrec.fst)
      apply Primrec.ite
      · exact Primrec.nat_le.comp
          (Primrec.list_length.comp (Primrec.fst.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      · exact Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact h.of_eq (fun p => by cases p.2 <;> rfl)
  have hstep : Computable (fun p : (ℕ × ℕ) × (ℕ × BitString) =>
      (eventAt B (p.2.1 + 1)).elim p.2.2
        (fun e => if e.2.2.1.length ≤ p.1.1 then e.2.2.1 else p.2.2)) := by
    have hev : Computable (fun p : (ℕ × ℕ) × (ℕ × BitString) =>
        eventAt B (p.2.1 + 1)) :=
      (canonical_enumeration_spec_tables B).2.2.comp
        (Computable.succ.comp (Computable.fst.comp Computable.snd))
    have hargs : Computable (fun p : (ℕ × ℕ) × (ℕ × BitString) =>
        ((p.1.1, p.2.2), eventAt B (p.2.1 + 1))) :=
      ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).pair hev
    exact (hselect.to_comp.comp hargs).of_eq (fun _ => rfl)
  have hrec := Computable.nat_rec (σ := BitString)
    (show Computable (fun p : ℕ × ℕ => p.2) from Computable.snd)
    (Computable.const ([] : BitString)) hstep.to₂
  exact hrec.of_eq (fun p => by
    induction p.2 with
    | zero => rfl
    | succ t ih => simp only [lastProgramReplay, ih])

/-- After a valid marker, the replay retains precisely that marker, since no later short
program can emit. -/
private lemma lastProgramReplay_eq (B : Base) (n : ℕ)
    (hvalid : validCandidate B n (markerCandidate B n) = true)
    (hlater : ∀ t > markerTick B n, ∀ i p x,
      eventAt B t = some (t, i, p, x) → n < p.length)
    (t : ℕ) (ht : markerTick B n ≤ t) :
    lastProgramReplay B n t = lastProgram B n := by
  obtain ⟨hlen, i, x, he⟩ :=
    (canonical_enumeration_spec_candidate B n (markerCandidate B n)).mp hvalid
  change (lastProgram B n).length ≤ n at hlen
  change eventAt B (markerTick B n) =
    some (markerTick B n, i, lastProgram B n, x) at he
  have hpos := (canonical_enumeration_spec_position B he).1
  induction t, ht using Nat.le_induction with
  | base =>
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hs, lastProgramReplay]
    rw [hs] at he
    simp only [he, Option.elim_some, hlen, ite_true]
  | succ t ht ih =>
    rw [lastProgramReplay]
    cases hev : eventAt B (t + 1) with
    | none => exact ih
    | some e =>
      have het := (canonical_enumeration_spec_sound B hev).1
      obtain ⟨te, i, p, x⟩ := e
      dsimp at het
      subst te
      have hlen' := hlater (t + 1) (by omega) i p x hev
      simpa only [Option.elim_some, Nat.not_le_of_lt hlen', ite_false] using ih

/-- Each bounded output set is completely visible at some finite tick. -/
private lemma exists_stageCount_ge_simpleCount (B : Base) (u : ℕ) :
    ∃ t, simpleCount B.V u ≤ stageCount B u t := by
  classical
  have hf := (simple_finite_card_lt B.V u).1
  have hex : ∀ x ∈ hf.toFinset, ∃ t, x ∈ stageOutputs B u t := by
    intro x hx
    exact (canonical_enumeration_spec_union B u x).mp (hf.mem_toFinset.mp hx)
  choose tick htick using hex
  let t := hf.toFinset.attach.sup (fun x => tick x.1 x.2)
  refine ⟨t, ?_⟩
  have hsub : hf.toFinset ⊆ stageOutputs B u t := by
    intro x hx
    have hxt : tick x hx ≤ t := Finset.le_sup (f := fun x => tick x.1 x.2)
      (Finset.mem_attach hf.toFinset ⟨x, hx⟩)
    exact (canonical_enumeration_spec_mono B u hxt).1 (htick x hx)
  have hcard := Finset.card_le_card hsub
  simpa only [simpleCount, stageCount, Set.ncard_eq_toFinset_card _ hf] using hcard

/-- A decoder with raw count advice: it first computes the upper scale `u` from the conditional
input `bits n`, then searches for the first tick at which the advised count is reached, and
returns the replay at that tick. -/
private def tailBoundDecoder (B : Base) (f : ℕ →. ℕ) : Map :=
  fun py =>
    let n := (Milovanov.decodeNat py.2).getD 0
    (f n).bind fun u =>
      (Nat.rfind (fun t => Part.some (decide
        (bitsToNat py.1 * 2 ^ (u + 1 - py.1.length) ≤
          stageCount B u t)))).map (lastProgramReplay B n)

/-- The fixed scale map, the count search and the finite replay form a partial computable
decoder. -/
private lemma tailBoundDecoder_partrec
    (B : Base) (f : ℕ →. ℕ) (hf : Partrec f) :
    Partrec (tailBoundDecoder B f) := by
  have hn : Computable (fun py : BitString × BitString =>
      (Milovanov.decodeNat py.2).getD 0) :=
    Computable.option_getD (bits_computable.2.comp Computable.snd) (Computable.const 0)
  have hamount : Primrec (fun p : BitString × ℕ =>
      bitsToNat p.1 * 2 ^ (p.2 + 1 - p.1.length)) :=
    Primrec.nat_mul.comp (bitsToNat_primrec.comp Primrec.fst)
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.succ.comp Primrec.snd)
          (Primrec.list_length.comp Primrec.fst)))
  have htest : Computable (fun p : ((BitString × BitString) × ℕ) × ℕ =>
      decide (bitsToNat p.1.1.1 * 2 ^ (p.1.2 + 1 - p.1.1.1.length) ≤
        stageCount B p.1.2 p.2)) := by
    have hargs : Computable (fun p : ((BitString × BitString) × ℕ) × ℕ =>
        (p.1.1.1, p.1.2)) :=
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.comp Computable.fst)
    have hA : Computable (fun p : ((BitString × BitString) × ℕ) × ℕ =>
        bitsToNat p.1.1.1 * 2 ^ (p.1.2 + 1 - p.1.1.1.length)) :=
      (hamount.to_comp.comp hargs).of_eq (fun _ => rfl)
    have hC : Computable (fun p : ((BitString × BitString) × ℕ) × ℕ =>
        stageCount B p.1.2 p.2) :=
      (canonical_enumeration_spec_outputs B).2.1.comp
        (Computable.snd.comp Computable.fst) Computable.snd
    have hle : Computable₂ (fun a b : ℕ => decide (a ≤ b)) :=
      Primrec.nat_le.decide.to_comp
    exact (hle.comp hA hC).of_eq (fun _ => rfl)
  have hsearch := Partrec.rfind htest.partrec.to₂
  have hpost : Computable (fun p : ((BitString × BitString) × ℕ) × ℕ =>
      lastProgramReplay B
        ((Milovanov.decodeNat p.1.1.2).getD 0) p.2) :=
    (lastProgramReplay_computable B).comp
      (hn.comp (Computable.fst.comp Computable.fst)) Computable.snd
  exact (hf.comp hn).bind (hsearch.map hpost.to₂).to₂

/-- Count advice strictly beyond the marker's count, and at most the total count, makes the
decoder return the marker. -/
private lemma tailBoundDecoder_produces
    (B : Base) (f : ℕ →. ℕ) (n u a b : ℕ)
    (hvalid : validCandidate B n (markerCandidate B n) = true)
    (hlater : ∀ t > markerTick B n, ∀ i p x,
      eventAt B t = some (t, i, p, x) → n < p.length)
    (hu : u ∈ f n) (ha : a < 2 ^ b)
    (hA : stageCount B u (markerTick B n) < a * 2 ^ (u + 1 - b))
    (hT : a * 2 ^ (u + 1 - b) ≤ simpleCount B.V u) :
    produces (tailBoundDecoder B f)
      (chunkAddress a b) (bits n) (lastProgram B n) := by
  dsimp [produces, tailBoundDecoder]
  rw [decodeNat_bits, Option.getD_some, Part.mem_bind_iff]
  refine ⟨u, hu, ?_⟩
  rw [bitsToNat_chunkAddress, chunkAddress_length a b ha]
  obtain ⟨s, hs⟩ := exists_stageCount_ge_simpleCount B u
  have hstop : ∃ t, a * 2 ^ (u + 1 - b) ≤ stageCount B u t :=
    ⟨s, hT.trans hs⟩
  let t := Nat.find hstop
  have htmem : t ∈ Nat.rfind (fun t => Part.some
      (decide (a * 2 ^ (u + 1 - b) ≤ stageCount B u t))) := by
    let test : ℕ →. Bool := fun t => Part.some
      (decide (a * 2 ^ (u + 1 - b) ≤ stageCount B u t))
    change t ∈ Nat.rfind test
    rw [Nat.mem_rfind]
    constructor
    · simp only [test, Part.mem_some_iff]
      exact (decide_eq_true (Nat.find_spec hstop)).symm
    · intro s hs
      simp only [test, Part.mem_some_iff]
      exact (decide_eq_false (Nat.find_min hstop hs)).symm
  have hmt : markerTick B n ≤ t := by
    by_contra h
    have hle : t ≤ markerTick B n := by omega
    have hc := (canonical_enumeration_spec_mono B u hle).2
    have ht : a * 2 ^ (u + 1 - b) ≤ stageCount B u t := Nat.find_spec hstop
    omega
  have hret := lastProgramReplay_eq B n hvalid hlater t hmt
  rw [Part.mem_map_iff]
  exact ⟨t, htmem, hret⟩

/-- By optimality of `B.V`, the marker has conditional complexity at most the raw count-advice
length plus a fixed decoder constant. -/
private lemma exists_condK_lastProgram_le
    (B : Base) (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ cD : ℕ, ∀ n u a b,
      validCandidate B n (markerCandidate B n) = true →
      (∀ t > markerTick B n, ∀ i p x,
        eventAt B t = some (t, i, p, x) → n < p.length) →
      u ∈ f n → a < 2 ^ b →
      stageCount B u (markerTick B n) < a * 2 ^ (u + 1 - b) →
      a * 2 ^ (u + 1 - b) ≤ simpleCount B.V u →
      condK B.V (lastProgram B n) (bits n) ≤ ((b + cD : ℕ) : ENat) := by
  obtain ⟨cD, hcD⟩ := B.optimalV.2 _
    (tailBoundDecoder_partrec B f hf)
  refine ⟨cD, fun n u a b hvalid hlater hu ha hA hT => ?_⟩
  have hprod := tailBoundDecoder_produces B f n u a b hvalid hlater hu ha hA hT
  have hK : condK (tailBoundDecoder B f)
      (lastProgram B n) (bits n) ≤ (b : ENat) := by
    apply (condK_le_iff _ _ _ b).mpr
    exact ⟨chunkAddress a b, by rw [programLength, chunkAddress_length a b ha], hprod⟩
  calc
    condK B.V (lastProgram B n) (bits n) ≤
        condK (tailBoundDecoder B f)
          (lastProgram B n) (bits n) + (cD : ENat) := hcD _ _
    _ ≤ (b : ENat) + (cD : ENat) := add_le_add hK le_rfl
    _ = ((b + cD : ℕ) : ENat) := by simp

/-- A fixed partial computable scale map has an exponential bound on its post-marker tail.
Blueprint node `lem:tail`. The additive exponent constant is quantified before both scales. -/
theorem last_program_tail_bound (B : Base) (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ cF n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ u, u ∈ f n → n < u →
      rest B n u ≤ 2 ^ (u - n + cF) := by
  obtain ⟨cD, hD⟩ := exists_condK_lastProgram_le B f hf
  obtain ⟨nV, h32V, hV⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨nL, h32L, hL⟩ := last_program_stabilizes_short_descriptions_no_later B
  obtain ⟨cW, nW, h32W, hW⟩ := last_program_conditional_complexity B
  refine ⟨cD + cW + 2, max nV (max nL nW), by omega, ?_⟩
  intro n hn u hu hnu
  have hnV : nV ≤ n := by omega
  have hnL : nL ≤ n := by omega
  have hnW : nW ≤ n := by omega
  let R := rest B n u
  let T := simpleCount B.V u
  have hT : T < 2 ^ (u + 1) := (simple_finite_card_lt B.V u).2
  have hcount : stageCount B u (markerTick B n) + R = T :=
    stageCount_add_rest_eq_simpleCount B n u
  have hR : R ≤ T := by omega
  by_cases hsmall : R < 2 ^ (u - n)
  · exact (Nat.le_of_lt hsmall).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  · have hlarge : 2 ^ (u - n) ≤ R := by omega
    obtain ⟨j, a, hj, ha, hjR, hjR2, hTR, hAT⟩ :=
      exists_count_threshold n u R T hnu hR hT hlarge
    let b := n - j + 1
    have hb : u + 1 - b = u - n + j := by dsimp [b]; omega
    have hA : stageCount B u (markerTick B n) < a * 2 ^ (u + 1 - b) := by
      rw [hb]
      omega
    have hAT' : a * 2 ^ (u + 1 - b) ≤ simpleCount B.V u := by
      rw [hb]
      exact hAT
    have hK := hD n u a b (hV n hnV).1 (hL n hnL) hu ha hA hAT'
    have hlow := (hW n hnW).2.1
    have hcast : (n : ENat) ≤ ((b + cD + cW : ℕ) : ENat) := by
      calc
        (n : ENat) ≤ condK B.V (lastProgram B n) (bits n) + (cW : ENat) := hlow
        _ ≤ ((b + cD : ℕ) : ENat) + (cW : ENat) := add_le_add hK le_rfl
        _ = ((b + cD + cW : ℕ) : ENat) := by simp
    have hnat : n ≤ b + cD + cW := ENat.natCast_le_natCast.mp hcast
    have hjbound : j ≤ cD + cW + 1 := by dsimp [b] at hnat; omega
    exact (Nat.le_of_lt hjR2).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

/-- The partial scale map of an advice program `p`: run `B.V` on `p` with condition `bits n` and
decode the output as a natural number. -/
private def adviceScaleMap (B : Base) (p : BitString) : ℕ →. ℕ :=
  fun n => (B.V (p, bits n)).bind (fun w => Part.ofOption (decodeNat w))

/-- Each fixed advice program gives a partial recursive scale map. -/
private lemma adviceScaleMap_partrec
    (B : Base) (p : BitString) :
    Partrec (adviceScaleMap B p) := by
  have h1 : Computable (fun n : ℕ => (p, bits n)) :=
    (Computable.const p).pair bits_computable.1
  have h2 : Partrec (fun n : ℕ => B.V (p, bits n)) :=
    B.optimalV.1.comp h1
  have h3 : Partrec₂ (fun (_ : ℕ) (w : BitString) => Part.ofOption (decodeNat w)) :=
    (Computable.ofOption (bits_computable.2.comp Computable.snd)).to₂
  exact h2.bind h3

/-- The tail bound is uniform over the finite family of advice programs of bounded length. -/
private lemma exists_uniform_adviceScaleMap_bound
    (B : Base) (advice : ℕ) :
    ∃ cA n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ p u,
      p.length ≤ advice →
      u ∈ adviceScaleMap B p n → n < u →
      rest B n u ≤ 2 ^ (u - n + cA) := by
  have h := fun p => last_program_tail_bound B _ (adviceScaleMap_partrec B p)
  choose cF n0 h32 hF using h
  let s := (boundedPrograms advice).toFinset
  use s.sup cF, max 32 (s.sup n0)
  constructor
  · exact le_max_left 32 (s.sup n0)
  · intro n hn p u hplen hpu hnu
    have hps : p ∈ s := by
      rw [List.mem_toFinset, mem_boundedPrograms_iff]
      exact hplen
    have hcF : cF p ≤ s.sup cF := Finset.le_sup hps
    have hn0 : n0 p ≤ s.sup n0 := Finset.le_sup hps
    have hn0_le_n : n0 p ≤ n := le_trans hn0 (le_max_right 32 (s.sup n0) |>.trans hn)
    have hrest := hF p n hn0_le_n u hpu hnu
    refine le_trans hrest (Nat.pow_le_pow_right (by decide) ?_)
    omega

/-- Bounded conditional complexity of `bits u` given `bits n` supplies a short advice program
whose scale map sends `n` to `u`. -/
private lemma exists_short_program_adviceScaleMap
    (B : Base) (advice n u : ℕ) :
    condK B.V (bits u) (bits n) ≤ (advice : ENat) →
    ∃ p : BitString, p.length ≤ advice ∧
      u ∈ adviceScaleMap B p n := by
  intro h
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff B.V (bits u) (bits n) advice).mp h
  use p
  constructor
  · exact hp_len
  · dsimp [adviceScaleMap]
    rw [Part.mem_bind_iff]
    use bits u
    constructor
    · exact hp_prod
    · simp [decodeNat_bits]

/-- Bounded conditional advice for the upper scale gives a uniform exponential tail bound.
Blueprint node `lem:tail`. The advice budget is fixed before the scales and the constant. -/
theorem last_program_tail_bound_advice (B : Base) (advice : ℕ) :
    ∃ cA n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ u, n < u →
      condK B.V (bits u) (bits n) ≤ (advice : ENat) →
      rest B n u ≤ 2 ^ (u - n + cA) := by
  obtain ⟨cA, n₀, hn₀, h2⟩ := exists_uniform_adviceScaleMap_bound B advice
  use cA, n₀, hn₀
  intro n hn u hlt hcond
  obtain ⟨p, hplen, hpu⟩ := exists_short_program_adviceScaleMap B advice n u hcond
  exact h2 n hn p u hplen hpu hlt

/-- At exponential upper scale the post-marker tail has a fixed integer multiplicative budget.
Blueprint node `cor:tail-budget`. -/
theorem exponential_tail_budget (B : Base) :
    ∃ c₁ n₀ : ℕ, 1 ≤ c₁ ∧ 32 ≤ n₀ ∧ ∀ n ≥ n₀,
      rest B n (2 ^ n) ≤ c₁ * 2 ^ (2 ^ n - n) := by
  have hf : Partrec (fun n : ℕ => (Part.some (2 ^ n) : Part ℕ)) :=
    Kolmogorov.primrec_two_pow_aux.to_comp.partrec
  obtain ⟨cF, n₀, hn₀, h⟩ :=
    last_program_tail_bound B (fun n => Part.some (2 ^ n)) hf
  refine ⟨2 ^ cF, n₀, Nat.one_le_two_pow, hn₀, fun n hn => ?_⟩
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have h1 := h n hn (2 ^ n) (Part.mem_some _) hlt
  calc rest B n (2 ^ n) ≤ 2 ^ (2 ^ n - n + cF) := h1
    _ = 2 ^ cF * 2 ^ (2 ^ n - n) := by rw [pow_add, mul_comm]

/-- Finding the first string of length `n + 1` that is missing from a list is primitive
recursive. -/
private theorem firstMissingString_primrec :
    Primrec (fun v : ℕ × List BitString =>
      (allStrings (v.1 + 1)).find? (fun s => decide (s ∉ v.2))) := by
  have hlist : Primrec (fun v : ℕ × List BitString => allStrings (v.1 + 1)) :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.succ.comp Primrec.fst)
  have hnotmem : Primrec₂ (fun (v : ℕ × List BitString) (s : BitString) =>
      decide (s ∉ v.2)) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂.of_eq ?_
    intro v s
    simp
  exact list_find?_primrec hlist hnotmem

/-- Testing whether a list of prefix observations contains the key `(p, b)` is primitive
recursive. -/
private theorem observationKeySeen_primrec :
    Primrec (fun v : (BitString × BitString) × List PrefixObservation =>
      v.2.any (fun e => decide (e.1 = v.1))) := by
  refine list_any_primrec Primrec.snd ?_
  have h : Primrec (fun q : ((BitString × BitString) × List PrefixObservation) ×
      PrefixObservation => decide (q.2.1 = q.1.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).decide
  exact h.to₂

/-- Parse the decoder input `pairCode (bits n) (pairCode (bits b.length) (b ++ p))`
into `(n, b, p)`. -/
private def parseDecoderInput (w : BitString) :
    Option (ℕ × BitString × BitString) :=
  (decodeNat (decodeFirst w)).bind fun n =>
    (decodeNat (decodeFirst (decodeSecond w))).map fun m =>
      (n, (decodeSecond (decodeSecond w)).take m, (decodeSecond (decodeSecond w)).drop m)

/-- `parseDecoderInput` inverts the encoding of the triple `(n, b, p)`. -/
private theorem parseDecoderInput_pairCode (n : ℕ) (b p : BitString) :
    parseDecoderInput (pairCode (bits n) (pairCode (bits b.length) (b ++ p))) =
      some (n, b, p) := by
  simp [parseDecoderInput, decodeFirst_pairCode, decodeSecond_pairCode, decodeNat_bits]

/-- Parsing the decoder input is computable. -/
private theorem parseDecoderInput_computable : Computable parseDecoderInput := by
  have h1 : Computable (fun w : BitString => decodeNat (decodeFirst w)) :=
    bits_computable.2.comp decodeFirst_computable
  have h2 : Computable (fun w : BitString => decodeNat (decodeFirst (decodeSecond w))) :=
    bits_computable.2.comp (decodeFirst_computable.comp decodeSecond_computable)
  have h5 : Primrec (fun z : (BitString × ℕ) × ℕ =>
      (z.1.2, (List.take z.2 (decodeSecond (decodeSecond z.1.1)),
        List.drop z.2 (decodeSecond (decodeSecond z.1.1))))) := by
    have hr : Primrec (fun z : (BitString × ℕ) × ℕ => decodeSecond (decodeSecond z.1.1)) :=
      CodedFiniteDistribution.decodeSecond_primrec.comp
        (CodedFiniteDistribution.decodeSecond_primrec.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (primrec_list_take.comp hr Primrec.snd)
        (primrec_list_drop.comp hr Primrec.snd))
  have h4 : Computable₂ (fun (w : BitString) (n : ℕ) =>
      (decodeNat (decodeFirst (decodeSecond w))).map fun m =>
        (n, (decodeSecond (decodeSecond w)).take m, (decodeSecond (decodeSecond w)).drop m)) := by
    have h6 : Computable (fun z : BitString × ℕ => decodeNat (decodeFirst (decodeSecond z.1))) :=
      h2.comp Computable.fst
    have h7 := Computable.option_map h6 h5.to_comp.to₂
    exact h7
  exact Computable.option_bind h1 h4

/-- The first numeric tick at which some D observation with key `(p, b)` has been recorded. -/
private def firstObservationTick (B : Base) (b p : BitString) : Part ℕ :=
  Nat.rfind (fun t => Part.some ((prefixHistory B t).any (fun e => decide (e.1 = (p, b)))))

/-- The decoder: parse `(n, b, p)`, find the first tick `s` of the key `(p, b)`, and output the
first string of length `n + 1` that is not among the outputs `stageOutputs B n s`. -/
private def missingOutputDecoder (B : Base) : Map := fun qy =>
  (Part.ofOption (parseDecoderInput qy.1)).bind fun v =>
    (firstObservationTick B v.2.1 v.2.2).bind fun s =>
      Part.ofOption ((allStrings (v.1 + 1)).find? (fun x => decide (x ∉ stageOutputList B v.1 s)))

/-- The decoder `missingOutputDecoder B` is partial computable. -/
private theorem missingOutputDecoder_partrec (B : Base) :
    Partrec (missingOutputDecoder B) := by
  have hparse : Partrec (fun qy : BitString × BitString =>
      (Part.ofOption (parseDecoderInput qy.1) : Part (ℕ × BitString × BitString))) := by
    have h : Computable (fun qy : BitString × BitString => parseDecoderInput qy.1) :=
      parseDecoderInput_computable.comp Computable.fst
    exact h.ofOption
  have hph : Computable (prefixHistory B) := (canonical_enumeration_spec_tables B).2.1
  have hseen : Computable₂ (fun (z : (BitString × BitString) × (ℕ × BitString × BitString))
      (t : ℕ) => (prefixHistory B t).any (fun e => decide (e.1 = (z.2.2.2, z.2.2.1)))) := by
    have hkey : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
        (u.1.2.2.2, u.1.2.2.1)) :=
      Computable.pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        Computable.fst))) (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        Computable.fst)))
    have hH : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
        prefixHistory B u.2) := hph.comp Computable.snd
    have h := observationKeySeen_primrec.to_comp.comp
      (Computable.pair hkey hH)
    exact h
  have hfirst : Partrec (fun z : (BitString × BitString) × (ℕ × BitString × BitString) =>
      firstObservationTick B z.2.2.1 z.2.2.2) :=
    Partrec.rfind hseen.partrec₂
  have hn : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
      u.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hout : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
      stageOutputList B u.1.2.1 u.2) :=
    Computable₂.comp (canonical_enumeration_spec_outputs B).1 hn Computable.snd
  have hpair : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
      (u.1.2.1, stageOutputList B u.1.2.1 u.2)) := Computable.pair hn hout
  have hopt : Computable (fun u : ((BitString × BitString) × (ℕ × BitString × BitString)) × ℕ =>
      (allStrings (u.1.2.1 + 1)).find?
        (fun x => decide (x ∉ stageOutputList B u.1.2.1 u.2))) := by
    have h := firstMissingString_primrec.to_comp.comp hpair
    exact h
  have hlast : Partrec₂ (fun (z : (BitString × BitString) × (ℕ × BitString × BitString))
      (s : ℕ) => (Part.ofOption ((allStrings (z.2.1 + 1)).find?
        (fun x => decide (x ∉ stageOutputList B z.2.1 s))) : Part BitString)) := hopt.ofOption
  have hmid : Partrec₂ (fun (qy : BitString × BitString) (v : ℕ × BitString × BitString) =>
      (firstObservationTick B v.2.1 v.2.2).bind fun s =>
        Part.ofOption ((allStrings (v.1 + 1)).find?
          (fun x => decide (x ∉ stageOutputList B v.1 s)))) := Partrec.bind hfirst hlast
  exact Partrec.bind hparse hmid

/-- There is an auxiliary plain decoder.  On the input
`pairCode (bits n) (pairCode (bits b.length) (b ++ p))` it recomputes the first tick `s` at which
the D observation `(p, b)` appears, replays `V` to that tick and outputs a string missing from
`stageOutputs B n s`. -/
private lemma exists_missing_stage_output_decoder (B : Base) :
    ∃ Dec : Map, Partrec Dec ∧ ∀ (n : ℕ) (b p : BitString) (s : ℕ),
      (∃ a, ((p, b), a) ∈ prefixHistory B s) →
      (∀ t < s, ∀ a, ((p, b), a) ∉ prefixHistory B t) →
      ∃ x : BitString, x ∉ stageOutputs B n s ∧
        x ∈ Dec (pairCode (bits n) (pairCode (bits b.length) (b ++ p)), []) := by
  refine ⟨missingOutputDecoder B, missingOutputDecoder_partrec B, ?_⟩
  intro n b p s ⟨a, ha⟩ hmin
  have hnodup : (stageOutputList B n s).Nodup := by
    unfold stageOutputList
    exact nodup_eraseDups_list _
  have hlen : (stageOutputList B n s).length < 2 ^ (n + 1) := by
    have h1 : (stageOutputList B n s).length = (stageOutputs B n s).card := by
      unfold stageOutputs
      exact (List.toFinset_card_of_nodup hnodup).symm
    have hsub : ((stageOutputs B n s : Finset BitString) : Set BitString) ⊆
        {x | Simple B.V x n} := fun x hx =>
      (canonical_enumeration_spec_union B n x).mpr ⟨s, Finset.mem_coe.mp hx⟩
    obtain ⟨hfin, hcard⟩ := simple_finite_card_lt B.V n
    have h2 : (stageOutputs B n s).card ≤ simpleCount B.V n := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub hfin
    omega
  obtain ⟨x0, hx0all, hx0missing⟩ := exists_mem_allStrings_not_mem_of_length_lt hnodup hlen
  obtain ⟨x, hxfind⟩ : ∃ x, (allStrings (n + 1)).find?
      (fun y => decide (y ∉ stageOutputList B n s)) = some x :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨x0, hx0all, by simp [hx0missing]⟩)
  have hxnot : x ∉ stageOutputList B n s := by simpa using List.find?_some hxfind
  refine ⟨x, ?_, ?_⟩
  · unfold stageOutputs
    rw [List.mem_toFinset]
    exact hxnot
  · have hany : ∀ t, (prefixHistory B t).any (fun e => decide (e.1 = (p, b))) = true ↔
        ∃ a', ((p, b), a') ∈ prefixHistory B t := by
      intro t
      rw [List.any_eq_true]
      constructor
      · rintro ⟨e, he, hdec⟩
        rw [decide_eq_true_eq] at hdec
        exact ⟨e.2, by rw [← hdec]; exact he⟩
      · rintro ⟨a', ha'⟩
        exact ⟨_, ha', by simp⟩
    have hsearch : s ∈ firstObservationTick B b p := by
      unfold firstObservationTick
      refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
      · rw [Part.mem_some_iff]
        exact ((hany s).mpr ⟨a, ha⟩).symm
      · intro t ht
        rw [Part.mem_some_iff]
        have hnot : ¬ (prefixHistory B t).any (fun e => decide (e.1 = (p, b))) = true :=
          fun h => by
            obtain ⟨a', ha'⟩ := (hany t).mp h
            exact hmin t ht a' ha'
        exact (Bool.eq_false_iff.mpr hnot).symm
    unfold missingOutputDecoder
    simp only [parseDecoderInput_pairCode]
    rw [Part.mem_bind_iff]
    refine ⟨(n, b, p), Part.mem_ofOption.mpr rfl, ?_⟩
    rw [Part.mem_bind_iff]
    refine ⟨s, hsearch, ?_⟩
    exact Part.mem_ofOption.mpr hxfind

/-- The bit string `bits t` is at most `⌈log₂ (t + 2)⌉` long. -/
private theorem bits_length_le_clog_two (t : ℕ) :
    (bits t).length ≤ Nat.clog 2 (t + 2) := by
  have h4 := length_integerCode_le t
  have h3 : (integerCode t).length = 2 * (bits t).length + 1 := by
    dsimp [integerCode]
    rw [length_sd]
  omega

/-- The decoder input is shorter than `n` by any fixed constant, for large `n`. -/
private theorem exists_pairCode_length_add_le (cD cDec : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a b p : BitString, 2 * (a.length + b.length) < n →
      p.length ≤ a.length + 2 * Nat.clog 2 (a.length + 2) + cD →
      (pairCode (bits n) (pairCode (bits b.length) (b ++ p))).length + cDec ≤ n := by
  refine ⟨256 + 8 * (cD + cDec + 2), fun n hn a b p hab hp => ?_⟩
  have hk : n + 2 ≤ 2 ^ (n / 16 + 2) := by
    have h16 : 16 ≤ n / 16 := by omega
    have h := four_mul_add_five_le_two_pow (n / 16) h16
    calc n + 2 ≤ 4 * (4 * (n / 16) + 5) := by omega
      _ ≤ 4 * 2 ^ (n / 16) := Nat.mul_le_mul_left 4 h
      _ = 2 ^ (n / 16 + 2) := by ring
  have hL : Nat.clog 2 (n + 2) ≤ n / 16 + 2 := Nat.clog_le_of_le_pow hk
  have hbn : (bits n).length ≤ Nat.clog 2 (n + 2) :=
    bits_length_le_clog_two n
  have hbb : (bits b.length).length ≤ Nat.clog 2 (n + 2) :=
    (bits_length_le_clog_two _).trans
      (Nat.clog_mono_right 2 (by omega))
  have hca : Nat.clog 2 (a.length + 2) ≤ Nat.clog 2 (n + 2) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [length_pairCode, List.length_append]
  omega

/-- For large `n`, every short relevant program has halted by the marker tick. -/
private lemma eventually_short_programs_halt_by_marker (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ a b p : BitString,
      2 * (a.length + b.length) < n →
      p.length ≤ literalBound B a →
      produces B.D p b a →
      ((p, b), a) ∈ prefixHistory B (markerTick B n) := by
  classical
  obtain ⟨n1, h32, hstab⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨Dec, hDec, hspec⟩ := exists_missing_stage_output_decoder B
  obtain ⟨cDec, hcDec⟩ := B.optimalV.2 Dec hDec
  obtain ⟨n2, hn2⟩ := exists_pairCode_length_add_le B.cD cDec
  refine ⟨max n1 n2, le_trans h32 (le_max_left _ _), ?_⟩
  intro n hn a b p hab hp hprod
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2' : n2 ≤ n := le_trans (le_max_right _ _) hn
  have hex : ∃ t, ∃ a', ((p, b), a') ∈ prefixHistory B t := by
    obtain ⟨t, ht⟩ := (canonical_enumeration_spec_prefix B p b a).mp hprod
    exact ⟨t, a, ht⟩
  have hs1 : ∃ a', ((p, b), a') ∈ prefixHistory B (Nat.find hex) := Nat.find_spec hex
  have hs2 : ∀ t < Nat.find hex, ∀ a', ((p, b), a') ∉ prefixHistory B t :=
    fun t ht a' ha' => Nat.find_min hex ht ⟨a', ha'⟩
  by_cases hle : Nat.find hex ≤ markerTick B n
  · obtain ⟨a', ha'⟩ := hs1
    have hmem : ((p, b), a') ∈ prefixHistory B (markerTick B n) :=
      (canonical_enumeration_spec_prefix_mono B hle).subset ha'
    have h1 : produces B.D p b a' := (canonical_enumeration_spec_prefix B p b a').mpr ⟨_, ha'⟩
    have ha'a : a' = a := Part.mem_unique h1 hprod
    rw [ha'a] at hmem
    exact hmem
  · exfalso
    have hlt : markerTick B n < Nat.find hex := not_le.mp hle
    obtain ⟨x, hxnot, hxDec⟩ := hspec n b p (Nat.find hex) hs1 hs2
    have hlen := hn2 n hn2' a b p hab hp
    have h1 : condK Dec x [] ≤
        (((pairCode (bits n) (pairCode (bits b.length) (b ++ p))).length : ℕ) : ENat) :=
      sInf_le ⟨_, hxDec, rfl⟩
    have h2 : plainK B.V x ≤ (n : ENat) := by
      calc plainK B.V x = condK B.V x [] := rfl
        _ ≤ condK Dec x [] + (cDec : ENat) := hcDec x []
        _ ≤ (((pairCode (bits n) (pairCode (bits b.length) (b ++ p))).length : ℕ) : ENat) +
              (cDec : ENat) := add_le_add h1 le_rfl
        _ ≤ (n : ENat) := by exact_mod_cast hlen
    have hsimple : x ∈ ((stageOutputs B n (markerTick B n) : Finset BitString) :
        Set BitString) := by
      rw [((hstab n hn1).2 n le_rfl)]
      exact h2
    exact hxnot ((canonical_enumeration_spec_mono B n hlt.le).1 hsimple)


/-- Short objects have exact conditional prefix complexity at the true marker's numeric tick.
Blueprint node `lem:short-prefix-exact`. The default is the fixed literal bound from `Base`. -/
theorem marker_stage_prefix_complexity_exact (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ a b : BitString,
      2 * (a.length + b.length) < n →
      (stagePrefixComplexity B (markerTick B n) a b : ENat) = KP B.D a b := by
  obtain ⟨n₀, hn₀, h_halt⟩ := eventually_short_programs_halt_by_marker B
  use n₀, hn₀
  intro n hn a b hab
  have h_bound_eq := canonical_enumeration_spec_prefix_bound B (markerTick B n) a b
  have h_bound : KP B.D a b ≤ literalBound B a := by
    calc
      KP B.D a b ≤ (stagePrefixComplexity B (markerTick B n) a b : ENat) := h_bound_eq.1
      _ ≤ (literalBound B a : ENat) := by exact_mod_cast h_bound_eq.2
  have h_ne_top : KP B.D a b ≠ ⊤ := by
    intro h_eq
    rw [h_eq] at h_bound
    have h_top_le := top_le_iff.mp h_bound
    exact ENat.top_ne_natCast _ h_top_le.symm
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top (M := B.D) (x := a) (y := b) h_ne_top
  have hp_len_le : p.length ≤ literalBound B a := by
    have h_p_len : (p.length : ENat) = KP B.D a b := by exact_mod_cast hp_len
    have h_p_le_enat : (p.length : ENat) ≤ (literalBound B a : ENat) := by
      calc (p.length : ENat) = KP B.D a b := h_p_len
        _ ≤ (literalBound B a : ENat) := h_bound
    exact_mod_cast h_p_le_enat
  have h_in_history := h_halt n hn a b p hab hp_len_le hp_prod
  have h_min := (canonical_enumeration_spec_prefix_min B (markerTick B n)
    (KP B.D a b).toNat a b).mpr
  have h_ex : ∃ p_1, ((p_1, b), a) ∈ prefixHistory B (markerTick B n) ∧
      p_1.length ≤ literalBound B a ∧ p_1.length ≤ (KP B.D a b).toNat := by
    use p
    refine ⟨h_in_history, hp_len_le, ?_⟩
    have h_p_len : p.length = (KP B.D a b).toNat := by
      have h1 : (p.length : ENat) = KP B.D a b := by exact_mod_cast hp_len
      have h2 : ENat.toNat (p.length : ENat) = ENat.toNat (KP B.D a b) := congrArg ENat.toNat h1
      rwa [ENat.toNat_natCast] at h2
    rw [h_p_len]
  have h_le_kp : stagePrefixComplexity B (markerTick B n) a b ≤ (KP B.D a b).toNat := by
    apply h_min
    right
    exact h_ex
  have h_le_kp_enat : (stagePrefixComplexity B (markerTick B n) a b : ENat) ≤ KP B.D a b := by
    have h_kp_eq : KP B.D a b = ((KP B.D a b).toNat : ENat) := by
      exact (ENat.natCast_toNat h_ne_top).symm
    rw [h_kp_eq]
    exact_mod_cast h_le_kp
  exact le_antisymm h_le_kp_enat h_bound_eq.1

/-- Exactness through the total witnessed-candidate interface requires the true marker program.
Blueprint node `lem:short-prefix-exact`. The supplied timestamp is checked, not guessed. -/
theorem marker_stage_prefix_complexity_exact_candidate (B : Base) :
    ∃ n₀ : ℕ, 32 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ candidate : Candidate,
      validCandidate B n candidate = true → candidate.1 = lastProgram B n →
      ∀ a b : BitString, 2 * (a.length + b.length) < n →
        (candidatePrefixComplexity B n candidate a b : ENat) = KP B.D a b := by
  obtain ⟨n₀_ex, hn₀_ex, hex⟩ := marker_stage_prefix_complexity_exact B
  obtain ⟨n₀_pos, hn₀_pos, hpos⟩ := last_program_stabilizes_short_descriptions_position B
  use max n₀_ex n₀_pos
  refine ⟨le_max_of_le_left hn₀_ex, fun n hn candidate hcand hprog a b hab => ?_⟩
  have hn_ex : n ≥ n₀_ex := le_trans (le_max_left _ _) hn
  have hn_pos : n ≥ n₀_pos := le_trans (le_max_right _ _) hn
  have hex' := hex n hn_ex a b hab
  have hpos' := hpos n hn_pos
  obtain ⟨_hpos_len, x, hx⟩ := hpos'
  have hcand_iff := (canonical_enumeration_spec_candidate B n candidate).mp hcand
  obtain ⟨_hlen, i, y, hy⟩ := hcand_iff
  rw [hprog] at hy
  have h_unique := canonical_enumeration_spec_unique B hx hy
  obtain ⟨h_tick, _h_pos, _h_val⟩ := h_unique
  rw [candidatePrefixComplexity]
  simp only [hcand, ite_true]
  rw [← h_tick]
  exact hex'

/-- One threshold covers all fixed-machine marker assertions before any padding is chosen.
Blueprint node `lem:short-prefix-exact`. This packages the shared `n₀ ≥ 32` convention. -/
theorem marker_stage_prefix_complexity_exact_common (B : Base) :
    ∃ n₀ cW c₁ : ℕ, 32 ≤ n₀ ∧ 1 ≤ c₁ ∧ ∀ n ≥ n₀,
      validCandidate B n (markerCandidate B n) = true ∧
      (∀ k ≤ n, (stageOutputs B k (markerTick B n) : Set BitString) =
        {x | Simple B.V x k}) ∧
      (∀ t > markerTick B n, ∀ i p x,
        eventAt B t = some (t, i, p, x) → n < p.length) ∧
      (eventHistory B (markerTick B n)).length = markerPosition B n + 1 ∧
      (lastProgram B n).length ≤ n ∧
      (n : ENat) ≤ condK B.V (lastProgram B n) (bits n) + cW ∧
      condK B.V (lastProgram B n) (bits n) ≤ (n : ENat) + cW ∧
      rest B n (2 ^ n) ≤ c₁ * 2 ^ (2 ^ n - n) ∧
      ∀ a b : BitString, 2 * (a.length + b.length) < n →
        (stagePrefixComplexity B (markerTick B n) a b : ENat) = KP B.D a b := by
  obtain ⟨n1, h32_1, h1⟩ := last_program_stabilizes_short_descriptions B
  obtain ⟨n2, h32_2, h2⟩ := last_program_stabilizes_short_descriptions_no_later B
  obtain ⟨n3, h32_3, h3⟩ := last_program_stabilizes_short_descriptions_position B
  obtain ⟨cW, n4, h32_4, h4⟩ := last_program_conditional_complexity B
  obtain ⟨c1, n5, hc1, h32_5, h5⟩ := exponential_tail_budget B
  obtain ⟨n6, h32_6, h6⟩ := marker_stage_prefix_complexity_exact B
  use max n1 (max n2 (max n3 (max n4 (max n5 n6)))), cW, c1
  refine ⟨?_, hc1, fun n hn => ?_⟩
  · exact le_trans h32_1 (le_max_left n1 _)
  · have hn1 : n1 ≤ n := by
      calc
        n1 ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_left n1 _
        _ ≤ n := hn
    have hn2 : n2 ≤ n := by
      calc
        n2 ≤ max n2 (max n3 (max n4 (max n5 n6))) := le_max_left n2 _
        _ ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_right n1 _
        _ ≤ n := hn
    have hn3 : n3 ≤ n := by
      calc
        n3 ≤ max n3 (max n4 (max n5 n6)) := le_max_left n3 _
        _ ≤ max n2 (max n3 (max n4 (max n5 n6))) := le_max_right n2 _
        _ ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_right n1 _
        _ ≤ n := hn
    have hn4 : n4 ≤ n := by
      calc
        n4 ≤ max n4 (max n5 n6) := le_max_left n4 _
        _ ≤ max n3 (max n4 (max n5 n6)) := le_max_right n3 _
        _ ≤ max n2 (max n3 (max n4 (max n5 n6))) := le_max_right n2 _
        _ ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_right n1 _
        _ ≤ n := hn
    have hn5 : n5 ≤ n := by
      calc
        n5 ≤ max n5 n6 := le_max_left n5 n6
        _ ≤ max n4 (max n5 n6) := le_max_right n4 _
        _ ≤ max n3 (max n4 (max n5 n6)) := le_max_right n3 _
        _ ≤ max n2 (max n3 (max n4 (max n5 n6))) := le_max_right n2 _
        _ ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_right n1 _
        _ ≤ n := hn
    have hn6 : n6 ≤ n := by
      calc
        n6 ≤ max n5 n6 := le_max_right n5 n6
        _ ≤ max n4 (max n5 n6) := le_max_right n4 _
        _ ≤ max n3 (max n4 (max n5 n6)) := le_max_right n3 _
        _ ≤ max n2 (max n3 (max n4 (max n5 n6))) := le_max_right n2 _
        _ ≤ max n1 (max n2 (max n3 (max n4 (max n5 n6)))) := le_max_right n1 _
        _ ≤ n := hn
    rcases h4 n hn4 with ⟨h4a, h4b, h4c⟩
    exact ⟨(h1 n hn1).1, (h1 n hn1).2, h2 n hn2, (h3 n hn3).1, h4a, h4b, h4c, h5 n hn5, h6 n hn6⟩

end Kolmogorov.Milovanov
