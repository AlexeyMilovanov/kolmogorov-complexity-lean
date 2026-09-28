import KolmogorovMathlib.AlgorithmicRandomness.Cantor
import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasure

/-!
# Recovering a computable branch from a semimeasure lower bound

If `a` is a lower-semicomputable continuous tree semimeasure and `w` is an
infinite binary sequence all of whose prefixes carry mass at least a fixed
`ε > 0`, then `w` is computable.

The argument is elementary.  Let `L = ⨅ n, a (w ↾ n)`; it is positive and
finite, and the values `a (w ↾ n)` decrease to `L`.  Pick a dyadic threshold
`η = 2⁻ʲ < L` and a level `N` with `a (w ↾ N) < L + η`.  Beyond level `N` the
sibling of the branch carries mass `< η`, because it competes with `a (w ↾ m+1)
≥ L` inside `a (w ↾ m) < L + η`.  Consequently, for `n ≥ N`, the prefix `w ↾ n`
is the *unique* string of length `n` extending `w ↾ N` with mass `> η`
(`eq_cantorPrefix_of_threshold`).

Since `a` is lower semicomputable, the property `η < a x` is semi-decidable, so
the unique extension can be found by an unbounded search; this is what
`computable_of_threshold` implements with `Nat.rfind`.
-/

open scoped ENNReal
open Encodable

namespace Kolmogorov

/-! ### Prefix bookkeeping -/

/-! ### The analytic step: a unique heavy extension -/

section Analysis

variable {a : BitString → ℝ≥0∞} {w : CantorSeq}

/-- Beyond the level `N` where the branch mass has almost settled, the sibling
of the branch is light. -/
private lemma sibling_lt (ha : IsContinuousTreeSemimeasure a) {L η : ℝ≥0∞}
    (hL_top : L ≠ ⊤) (hL : ∀ n, L ≤ a (cantorPrefix w n)) {N : ℕ}
    (hN : a (cantorPrefix w N) < L + η) {m : ℕ} (hm : N ≤ m) :
    a (cantorPrefix w m ++ [!(w m)]) < η := by
  set y := cantorPrefix w m ++ [!(w m)] with hy
  have hchildren := ha.2 (cantorPrefix w m)
  have hpair : a y + a (cantorPrefix w (m + 1)) ≤ a (cantorPrefix w m) := by
    rw [cantorPrefix_succ]
    cases hbit : w m
    · simpa [hy, hbit, add_comm] using hchildren
    · simpa [hy, hbit] using hchildren
  have hmono : a (cantorPrefix w m) ≤ a (cantorPrefix w N) :=
    ha.antitone_of_prefix (cantorPrefix_mono w hm)
  have hkey : a y + L < η + L := by
    calc a y + L ≤ a y + a (cantorPrefix w (m + 1)) := add_le_add le_rfl (hL (m + 1))
      _ ≤ a (cantorPrefix w m) := hpair
      _ ≤ a (cantorPrefix w N) := hmono
      _ < L + η := hN
      _ = η + L := add_comm _ _
  exact (ENNReal.add_lt_add_iff_right hL_top).mp hkey

/-- **Unique heavy extension.**  There are a threshold `2⁻ʲ` and a level `N`
such that every prefix of `w` is heavier than the threshold, while for `n ≥ N`
the prefix `w ↾ n` is the only string of length `n` extending `w ↾ N` whose mass
exceeds the threshold. -/
theorem exists_threshold_level (ha : IsContinuousTreeSemimeasure a) {ε : ℝ≥0∞}
    (hε : 0 < ε) (hb : ∀ n, ε ≤ a (cantorPrefix w n)) :
    ∃ N j : ℕ, (∀ n, (2 : ℝ≥0∞)⁻¹ ^ j < a (cantorPrefix w n)) ∧
      ∀ n, N ≤ n → ∀ x : BitString, x.length = n → cantorPrefix w N <+: x →
        (2 : ℝ≥0∞)⁻¹ ^ j < a x → x = cantorPrefix w n := by
  set L : ℝ≥0∞ := ⨅ n, a (cantorPrefix w n) with hLdef
  have hL_le : ∀ n, L ≤ a (cantorPrefix w n) := fun n => iInf_le _ n
  have hL_pos : 0 < L := lt_of_lt_of_le hε (le_iInf hb)
  have hL_top : L ≠ ⊤ := by
    have h1 : L ≤ a (cantorPrefix w 0) := hL_le 0
    have h2 : a (cantorPrefix w 0) ≤ 1 := ha.le_one _
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (h1.trans h2)
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_two_pow_lt hL_pos.ne'
  set η : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ j with hηdef
  have hη_pos : 0 < η := ENNReal.pow_pos (by simp) _
  have hfirst : ∀ n, η < a (cantorPrefix w n) := fun n => lt_of_lt_of_le hj (hL_le n)
  have hlt : L < L + η := ENNReal.lt_add_right hL_top hη_pos.ne'
  obtain ⟨N, hN⟩ := iInf_lt_iff.mp hlt
  refine ⟨N, j, hfirst, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro x hlen hpre _
    exact (hpre.eq_of_length (by rw [hlen, cantorPrefix_length])).symm ▸ rfl
  | succ n hn ih =>
    intro x hlen hpre hgt
    have hx_ne : x ≠ [] := by
      intro h
      rw [h] at hlen
      simp at hlen
    obtain ⟨x', b, rfl⟩ : ∃ x' b, x = x' ++ [b] := by
      rcases List.eq_nil_or_concat x with h1 | ⟨y, c, hy⟩
      · exact absurd h1 hx_ne
      · exact ⟨y, c, by simpa using hy⟩
    have hlen' : x'.length = n := by simpa using hlen
    have hpre' : cantorPrefix w N <+: x' := by
      have hN_le : N ≤ x'.length := by rw [hlen']; exact hn
      have h1 : cantorPrefix w N = (x' ++ [b]).take (cantorPrefix w N).length :=
        List.prefix_iff_eq_take.mp hpre
      rw [cantorPrefix_length] at h1
      rw [List.take_append_of_le_length hN_le] at h1
      exact h1 ▸ List.take_prefix _ _
    have hgt' : η < a x' := lt_of_lt_of_le hgt (ha.antitone_of_prefix ⟨[b], rfl⟩)
    have hx' : x' = cantorPrefix w n := ih x' hlen' hpre' hgt'
    subst hx'
    by_cases hb' : b = w n
    · rw [hb', cantorPrefix_succ]
    · exfalso
      have hbnot : b = !(w n) := by
        cases hbb : b <;> cases hww : w n <;> simp_all
      rw [hbnot] at hgt
      exact absurd hgt (not_lt.mpr (le_of_lt (sibling_lt ha hL_top hL_le hN hn)))

end Analysis

/-! ### The search -/

/-- The candidate string coded by `t`: the fixed prefix `σ` extended by the
string coded by the second component of `t`. -/
def searchCandidate (σ : BitString) (t : ℕ) : BitString :=
  σ ++ ((decode (α := BitString) (Nat.unpair t).2).getD [])

private lemma searchCandidate_computable (σ : BitString) :
    Computable (fun p : ℕ × ℕ => searchCandidate σ p.2) := by
  have hz : Computable (fun p : ℕ × ℕ =>
      ((decode (α := BitString) (Nat.unpair p.2).2).getD [])) :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
      (Computable.const [])
  exact Primrec.list_append.to_comp.comp (Computable.const σ) hz

private lemma searchStage_computable : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).1) :=
  (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp

private lemma searchApprox_computable (σ : BitString)
    (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2))
    (u : ℕ × ℕ → ℕ) (hu : Computable u) :
    Computable (fun p : ℕ × ℕ => approx (u p) (searchCandidate σ p.2) []) :=
  hcomp.comp (hu.pair ((searchCandidate_computable σ).pair (Computable.const [])))

/-- The search predicate: at stage `s = (t).1`, the candidate coded by `t` has
the right length and its stage-`s` approximation already exceeds `2⁻ʲ`. -/
def searchPred (σ : BitString) (approx : ℕ → BitString → BitString → ℕ) (j n t : ℕ) : Bool :=
  decide ((searchCandidate σ t).length = σ.length + n + 1) &&
    decide (2 ^ (Nat.unpair t).1 <
      approx (Nat.unpair t).1 (searchCandidate σ t) [] * 2 ^ j)

private lemma searchLen_computable (σ : BitString) :
    Computable (fun p : ℕ × ℕ =>
      decide ((searchCandidate σ p.2).length = σ.length + p.1 + 1)) :=
  (PrimrecRel.decide Primrec.eq).to_comp.comp
    (Primrec.list_length.to_comp.comp (searchCandidate_computable σ))
    (Primrec.succ.to_comp.comp
      ((Primrec.nat_add.comp (Primrec.const σ.length) Primrec.fst).to_comp))

private lemma searchNum_computable (σ : BitString) (j : ℕ)
    (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2))
    (u : ℕ × ℕ → ℕ) (hu : Computable u) :
    Computable (fun p : ℕ × ℕ =>
      decide (2 ^ u p < approx (u p) (searchCandidate σ p.2) [] * 2 ^ j)) := by
  have hpow : Computable (fun p : ℕ × ℕ => 2 ^ u p) :=
    primrec_two_pow_aux.to_comp.comp hu
  have hmul : Computable (fun p : ℕ × ℕ =>
      approx (u p) (searchCandidate σ p.2) [] * 2 ^ j) :=
    (Primrec.nat_mul.comp Primrec.id (Primrec.const (2 ^ j))).to_comp.comp
      (searchApprox_computable σ approx hcomp u hu)
  exact (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hpow hmul

private lemma searchPred_computable (σ : BitString) (j : ℕ)
    (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable₂ (searchPred σ approx j) :=
  Primrec.and.to_comp.comp (searchLen_computable σ)
    (searchNum_computable σ j approx hcomp _ searchStage_computable)

/-- The bit produced by the search: the `n`-th bit of the first heavy candidate
found. -/
noncomputable def searchBit (σ : BitString) (approx : ℕ → BitString → BitString → ℕ)
    (j n : ℕ) : Part Bool :=
  (Nat.rfind fun t => (searchPred σ approx j n t : Part Bool)).map
    fun t => (searchCandidate σ t).getD n false

private lemma searchBit_partrec (σ : BitString) (j : ℕ)
    (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Partrec (searchBit σ approx j) := by
  have hout : Computable₂ (fun n t : ℕ => (searchCandidate σ t).getD n false) := by
    have hcand : Computable (fun p : ℕ × ℕ => searchCandidate σ p.2) :=
      searchCandidate_computable σ
    exact (Primrec.list_getD false).to_comp.comp hcand Computable.fst
  exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ (searchPred_computable σ j approx hcomp)))
    hout

/-! ### Numeric threshold bookkeeping -/

private lemma inv_two_pow_lt_dyadicValue_iff (j m s : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ j < dyadicValue m s ↔ 2 ^ s < m * 2 ^ j := by
  rw [dyadicValue, ← ENNReal.inv_pow,
    ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp))]
  rw [show ((2 : ℝ≥0∞) ^ j)⁻¹ * 2 ^ s = (2 : ℝ≥0∞) ^ s / 2 ^ j by
    rw [ENNReal.div_eq_inv_mul]]
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp))]
  constructor
  · intro h
    have : ((2 ^ s : ℕ) : ℝ≥0∞) < ((m * 2 ^ j : ℕ) : ℝ≥0∞) := by push_cast; exact h
    exact_mod_cast this
  · intro h
    have : ((2 ^ s : ℕ) : ℝ≥0∞) < ((m * 2 ^ j : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    push_cast at this
    exact this

/-! ### From the threshold data to computability -/

/-- A sequence all of whose prefixes carry semimeasure above `2 ^ (-j)`, and which from some length
on is the only such extension of its own prefix, is computable. -/
theorem computable_of_threshold {a : BitString → ℝ≥0∞} {w : CantorSeq}
    (hlsc : IsLSC (fun x _ => a x)) {N j : ℕ}
    (h1 : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ j < a (cantorPrefix w n))
    (h2 : ∀ n, N ≤ n → ∀ x : BitString, x.length = n → cantorPrefix w N <+: x →
      (2 : ℝ≥0∞)⁻¹ ^ j < a x → x = cantorPrefix w n) :
    Computable w := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  set σ : BitString := cantorPrefix w N with hσ
  have hσ_len : σ.length = N := by rw [hσ, cantorPrefix_length]
  have hsup' : ∀ x : BitString, (⨆ s, dyadicValue (approx s x []) s) = a x :=
    fun x => hsup x []
  have hheavy : ∀ x : BitString,
      ((2 : ℝ≥0∞)⁻¹ ^ j < a x ↔ ∃ s, 2 ^ s < approx s x [] * 2 ^ j) := by
    intro x
    constructor
    · intro hx
      rw [← hsup' x] at hx
      obtain ⟨s, hs⟩ := lt_iSup_iff.mp hx
      exact ⟨s, (inv_two_pow_lt_dyadicValue_iff j _ s).mp hs⟩
    · rintro ⟨s, hs⟩
      have hds : (2 : ℝ≥0∞)⁻¹ ^ j < dyadicValue (approx s x []) s :=
        (inv_two_pow_lt_dyadicValue_iff j _ s).mpr hs
      refine lt_of_lt_of_le hds ?_
      rw [← hsup' x]
      exact le_iSup (fun s => dyadicValue (approx s x []) s) s
  -- every witness of the search predicate produces the true branch
  have hsound : ∀ n t : ℕ, searchPred σ approx j n t = true →
      searchCandidate σ t = cantorPrefix w (N + n + 1) := by
    intro n t ht
    rw [searchPred, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
    obtain ⟨hlen, hnum⟩ := ht
    rw [hσ_len] at hlen
    refine h2 (N + n + 1) (by omega) _ hlen ?_ ?_
    · exact ⟨(decode (α := BitString) (Nat.unpair t).2).getD [], rfl⟩
    · exact (hheavy _).mpr ⟨(Nat.unpair t).1, hnum⟩
  -- the search terminates
  have hcomplete : ∀ n : ℕ, ∃ t, searchPred σ approx j n t = true := by
    intro n
    have hpre : σ <+: cantorPrefix w (N + n + 1) :=
      cantorPrefix_mono w (by omega)
    obtain ⟨z, hz⟩ := hpre
    obtain ⟨s, hs⟩ := (hheavy (cantorPrefix w (N + n + 1))).mp (h1 (N + n + 1))
    refine ⟨Nat.pair s (encode z), ?_⟩
    have hcand : searchCandidate σ (Nat.pair s (encode z)) = cantorPrefix w (N + n + 1) := by
      rw [searchCandidate, Nat.unpair_pair]
      simp [hz]
    rw [searchPred, hcand, Nat.unpair_pair]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by rw [cantorPrefix_length, hσ_len], hs⟩
  have hbit : ∀ n : ℕ, searchBit σ approx j n = Part.some (w n) := by
    intro n
    rw [Part.eq_some_iff]
    have hdom : (Nat.rfind fun t => (searchPred σ approx j n t : Part Bool)).Dom := by
      rw [Nat.rfind_dom]
      obtain ⟨t, ht⟩ := hcomplete n
      exact ⟨t, by simpa using ht, fun {m} _ => trivial⟩
    set t := (Nat.rfind fun t => (searchPred σ approx j n t : Part Bool)).get hdom with htdef
    have htmem : t ∈ (Nat.rfind fun t => (searchPred σ approx j n t : Part Bool)) :=
      Part.get_mem hdom
    have hspec := Nat.rfind_spec htmem
    have ht : searchPred σ approx j n t = true := by simpa using hspec
    have hcand := hsound n t ht
    rw [searchBit]
    refine Part.mem_map_iff _ |>.mpr ⟨t, htmem, ?_⟩
    rw [hcand]
    have hlt : n < N + n + 1 := by omega
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [cantorPrefix_length]; omega)]
    simp
  have hpart : Partrec (searchBit σ approx j) := searchBit_partrec σ j approx hcomp
  exact hpart.of_eq hbit

/-- **A branch of uniformly positive mass is computable.** -/
theorem computable_of_branch_lower_bound {a : BitString → ℝ≥0∞} {w : CantorSeq}
    (ha : IsLowerSemicomputableContinuousSemimeasure a) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hb : ∀ n, ε ≤ a (cantorPrefix w n)) :
    Computable w := by
  obtain ⟨N, j, h1, h2⟩ := exists_threshold_level ha.1 hε hb
  exact computable_of_threshold ha.2 h1 h2

end Kolmogorov
