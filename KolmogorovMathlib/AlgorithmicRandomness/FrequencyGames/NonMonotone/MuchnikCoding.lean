/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.BoundedBetStrategy

/-!
# Muchnik Coding

Coding lemmas for the argument that a sequence of relative prefix dimension below `β < 1` is
not Kolmogorov--Loveland random relative to the oracle.  The module contains the coding
estimates for pairs of strings, the finite chain construction (`finite_chain`), the splitting
of a sequence into two halves (`split`), and the final enumeration (`enumeration`) of strings
of small relative complexity.  The enumeration satisfies Kraft's inequality on its finite
subsets and meets every tail of a sequence of relative dimension below `β` in arbitrarily
long prefixes.

This is a technical part of the treatment of betting strategies and randomness in the book by
Shen, Uspensky and Vereshchagin, *Kolmogorov complexity and algorithmic randomness*.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- `Nat.size` of a sum. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_size_add (a b : ℕ) :
    Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have hb : b < 2 ^ Nat.size b := Nat.lt_size_self b
  have h1 : 2 ^ Nat.size a ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  have h2 : 2 ^ Nat.size b ≤ 2 ^ (Nat.size a + Nat.size b) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  calc a + b < 2 ^ Nat.size a + 2 ^ Nat.size b := Nat.add_lt_add ha hb
    _ ≤ 2 ^ (Nat.size a + Nat.size b) + 2 ^ (Nat.size a + Nat.size b) := Nat.add_le_add h1 h2
    _ = 2 ^ (Nat.size a + Nat.size b + 1) := by rw [pow_succ]; ring

/-- Relative prefix complexity is at most twice the length plus a constant. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_length_bound (B : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString, PointToSet.oracleComplexity B x ≤ 2 * x.length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec B).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have hb : KPPlain (PointToSet.optimalOraclePrefix B) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix B) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ (2 * (x.length : ℕ∞) + c₂) + c₁ := by gcongr; exact hc₂ x
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using hb)

/-- An oracle prefix description can encode an ordinary shortest plain program with a
self-delimiting description of its length. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_prefix_cost
    (A : Set ℕ) (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x : BitString,
      PointToSet.oracleComplexity A x ≤ (plainK V x).toNat +
        2 * (Nat.bits (plainK V x).toNat).length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₁ + c₂ + c₃, fun x => ?_⟩
  have hfinite : plainK V x ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainK_le_length V hV
    exact ne_top_of_le_natCast_add (hc x)
  have hx : plainK V x = ((plainK V x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfinite).symm
  have h : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      (((plainK V x).toNat + 2 * (Nat.bits (plainK V x).toNat).length +
        (c₁ + c₂ + c₃) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          KPPlain U (Nat.bits (plainK V x).toNat) + c₂ + c₁ := by
        gcongr
        exact hc₂ x _ hx
      _ ≤ ((plainK V x).toNat : ℕ∞) +
          (2 * ((Nat.bits (plainK V x).toNat).length : ℕ∞) + c₃) + c₂ + c₁ := by
        gcongr
        exact hc₃ _
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using h)

/-- The relative prefix complexity of the binary expansion of `j` is `|bin j| + O(log |bin j|)`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_nat_cost (B : Set ℕ) :
    ∃ c : ℕ, ∀ j : ℕ, PointToSet.oracleComplexity B (Nat.bits j) ≤
      Nat.size j + 2 * Nat.size (Nat.size j) + c := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨c₁, hc₁⟩ := not_isMisesKLRandom_of_plainK_lt_yside_prefix_cost B V hV
  obtain ⟨c₂, hc₂⟩ := plainK_le_length V hV
  refine ⟨c₁ + c₂ + 2 * (Nat.size c₂ + 1), fun j => ?_⟩
  have h1 := hc₁ (Nat.bits j)
  have h2 : (plainK V (Nat.bits j)).toNat ≤ Nat.size j + c₂ := by
    have h := hc₂ (Nat.bits j)
    have h' : plainK V (Nat.bits j) ≤ (((Nat.bits j).length + c₂ : ℕ) : ℕ∞) := by
      simpa [programLength] using h
    have := ENat.toNat_le_of_le_natCast h'
    rw [Nat.size_eq_bits_len] at this
    exact this
  have h3 : (Nat.bits (plainK V (Nat.bits j)).toNat).length ≤
      Nat.size (Nat.size j) + Nat.size c₂ + 1 := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size h2).trans (not_isMisesKLRandom_of_plainK_lt_yside_size_add _ _)
  omega

/-- The relation `K^A(<X↾h, y'>) ≤ m` is relatively enumerable in `A'`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_R (A A' : Set ℕ)
    (hA : RecursiveIn {charOracle A'} (charOracle A))
    (X : CantorSeq) (hX : ComputableIn {charOracle A'} (fun h : ℕ => cantorPrefix X h)) :
    PointToSet.IsREIn A' (fun p : ℕ × ℕ × BitString =>
      PointToSet.oracleComplexity A (pairCode (cantorPrefix X p.1) p.2.2) ≤ p.2.1) := by
  have h1 : PointToSet.IsREIn A' (fun iq : BitString × ℚ =>
      (PointToSet.oracleComplexity A iq.1 : ℝ) < (iq.2 : ℝ)) :=
    (PointToSet.isREIn_oracleComplexity_lt A).mono_oracle hA
  have hf : ComputableIn {charOracle A'} (fun p : ℕ × ℕ × BitString =>
      (pairCode (cantorPrefix X p.1) p.2.2, ((p.2.1 + 1 : ℕ) : ℚ))) := by
    have hpair : Computable (fun q : BitString × BitString => pairCode q.1 q.2) :=
      pairCode_computable
    have hq1 : ComputableIn {charOracle A'} (fun p : ℕ × ℕ × BitString => cantorPrefix X p.1) :=
      hX.comp ComputableIn.fst
    have hq2 : ComputableIn {charOracle A'} (fun p : ℕ × ℕ × BitString => p.2.2) :=
      (Computable.snd.comp Computable.snd).computableIn
    have hq3 : ComputableIn {charOracle A'}
        (fun p : ℕ × ℕ × BitString => ((p.2.1 + 1 : ℕ) : ℚ)) :=
      (computable_nat_to_rat.comp (Computable.succ.comp
        (Computable.fst.comp Computable.snd))).computableIn
    exact (hpair.computableIn.comp (hq1.pair hq2)).pair hq3
  have h2 := h1.comp hf
  have heq : (fun p : ℕ × ℕ × BitString =>
      PointToSet.oracleComplexity A (pairCode (cantorPrefix X p.1) p.2.2) ≤ p.2.1) =
      (fun p : ℕ × ℕ × BitString =>
        (PointToSet.oracleComplexity A (pairCode (cantorPrefix X p.1) p.2.2) : ℝ) <
          ((((p.2.1 + 1 : ℕ) : ℚ)) : ℝ)) := by
    funext p
    apply propext
    push_cast
    constructor
    · intro h
      exact_mod_cast Nat.lt_succ_of_le h
    · intro h
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h)
  rw [heq]
  exact h2

/-- A computable function applied to an oracle-computable one is oracle-computable. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside_comp
    {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) {f : β → σ} {g : α → β} (hf : Computable f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => f (g a)) :=
  hf.computableIn.comp hg

/-- Stage entry `o` of an enumeration of triples `(h, m, y)` has tag `p = (h, m)`. -/
private def not_isMisesKLRandom_of_plainK_lt_yside_tag
    (o : Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) : Bool :=
  decide (o.map (fun q => (q.1, q.2.1)) = some p)

private lemma not_isMisesKLRandom_of_plainK_lt_yside_tag_iff
    (o : Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) :
    not_isMisesKLRandom_of_plainK_lt_yside_tag o p = true ↔ ∃ y, o = some (p.1, p.2, y) := by
  cases o with
  | none => simp [not_isMisesKLRandom_of_plainK_lt_yside_tag]
  | some q =>
    obtain ⟨a, b, y⟩ := q
    simp only [not_isMisesKLRandom_of_plainK_lt_yside_tag, Option.map_some, Option.some.injEq,
      decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p1, p2⟩ := p
      simp only [Prod.mk.injEq] at h
      exact ⟨y, by simp [h.1, h.2]⟩
    · rintro ⟨y', hy'⟩
      simp only [Prod.mk.injEq] at hy'
      exact Prod.ext hy'.1 hy'.2.1

/-- The value of a stage entry (the string component). -/
private def not_isMisesKLRandom_of_plainK_lt_yside_val (o : Option (ℕ × ℕ × BitString)) :
    BitString :=
  (o.map (fun q => q.2.2)).getD []

/-- Number of stages `r < s` whose entry has tag `p`. -/
private def not_isMisesKLRandom_of_plainK_lt_yside_cnt
    (E : ℕ → Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s +
      cond (not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) p) 1 0

/-- Stage `s` lists an entry of tag `t.1` and rank `t.2`. -/
private def not_isMisesKLRandom_of_plainK_lt_yside_hit
    (E : ℕ → Option (ℕ × ℕ × BitString)) (t : (ℕ × ℕ) × ℕ) (s : ℕ) : Bool :=
  not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) t.1 &&
    decide (not_isMisesKLRandom_of_plainK_lt_yside_cnt E t.1 s = t.2)

/-- The entry of tag `t.1` and rank `t.2` of the enumeration. -/
private def not_isMisesKLRandom_of_plainK_lt_yside_rankDecode
    (E : ℕ → Option (ℕ × ℕ × BitString)) (t : (ℕ × ℕ) × ℕ) : Part BitString :=
  (Nat.rfind (fun s => Part.some (not_isMisesKLRandom_of_plainK_lt_yside_hit E t s))).map
    (fun s => not_isMisesKLRandom_of_plainK_lt_yside_val (E s))

private lemma not_isMisesKLRandom_of_plainK_lt_yside_primrec_tag :
    Primrec (fun u : Option (ℕ × ℕ × BitString) × (ℕ × ℕ) =>
      not_isMisesKLRandom_of_plainK_lt_yside_tag u.1 u.2) := by
  unfold not_isMisesKLRandom_of_plainK_lt_yside_tag
  refine primrec_decideEq.comp
    (Primrec.option_map Primrec.fst ?_) (Primrec.option_some.comp Primrec.snd)
  exact ((Primrec.fst.comp Primrec.snd).pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to₂

private lemma not_isMisesKLRandom_of_plainK_lt_yside_primrec_val :
    Primrec (fun o : Option (ℕ × ℕ × BitString) =>
      not_isMisesKLRandom_of_plainK_lt_yside_val o) := by
  unfold not_isMisesKLRandom_of_plainK_lt_yside_val
  exact Primrec.option_getD.comp
    (Primrec.option_map Primrec.id (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂)
    (Primrec.const [])

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_computable
    (B : Set ℕ) (E : ℕ → Option (ℕ × ℕ × BitString)) (hE : ComputableIn {charOracle B} E) :
    ComputableIn {charOracle B}
      (fun a : (ℕ × ℕ) × ℕ => not_isMisesKLRandom_of_plainK_lt_yside_cnt E a.1 a.2) := by
  have hstepFn : Primrec (fun u : Bool × ℕ => u.2 + cond u.1 1 0) :=
    Primrec.nat_add.comp Primrec.snd
      (Primrec.cond Primrec.fst (Primrec.const 1) (Primrec.const 0))
  have hstep : ComputableIn₂ {charOracle B}
      (fun (a : (ℕ × ℕ) × ℕ) (yi : ℕ × ℕ) =>
        yi.2 + cond (not_isMisesKLRandom_of_plainK_lt_yside_tag (E yi.1) a.1) 1 0) := by
    have hE' : ComputableIn {charOracle B}
        (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) => E p.2.1) :=
      hE.comp (Computable.fst.comp Computable.snd).computableIn
    have hp : ComputableIn {charOracle B}
        (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) => p.1.1) :=
      (Computable.fst.comp Computable.fst).computableIn
    have hsnd : ComputableIn {charOracle B}
        (fun p : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) => p.2.2) :=
      (Computable.snd.comp Computable.snd).computableIn
    have htag := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      not_isMisesKLRandom_of_plainK_lt_yside_primrec_tag.to_comp (hE'.pair hp)
    have hfin := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      hstepFn.to_comp (htag.pair hsnd)
    exact hfin
  have hrec := ComputableIn.nat_rec
    (f := fun a : (ℕ × ℕ) × ℕ => a.2) (g := fun _ => (0 : ℕ))
    (h := fun (a : (ℕ × ℕ) × ℕ) (yi : ℕ × ℕ) =>
      yi.2 + cond (not_isMisesKLRandom_of_plainK_lt_yside_tag (E yi.1) a.1) 1 0)
    (Computable.snd.computableIn) (ComputableIn.const 0) hstep
  refine hrec.of_eq (fun a => ?_)
  obtain ⟨p, s⟩ := a
  change @Nat.rec (fun _ => ℕ) 0 (fun y ih => ih +
      cond (not_isMisesKLRandom_of_plainK_lt_yside_tag (E y) p) 1 0) s =
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [not_isMisesKLRandom_of_plainK_lt_yside_cnt]
    rw [← ih]

private lemma not_isMisesKLRandom_of_plainK_lt_yside_rankDecode_partrecIn
    (B : Set ℕ) (E : ℕ → Option (ℕ × ℕ × BitString)) (hE : ComputableIn {charOracle B} E) :
    PartrecIn {charOracle B} (not_isMisesKLRandom_of_plainK_lt_yside_rankDecode E) := by
  have hcnt := not_isMisesKLRandom_of_plainK_lt_yside_cnt_computable B E hE
  have hhit : ComputableIn₂ {charOracle B}
      (fun (t : (ℕ × ℕ) × ℕ) (s : ℕ) => not_isMisesKLRandom_of_plainK_lt_yside_hit E t s) := by
    have hE' : ComputableIn {charOracle B} (fun p : ((ℕ × ℕ) × ℕ) × ℕ => E p.2) :=
      hE.comp (Computable.snd).computableIn
    have hp : ComputableIn {charOracle B} (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1) :=
      (Computable.fst.comp Computable.fst).computableIn
    have htag := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      not_isMisesKLRandom_of_plainK_lt_yside_primrec_tag.to_comp (hE'.pair hp)
    have hc : ComputableIn {charOracle B}
        (fun p : ((ℕ × ℕ) × ℕ) × ℕ => not_isMisesKLRandom_of_plainK_lt_yside_cnt E p.1.1 p.2) :=
      hcnt.comp (((Computable.fst.comp Computable.fst).computableIn).pair
        (Computable.snd).computableIn)
    have hr : ComputableIn {charOracle B} (fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.2) :=
      (Computable.snd.comp Computable.fst).computableIn
    have heq := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      primrec_decideEq.to_comp (hc.pair hr)
    have hfin := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      Primrec.and.to_comp (htag.pair heq)
    exact hfin
  have h1 : PartrecIn {charOracle B} (fun t : (ℕ × ℕ) × ℕ =>
      Nat.rfind (fun s => Part.some (not_isMisesKLRandom_of_plainK_lt_yside_hit E t s))) :=
    PartrecIn.rfind hhit.partrecIn₂
  have h2 : ComputableIn₂ {charOracle B}
      (fun (_ : (ℕ × ℕ) × ℕ) (s : ℕ) => not_isMisesKLRandom_of_plainK_lt_yside_val (E s)) := by
    have hEs : ComputableIn {charOracle B} (fun p : ((ℕ × ℕ) × ℕ) × ℕ => E p.2) :=
      hE.comp (Computable.snd).computableIn
    have hfin := not_isMisesKLRandom_of_plainK_lt_yside_comp {charOracle B}
      not_isMisesKLRandom_of_plainK_lt_yside_primrec_val.to_comp hEs
    exact hfin
  exact PartrecIn.map h1 h2

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_mono
    (E : ℕ → Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) {s s' : ℕ} (h : s ≤ s') :
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s ≤
      not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [not_isMisesKLRandom_of_plainK_lt_yside_cnt]
    exact Nat.le_add_right _ _

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_succ_of_tag
    (E : ℕ → Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) {s : ℕ}
    (ht : not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) p = true) :
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p (s + 1) =
      not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s + 1 := by
  simp [not_isMisesKLRandom_of_plainK_lt_yside_cnt, ht]

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_lt_of_tag
    (E : ℕ → Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) {s s' : ℕ}
    (ht : not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) p = true) (hss : s < s') :
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s + 1 ≤
      not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s' := by
  rw [← not_isMisesKLRandom_of_plainK_lt_yside_cnt_succ_of_tag E p ht]
  exact not_isMisesKLRandom_of_plainK_lt_yside_cnt_mono E p (Nat.succ_le_of_lt hss)

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_eq_card
    (E : ℕ → Option (ℕ × ℕ × BitString)) (p : ℕ × ℕ) (s : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s =
      ((Finset.range s).filter
        (fun r => not_isMisesKLRandom_of_plainK_lt_yside_tag (E r) p = true)).card := by
  induction s with
  | zero => simp [not_isMisesKLRandom_of_plainK_lt_yside_cnt]
  | succ s ih =>
    rw [not_isMisesKLRandom_of_plainK_lt_yside_cnt, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) p = true
    · simp [h, Finset.card_insert_of_notMem]
    · simp [h]

private lemma not_isMisesKLRandom_of_plainK_lt_yside_cnt_le_card
    (E : ℕ → Option (ℕ × ℕ × BitString))
    (hEinj : ∀ s t w, E s = some w → E t = some w → s = t)
    (p : ℕ × ℕ) (T : Finset BitString)
    (hT : ∀ r, not_isMisesKLRandom_of_plainK_lt_yside_tag (E r) p = true →
      not_isMisesKLRandom_of_plainK_lt_yside_val (E r) ∈ T) (s : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_yside_cnt E p s ≤ T.card := by
  rw [not_isMisesKLRandom_of_plainK_lt_yside_cnt_eq_card]
  apply Finset.card_le_card_of_injOn (fun r => not_isMisesKLRandom_of_plainK_lt_yside_val (E r))
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hr
    exact hT r hr.2
  · intro r hr r' hr' hrr'
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hr hr'
    obtain ⟨y, hy⟩ := (not_isMisesKLRandom_of_plainK_lt_yside_tag_iff _ _).mp hr.2
    obtain ⟨y', hy'⟩ := (not_isMisesKLRandom_of_plainK_lt_yside_tag_iff _ _).mp hr'.2
    simp only [not_isMisesKLRandom_of_plainK_lt_yside_val, hy, hy', Option.map_some,
      Option.getD_some] at hrr'
    subst hrr'
    exact hEinj r r' _ hy hy'

private lemma not_isMisesKLRandom_of_plainK_lt_yside_hit_unique
    (E : ℕ → Option (ℕ × ℕ × BitString)) (t : (ℕ × ℕ) × ℕ) {s s' : ℕ}
    (hs : not_isMisesKLRandom_of_plainK_lt_yside_hit E t s = true)
    (hs' : not_isMisesKLRandom_of_plainK_lt_yside_hit E t s' = true) : s = s' := by
  simp only [not_isMisesKLRandom_of_plainK_lt_yside_hit, Bool.and_eq_true,
    decide_eq_true_eq] at hs hs'
  rcases lt_trichotomy s s' with h | h | h
  · have := not_isMisesKLRandom_of_plainK_lt_yside_cnt_lt_of_tag E t.1 hs.1 h
    omega
  · exact h
  · have := not_isMisesKLRandom_of_plainK_lt_yside_cnt_lt_of_tag E t.1 hs'.1 h
    omega

private lemma not_isMisesKLRandom_of_plainK_lt_yside_rankDecode_mem
    (E : ℕ → Option (ℕ × ℕ × BitString)) (h m : ℕ) (y : BitString) (s : ℕ)
    (hs : E s = some (h, m, y)) :
    y ∈ not_isMisesKLRandom_of_plainK_lt_yside_rankDecode E
      ((h, m), not_isMisesKLRandom_of_plainK_lt_yside_cnt E (h, m) s) := by
  have htag : not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) (h, m) = true :=
    (not_isMisesKLRandom_of_plainK_lt_yside_tag_iff _ _).mpr ⟨y, hs⟩
  have hhit : not_isMisesKLRandom_of_plainK_lt_yside_hit E
      ((h, m), not_isMisesKLRandom_of_plainK_lt_yside_cnt E (h, m) s) s = true := by
    simp [not_isMisesKLRandom_of_plainK_lt_yside_hit, htag]
  unfold not_isMisesKLRandom_of_plainK_lt_yside_rankDecode
  rw [Part.mem_map_iff]
  refine ⟨s, ?_, by simp [not_isMisesKLRandom_of_plainK_lt_yside_val, hs]⟩
  refine Nat.mem_rfind.mpr ⟨by simp [hhit], ?_⟩
  intro s' hs'
  rw [Part.mem_some_iff]
  by_contra hne
  have hfalse : ¬ (not_isMisesKLRandom_of_plainK_lt_yside_hit E
      ((h, m), not_isMisesKLRandom_of_plainK_lt_yside_cnt E (h, m) s) s' = false) :=
    fun h' => hne h'.symm
  have htrue : not_isMisesKLRandom_of_plainK_lt_yside_hit E
      ((h, m), not_isMisesKLRandom_of_plainK_lt_yside_cnt E (h, m) s) s' = true := by
    simpa using hfalse
  have := not_isMisesKLRandom_of_plainK_lt_yside_hit_unique E _ hhit htrue
  omega

/-- **Y-side coding bound.**  If `y` is in the (finite, of size `≤ 2 ^ d`) section of strings `y'`
with `K^A(<X↾h, y'>) ≤ m`, then `K^{A'}(y) ≤ d + 2 |m| + 2 |d| + 2 |h| + c`, for oracles `A'`
computing `A` and the prefixes of `X`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_yside
    (A A' : Set ℕ) (hA : RecursiveIn {charOracle A'} (charOracle A))
    (X : CantorSeq) (hX : ComputableIn {charOracle A'} (fun h : ℕ => cantorPrefix X h)) :
    ∃ c : ℕ, ∀ (h m d : ℕ) (y : BitString) (T : Finset BitString), T.card ≤ 2 ^ d →
      (∀ y', PointToSet.oracleComplexity A (pairCode (cantorPrefix X h) y') ≤ m → y' ∈ T) →
      PointToSet.oracleComplexity A (pairCode (cantorPrefix X h) y) ≤ m →
      PointToSet.oracleComplexity A' y ≤
        d + 2 * Nat.size m + 2 * Nat.size d + 2 * Nat.size h + c := by
  obtain ⟨E, ⟨hEc, hEiff⟩, hEinj⟩ :=
    PointToSet.relative_enumeration_injective A' _
      (not_isMisesKLRandom_of_plainK_lt_yside_R A A' hA X hX)
  have hdec : ComputableIn {charOracle A'} (fun xs : List BitString =>
      ((decodeBits xs.headI, decodeBits xs.tail.headI), decodeBits xs.tail.tail.headI)) := by
    have hprim : Primrec (fun xs : List BitString =>
        ((decodeBits xs.headI, decodeBits xs.tail.headI), decodeBits xs.tail.tail.headI)) :=
      ((primrec_decodeBits.comp Primrec.list_headI).pair
        (primrec_decodeBits.comp (Primrec.list_headI.comp Primrec.list_tail))).pair
        (primrec_decodeBits.comp
          (Primrec.list_headI.comp (Primrec.list_tail.comp Primrec.list_tail)))
    exact hprim.to_comp.computableIn
  let F : List BitString →. BitString := fun xs =>
    not_isMisesKLRandom_of_plainK_lt_yside_rankDecode E
      ((decodeBits xs.headI, decodeBits xs.tail.headI), decodeBits xs.tail.tail.headI)
  have hF : PartrecIn {charOracle A'} F :=
    (not_isMisesKLRandom_of_plainK_lt_yside_rankDecode_partrecIn A' E hEc).comp hdec
  obtain ⟨c₁, hc₁⟩ := PointToSet.oracle_tuple_bounds_composition A' 3 F hF
  obtain ⟨c₂, hc₂⟩ := not_isMisesKLRandom_of_plainK_lt_yside_length_bound A'
  obtain ⟨c₃, hc₃⟩ := not_isMisesKLRandom_of_plainK_lt_yside_nat_cost A'
  refine ⟨c₁ + 2 * c₂ + c₃, ?_⟩
  intro h m d y T hT hmem hy
  obtain ⟨s, hs⟩ := (hEiff (h, m, y)).mp hy
  have hfind := not_isMisesKLRandom_of_plainK_lt_yside_rankDecode_mem E h m y s hs
  set j := not_isMisesKLRandom_of_plainK_lt_yside_cnt E (h, m) s with hj
  -- the rank is below `2 ^ d`
  have hjlt : j < 2 ^ d := by
    have htag : not_isMisesKLRandom_of_plainK_lt_yside_tag (E s) (h, m) = true :=
      (not_isMisesKLRandom_of_plainK_lt_yside_tag_iff _ _).mpr ⟨y, hs⟩
    have hsucc := not_isMisesKLRandom_of_plainK_lt_yside_cnt_succ_of_tag E (h, m) htag
    have hle := not_isMisesKLRandom_of_plainK_lt_yside_cnt_le_card E hEinj (h, m) T
      (fun r hr => by
        obtain ⟨v, hv⟩ := (not_isMisesKLRandom_of_plainK_lt_yside_tag_iff _ _).mp hr
        have hvmem : PointToSet.oracleComplexity A
            (pairCode (cantorPrefix X h) v) ≤ m :=
          (hEiff (h, m, v)).mpr ⟨r, hv⟩
        simp only [not_isMisesKLRandom_of_plainK_lt_yside_val, hv, Option.map_some,
          Option.getD_some]
        exact hmem v hvmem) (s + 1)
    omega
  have hmemF : y ∈ F [Nat.bits h, Nat.bits m, Nat.bits j] := by
    simp only [F, List.headI, List.tail_cons, decodeBits_natBits]
    exact hfind
  have key := hc₁ [Nat.bits h, Nat.bits m, Nat.bits j] y rfl hmemF
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at key
  have e1 := hc₂ (Nat.bits h)
  have e2 := hc₂ (Nat.bits m)
  have e3 := hc₃ j
  rw [Nat.size_eq_bits_len] at e1 e2
  have hsj : Nat.size j ≤ d := Nat.size_le.mpr hjlt
  have hss : Nat.size (Nat.size j) ≤ Nat.size d := Nat.size_le_size hsj
  omega

/-- Kraft's inequality for the relative prefix complexity: every finite set of strings has
`∑ 2^{-K^A(x)} ≤ 1`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_kraft (A : Set ℕ) (D : Finset BitString) :
    ∑ x ∈ D, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x ≤ 1 := by
  let U := PointToSet.optimalOraclePrefix A
  have hterm (x : BitString) : complexityWeight (KP U x []) =
      (2 : ENNReal)⁻¹ ^ PointToSet.oracleComplexity A x := by
    rw [← complexityWeight_coe, PointToSet.oracleComplexity,
      PointToSet.oraclePrefixComplexity_coe]
    rfl
  have hsum : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum (fun x => complexityWeight_KP_le_aprioriMeasure U x [])).trans
      (tsum_aprioriMeasure_le_one U [] (PointToSet.exists_optimalOraclePrefix_spec A).2.1)
  have hfinite : ∀ x ∈ D, complexityWeight (KP U x []) ≠ ⊤ := by
    intro x hx
    rw [hterm]
    exact ENNReal.pow_ne_top (by norm_num)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top ((ENNReal.sum_le_tsum D).trans hsum)
  rw [ENNReal.toReal_sum hfinite, ENNReal.toReal_one] at hreal
  simpa only [hterm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using hreal

/-- At most `2 ^ m` strings have relative prefix complexity at most `m`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_card_le (A : Set ℕ) (m : ℕ)
    (D : Finset BitString) (hD : ∀ z ∈ D, PointToSet.oracleComplexity A z ≤ m) :
    D.card ≤ 2 ^ m := by
  have h1 := not_isMisesKLRandom_of_plainK_lt_gen_kraft A D
  have h2 : ∑ x ∈ D, (2 : ℝ)⁻¹ ^ m ≤
      ∑ x ∈ D, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x :=
    Finset.sum_le_sum (fun x hx =>
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hD x hx))
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 : (D.card : ℝ) * (2 : ℝ)⁻¹ ^ m ≤ 1 := h2.trans h1
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have h4 : (D.card : ℝ) ≤ 2 ^ m := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one hpos] at h3
    exact h3
  exact_mod_cast h4

/-- The section `{y' | K^A(⟨x, y'⟩) ≤ m}` is a finite set; its cardinality is between two
consecutive powers of two, and the exponent is at most `m`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_section (A : Set ℕ) (x y : BitString)
    (m : ℕ) (hy : PointToSet.oracleComplexity A (pairCode x y) ≤ m) :
    ∃ (T : Finset BitString) (d : ℕ),
      (∀ y', y' ∈ T ↔ PointToSet.oracleComplexity A (pairCode x y') ≤ m) ∧
      2 ^ d ≤ T.card ∧ T.card < 2 ^ (d + 1) ∧ d ≤ m := by
  have hinj : Function.Injective (fun y' : BitString => pairCode x y') := by
    intro a b h
    exact congrArg Prod.snd (pairCode_injective (a₁ := (x, a)) (a₂ := (x, b)) h)
  have hfin : {y' : BitString | PointToSet.oracleComplexity A (pairCode x y') ≤ m}.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (2 ^ m + 1)
    have hle := not_isMisesKLRandom_of_plainK_lt_gen_card_le A m
      (t.image (fun y' => pairCode x y')) (by
        intro z hz
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz
        exact hts hy')
    rw [Finset.card_image_of_injective _ hinj] at hle
    omega
  have hmem : ∀ y', y' ∈ hfin.toFinset ↔
      PointToSet.oracleComplexity A (pairCode x y') ≤ m := by
    intro y'
    simp
  have hy_mem : y ∈ hfin.toFinset := (hmem y).mpr hy
  have hpos : hfin.toFinset.card ≠ 0 := Finset.card_ne_zero_of_mem hy_mem
  have hcard : hfin.toFinset.card ≤ 2 ^ m := by
    have hle := not_isMisesKLRandom_of_plainK_lt_gen_card_le A m
      (hfin.toFinset.image (fun y' => pairCode x y')) (by
        intro z hz
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz
        exact (hmem y').mp hy')
    rwa [Finset.card_image_of_injective _ hinj] at hle
  refine ⟨hfin.toFinset, Nat.log 2 hfin.toFinset.card, hmem, Nat.pow_log_le_self 2 hpos,
    Nat.lt_pow_succ_log_self (by norm_num) _, ?_⟩
  have h2 : 2 ^ Nat.log 2 hfin.toFinset.card ≤ 2 ^ m :=
    (Nat.pow_log_le_self 2 hpos).trans hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- The binary length of a product is at most the sum of the binary lengths. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_size_mul_le (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- A linear function of `n` has binary length at most `size n` plus a constant. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_size_lin (c n : ℕ) :
    Nat.size (2 * n + c + 1) ≤ Nat.size n + (1 + Nat.size (c + 3)) := by
  have h1 : 2 * n + c + 1 ≤ (n + 1) * (c + 3) := by nlinarith
  have h2 : Nat.size (n + 1) ≤ Nat.size n + 1 := by
    rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self n
    omega
  calc Nat.size (2 * n + c + 1) ≤ Nat.size ((n + 1) * (c + 3)) := Nat.size_le_size h1
    _ ≤ Nat.size (n + 1) + Nat.size (c + 3) :=
        not_isMisesKLRandom_of_plainK_lt_gen_size_mul_le _ _
    _ ≤ Nat.size n + (1 + Nat.size (c + 3)) := by omega

/-- Literal prefix descriptions bound the relative prefix complexity. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_length_bound (A : Set ℕ) :
    ∃ c : ℕ, ∀ x : BitString, PointToSet.oracleComplexity A x ≤ 2 * x.length + c := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₁, hc₁⟩ := (PointToSet.exists_optimalOraclePrefix_spec A).2.2 U
    ((PointToSet.isDecompressorIn_iff_partrecIn _ _).mpr hU.isDecompressor.partrecIn)
    hU.isPrefixMachine
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c₂ + c₁, fun x => ?_⟩
  have hb : KPPlain (PointToSet.optimalOraclePrefix A) x ≤
      ((2 * x.length + (c₂ + c₁) : ℕ) : ℕ∞) := by
    calc
      KPPlain (PointToSet.optimalOraclePrefix A) x ≤ KPPlain U x + c₁ := hc₁ x []
      _ ≤ (2 * (x.length : ℕ∞) + c₂) + c₁ := by gcongr; exact hc₂ x
      _ = _ := by push_cast; ring
  exact ENat.natCast_le_natCast.mp (by
    simpa only [PointToSet.oracleComplexity, PointToSet.oraclePrefixComplexity_coe,
      PointToSet.oraclePrefixComplexity, KPPlain] using hb)

/-- The de-interleaving map: from a string `p` the pair code of its entries at positions
`2 i + o` and `2 i + (1 - o)`, `i < |p| / 2`. -/
private def not_isMisesKLRandom_of_plainK_lt_gen_deint (o : ℕ) (p : BitString) :
    BitString :=
  pairCode ((List.range (p.length / 2)).map (fun i => p.getD (2 * i + o) false))
    ((List.range (p.length / 2)).map (fun i => p.getD (2 * i + (1 - o)) false))

private lemma not_isMisesKLRandom_of_plainK_lt_gen_getD (o : ℕ) :
    Primrec₂ (fun (p : BitString) (i : ℕ) => p.getD (2 * i + o) false) := by
  have h2 : Primrec (fun q : BitString × ℕ => 2 * q.2 + o) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const o)
  exact (Primrec.list_getD false).comp Primrec.fst h2

private lemma not_isMisesKLRandom_of_plainK_lt_gen_range :
    Primrec (fun p : BitString => List.range (p.length / 2)) :=
  Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))

private lemma not_isMisesKLRandom_of_plainK_lt_gen_map (o : ℕ) :
    Primrec (fun p : BitString =>
      (List.range (p.length / 2)).map (fun i => p.getD (2 * i + o) false)) :=
  Primrec.list_map (f := fun p : BitString => List.range (p.length / 2))
    (g := fun (p : BitString) (i : ℕ) => p.getD (2 * i + o) false)
    not_isMisesKLRandom_of_plainK_lt_gen_range
    (not_isMisesKLRandom_of_plainK_lt_gen_getD o)

private lemma not_isMisesKLRandom_of_plainK_lt_gen_deint_computable (o : ℕ) :
    Computable (not_isMisesKLRandom_of_plainK_lt_gen_deint o) := by
  have hx : Computable (fun p : BitString =>
      (List.range (p.length / 2)).map (fun i => p.getD (2 * i + o) false)) :=
    (not_isMisesKLRandom_of_plainK_lt_gen_map o).to_comp
  have hy : Computable (fun p : BitString =>
      (List.range (p.length / 2)).map (fun i => p.getD (2 * i + (1 - o)) false)) :=
    (not_isMisesKLRandom_of_plainK_lt_gen_map (1 - o)).to_comp
  have h := pairCode_computable.comp (hx.pair hy)
  exact h

private lemma not_isMisesKLRandom_of_plainK_lt_gen_deint_eq (X Y P : CantorSeq) (o : ℕ)
    (ho : o < 2) (hPX : ∀ i, P (2 * i + o) = X i) (hPY : ∀ i, P (2 * i + (1 - o)) = Y i)
    (n : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_gen_deint o (cantorPrefix P n) =
      pairCode (cantorPrefix X (n / 2)) (cantorPrefix Y (n / 2)) := by
  unfold not_isMisesKLRandom_of_plainK_lt_gen_deint
  rw [cantorPrefix_length]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n / 2 := by simpa using h2
      simp only [List.getElem_map, List.getElem_range, cantorPrefix_getElem]
      rw [List.getD_eq_getElem _ _ (by simp; omega), cantorPrefix_getElem, hPX]
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n / 2 := by simpa using h2
      simp only [List.getElem_map, List.getElem_range, cantorPrefix_getElem]
      rw [List.getD_eq_getElem _ _ (by simp; omega), cantorPrefix_getElem, hPY]

/-- The pair of the two halves is computable from the prefix, uniformly in `n`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_gen_pair_le (A : Set ℕ) (X Y P : CantorSeq)
    (o : ℕ) (ho : o < 2) (hPX : ∀ i, P (2 * i + o) = X i)
    (hPY : ∀ i, P (2 * i + (1 - o)) = Y i) :
    ∃ c : ℕ, ∀ n : ℕ,
      PointToSet.oracleComplexity A
          (pairCode (cantorPrefix X (n / 2)) (cantorPrefix Y (n / 2))) ≤
        PointToSet.oracleComplexity A (cantorPrefix P n) + c := by
  let F : List BitString →. BitString := fun xs =>
    Part.some (not_isMisesKLRandom_of_plainK_lt_gen_deint o xs.headI)
  have hF : PartrecIn {charOracle A} F :=
    (((not_isMisesKLRandom_of_plainK_lt_gen_deint_computable o).comp
      Primrec.list_headI.to_comp)).computableIn.partrecIn
  obtain ⟨c, hc⟩ := PointToSet.oracle_tuple_bounds_composition A 1 F hF
  refine ⟨c, fun n => ?_⟩
  have h := hc [cantorPrefix P n]
    (not_isMisesKLRandom_of_plainK_lt_gen_deint o (cantorPrefix P n)) (by simp)
    (by simp [F])
  rw [not_isMisesKLRandom_of_plainK_lt_gen_deint_eq X Y P o ho hPX hPY n] at h
  simpa using h

/-- Generic form of the finite chain inequality (Step 4 of the proof of
`not_isMisesKLRandom_of_plainK_lt`): for two interleaved sequences `X`, `Y` (at positions
`2 i + o` and `2 i + (1 - o)` of `P`), if the oracle `A'` computes `A` and the prefixes of `X`,
then `K^A(X↾h) + K^{A'}(Y↾h) ≤ K^A(P↾n) + O(log n)` for `h = n / 2`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_generic_chain
    (A A' : Set ℕ) (hA : RecursiveIn {charOracle A'} (charOracle A))
    (X Y P : CantorSeq) (o : ℕ) (ho : o < 2)
    (hX : ComputableIn {charOracle A'} (fun h : ℕ => cantorPrefix X h))
    (hPX : ∀ i, P (2 * i + o) = X i) (hPY : ∀ i, P (2 * i + (1 - o)) = Y i) :
    ∃ c : ℕ, ∀ n : ℕ,
      PointToSet.oracleComplexity A (cantorPrefix X (n / 2)) +
          PointToSet.oracleComplexity A' (cantorPrefix Y (n / 2)) ≤
        PointToSet.oracleComplexity A (cantorPrefix P n) + logSlack c n := by
  obtain ⟨c1, h1⟩ := not_isMisesKLRandom_of_plainK_lt_xside A
  obtain ⟨c2, h2⟩ := not_isMisesKLRandom_of_plainK_lt_yside A A' hA X hX
  obtain ⟨c3, h3⟩ := not_isMisesKLRandom_of_plainK_lt_gen_pair_le A X Y P o ho hPX hPY
  obtain ⟨c4, h4⟩ := not_isMisesKLRandom_of_plainK_lt_gen_length_bound A
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 1 + Nat.size (c3 + c4 + 3) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = c1 + c2 + c3 + 1 + 10 * K + 10 := ⟨_, rfl⟩
  refine ⟨c, fun n => ?_⟩
  have hls : logSlack c n = c * Nat.size n + c := by
    unfold logSlack
    rw [Nat.size_eq_bits_len]
  rw [hls]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = PointToSet.oracleComplexity A
      (pairCode (cantorPrefix X (n / 2)) (cantorPrefix Y (n / 2))) := ⟨_, rfl⟩
  have hm3 : m ≤ PointToSet.oracleComplexity A (cantorPrefix P n) + c3 := by
    rw [hm]; exact h3 n
  have hm4 : PointToSet.oracleComplexity A (cantorPrefix P n) ≤ 2 * n + c4 := by
    have := h4 (cantorPrefix P n)
    rwa [cantorPrefix_length] at this
  obtain ⟨T, d, hTmem, hd1, hd2, hdm⟩ :=
    not_isMisesKLRandom_of_plainK_lt_gen_section A (cantorPrefix X (n / 2))
      (cantorPrefix Y (n / 2)) m (le_of_eq hm.symm)
  have hyT : cantorPrefix Y (n / 2) ∈ T := (hTmem _).mpr (le_of_eq hm.symm)
  obtain ⟨T1, hT1sub, hT1card⟩ := Finset.exists_subset_card_eq hd1
  have hx1 := h1 (cantorPrefix X (n / 2)) m d T1 hT1card
    (fun y' hy' => (hTmem y').mp (hT1sub hy'))
  have hy1 := h2 (n / 2) m (d + 1) (cantorPrefix Y (n / 2)) T hd2.le
    (fun y' hy' => (hTmem y').mpr hy') ((hTmem _).mp hyT)
  have hu : ∀ t : ℕ, t ≤ 2 * n + (c3 + c4) + 1 → Nat.size t ≤ Nat.size n + K := by
    intro t ht
    have := (Nat.size_le_size ht).trans
      (not_isMisesKLRandom_of_plainK_lt_gen_size_lin (c3 + c4) n)
    rw [hK]
    exact this
  have hsm : Nat.size m ≤ Nat.size n + K := hu m (by omega)
  have hsd : Nat.size d ≤ Nat.size n + K := hu d (by omega)
  have hsd1 : Nat.size (d + 1) ≤ Nat.size n + K := hu (d + 1) (by omega)
  have hsh : Nat.size (n / 2) ≤ Nat.size n + K := hu (n / 2) (by omega)
  have hcs : 10 * Nat.size n ≤ c * Nat.size n := Nat.mul_le_mul_right _ (by omega)
  omega


/-- Oracle fact: if membership in `A` is membership in `A'` gated by a primitive recursive
test, then the characteristic function of `A` is recursive in that of `A'`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_step4inst_recursiveIn_gate
    (A A' : Set ℕ) (g : ℕ → Bool) (hg : Primrec g)
    (h : ∀ m, m ∈ A ↔ (g m = true ∧ m ∈ A')) :
    RecursiveIn {charOracle A'} (charOracle A) := by
  have hO : PartrecIn {charOracle A'} (charOracle A') :=
    PartrecIn.oracle _ (Set.mem_singleton _)
  have hc : PartrecIn {charOracle A'}
      (fun m : ℕ => cond (g m) (charOracle A' m) (Part.some ((fun _ : ℕ => (0 : ℕ)) m))) :=
    PartrecIn.cond_some (g := fun _ : ℕ => (0 : ℕ)) hg.to_comp.computableIn hO
      (Primrec.const 0).to_comp.computableIn
  refine PartrecIn.of_eq hc (fun m => ?_)
  by_cases hm : m ∈ A'
  · by_cases hgm : g m = true
    · have hA : m ∈ A := (h m).2 ⟨hgm, hm⟩
      simp [charOracle, hgm, hm, hA]
    · have hA : m ∉ A := fun hmA => hgm ((h m).1 hmA).1
      simp [charOracle, hgm, hm, hA]
  · by_cases hgm : g m = true
    · have hA : m ∉ A := fun hmA => hm ((h m).1 hmA).2
      simp [charOracle, hgm, hm, hA]
    · have hA : m ∉ A := fun hmA => hgm ((h m).1 hmA).1
      simp [charOracle, hgm, hm, hA]

/-- Oracle fact: a sequence whose bits are oracle queries at primitive recursive positions is
computable in the oracle. -/
private lemma not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_bit
    (A' : Set ℕ) (X : CantorSeq) (g : ℕ → ℕ) (hg : Primrec g)
    (h : ∀ i, X i = true ↔ g i ∈ A') :
    ComputableIn {charOracle A'} X := by
  have hO : PartrecIn {charOracle A'} (charOracle A') :=
    PartrecIn.oracle _ (Set.mem_singleton _)
  have h1 : PartrecIn {charOracle A'} (fun i : ℕ => charOracle A' (g i)) :=
    hO.comp hg.to_comp.computableIn
  have h2 : PartrecIn {charOracle A'}
      (fun i : ℕ => (charOracle A' (g i)).map (fun n : ℕ => decide (n = 1))) :=
    PartrecIn.map h1
      (Computable₂.computableIn₂ (Primrec₂.to_comp
        (Primrec.to₂ (PrimrecPred.decide
          (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))))))
  have h3 : PartrecIn {charOracle A'} (X : ℕ →. Bool) := by
    refine PartrecIn.of_eq_tot h2 (fun i => ?_)
    by_cases hi : g i ∈ A'
    · have : X i = true := (h i).2 hi
      simp [charOracle, hi, this]
    · have : X i = false := by
        cases hX : X i
        · rfl
        · exact absurd ((h i).1 hX) hi
      simp [charOracle, hi, this]
  exact h3

/-- The prefixes of an oracle-computable sequence are oracle-computable. -/
private lemma not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_prefix
    (A' : Set ℕ) (X : CantorSeq) (hX : ComputableIn {charOracle A'} X) :
    ComputableIn {charOracle A'} (fun n : ℕ => cantorPrefix X n) := by
  have hstep : ComputableIn₂ {charOracle A'}
      (fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [X p.1]) := by
    have happ : ComputableIn {charOracle A'} (fun z : BitString × Bool => z.1 ++ [z.2]) :=
      Primrec.computableIn Primrec.list_concat
    have harg : ComputableIn {charOracle A'}
        (fun q : ℕ × (ℕ × BitString) => (q.2.2, X q.2.1)) :=
      ComputableIn.pair (ComputableIn.snd.comp ComputableIn.snd)
        (hX.comp (ComputableIn.fst.comp ComputableIn.snd))
    exact happ.comp harg
  have hrec := ComputableIn.nat_rec (O := {charOracle A'}) (f := fun n : ℕ => n)
    (g := fun _ : ℕ => ([] : BitString)) (h := fun (_ : ℕ) (p : ℕ × BitString) => p.2 ++ [X p.1])
    ComputableIn.id (ComputableIn.const []) hstep
  refine ComputableIn.of_eq hrec (fun n => ?_)
  induction n with
  | zero => simp [cantorPrefix]
  | succ n ih =>
    rw [cantorPrefix_succ, ← ih]

/-- Gate: outside the residue class `r` mod `2 ^ k` the background of level `k` is the
background of the finer level `k + 1` (with a residue `r'` reducing to `r`). -/
private lemma not_isMisesKLRandom_of_plainK_lt_step4inst_gate
    (w : CantorSeq) (k r r' : ℕ) (hr' : r' % 2 ^ k = r) (m : ℕ) :
    m ∈ not_isMisesKLRandom_of_plainK_lt_background w k r ↔
      (decide (m % 2 ^ k ≠ r) = true ∧
        m ∈ not_isMisesKLRandom_of_plainK_lt_background w (k + 1) r') := by
  have hmod : m % 2 ^ (k + 1) % 2 ^ k = m % 2 ^ k :=
    Nat.mod_mod_of_dvd m (pow_dvd_pow 2 (Nat.le_succ k))
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨decide_eq_true h1, ?_, h2⟩
    intro heq
    apply h1
    rw [← hmod, heq, hr']
  · rintro ⟨h1, _, h3⟩
    exact ⟨of_decide_eq_true h1, h3⟩

/-- Positions of a finer column are not in the finer background at a different residue. -/
private lemma not_isMisesKLRandom_of_plainK_lt_step4inst_bit
    (w : CantorSeq) (k r' r'' : ℕ) (hr' : r' < 2 ^ (k + 1)) (hne : r' ≠ r'') (i : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_column w (k + 1) r' i = true ↔
      (2 ^ (k + 1) * i + r') ∈ not_isMisesKLRandom_of_plainK_lt_background w (k + 1) r'' := by
  have hmod : (2 ^ (k + 1) * i + r') % 2 ^ (k + 1) = r' := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr']
  constructor
  · intro h
    exact ⟨by rw [hmod]; exact hne, h⟩
  · rintro ⟨_, h2⟩
    exact h2

/-- Step 4 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
the finite, relativized chain inequality for a column and its even and odd parts.
In each ordering, the second description may use the first part as an oracle.
Relative symmetry of information, followed by encoding the length and the first
complexity in logarithmic space, gives this inequality. Both children have length
`n / 2`, so an odd final bit of the parent is simply discarded. -/
lemma not_isMisesKLRandom_of_plainK_lt_finite_chain
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) :
    let col := not_isMisesKLRandom_of_plainK_lt_column w
    let bg := not_isMisesKLRandom_of_plainK_lt_background w
    ∃ c : ℕ, ∀ n : ℕ,
      PointToSet.oracleComplexity (bg k r) (cantorPrefix (col (k + 1) r) (n / 2)) +
          PointToSet.oracleComplexity (bg (k + 1) (r + 2 ^ k))
            (cantorPrefix (col (k + 1) (r + 2 ^ k)) (n / 2)) ≤
        PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n) + logSlack c n ∧
      PointToSet.oracleComplexity (bg k r)
          (cantorPrefix (col (k + 1) (r + 2 ^ k)) (n / 2)) +
          PointToSet.oracleComplexity (bg (k + 1) r) (cantorPrefix (col (k + 1) r) (n / 2)) ≤
        PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n) + logSlack c n := by
  intro col bg
  have hk : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hr1 : r < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hr2 : r + 2 ^ k < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hmodr : r % 2 ^ k = r := Nat.mod_eq_of_lt hr
  have hmodr2 : (r + 2 ^ k) % 2 ^ k = r := by
    rw [Nat.add_mod_right, hmodr]
  have hgate : Primrec (fun m : ℕ => decide (m % 2 ^ k ≠ r)) :=
    PrimrecPred.decide (PrimrecPred.not (PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp Primrec.id (Primrec.const (2 ^ k))) (Primrec.const r)))
  have hposr : Primrec (fun i : ℕ => 2 ^ (k + 1) * i + r) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _) Primrec.id) (Primrec.const _)
  have hposr2 : Primrec (fun i : ℕ => 2 ^ (k + 1) * i + (r + 2 ^ k)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const _) Primrec.id) (Primrec.const _)
  -- (a): the oracle `bg (k + 1) (r + 2 ^ k)` computes `bg k r` and the even part
  have hA₁ : RecursiveIn {charOracle (bg (k + 1) (r + 2 ^ k))} (charOracle (bg k r)) :=
    not_isMisesKLRandom_of_plainK_lt_step4inst_recursiveIn_gate _ _ _ hgate
      (not_isMisesKLRandom_of_plainK_lt_step4inst_gate w k r (r + 2 ^ k) hmodr2)
  have hX₁ : ComputableIn {charOracle (bg (k + 1) (r + 2 ^ k))}
      (fun h : ℕ => cantorPrefix (col (k + 1) r) h) :=
    not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_prefix _ _
      (not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_bit _ _ _ hposr
        (not_isMisesKLRandom_of_plainK_lt_step4inst_bit w k r (r + 2 ^ k) hr1
          (by omega)))
  obtain ⟨c₁, hc₁⟩ := not_isMisesKLRandom_of_plainK_lt_generic_chain
    (bg k r) (bg (k + 1) (r + 2 ^ k)) hA₁ (col (k + 1) r) (col (k + 1) (r + 2 ^ k)) (col k r)
    0 (by norm_num) hX₁
    (fun i => by
      change w (2 ^ k * (2 * i + 0) + r) = w (2 ^ (k + 1) * i + r)
      congr 1
      ring)
    (fun i => by
      change w (2 ^ k * (2 * i + (1 - 0)) + r) = w (2 ^ (k + 1) * i + (r + 2 ^ k))
      congr 1
      simp only [Nat.sub_zero]
      ring)
  -- (b): the oracle `bg (k + 1) r` computes `bg k r` and the odd part
  have hA₂ : RecursiveIn {charOracle (bg (k + 1) r)} (charOracle (bg k r)) :=
    not_isMisesKLRandom_of_plainK_lt_step4inst_recursiveIn_gate _ _ _ hgate
      (not_isMisesKLRandom_of_plainK_lt_step4inst_gate w k r r hmodr)
  have hX₂ : ComputableIn {charOracle (bg (k + 1) r)}
      (fun h : ℕ => cantorPrefix (col (k + 1) (r + 2 ^ k)) h) :=
    not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_prefix _ _
      (not_isMisesKLRandom_of_plainK_lt_step4inst_computableIn_bit _ _ _ hposr2
        (not_isMisesKLRandom_of_plainK_lt_step4inst_bit w k (r + 2 ^ k) r hr2
          (by omega)))
  obtain ⟨c₂, hc₂⟩ := not_isMisesKLRandom_of_plainK_lt_generic_chain
    (bg k r) (bg (k + 1) r) hA₂ (col (k + 1) (r + 2 ^ k)) (col (k + 1) r) (col k r)
    1 (by norm_num) hX₂
    (fun i => by
      change w (2 ^ k * (2 * i + 1) + r) = w (2 ^ (k + 1) * i + (r + 2 ^ k))
      congr 1
      ring)
    (fun i => by
      change w (2 ^ k * (2 * i + (1 - 1)) + r) = w (2 ^ (k + 1) * i + r)
      congr 1
      simp only [Nat.sub_self]
      ring)
  refine ⟨c₁ + c₂, fun n => ⟨?_, ?_⟩⟩
  · exact (hc₁ n).trans (Nat.add_le_add_left (logSlack_mono_left (Nat.le_add_right c₁ c₂) n) _)
  · exact (hc₂ n).trans (Nat.add_le_add_left (logSlack_mono_left (Nat.le_add_left c₂ c₁) n) _)

/-- Step 4 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
the relativized complexity chain rule for a dyadic column and its two halves.
In either ordering, its density is at least half the density of the first half
with the old background plus half the density of the second half with the first
half added to the background. This is the equal-density instance of Lemma 40 of
Merkle--Miller--Nies--Reimann--Stephan, *Kolmogorov-Loveland randomness and stochasticity*.
The additional oracle is exactly the complement of the second column, not an
arbitrarily chosen oracle. -/
private lemma not_isMisesKLRandom_of_plainK_lt_chain
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) :
    let col := not_isMisesKLRandom_of_plainK_lt_column w
    let bg := not_isMisesKLRandom_of_plainK_lt_background w
    (Applications.oraclePrefixDim (bg k r) (col (k + 1) r) +
        Applications.oraclePrefixDim (bg (k + 1) (r + 2 ^ k))
          (col (k + 1) (r + 2 ^ k))) / 2 ≤
      Applications.oraclePrefixDim (bg k r) (col k r) ∧
    (Applications.oraclePrefixDim (bg k r) (col (k + 1) (r + 2 ^ k)) +
        Applications.oraclePrefixDim (bg (k + 1) r) (col (k + 1) r)) / 2 ≤
      Applications.oraclePrefixDim (bg k r) (col k r) := by
  let col := not_isMisesKLRandom_of_plainK_lt_column w
  let bg := not_isMisesKLRandom_of_plainK_lt_background w
  obtain ⟨c, hc⟩ := not_isMisesKLRandom_of_plainK_lt_finite_chain w k r hr
  have hp := not_isMisesKLRandom_of_plainK_lt_bounded (bg k r) (col k r)
  constructor
  · exact not_isMisesKLRandom_of_plainK_lt_normalize
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col (k + 1) r) n))
      (fun n => PointToSet.oracleComplexity (bg (k + 1) (r + 2 ^ k))
        (cantorPrefix (col (k + 1) (r + 2 ^ k)) n))
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n))
      c hp (fun n => (hc n).1)
  · exact not_isMisesKLRandom_of_plainK_lt_normalize
      (fun n => PointToSet.oracleComplexity (bg k r)
        (cantorPrefix (col (k + 1) (r + 2 ^ k)) n))
      (fun n => PointToSet.oracleComplexity (bg (k + 1) r) (cantorPrefix (col (k + 1) r) n))
      (fun n => PointToSet.oracleComplexity (bg k r) (cantorPrefix (col k r) n))
      c hp (fun n => (hc n).2)

/-- Step 5 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
choose a column whose conditional density is near the infimum over all dyadic
columns. Applying Step 4 in both orders gives two halves whose densities, relative
to the same complementary bits, are below the prescribed strict upper bound.
This is the strict-bound version of Bienvenu's splitting argument (Lemma 12 of
*Kolmogorov-Loveland stochasticity and Kolmogorov complexity*). -/
lemma not_isMisesKLRandom_of_plainK_lt_split
    (w : CantorSeq) (β : ℝ) (hw : Applications.oraclePrefixDim ∅ w < β) :
    ∃ k r : ℕ, r < 2 ^ k ∧
      Applications.oraclePrefixDim
        (not_isMisesKLRandom_of_plainK_lt_background w k r)
        (not_isMisesKLRandom_of_plainK_lt_column w (k + 1) r) < β ∧
      Applications.oraclePrefixDim
        (not_isMisesKLRandom_of_plainK_lt_background w k r)
        (not_isMisesKLRandom_of_plainK_lt_column w (k + 1) (r + 2 ^ k)) < β := by
  let col := not_isMisesKLRandom_of_plainK_lt_column w
  let bg := not_isMisesKLRandom_of_plainK_lt_background w
  let D : Set ℝ := {d | ∃ k r : ℕ, r < 2 ^ k ∧ d =
    Applications.oraclePrefixDim (bg k r) (col k r)}
  have hroot : Applications.oraclePrefixDim ∅ w ∈ D := by
    refine ⟨0, 0, by norm_num, ?_⟩
    have hb0 : bg 0 0 = ∅ := by
      ext n
      simp [bg, not_isMisesKLRandom_of_plainK_lt_background, Nat.mod_one]
    have hc0 : col 0 0 = w := by
      funext n
      simp [col, not_isMisesKLRandom_of_plainK_lt_column]
    rw [hb0, hc0]
  have hD : D.Nonempty := ⟨_, hroot⟩
  have hb : BddBelow D := by
    refine ⟨0, ?_⟩
    rintro d ⟨k, r, hr, rfl⟩
    exact not_isMisesKLRandom_of_plainK_lt_nonneg _ _
  have ht : sInf D < β := (csInf_le hb hroot).trans_lt hw
  obtain ⟨d, ⟨k, r, hr, rfl⟩, hd⟩ :=
    exists_lt_of_csInf_lt hD (show sInf D < (β + sInf D) / 2 by linarith)
  have hr₀ : r < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hr₁ : r + 2 ^ k < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have h₀ : sInf D ≤ Applications.oraclePrefixDim (bg (k + 1) r) (col (k + 1) r) :=
    csInf_le hb ⟨k + 1, r, hr₀, rfl⟩
  have h₁ : sInf D ≤ Applications.oraclePrefixDim (bg (k + 1) (r + 2 ^ k))
      (col (k + 1) (r + 2 ^ k)) :=
    csInf_le hb ⟨k + 1, r + 2 ^ k, hr₁, rfl⟩
  have hchain := not_isMisesKLRandom_of_plainK_lt_chain w k r hr
  change (_ + _) / 2 ≤ _ ∧ (_ + _) / 2 ≤ _ at hchain
  exact ⟨k, r, hr, by change Applications.oraclePrefixDim (bg k r) _ < β; linarith [hchain.1],
    by change Applications.oraclePrefixDim (bg k r) _ < β; linarith [hchain.2]⟩

/-- Step 6 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
dropping a fixed number of symbols costs only a constant in relative complexity.
Thus a strict bound on lower complexity density gives arbitrarily long
compressible prefixes of each tail, with the same strict rate bound. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tails
    (A : Set ℕ) (u : CantorSeq) (β : ℝ)
    (hu : Applications.oraclePrefixDim A u < β) (m N : ℕ) :
    ∃ n : ℕ, N < n ∧
      (PointToSet.oracleComplexity A (cantorPrefix (fun i => u (m + i)) n) : ℝ) < β * n := by
  let z : ℕ → ℝ := fun n => (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) / n
  have hb : IsBoundedUnder (· ≤ ·) atTop z :=
    not_isMisesKLRandom_of_plainK_lt_bounded A u
  obtain ⟨γ, hγ₀, hγ₁⟩ := exists_between hu
  have hf : ∃ᶠ n : ℕ in atTop, z n < γ :=
    frequently_lt_of_liminf_lt hb.isCoboundedUnder_ge hγ₀
  let F : List BitString →. BitString := fun xs => Part.some (xs.headI.drop m)
  have hF : PartrecIn {charOracle A} F :=
    ((Primrec.list_drop.comp (Primrec.const m) Primrec.list_headI).to_comp).computableIn.partrecIn
  obtain ⟨c, hc⟩ := PointToSet.oracle_tuple_bounds_composition A 1 F hF
  have hdrop (x : BitString) : PointToSet.oracleComplexity A (x.drop m) ≤
      PointToSet.oracleComplexity A x + c := by
    simpa using hc [x] (x.drop m) (by simp) (by simp [F])
  obtain ⟨L, hL⟩ := exists_nat_gt (((c : ℝ) + β * m) / (β - γ))
  obtain ⟨n, hn, hnlarge⟩ :=
    (hf.and_eventually (eventually_gt_atTop (max L (m + N)))).exists
  have hmn : m ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hLn : (L : ℝ) ≤ n := by exact_mod_cast (show L ≤ n by omega)
  have hmargin : (c : ℝ) + β * m < (β - γ) * n := by
    have := (div_lt_iff₀ (sub_pos.mpr hγ₁)).mp hL
    nlinarith
  have hpre : (PointToSet.oracleComplexity A (cantorPrefix u n) : ℝ) < γ * n :=
    (div_lt_iff₀ hnR).mp hn
  have heq : (cantorPrefix u n).drop m =
      cantorPrefix (fun i => u (m + i)) (n - m) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_drop, cantorPrefix_getElem]
  have hcost : (PointToSet.oracleComplexity A
      (cantorPrefix (fun i => u (m + i)) (n - m)) : ℝ) ≤
      PointToSet.oracleComplexity A (cantorPrefix u n) + c := by
    exact_mod_cast (heq ▸ hdrop (cantorPrefix u n))
  refine ⟨n - m, by omega, ?_⟩
  rw [Nat.cast_sub hmn]
  nlinarith

/-- Step 6 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
relative prefix complexity supplies a Kraft bound on every finite set of strings
whose complexities are less than `β` times their lengths. -/
private lemma not_isMisesKLRandom_of_plainK_lt_kraft
    (A : Set ℕ) (β : ℝ) (D : Finset BitString)
    (hD : ∀ x ∈ D, (PointToSet.oracleComplexity A x : ℝ) < β * x.length) :
    ∑ x ∈ D, (2 : ℝ) ^ (-β * x.length) ≤ 1 := by
  let U := PointToSet.optimalOraclePrefix A
  have hterm (x : BitString) : complexityWeight (KP U x []) =
      (2 : ENNReal)⁻¹ ^ PointToSet.oracleComplexity A x := by
    rw [← complexityWeight_coe, PointToSet.oracleComplexity,
      PointToSet.oraclePrefixComplexity_coe]
    rfl
  have hsum : (∑' x : BitString, complexityWeight (KP U x [])) ≤ 1 :=
    (ENNReal.tsum_le_tsum (fun x => complexityWeight_KP_le_aprioriMeasure U x [])).trans
      (tsum_aprioriMeasure_le_one U [] (PointToSet.exists_optimalOraclePrefix_spec A).2.1)
  have hfinite : ∀ x ∈ D, complexityWeight (KP U x []) ≠ ⊤ := by
    intro x hx
    rw [hterm]
    exact ENNReal.pow_ne_top (by norm_num)
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top ((ENNReal.sum_le_tsum D).trans hsum)
  rw [ENNReal.toReal_sum hfinite, ENNReal.toReal_one] at hreal
  have hbound : ∑ x ∈ D, (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x ≤ 1 := by
    simpa only [hterm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using hreal
  apply le_trans (Finset.sum_le_sum (fun x hx => ?_)) hbound
  calc
    (2 : ℝ) ^ (-β * x.length) ≤ (2 : ℝ) ^ (-(PointToSet.oracleComplexity A x : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have := hD x hx; linarith)
    _ = (2 : ℝ)⁻¹ ^ PointToSet.oracleComplexity A x := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

/-- Step 6 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
enumerate the strings with relative prefix complexity below `β` times their
length. Kraft's inequality bounds every finite subset of the enumeration, and
every tail of a sequence of relative dimension below `β` has arbitrarily long
prefixes in it. The same enumeration works for every such sequence and every
tail; no sequence-dependent subsequence of lengths is supplied to the algorithm. -/
lemma not_isMisesKLRandom_of_plainK_lt_enumeration
    (A : Set ℕ) (β : ℚ) (_hβ : 0 < β) (_hβ1 : β < 1) :
    ∃ E : ℕ → Option BitString,
      ComputableIn {charOracle A} E ∧
      (∀ D : Finset BitString, (∀ x ∈ D, ∃ t, E t = some x) →
        ∑ x ∈ D, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1) ∧
      ∀ u : CantorSeq, Applications.oraclePrefixDim A u < β →
        ∀ m N : ℕ, ∃ n t : ℕ, N < n ∧
          E t = some (cantorPrefix (fun i => u (m + i)) n) := by
  have hthreshold : Computable (fun x : BitString => (x, β * (x.length : ℚ))) :=
    Computable.id.pair (computable₂_ratMul.comp (Computable.const β)
      (computable_nat_to_rat.comp Computable.list_length))
  have hRE : PointToSet.IsREIn A
      (fun x : BitString => (PointToSet.oracleComplexity A x : ℝ) < (β : ℝ) * x.length) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using
      (PointToSet.isREIn_oracleComplexity_lt A).comp hthreshold.computableIn
  obtain ⟨E, hE, henum⟩ := (PointToSet.relative_enumeration A _).mp hRE
  refine ⟨E, hE, ?_, ?_⟩
  · intro D hD
    exact not_isMisesKLRandom_of_plainK_lt_kraft A β D
      (fun x hx => (henum x).mpr (hD x hx))
  · intro u hu m N
    obtain ⟨n, hn, hcost⟩ :=
      not_isMisesKLRandom_of_plainK_lt_tails A u β hu m N
    obtain ⟨t, ht⟩ := (henum (cantorPrefix (fun i => u (m + i)) n)).mp (by simpa using hcost)
    exact ⟨n, t, hn, ht⟩

end Kolmogorov.FrequencyGames
