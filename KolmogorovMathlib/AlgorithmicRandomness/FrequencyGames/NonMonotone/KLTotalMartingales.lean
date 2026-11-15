/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLBetting

/-!
# Total Non-Monotonic Martingales

For non-monotonic betting strategies it does not matter whether the strategy is total or merely
partial computable: a sequence is Kolmogorov-Loveland random if and only if no total computable
non-monotonic strategy wins on it (`isKLRandom_iff_total`, SUV p. 309, by the argument of
Theorem 191).  The proof normalizes a winning strategy so that it never over-bets, splits it
by the parity of the requested indices, and simulates it by a total strategy.  The module also
names the open question whether Kolmogorov-Loveland randomness and Martin-Lof randomness
coincide (`KLRandomnessEqualsMartinLofQuestion`).
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

/-- Step 1 def of the proof of `isKLRandom_iff_total`: the betting strategy only bets on
the specified parity of indices -/
private def isKLRandom_iff_total_OnlyBetsOnParity (b : KLBetting) (p : Bool) : Prop :=
  ∀ x n, n ∈ b.next x → Nat.bodd n ≠ p →
    ∀ q ∈ b.capital x, ∀ c : Bool, ∀ q' ∈ b.capital (x ++ [c]), q' = q

/-- Step 1 def of the proof of `isKLRandom_iff_total`: the betting strategy does not
overbet (increase capital by more than 2x) -/
private def isKLRandom_iff_total_NoOverBet (b : KLBetting) : Prop :=
  ∀ x, ∀ q ∈ b.capital x, ∀ c : Bool, ∀ q' ∈ b.capital (x ++ [c]), q' ≤ 2 * q

/-- The pair of factors `(f_B, f_N)` by which the accounts `(B, N)` of the over-bet normalization
are multiplied on the child `c`, given `q = β.capital y` and the tagged halting child `(a, v)`. -/
private def isKLRandom_iff_total_normalize_fac (q : ℚ) (a : Bool) (v : ℚ)
    (c : Bool) : ℚ × ℚ :=
  if 2 * q < v then (if c = a then (2, 1) else (0, 1))
  else if 0 < q then (if c = a then (1, (1 + v / q) / 2) else (1, (3 - v / q) / 2))
  else (1, 1)

/-- One step of the fold: the state is `(history, B, N)`; wait for `q = cap history` and the tagged
halting child `k history`, then extend the history by `c` and multiply the accounts. -/
private def isKLRandom_iff_total_normalize_step (cap : BitString →. ℚ)
    (k : BitString →. Bool × ℚ) (s : BitString × ℚ × ℚ) (c : Bool) :
    Part (BitString × ℚ × ℚ) :=
  (cap s.1).bind fun q => (k s.1).map fun t =>
    (s.1 ++ [c],
      s.2.1 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).1,
      s.2.2 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).2)

/-- The step of the fold, in the shape expected by `pfoldl`. -/
private def isKLRandom_iff_total_normalize_F (cap : BitString →. ℚ)
    (k : BitString →. Bool × ℚ) : Unit → (BitString × ℚ × ℚ) → Bool →. (BitString × ℚ × ℚ) :=
  fun _ s c => isKLRandom_iff_total_normalize_step cap k s c

/-- The accounts `(B, N)` after the history `x`: a partial left fold from `(1, 1)`. -/
private def isKLRandom_iff_total_normalize_G (cap : BitString →. ℚ)
    (k : BitString →. Bool × ℚ) (x : BitString) : Part (ℚ × ℚ) :=
  (pfoldl (isKLRandom_iff_total_normalize_F cap k)
    () ([], 1, 1) x).map fun s => s.2

/-- The normalized capital `(B + N) / 2`. -/
private def isKLRandom_iff_total_normalize_cap (cap : BitString →. ℚ)
    (k : BitString →. Bool × ℚ) (x : BitString) : Part ℚ :=
  (isKLRandom_iff_total_normalize_G cap k x).map fun p => (p.1 + p.2) / 2

/-- Step 1 of the proof of `isKLRandom_iff_total_normalize`: the
first-halting-child selector.  If `β.capital` is partial computable, there is a partial computable
`k` returning a tagged halting child: `k x` is defined iff some child of `x` has defined capital,
and
any value `(a, v)` of `k x` satisfies `v ∈ β.capital (x ++ [a])`.  (`Partrec.merge'` on the two
tagged child computations, tag via `hc.comp (Computable.list_append.comp Computable.id
(Computable.const [b]))` and `.map (Computable.pair (Computable.const b) Computable.snd).to₂`.) -/
private lemma isKLRandom_iff_total_tag (β : KLBetting)
    (hcap : Partrec β.capital) :
    ∃ k : BitString →. Bool × ℚ, Partrec k ∧ ∀ x,
      (∀ t ∈ k x, t.2 ∈ β.capital (x ++ [t.1])) ∧
      ((k x).Dom ↔ (β.capital (x ++ [false])).Dom ∨ (β.capital (x ++ [true])).Dom) := by
  have hmk : ∀ b : Bool, Partrec fun x : BitString =>
      (β.capital (x ++ [b])).map fun v => (b, v) := fun b =>
    (hcap.comp (Computable.list_append.comp Computable.id (Computable.const [b]))).map
      (Computable.pair (Computable.const b) Computable.snd).to₂
  obtain ⟨k, hk, hk'⟩ := Partrec.merge' (hmk false) (hmk true)
  refine ⟨k, hk, fun x => ⟨fun t ht => ?_, ?_⟩⟩
  · rcases (hk' x).1 t ht with h | h
    · obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).1 h
      exact hv
    · obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).1 h
      exact hv
  · simp only [(hk' x).2, Part.map_Dom]

/-- Auxiliary computability lemma: the guarded quotient `v / q` (`0` unless `0 < q`) is computable,
via `computable_of_num_den`. -/
private lemma isKLRandom_iff_total_partrec_aux_div :
    Computable (fun p : ℚ × ℚ => if 0 < p.1 then p.2 / p.1 else 0) := by
  have hnum : Computable
      (fun p : ℚ × ℚ => p.2.num * (p.1.den : ℤ) * ((min 1 p.1.num.toNat : ℕ) : ℤ)) := by
    have h1 : Computable (fun p : ℚ × ℚ => p.2.num) := computable_ratNum.comp Computable.snd
    have h2 : Computable (fun p : ℚ × ℚ => (p.1.den : ℤ)) :=
      ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.fst)
    have h3' : Computable (fun p : ℚ × ℚ => min 1 p.1.num.toNat) :=
      Primrec.nat_min.to_comp.comp (Computable.const 1)
        (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp Computable.fst))
    have h3 : Computable (fun p : ℚ × ℚ => ((min 1 p.1.num.toNat : ℕ) : ℤ)) :=
      ComputableReals.primrec_natCastInt.to_comp.comp h3'
    exact Computable₂.comp primrec_intMul.to_comp (Computable₂.comp primrec_intMul.to_comp h1 h2) h3
  have hden : Computable (fun p : ℚ × ℚ => p.2.den * max 1 p.1.num.toNat) := by
    have hd1 : Computable (fun p : ℚ × ℚ => p.2.den) := computable_ratDen.comp Computable.snd
    have hm : Computable (fun p : ℚ × ℚ => max 1 p.1.num.toNat) :=
      Primrec.nat_max.to_comp.comp (Computable.const 1)
        (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp Computable.fst))
    exact Computable₂.comp Primrec.nat_mul.to_comp hd1 hm
  refine computable_of_num_den (f := fun p : ℚ × ℚ => if 0 < p.1 then p.2 / p.1 else 0)
    hnum hden (fun p => Nat.mul_pos p.2.den_pos (lt_of_lt_of_le Nat.one_pos (le_max_left _ _)))
    (fun p => ?_)
  have h2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
  have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
  have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
  have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
  by_cases h : 0 < p.1
  · have hn : 0 < p.1.num := Rat.num_pos.mpr h
    have ht : ((p.1.num.toNat : ℕ) : ℤ) = p.1.num := Int.toNat_of_nonneg hn.le
    have hmin : min 1 p.1.num.toNat = 1 := by omega
    have hmax : max 1 p.1.num.toNat = p.1.num.toNat := by omega
    rw [ite_eq_left h, hmin, hmax]
    push_cast
    have ht' : ((p.1.num.toNat : ℕ) : ℚ) = (p.1.num : ℚ) := by exact_mod_cast ht
    rw [ht', h2, h1]
    have hq : p.1 ≠ 0 := h.ne'
    field_simp
  · have hn : p.1.num ≤ 0 := Rat.num_nonpos.mpr (not_lt.mp h)
    have hmin : min 1 p.1.num.toNat = 0 := by omega
    rw [ite_eq_right h, hmin]
    simp

/-- Auxiliary computability lemma: the factor pair `fac` is computable (case distinction on
rational comparisons). -/
private lemma isKLRandom_iff_total_partrec_aux_fac :
    Computable (fun p : ℚ × Bool × ℚ × Bool =>
      isKLRandom_iff_total_normalize_fac p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hq : Computable (fun p : ℚ × Bool × ℚ × Bool => p.1) := Computable.fst
  have ha : Computable (fun p : ℚ × Bool × ℚ × Bool => p.2.1) := Computable.fst.comp Computable.snd
  have hv : Computable (fun p : ℚ × Bool × ℚ × Bool => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hc : Computable (fun p : ℚ × Bool × ℚ × Bool => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hq2 : Computable (fun p : ℚ × Bool × ℚ × Bool => 2 * p.1) :=
    computable₂_ratMul.comp (Computable.const 2) hq
  have hlt : Computable (fun p : ℚ × Bool × ℚ × Bool => decide (2 * p.1 < p.2.2.1)) :=
    computable₂_ratLt.comp hq2 hv
  have hpos : Computable (fun p : ℚ × Bool × ℚ × Bool => decide (0 < p.1)) :=
    computable₂_ratLt.comp (Computable.const 0) hq
  have heq : Computable (fun p : ℚ × Bool × ℚ × Bool => decide (p.2.2.2 = p.2.1)) :=
    (Primrec.eq.decide.to_comp).comp hc ha
  have hdiv := isKLRandom_iff_total_partrec_aux_div.comp
    (Computable.pair hq hv)
  have key : ∀ d : ℚ × Bool × ℚ × Bool → ℚ, Computable d →
      Computable (fun p : ℚ × Bool × ℚ × Bool =>
        cond (decide (2 * p.1 < p.2.2.1))
          (cond (decide (p.2.2.2 = p.2.1)) ((2 : ℚ), (1 : ℚ)) ((0 : ℚ), (1 : ℚ)))
          (cond (decide (0 < p.1))
            (cond (decide (p.2.2.2 = p.2.1)) ((1 : ℚ), (1 + d p) / 2) ((1 : ℚ), (3 - d p) / 2))
            ((1 : ℚ), (1 : ℚ)))) := by
    intro d hd
    have hn1 : Computable (fun p => (1 + d p) / 2) :=
      computable_ratHalf.comp (computable₂_ratAdd.comp (Computable.const 1) hd)
    have hn2 : Computable (fun p => (3 - d p) / 2) :=
      computable_ratHalf.comp (computable₂_ratSub.comp (Computable.const 3) hd)
    exact Computable.cond hlt
      (Computable.cond heq (Computable.const _) (Computable.const _))
      (Computable.cond hpos
        (Computable.cond heq (Computable.pair (Computable.const _) hn1)
          (Computable.pair (Computable.const _) hn2))
        (Computable.const _))
  refine (key _ hdiv).of_eq fun p => ?_
  obtain ⟨q, a, v, c⟩ := p
  simp only [isKLRandom_iff_total_normalize_fac]
  by_cases h1 : 2 * q < v
  · by_cases h2 : c = a <;> simp [h1, h2]
  · by_cases h3 : 0 < q
    · by_cases h2 : c = a <;> simp [h1, h2, h3]
    · simp [h1, h3]

/-- Step 2 of the proof of `isKLRandom_iff_total_normalize`: the
normalized capital is partial computable (`partrec_pfoldl` from `GacsDayPartrecFold`, with the state
`(history, B, N)`; the step uses `cap` and `k` on the history and the computable rational
arithmetic of `fac`, which is a case distinction on rational comparisons). -/
private lemma isKLRandom_iff_total_partrec
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) (hcap : Partrec cap) (hk : Partrec k) :
    Partrec (isKLRandom_iff_total_normalize_cap cap k) := by
  have hF : Partrec (fun a : Unit × (BitString × ℚ × ℚ) × Bool =>
      isKLRandom_iff_total_normalize_F cap k a.1 a.2.1 a.2.2) := by
    simp only [isKLRandom_iff_total_normalize_F,
      isKLRandom_iff_total_normalize_step]
    refine Partrec.bind (hcap.comp (Computable.fst.comp (Computable.fst.comp Computable.snd))) ?_
    refine Partrec.map (hk.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.snd.comp Computable.fst)))) ?_
    -- the variables of the step
    have hhist : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.1.1.2.1.1) :=
      Computable.fst.comp (Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst)))
    have hB : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.1.1.2.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))))
    have hN : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.1.1.2.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp Computable.fst))))
    have hc : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.1.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hq : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.1.2) := Computable.snd.comp Computable.fst
    have ha : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.2.1) := Computable.fst.comp Computable.snd
    have hv : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        x.2.2) := Computable.snd.comp Computable.snd
    have hfac := isKLRandom_iff_total_partrec_aux_fac.comp
      (Computable.pair hq (Computable.pair ha (Computable.pair hv hc)))
    have key : Computable (fun x : ((Unit × (BitString × ℚ × ℚ) × Bool) × ℚ) × (Bool × ℚ) =>
        (x.1.1.2.1.1 ++ [x.1.1.2.2],
          x.1.1.2.1.2.1 *
            (isKLRandom_iff_total_normalize_fac x.1.2 x.2.1 x.2.2 x.1.1.2.2).1,
          x.1.1.2.1.2.2 *
            (isKLRandom_iff_total_normalize_fac x.1.2 x.2.1 x.2.2 x.1.1.2.2).2))
                :=
      Computable.pair
        (Computable.list_append.comp hhist
          (Computable.list_cons.comp hc (Computable.const [])))
        (Computable.pair
          (computable₂_ratMul.comp hB (Computable.fst.comp hfac))
          (computable₂_ratMul.comp hN (Computable.snd.comp hfac)))
    exact key.to₂
  have hPfoldl := partrec_pfoldl hF
  have hinit : Computable (fun x : BitString => ((), (([] : BitString), (1 : ℚ), (1 : ℚ)), x)) :=
    Computable.pair (Computable.const ()) (Computable.pair (Computable.const _) Computable.id)
  have hG : Partrec (isKLRandom_iff_total_normalize_G cap k) :=
    Partrec.map (hPfoldl.comp hinit) (Computable.snd.comp Computable.snd)
  exact Partrec.map hG
    (computable_ratHalf.comp (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)))

private lemma isKLRandom_iff_total_normalize_aux_pfoldl_fst
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) (x : BitString) :
    ∀ (l0 : BitString) (B N : ℚ) (s : BitString × ℚ × ℚ),
      s ∈ pfoldl (isKLRandom_iff_total_normalize_F cap k) () (l0, B, N) x →
        s.1 = l0 ++ x := by
  induction x with
  | nil =>
    intro l0 B N s hs
    rw [pfoldl_nil] at hs
    rw [Part.mem_some_iff.1 hs]; simp
  | cons b t ih =>
    intro l0 B N s hs
    rw [pfoldl_cons, Part.mem_bind_iff] at hs
    obtain ⟨s', hs', hs⟩ := hs
    have h1 := ih _ _ _ s hs
    have h2 : s'.1 = l0 ++ [b] := by
      simp only [isKLRandom_iff_total_normalize_F,
        isKLRandom_iff_total_normalize_step, Part.mem_bind_iff,
        Part.mem_map_iff] at hs'
      obtain ⟨q, _, t', _, rfl⟩ := hs'
      rfl
    rw [h1, h2]; simp

private lemma isKLRandom_iff_total_normalize_aux_G_nil
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) :
    (1, 1) ∈ isKLRandom_iff_total_normalize_G cap k [] := by
  simp [isKLRandom_iff_total_normalize_G, pfoldl_nil]

private lemma isKLRandom_iff_total_normalize_aux_G_append_mem
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) (x : BitString)
    (c : Bool) (B' N' : ℚ) :
    (B', N') ∈ isKLRandom_iff_total_normalize_G cap k (x ++ [c]) ↔
      ∃ B N, (B, N) ∈ isKLRandom_iff_total_normalize_G cap k x ∧
        ∃ q ∈ cap x, ∃ t ∈ k x,
      B' = B * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).1 ∧
        N' = N * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).2 := by
  constructor
  · intro h
    simp only [isKLRandom_iff_total_normalize_G, pfoldl_append,
      Part.mem_map_iff, Part.mem_bind_iff] at h
    obtain ⟨s, ⟨s', hs', hs⟩, hsn⟩ := h
    simp only [pfoldl_cons, pfoldl_nil, Part.bind_some_right] at hs
    have hfst := isKLRandom_iff_total_normalize_aux_pfoldl_fst cap k x _ _ _ s'
        hs'
    simp only [isKLRandom_iff_total_normalize_F,
      isKLRandom_iff_total_normalize_step, Part.mem_bind_iff,
      Part.mem_map_iff] at hs
    obtain ⟨q, hq, t, ht, rfl⟩ := hs
    refine ⟨s'.2.1, s'.2.2, (Part.mem_map_iff _).2 ⟨s', hs', rfl⟩, q, ?_, t, ?_, ?_⟩
    · simpa [hfst] using hq
    · simpa [hfst] using ht
    · simp only [Prod.mk.injEq] at hsn
      exact ⟨hsn.1.symm, hsn.2.symm⟩
  · rintro ⟨B, N, hBN, q, hq, t, ht, rfl, rfl⟩
    unfold isKLRandom_iff_total_normalize_G at hBN ⊢
    obtain ⟨s', hs', hs'e⟩ := (Part.mem_map_iff _).1 hBN
    have hfst := isKLRandom_iff_total_normalize_aux_pfoldl_fst cap k x _ _ _ s'
        hs'
    simp only [List.nil_append] at hfst
    refine (Part.mem_map_iff _).2 ⟨(x ++ [c],
      s'.2.1 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).1,
      s'.2.2 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).2), ?_, ?_⟩
    · rw [pfoldl_append, Part.mem_bind_iff]
      refine ⟨s', hs', ?_⟩
      rw [pfoldl_cons, Part.mem_bind_iff]
      refine ⟨(x ++ [c],
        s'.2.1 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).1,
        s'.2.2 * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).2), ?_, ?_⟩
      · simp only [isKLRandom_iff_total_normalize_F,
          isKLRandom_iff_total_normalize_step, Part.mem_bind_iff,
          Part.mem_map_iff]
        exact ⟨q, by rwa [hfst], t, by rwa [hfst], by simp [hfst]⟩
      · rw [pfoldl_nil]; exact Part.mem_some _
    · have hB : s'.2.1 = B := congrArg Prod.fst hs'e
      have hN : s'.2.2 = N := congrArg Prod.snd hs'e
      simp [hB, hN]

private lemma isKLRandom_iff_total_normalize_aux_fac_sum
    (q : ℚ) (a : Bool) (v : ℚ) :
    (isKLRandom_iff_total_normalize_fac q a v false).1 +
        (isKLRandom_iff_total_normalize_fac q a v true).1 = 2 ∧
      (isKLRandom_iff_total_normalize_fac q a v false).2 +
        (isKLRandom_iff_total_normalize_fac q a v true).2 = 2 := by
  refine ⟨?_, ?_⟩ <;> by_cases h1 : 2 * q < v <;> by_cases h2 : 0 < q <;> cases a <;>
    simp [isKLRandom_iff_total_normalize_fac, h1, h2] <;> try ring

private lemma isKLRandom_iff_total_normalize_aux_fac_bounds
    (q : ℚ) (a : Bool) (v : ℚ) (c : Bool) (hq : 0 ≤ q) (hv : 0 ≤ v) :
    0 ≤ (isKLRandom_iff_total_normalize_fac q a v c).1 ∧
      (isKLRandom_iff_total_normalize_fac q a v c).1 ≤ 2 ∧
      0 < (isKLRandom_iff_total_normalize_fac q a v c).2 ∧
      (isKLRandom_iff_total_normalize_fac q a v c).2 ≤ 3 / 2 := by
  by_cases h1 : 2 * q < v
  · by_cases hca : c = a <;>
      simp [isKLRandom_iff_total_normalize_fac, h1, hca] <;> norm_num
  · by_cases h2 : 0 < q
    · have hr0 : 0 ≤ v / q := div_nonneg hv hq
      have hr2 : v / q ≤ 2 := by
        rw [div_le_iff₀ h2]; linarith
      unfold isKLRandom_iff_total_normalize_fac
      rw [ite_eq_right h1, ite_eq_left h2]
      by_cases hca : c = a
      · rw [ite_eq_left hca]
        change 0 ≤ (1 : ℚ) ∧ (1 : ℚ) ≤ 2 ∧ 0 < (1 + v / q) / 2 ∧ (1 + v / q) / 2 ≤ 3 / 2
        exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
      · rw [ite_eq_right hca]
        change 0 ≤ (1 : ℚ) ∧ (1 : ℚ) ≤ 2 ∧ 0 < (3 - v / q) / 2 ∧ (3 - v / q) / 2 ≤ 3 / 2
        exact ⟨by norm_num, by norm_num, by linarith, by linarith⟩
    · simp [isKLRandom_iff_total_normalize_fac, h1, h2]; norm_num

private lemma isKLRandom_iff_total_normalize_aux_G_inv
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ)
    (hnn : ∀ x, ∀ q ∈ cap x, 0 ≤ q) (hk : ∀ x, ∀ t ∈ k x, t.2 ∈ cap (x ++ [t.1])) :
    ∀ x B N, (B, N) ∈ isKLRandom_iff_total_normalize_G cap k x →
      0 ≤ B ∧ 0 < N := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro B N h
    have := Part.mem_unique h
      (isKLRandom_iff_total_normalize_aux_G_nil cap k)
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    norm_num
  | append_singleton x c ih =>
    intro B' N' h
    obtain ⟨B, N, hBN, q, hq, t, ht, rfl, rfl⟩ :=
      (isKLRandom_iff_total_normalize_aux_G_append_mem cap k x c B' N').1 h
    obtain ⟨hB, hN⟩ := ih B N hBN
    obtain ⟨b1, b2, b3, b4⟩ :=
      isKLRandom_iff_total_normalize_aux_fac_bounds q t.1 t.2 c (hnn x q hq)
        (hnn _ _ (hk x t ht))
    exact ⟨mul_nonneg hB b1, mul_pos hN b3⟩

/-- Step 3 of the proof of `isKLRandom_iff_total_normalize`: algebra of
the normalized capital.  For a nonnegative partial capital `cap` and a tag selector `k` returning
only values of children of `cap`: the capital is `1` at `[]`, strictly positive, never overbets, and
fair (every factor pair `(f_B(c), f_N(c))` of the two children sums to `(2, 2)`, `N > 0`,
`f_B ∈ {0, 1, 2}`, `f_N ∈ {1} ∪ [1/2, 3/2]`). -/
private lemma isKLRandom_iff_total_algebra
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) (hnn : ∀ x, ∀ q ∈ cap x, 0 ≤ q)
    (hk : ∀ x, ∀ t ∈ k x, t.2 ∈ cap (x ++ [t.1])) :
    (1 : ℚ) ∈ isKLRandom_iff_total_normalize_cap cap k [] ∧
    (∀ x, ∀ q ∈ isKLRandom_iff_total_normalize_cap cap k x, 0 < q) ∧
    (∀ x, ∀ q ∈ isKLRandom_iff_total_normalize_cap cap k x, ∀ c : Bool,
      ∀ q' ∈ isKLRandom_iff_total_normalize_cap cap k (x ++ [c]), q' ≤ 2 * q) ∧
    (∀ x q q₀ q₁, q ∈ isKLRandom_iff_total_normalize_cap cap k x →
      q₀ ∈ isKLRandom_iff_total_normalize_cap cap k (x ++ [false]) →
      q₁ ∈ isKLRandom_iff_total_normalize_cap cap k (x ++ [true]) →
      q = (q₀ + q₁) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Part.mem_map_iff _).2
      ⟨(1, 1), isKLRandom_iff_total_normalize_aux_G_nil cap k, by norm_num⟩
  · intro x q hq
    obtain ⟨⟨B, N⟩, hBN, rfl⟩ := (Part.mem_map_iff _).1 hq
    obtain ⟨hB, hN⟩ :=
      isKLRandom_iff_total_normalize_aux_G_inv cap k hnn hk x B N hBN
    change 0 < (B + N) / 2
    linarith
  · intro x q hq c q' hq'
    obtain ⟨⟨B, N⟩, hBN, rfl⟩ := (Part.mem_map_iff _).1 hq
    obtain ⟨⟨B', N'⟩, hBN', rfl⟩ := (Part.mem_map_iff _).1 hq'
    obtain ⟨B1, N1, h1, q1, hq1, t, ht, rfl, rfl⟩ :=
      (isKLRandom_iff_total_normalize_aux_G_append_mem cap k x c B' N').1 hBN'
    have := Part.mem_unique h1 hBN
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨hB, hN⟩ :=
      isKLRandom_iff_total_normalize_aux_G_inv cap k hnn hk x B1 N1 hBN
    obtain ⟨b1, b2, b3, b4⟩ :=
      isKLRandom_iff_total_normalize_aux_fac_bounds q1 t.1 t.2 c
        (hnn x q1 hq1) (hnn _ _ (hk x t ht))
    change (B1 * (isKLRandom_iff_total_normalize_fac q1 t.1 t.2 c).1 +
      N1 * (isKLRandom_iff_total_normalize_fac q1 t.1 t.2 c).2) / 2 ≤
        2 * ((B1 + N1) / 2)
    nlinarith [mul_le_mul_of_nonneg_left b2 hB, mul_le_mul_of_nonneg_left b4 hN.le]
  · intro x q q₀ q₁ hq hq0 hq1
    obtain ⟨⟨B, N⟩, hBN, rfl⟩ := (Part.mem_map_iff _).1 hq
    obtain ⟨⟨B0, N0⟩, hBN0, rfl⟩ := (Part.mem_map_iff _).1 hq0
    obtain ⟨⟨B1, N1⟩, hBN1, rfl⟩ := (Part.mem_map_iff _).1 hq1
    obtain ⟨Ba, Na, ha, qa, hqa, ta, hta, hB0, hN0⟩ :=
      (isKLRandom_iff_total_normalize_aux_G_append_mem cap k x false B0 N0).1
        hBN0
    obtain ⟨Bb, Nb, hb, qb, hqb, tb, htb, hB1, hN1⟩ :=
      (isKLRandom_iff_total_normalize_aux_G_append_mem cap k x true B1 N1).1
        hBN1
    have e1 := Part.mem_unique ha hBN
    have e2 := Part.mem_unique hb hBN
    simp only [Prod.mk.injEq] at e1 e2
    have eq := Part.mem_unique hqa hqb
    have et := Part.mem_unique hta htb
    obtain ⟨s1, s2⟩ :=
      isKLRandom_iff_total_normalize_aux_fac_sum qa ta.1 ta.2
    change (B + N) / 2 = ((B0 + N0) / 2 + (B1 + N1) / 2) / 2
    rw [hB0, hN0, hB1, hN1, e1.1, e1.2, e2.1, e2.2, ← eq, ← et]
    have : B * (isKLRandom_iff_total_normalize_fac qa ta.1 ta.2 false).1 +
        B * (isKLRandom_iff_total_normalize_fac qa ta.1 ta.2 true).1 =
          2 * B := by
      rw [← mul_add, s1]; ring
    have : N * (isKLRandom_iff_total_normalize_fac qa ta.1 ta.2 false).2 +
        N * (isKLRandom_iff_total_normalize_fac qa ta.1 ta.2 true).2 =
          2 * N := by
      rw [← mul_add, s2]; ring
    linarith

/-- Step 4a of the proof of `isKLRandom_iff_total_normalize`: the pure
growth lemma.  Let `c` be a nonnegative unbounded sequence (the capital of `β` along the run) and
`B, N` sequences from `1` whose steps are: an over-bet step (`c (t+1) > 2 c t`, `B` doubles, `N`
unchanged), or a normal step (`c (t+1) ≤ 2 c t`, `B` unchanged, and either `c t > 0` and `N` is
multiplied by `(1 + c(t+1)/c t)/2`, or `c t = 0` and `N` unchanged).  Then `(B + N)/2` is unbounded.
Proof: with infinitely many over-bets `B → ∞` (`B ≥ 1` is nondecreasing, `N > 0`); otherwise after
the last over-bet `c` stays positive (a zero stays zero, contradicting unboundedness) and AM-GM
`(1 + ρ)/2 ≥ √ρ` gives `N_T ≥ N_{t₀} √(c_T / c_{t₀}) → ∞`. -/
private lemma isKLRandom_iff_total_growth (c B N : ℕ → ℚ)
    (hc0 : ∀ t, 0 ≤ c t) (hB0 : B 0 = 1) (hN0 : N 0 = 1)
    (hstep : ∀ t, (2 * c t < c (t + 1) ∧ B (t + 1) = 2 * B t ∧ N (t + 1) = N t) ∨
      (c (t + 1) ≤ 2 * c t ∧ B (t + 1) = B t ∧
        ((0 < c t ∧ N (t + 1) = N t * ((1 + c (t + 1) / c t) / 2)) ∨
          (c t = 0 ∧ N (t + 1) = N t))))
    (hunb : ¬ BddAbove (Set.range fun t => (c t : ℝ))) :
    ¬ BddAbove (Set.range fun t => (((B t + N t) / 2 : ℚ) : ℝ)) := by
  classical
  have hunbQ : ∀ R : ℚ, ∃ t, R < c t := by
    intro R
    obtain ⟨y, ⟨t, rfl⟩, h⟩ := not_bddAbove_iff.mp hunb (R : ℝ)
    exact ⟨t, by exact_mod_cast (show (R : ℝ) < (c t : ℝ) from h)⟩
  have hN : ∀ t, 0 < N t := by
    intro t
    induction t with
    | zero => rw [hN0]; norm_num
    | succ t ih =>
      rcases hstep t with ⟨_, _, h⟩ | ⟨_, _, ⟨hc, h⟩ | ⟨_, h⟩⟩
      · rw [h]; exact ih
      · rw [h]
        have : 0 ≤ c (t + 1) / c t := div_nonneg (hc0 _) hc.le
        have h2 : 0 < (1 + c (t + 1) / c t) / 2 := by linarith
        exact mul_pos ih h2
      · rw [h]; exact ih
  obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → ℕ, f 0 = 0 ∧
      ∀ t, f (t + 1) = f t + if 2 * c t < c (t + 1) then 1 else 0 :=
    ⟨fun t => ∑ i ∈ Finset.range t, if 2 * c i < c (i + 1) then 1 else 0, by simp,
      fun t => Finset.sum_range_succ _ _⟩
  have hBf : ∀ t, B t = 2 ^ f t := by
    intro t
    induction t with
    | zero => rw [hB0, hf0]; norm_num
    | succ t ih =>
      rcases hstep t with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
      · rw [hfs, ite_eq_left h1, h2, ih, pow_succ]; ring
      · rw [hfs, ite_eq_right (not_lt.mpr h1), h2, ih]; simp
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨q, hq⟩ := exists_rat_gt M
  have hbd : ∀ t, B t + N t ≤ 2 * q := by
    intro t
    have h1 := hM ⟨t, rfl⟩
    have h2 : ((B t + N t) / 2 : ℚ) ≤ q := by
      have : (((B t + N t) / 2 : ℚ) : ℝ) ≤ (q : ℝ) := h1.trans hq.le
      exact_mod_cast this
    linarith
  have hBq : ∀ t, B t ≤ 2 * q := fun t => by linarith [hbd t, hN t]
  have hNq : ∀ t, N t ≤ 2 * q := by
    intro t
    have : 0 < B t := by rw [hBf]; positivity
    linarith [hbd t]
  have hfK : ∀ t, f t ≤ ⌈2 * q⌉₊ := by
    intro t
    have h1 : f t < 2 ^ f t := Nat.lt_two_pow_self
    have h2 : (f t : ℚ) < 2 ^ f t := by exact_mod_cast h1
    have h3 : (f t : ℚ) < ⌈2 * q⌉₊ := by
      calc (f t : ℚ) < 2 ^ f t := h2
        _ = B t := (hBf t).symm
        _ ≤ 2 * q := hBq t
        _ ≤ ⌈2 * q⌉₊ := Nat.le_ceil _
    exact_mod_cast h3.le
  have hbddf : BddAbove (Set.range f) := ⟨⌈2 * q⌉₊, by rintro _ ⟨t, rfl⟩; exact hfK t⟩
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem hne hbddf
  have hmax : ∀ s, f s ≤ f T := by
    intro s
    rw [hT]
    exact le_csSup hbddf ⟨s, rfl⟩
  have hmono : Monotone f := monotone_nat_of_le_succ (fun t => by rw [hfs]; omega)
  have hnoO : ∀ s, T ≤ s → ¬ 2 * c s < c (s + 1) := by
    intro s hs hO
    have h1 := hfs s
    rw [ite_eq_left hO] at h1
    have h2 := hmax (s + 1)
    have h3 := hmono hs
    omega
  have hstep' : ∀ s, T ≤ s → c (s + 1) ≤ 2 * c s ∧
      ((0 < c s ∧ N (s + 1) = N s * ((1 + c (s + 1) / c s) / 2)) ∨
        (c s = 0 ∧ N (s + 1) = N s)) := by
    intro s hs
    rcases hstep s with ⟨h1, _, _⟩ | ⟨h1, _, h3⟩
    · exact absurd h1 (hnoO s hs)
    · exact ⟨h1, h3⟩
  have hpos : ∀ s, T ≤ s → 0 < c s := by
    intro s hs
    by_contra hneg
    have hz : c s = 0 := le_antisymm (not_lt.mp hneg) (hc0 s)
    have hzero : ∀ u, c (s + u) = 0 := by
      intro u
      induction u with
      | zero => simpa using hz
      | succ u ih =>
        have h1 := (hstep' (s + u) (by omega)).1
        have h2 := hc0 (s + u + 1)
        have : c (s + (u + 1)) = c (s + u + 1) := by rw [add_assoc]
        rw [this]
        linarith
    obtain ⟨t, ht⟩ := hunbQ (∑ i ∈ Finset.range s, c i)
    by_cases hts : t < s
    · have := Finset.single_le_sum (f := c) (fun i _ => hc0 i) (Finset.mem_range.2 hts)
      linarith
    · have h1 : c t = 0 := by
        have := hzero (t - s)
        rwa [show s + (t - s) = t by omega] at this
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range s) => hc0 i)
      linarith
  have hind : ∀ n, N T ^ 2 * c (T + n) ≤ N (T + n) ^ 2 * c T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : T ≤ T + n := by omega
      obtain ⟨_, hcase⟩ := hstep' (T + n) hs
      rcases hcase with ⟨hcs, hNs⟩ | ⟨hz, _⟩
      · set s := T + n with hsdef
        have hρ0 : 0 ≤ c (s + 1) / c s := div_nonneg (hc0 _) hcs.le
        have hρ : c (s + 1) / c s * c s = c (s + 1) := div_mul_cancel₀ _ hcs.ne'
        set ρ := c (s + 1) / c s with hρdef
        have h1 : ρ ≤ ((1 + ρ) / 2) ^ 2 := by nlinarith [sq_nonneg (1 - ρ)]
        have h2 : 0 ≤ N s ^ 2 * c T := mul_nonneg (sq_nonneg _) (hc0 T)
        change N T ^ 2 * c (s + 1) ≤ N (s + 1) ^ 2 * c T
        calc N T ^ 2 * c (s + 1) = (N T ^ 2 * c s) * ρ := by rw [← hρ]; ring
          _ ≤ (N s ^ 2 * c T) * ρ := mul_le_mul_of_nonneg_right ih hρ0
          _ ≤ (N s ^ 2 * c T) * ((1 + ρ) / 2) ^ 2 := mul_le_mul_of_nonneg_left h1 h2
          _ = N (s + 1) ^ 2 * c T := by rw [hNs]; ring
      · exact absurd hz (hpos _ hs).ne'
  have hNT : 0 < N T := hN T
  have hcT : 0 < c T := hpos T le_rfl
  set D : ℚ := (2 * q) ^ 2 * c T / N T ^ 2 with hD
  have hDnn : 0 ≤ D := div_nonneg (mul_nonneg (sq_nonneg _) hcT.le) (sq_nonneg _)
  have hND : N T ^ 2 * D = (2 * q) ^ 2 * c T := by
    rw [hD]; field_simp
  obtain ⟨t, ht⟩ := hunbQ ((∑ i ∈ Finset.range T, c i) + D + 1)
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range T, c i := Finset.sum_nonneg (fun i _ => hc0 i)
  by_cases htT : t < T
  · have := Finset.single_le_sum (f := c) (fun i _ => hc0 i) (Finset.mem_range.2 htT)
    linarith
  · have hTt : T ≤ t := not_lt.mp htT
    have h1 := hind (t - T)
    rw [show T + (t - T) = t by omega] at h1
    have h2 : D < c t := by linarith
    have h3 : N T ^ 2 * D < N T ^ 2 * c t := mul_lt_mul_of_pos_left h2 (by positivity)
    have h4 : (2 * q) ^ 2 * c T < N t ^ 2 * c T := by linarith
    have h5 : (2 * q) ^ 2 < N t ^ 2 := lt_of_mul_lt_mul_right h4 hcT.le
    have h6 : N t ^ 2 ≤ (2 * q) ^ 2 := pow_le_pow_left₀ (hN t).le (hNq t) 2
    linarith

/-- Step 4b of the proof of `isKLRandom_iff_total_normalize`: one step
of the accounts along a string.  If `(B, N)` is the value of the fold at `x`, `q ∈ cap x` and
`q' ∈ cap (x ++ [c])`, then the fold is defined at `x ++ [c]`, and its value `(B', N')` is an
over-bet step (`q' > 2 q`, `B' = 2 B`, `N' = N`) or a normal step (`q' ≤ 2 q`, `B' = B`, and
`N' = N (1 + q'/q)/2` if `q > 0`, `N' = N` if `q = 0`).  Uses fairness of `cap` on jointly defined
triples: the over-bet child's sibling cannot be defined (it would be negative); for the tagged
sibling `(3 - r)/2 = (1 + (2q - v)/q)/2 = (1 + q'/q)/2`. -/
private lemma isKLRandom_iff_total_onestep
    (cap : BitString →. ℚ) (k : BitString →. Bool × ℚ) (hnn : ∀ x, ∀ q ∈ cap x, 0 ≤ q)
    (hfair : ∀ x q q₀ q₁, q ∈ cap x → q₀ ∈ cap (x ++ [false]) → q₁ ∈ cap (x ++ [true]) →
      q = (q₀ + q₁) / 2)
    (hk : ∀ x, (∀ t ∈ k x, t.2 ∈ cap (x ++ [t.1])) ∧
      ((k x).Dom ↔ (cap (x ++ [false])).Dom ∨ (cap (x ++ [true])).Dom))
    (x : BitString) (B N q : ℚ) (c : Bool) (q' : ℚ)
    (hG : (B, N) ∈ isKLRandom_iff_total_normalize_G cap k x)
    (hq : q ∈ cap x) (hq' : q' ∈ cap (x ++ [c])) :
    ∃ B' N', (B', N') ∈ isKLRandom_iff_total_normalize_G cap k (x ++ [c]) ∧
      ((2 * q < q' ∧ B' = 2 * B ∧ N' = N) ∨
       (q' ≤ 2 * q ∧ B' = B ∧
        ((0 < q ∧ N' = N * ((1 + q' / q) / 2)) ∨ (q = 0 ∧ N' = N)))) := by
  have hdom : (k x).Dom := (hk x).2.2 (by
    cases c
    · exact Or.inl hq'.1
    · exact Or.inr hq'.1)
  obtain ⟨t, ht⟩ : ∃ t, t ∈ k x := ⟨(k x).get hdom, Part.get_mem hdom⟩
  have hv : t.2 ∈ cap (x ++ [t.1]) := (hk x).1 t ht
  have hv0 : 0 ≤ t.2 := hnn _ _ hv
  have hq0 : 0 ≤ q := hnn _ _ hq
  have hq'0 : 0 ≤ q' := hnn _ _ hq'
  have hsame : c = t.1 → q' = t.2 := fun h => by
    subst h; exact Part.mem_unique hq' hv
  have hdiff : c ≠ t.1 → q' = 2 * q - t.2 := fun h => by
    have : q = (q' + t.2) / 2 ∨ q = (t.2 + q') / 2 := by
      rcases hc : c with _ | _ <;> rcases ha : t.1 with _ | _
      · exact absurd (hc.trans ha.symm) h
      · rw [hc] at hq'; rw [ha] at hv
        exact Or.inl (hfair x q q' t.2 hq hq' hv)
      · rw [hc] at hq'; rw [ha] at hv
        exact Or.inr (hfair x q t.2 q' hq hv hq')
      · exact absurd (hc.trans ha.symm) h
    rcases this with h | h <;> linarith
  refine ⟨B * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).1,
    N * (isKLRandom_iff_total_normalize_fac q t.1 t.2 c).2,
    (isKLRandom_iff_total_normalize_aux_G_append_mem cap k x c _ _).2
      ⟨B, N, hG, q, hq, t, ht, rfl, rfl⟩, ?_⟩
  unfold isKLRandom_iff_total_normalize_fac
  by_cases h1 : 2 * q < t.2
  · by_cases hc : c = t.1
    · have := hsame hc
      simp only [h1, hc, ite_true]
      left; refine ⟨by linarith, by ring, by ring⟩
    · have := hdiff hc
      exfalso; linarith
  · by_cases h2 : 0 < q
    · by_cases hc : c = t.1
      · have := hsame hc
        simp only [ite_eq_right h1, ite_eq_left h2, ite_eq_left hc]
        right; refine ⟨by linarith, by ring, Or.inl ⟨h2, by rw [this]⟩⟩
      · have := hdiff hc
        simp only [ite_eq_right h1, ite_eq_left h2, ite_eq_right hc]
        right
        refine ⟨by linarith, by ring, Or.inl ⟨h2, ?_⟩⟩
        rw [this]
        field_simp
        ring
    · have hq00 : q = 0 := le_antisymm (not_lt.1 h2) hq0
      have hv00 : t.2 = 0 := by
        have := not_lt.1 h1
        linarith
      have hq'00 : q' = 0 := by
        by_cases hc : c = t.1
        · rw [hsame hc, hv00]
        · rw [hdiff hc, hv00, hq00]; ring
      simp only [h1, h2, ite_false]
      right
      exact ⟨by linarith, by ring, Or.inr ⟨hq00, by ring⟩⟩

/-- Step 4c of the proof of `isKLRandom_iff_total_normalize`: winning.
If `β` wins on `w`, its run `x_t = β.toRule.revealed w t` extends by one bit at each step
(`x_{t+1} = x_t ++ [c_t]`, as `t ≤ |x_t|`), `β.capital x_t` is defined, so by step 4b the fold is
defined along the run with `(B_t, N_t)` satisfying the hypotheses of step 4a (with `c_t` the capital
of `β`, `B_0 = N_0 = 1`), and `(B_t + N_t)/2` is unbounded. -/
private lemma isKLRandom_iff_total_wins (β : KLBetting)
    (k : BitString →. Bool × ℚ)
    (hk : ∀ x, (∀ t ∈ k x, t.2 ∈ β.capital (x ++ [t.1])) ∧
      ((k x).Dom ↔ (β.capital (x ++ [false])).Dom ∨ (β.capital (x ++ [true])).Dom))
    (w : CantorSeq) (hw : β.Wins w) :
    (∀ t, (isKLRandom_iff_total_normalize_cap β.capital k
        (β.toRule.revealed w t)).Dom) ∧
    ¬ BddAbove {r : ℝ | ∃ t, ∃ q ∈ isKLRandom_iff_total_normalize_cap β.capital k
        (β.toRule.revealed w t), (q : ℝ) = r} := by
  classical
  obtain ⟨hlen, hdom, hunb⟩ := hw
  set x : ℕ → BitString := β.toRule.revealed w with hx
  have hrec : ∀ t, x (t + 1) = if h : (β.next (x t)).Dom then
      x t ++ [w ((β.next (x t)).get h)] else x t := fun t => rfl
  have hle : ∀ t, (x t).length ≤ t := by
    intro t
    induction t with
    | zero => simp [hx, KLRule.revealed]
    | succ t ih =>
      rw [hrec]
      split_ifs
      · simp only [List.length_append, List.length_singleton]
        omega
      · omega
  have hlen' : ∀ t, (x t).length = t := fun t => le_antisymm (hle t) (hlen t)
  have hsucc : ∀ t, ∃ b : Bool, x (t + 1) = x t ++ [b] := by
    intro t
    have hd : (β.next (x t)).Dom := by
      by_contra hnd
      have h1 : x (t + 1) = x t := by
        rw [hrec]
        exact dite_eq_right hnd
      have := hlen' (t + 1)
      rw [h1, hlen' t] at this
      omega
    refine ⟨w ((β.next (x t)).get hd), ?_⟩
    rw [hrec]
    exact dite_eq_left hd
  choose b hb using hsucc
  -- capital of `β` along the run
  have hq : ∀ t, ((β.capital (x t)).get (hdom t)) ∈ β.capital (x t) := fun t => Part.get_mem _
  set c : ℕ → ℚ := fun t => (β.capital (x t)).get (hdom t) with hc
  have hcmem : ∀ t, c t ∈ β.capital (x t) := hq
  have hstep : ∀ t (p : ℚ × ℚ), ∃ p' : ℚ × ℚ,
      p ∈ isKLRandom_iff_total_normalize_G β.capital k (x t) →
        p' ∈ isKLRandom_iff_total_normalize_G β.capital k (x (t + 1)) ∧
        ((2 * c t < c (t + 1) ∧ p'.1 = 2 * p.1 ∧ p'.2 = p.2) ∨
          (c (t + 1) ≤ 2 * c t ∧ p'.1 = p.1 ∧
            ((0 < c t ∧ p'.2 = p.2 * ((1 + c (t + 1) / c t) / 2)) ∨
              (c t = 0 ∧ p'.2 = p.2)))) := by
    intro t p
    by_cases hp : p ∈ isKLRandom_iff_total_normalize_G β.capital k (x t)
    · have hcm : c (t + 1) ∈ β.capital (x t ++ [b t]) := by
        rw [← hb t]; exact hcmem (t + 1)
      obtain ⟨B', N', hG', hrel⟩ :=
        isKLRandom_iff_total_onestep β.capital k β.nonneg
          β.fair hk (x t) p.1 p.2 (c t) (b t) (c (t + 1)) hp (hcmem t) hcm
      refine ⟨(B', N'), fun _ => ⟨?_, hrel⟩⟩
      rw [hb t]; exact hG'
    · exact ⟨p, fun h => absurd h hp⟩
  choose f hf using hstep
  set S : ℕ → ℚ × ℚ := fun t => Nat.rec (1, 1) (fun t p => f t p) t with hS
  have hS0 : S 0 = (1, 1) := rfl
  have hSs : ∀ t, S (t + 1) = f t (S t) := fun t => rfl
  have hSG : ∀ t, S t ∈ isKLRandom_iff_total_normalize_G β.capital k (x t) := by
    intro t
    induction t with
    | zero => exact isKLRandom_iff_total_normalize_aux_G_nil β.capital k
    | succ t ih => rw [hSs]; exact (hf t (S t) ih).1
  have hcap : ∀ t, isKLRandom_iff_total_normalize_cap β.capital k (x t) =
      Part.some ((((S t).1 + (S t).2) / 2 : ℚ)) := by
    intro t
    unfold isKLRandom_iff_total_normalize_cap
    exact Part.eq_some_iff.2 (Part.mem_map_iff _ |>.2 ⟨S t, hSG t, rfl⟩)
  have hcmem' : ∀ t, ∀ q ∈ isKLRandom_iff_total_normalize_cap β.capital k (x t),
      q = ((S t).1 + (S t).2) / 2 := by
    intro t q hq'
    rw [hcap t] at hq'
    exact Part.mem_some_iff.1 hq'
  refine ⟨fun t => ?_, ?_⟩
  · rw [hcap t]; trivial
  · have hgrow := isKLRandom_iff_total_growth c
      (fun t => (S t).1) (fun t => (S t).2) (fun t => β.nonneg _ _ (hcmem t))
      (by rw [hS0]) (by rw [hS0]) (fun t => by
        have := (hf t (S t) (hSG t)).2
        rw [← hSs] at this
        exact this) (by
        intro hbdd
        apply hunb
        obtain ⟨M, hM⟩ := hbdd
        refine ⟨M, ?_⟩
        rintro r ⟨t, q, hqt, rfl⟩
        have : q = c t := Part.mem_unique hqt (hcmem t)
        subst this
        exact hM ⟨t, rfl⟩)
    intro hbdd
    apply hgrow
    obtain ⟨M, hM⟩ := hbdd
    refine ⟨M, ?_⟩
    rintro r ⟨t, rfl⟩
    exact hM ⟨t, _, by rw [hcap t]; exact Part.mem_some _, rfl⟩

/-- Step 1 of the proof of `isKLRandom_iff_total_split` (Stage A: over-bet
normalization).  Replace `β` by a strategy `γ` with the same scan function whose capital is partial
computable, equal to `1` at the empty string, strictly positive wherever defined, never overbets,
and
which still wins on every sequence on which `β` wins.

Construction: let `γ(x) = (B(x) + N(x)) / 2`, where the pair `(B, N)` is computed by a left fold
over
the history from `(1, 1)`. At a proper prefix `y` of `x`, wait for `q = β.capital y` and for the
first
halting child (`Partrec.merge'` on the two tagged child computations; defined iff some child halts),
with tag `a` and value `v`: if `v > 2q` (over-bet; its sibling is undefined), `B` is multiplied by
`2`
on child `a` and by `0` on child `ā`, `N` by `1`; if `v ≤ 2q` and `q > 0`, with `r = v / q ∈ [0,
2]`,
`B` is multiplied by `1`, `N` by `(1 + r) / 2` on child `a` and by `(3 - r) / 2` on child `ā`; if
`q = 0`, both by `1`.  Every factor pair sums to `2` (fairness on jointly defined triples), `N > 0`
(positivity), `γ(xc) ≤ 2 γ(x)`.  Winning: with infinitely many over-bets along the run `B → ∞`;
otherwise after the last over-bet `β`'s capital is positive on the run (a zero stays zero) and
AM-GM `(1 + r) / 2 ≥ √r` gives `N_T ≥ 2^{-t₀} √(c_T / c_{t₀}) → ∞`.  (Never play the exact ratio on
normal steps and never multiply `B * N`.) -/
private lemma isKLRandom_iff_total_normalize (β : KLBetting)
    (hcap : Partrec β.capital) :
    ∃ γ : KLBetting, γ.next = β.next ∧ Partrec γ.capital ∧ (1 : ℚ) ∈ γ.capital [] ∧
      (∀ x, ∀ q ∈ γ.capital x, 0 < q) ∧ isKLRandom_iff_total_NoOverBet γ ∧
      ∀ w, β.Wins w → γ.Wins w := by
  obtain ⟨k, hk, hkspec⟩ := isKLRandom_iff_total_tag β hcap
  obtain ⟨h1, hpos, hnb, hfair⟩ := isKLRandom_iff_total_algebra
    β.capital k β.nonneg (fun x => (hkspec x).1)
  refine ⟨{ next := β.next
            capital := isKLRandom_iff_total_normalize_cap β.capital k
            noRepeat := β.noRepeat
            nonneg := fun x q hq => (hpos x q hq).le
            fair := hfair }, rfl,
    isKLRandom_iff_total_partrec β.capital k hcap hk,
    h1, hpos, hnb, ?_⟩
  intro w hw
  obtain ⟨hd, hb⟩ := isKLRandom_iff_total_wins β k hkspec w hw
  exact ⟨hw.1, hd, hb⟩

/-- Total rational division, `0` unless the denominator is positive. -/
private def isKLRandom_iff_total_parity_divd (a b : ℚ) : ℚ :=
  if 0 < b then a / b else 0

private lemma isKLRandom_iff_total_parity_divd_computable :
    Computable₂ isKLRandom_iff_total_parity_divd := by
  have hc : Computable (fun p : ℚ × ℚ => decide (0 < p.2.num.toNat)) := by
    have h1 : Computable (fun p : ℚ × ℚ => p.2.num.toNat) :=
      ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp Computable.snd)
    exact (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide.to_comp.comp h1
  have hN : Computable (fun p : ℚ × ℚ => if 0 < p.2.num.toNat then p.1.num * (p.2.den : ℤ) else 0)
      := by
    have : Computable (fun p : ℚ × ℚ => cond (decide (0 < p.2.num.toNat)) (p.1.num * (p.2.den : ℤ))
                                          0) :=
      Computable.cond hc
        (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.fst)
          (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.snd)))
        (Computable.const 0)
    exact this.of_eq fun p => by by_cases h : 0 < p.2.num.toNat <;> simp [h]
  have hD : Computable (fun p : ℚ × ℚ => if 0 < p.2.num.toNat then p.1.den * p.2.num.toNat else 1)
      := by
    have : Computable (fun p : ℚ × ℚ => cond (decide (0 < p.2.num.toNat)) (p.1.den * p.2.num.toNat)
                                          1) :=
      Computable.cond hc
        (Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst)
          (ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp Computable.snd)))
        (Computable.const 1)
    exact this.of_eq fun p => by by_cases h : 0 < p.2.num.toNat <;> simp [h]
  refine computable_of_num_den
    (f := fun p : ℚ × ℚ => isKLRandom_iff_total_parity_divd p.1 p.2) hN hD ?_ ?_
  · intro p
    by_cases h : 0 < p.2.num.toNat
    · simp [h, Nat.pos_of_ne_zero, p.1.den_nz]
    · simp [h]
  · intro p
    by_cases h : 0 < p.2.num.toNat
    · have hb : 0 < p.2 := by
        rw [← Rat.num_pos]; omega
      simp only [h, ite_true, isKLRandom_iff_total_parity_divd, hb]
      have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
      have h2 : (p.2.num : ℚ) = p.2 * (p.2.den : ℚ) := (Rat.mul_den_eq_num p.2).symm
      have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
      have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
      have hn2 : ((p.2.num.toNat : ℕ) : ℚ) = p.2.num := by
        have : ((p.2.num.toNat : ℕ) : ℤ) = p.2.num := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      push_cast
      rw [hn2, h1, h2]
      have : p.2 ≠ 0 := hb.ne'
      field_simp
    · have hb : ¬ 0 < p.2 := by
        rw [← Rat.num_pos]; omega
      simp [h, isKLRandom_iff_total_parity_divd, hb]

/-- One step of the parity-restricted capital: the factor `γ z / γ y` if the card `γ.next y` has
parity `p`, and `1` otherwise (defined iff `γ.next y`, `γ z`, `γ y` are). -/
private def isKLRandom_iff_total_parity_stepf (γ : KLBetting) (p : Bool)
    (y z : BitString) (i : ℚ) : Part ℚ :=
  (γ.next y).bind fun m => (γ.capital z).bind fun gz => (γ.capital y).map fun gy =>
    i * (if Nat.bodd m = p then isKLRandom_iff_total_parity_divd gz gy else 1)

private def isKLRandom_iff_total_parity_recf (γ : KLBetting) (p : Bool)
    (x : BitString) (n : ℕ) : Part ℚ :=
  Nat.rec (motive := fun _ => Part ℚ) (Part.some 1)
    (fun n IH => IH.bind fun i =>
      isKLRandom_iff_total_parity_stepf γ p (x.take n) (x.take (n + 1)) i) n

/-- The capital `b_p` of the parity split: a left fold over the prefixes. -/
private def isKLRandom_iff_total_parity_cap (γ : KLBetting) (p : Bool)
    (x : BitString) : Part ℚ :=
  isKLRandom_iff_total_parity_recf γ p x x.length

private lemma isKLRandom_iff_total_parity_recf_append (γ : KLBetting) (p : Bool)
    (x l : BitString) (n : ℕ) (hn : n ≤ x.length) :
    isKLRandom_iff_total_parity_recf γ p (x ++ l) n =
      isKLRandom_iff_total_parity_recf γ p x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (isKLRandom_iff_total_parity_recf γ p (x ++ l) n).bind _ =
      (isKLRandom_iff_total_parity_recf γ p x n).bind _
    rw [ih (by omega), List.take_append_of_le_length (by omega),
      List.take_append_of_le_length hn]

private lemma isKLRandom_iff_total_parity_cap_nil (γ : KLBetting) (p : Bool) :
    isKLRandom_iff_total_parity_cap γ p [] = Part.some 1 := rfl

private lemma isKLRandom_iff_total_parity_cap_snoc (γ : KLBetting) (p : Bool)
    (x : BitString) (c : Bool) :
    isKLRandom_iff_total_parity_cap γ p (x ++ [c]) =
      (isKLRandom_iff_total_parity_cap γ p x).bind fun i =>
        isKLRandom_iff_total_parity_stepf γ p x (x ++ [c]) i := by
  unfold isKLRandom_iff_total_parity_cap
  rw [List.length_append, List.length_singleton]
  change (isKLRandom_iff_total_parity_recf γ p (x ++ [c]) x.length).bind _ = _
  rw [isKLRandom_iff_total_parity_recf_append γ p x [c] x.length le_rfl,
    List.take_left, List.take_of_length_le (by simp)]

private lemma isKLRandom_iff_total_parity_cap_snoc_mem (γ : KLBetting) (p : Bool)
    (x : BitString) (c : Bool) (q' : ℚ) :
    q' ∈ isKLRandom_iff_total_parity_cap γ p (x ++ [c]) ↔
      ∃ i ∈ isKLRandom_iff_total_parity_cap γ p x, ∃ m ∈ γ.next x,
      ∃ gz ∈ γ.capital (x ++ [c]), ∃ gy ∈ γ.capital x,
        q' = i * (if Nat.bodd m = p then isKLRandom_iff_total_parity_divd gz gy
          else 1) := by
  rw [isKLRandom_iff_total_parity_cap_snoc]
  simp only [isKLRandom_iff_total_parity_stepf, Part.mem_bind_iff,
    Part.mem_map_iff]
  constructor
  · rintro ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩
    exact ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩
  · rintro ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩
    exact ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩

private lemma isKLRandom_iff_total_parity_cap_partrec (γ : KLBetting)
    (hnext : Partrec γ.next) (hcap : Partrec γ.capital) (p : Bool) :
    Partrec (isKLRandom_iff_total_parity_cap γ p) := by
  have hy : Computable (fun q : BitString × (ℕ × ℚ) => q.1.take q.2.1) :=
    Primrec.list_take.to_comp.comp (Computable.fst.comp Computable.snd) Computable.fst
  have hz : Computable (fun q : BitString × (ℕ × ℚ) => q.1.take (q.2.1 + 1)) :=
    Primrec.list_take.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 1))
      Computable.fst
  have hstep : Partrec₂ (fun (x : BitString) (ni : ℕ × ℚ) =>
      isKLRandom_iff_total_parity_stepf γ p (x.take ni.1) (x.take (ni.1 + 1))
        ni.2) := by
    unfold isKLRandom_iff_total_parity_stepf
    refine Partrec.bind (hnext.comp hy) ?_
    refine Partrec.bind (hcap.comp (hz.comp Computable.fst)) ?_
    refine Partrec.map (hcap.comp (hy.comp (Computable.fst.comp Computable.fst))) ?_
    have hcb0 : Computable (fun m : ℕ => decide (Nat.bodd m = p)) :=
      (PrimrecRel.comp (Primrec.eq (α := Bool)) Primrec.nat_bodd (Primrec.const p)).decide.to_comp
    have hm : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ => s.1.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hcb : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ =>
        decide (Nat.bodd s.1.1.2 = p)) := hcb0.comp hm
    have hdv : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ =>
        isKLRandom_iff_total_parity_divd s.1.2 s.2) :=
      isKLRandom_iff_total_parity_divd_computable.comp
        (Computable.snd.comp Computable.fst) Computable.snd
    have hi : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ => s.1.1.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst)))
    have hfac : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ =>
        cond (decide (Nat.bodd s.1.1.2 = p))
          (isKLRandom_iff_total_parity_divd s.1.2 s.2) 1) :=
      Computable.cond hcb hdv (Computable.const 1)
    have hfin : Computable (fun s : (((BitString × (ℕ × ℚ)) × ℕ) × ℚ) × ℚ =>
        s.1.1.1.2.2 * cond (decide (Nat.bodd s.1.1.2 = p))
          (isKLRandom_iff_total_parity_divd s.1.2 s.2) 1) :=
      Computable₂.comp (f := fun a b : ℚ => a * b) computable₂_ratMul hi hfac
    refine Computable.of_eq hfin (fun s => ?_)
    by_cases h : Nat.bodd s.1.1.2 = p <;> simp [h]
  exact (Partrec.nat_rec (f := List.length) (g := fun _ => Part.some 1)
    (h := fun (x : BitString) (ni : ℕ × ℚ) =>
      isKLRandom_iff_total_parity_stepf γ p (x.take ni.1) (x.take (ni.1 + 1))
        ni.2)
    Computable.list_length (Computable.const (1 : ℚ)).partrec hstep).of_eq fun x => rfl

private lemma isKLRandom_iff_total_parity_divd_of_pos {a b : ℚ} (hb : 0 < b) :
    isKLRandom_iff_total_parity_divd a b = a / b := ite_eq_left hb

private lemma isKLRandom_iff_total_parity_cap_pos (γ : KLBetting)
    (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q) (p : Bool) :
    ∀ x, ∀ q ∈ isKLRandom_iff_total_parity_cap γ p x, 0 < q := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro q hq
    rw [isKLRandom_iff_total_parity_cap_nil] at hq
    rw [Part.mem_some_iff.1 hq]; exact one_pos
  | append_singleton y c ih =>
    intro q hq
    obtain ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩ :=
      (isKLRandom_iff_total_parity_cap_snoc_mem γ p y c q).1 hq
    have hi0 := ih i hi
    have hgz0 := hpos _ gz hgz
    have hgy0 := hpos _ gy hgy
    split_ifs
    · rw [isKLRandom_iff_total_parity_divd_of_pos hgy0]; positivity
    · simpa using hi0

private lemma isKLRandom_iff_total_parity_cap_fair (γ : KLBetting)
    (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q) (p : Bool)
    (x : BitString) (q q₀ q₁ : ℚ) (hq : q ∈ isKLRandom_iff_total_parity_cap γ p x)
    (hq₀ : q₀ ∈ isKLRandom_iff_total_parity_cap γ p (x ++ [false]))
    (hq₁ : q₁ ∈ isKLRandom_iff_total_parity_cap γ p (x ++ [true])) :
    q = (q₀ + q₁) / 2 := by
  obtain ⟨i₀, hi₀, m₀, hm₀, gz₀, hgz₀, gy₀, hgy₀, rfl⟩ :=
    (isKLRandom_iff_total_parity_cap_snoc_mem γ p x false _).1 hq₀
  obtain ⟨i₁, hi₁, m₁, hm₁, gz₁, hgz₁, gy₁, hgy₁, rfl⟩ :=
    (isKLRandom_iff_total_parity_cap_snoc_mem γ p x true _).1 hq₁
  have e1 := Part.mem_unique hi₀ hq
  have e2 := Part.mem_unique hi₁ hq
  have e3 := Part.mem_unique hm₀ hm₁
  have e4 := Part.mem_unique hgy₀ hgy₁
  subst e1 e2 e3 e4
  have hfair := γ.fair x gy₀ gz₀ gz₁ hgy₀ hgz₀ hgz₁
  have hgy0 := hpos _ gy₀ hgy₀
  split_ifs
  · rw [isKLRandom_iff_total_parity_divd_of_pos hgy0,
      isKLRandom_iff_total_parity_divd_of_pos hgy0]
    have : gz₀ + gz₁ = 2 * gy₀ := by linarith
    field_simp
    linear_combination (-i₁) * this
  · ring

private def isKLRandom_iff_total_parity_bet (γ : KLBetting)
    (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q) (p : Bool) : KLBetting where
  next := γ.next
  capital := isKLRandom_iff_total_parity_cap γ p
  noRepeat := γ.noRepeat
  nonneg := fun x q hq =>
    (isKLRandom_iff_total_parity_cap_pos γ hpos p x q hq).le
  fair := fun x q q₀ q₁ hq hq₀ hq₁ =>
    isKLRandom_iff_total_parity_cap_fair γ hpos p x q q₀ q₁ hq hq₀ hq₁

private lemma isKLRandom_iff_total_parity_bet_parity (γ : KLBetting)
    (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q) (p : Bool) :
    isKLRandom_iff_total_OnlyBetsOnParity
      (isKLRandom_iff_total_parity_bet γ hpos p) p := by
  intro x n hn hnp q hq c q' hq'
  obtain ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩ :=
    (isKLRandom_iff_total_parity_cap_snoc_mem γ p x c q').1 hq'
  have e1 := Part.mem_unique hi hq
  have e2 : m = n := Part.mem_unique hm hn
  subst e1 e2
  rw [ite_eq_right hnp, mul_one]

private lemma isKLRandom_iff_total_parity_bet_nobet (γ : KLBetting)
    (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q)
    (hnobet : isKLRandom_iff_total_NoOverBet γ) (p : Bool) :
    isKLRandom_iff_total_NoOverBet
      (isKLRandom_iff_total_parity_bet γ hpos p) := by
  intro x q hq c q' hq'
  obtain ⟨i, hi, m, hm, gz, hgz, gy, hgy, rfl⟩ :=
    (isKLRandom_iff_total_parity_cap_snoc_mem γ p x c q').1 hq'
  have e1 := Part.mem_unique hi hq
  subst e1
  have hq0 := isKLRandom_iff_total_parity_cap_pos γ hpos p x i hq
  have hgy0 := hpos _ gy hgy
  have hle := hnobet x gy hgy c gz hgz
  split_ifs
  · rw [isKLRandom_iff_total_parity_divd_of_pos hgy0]
    have : gz / gy ≤ 2 := by rw [div_le_iff₀ hgy0]; linarith
    nlinarith
  · linarith

private lemma isKLRandom_iff_total_parity_cap_prod (γ : KLBetting)
    (h1 : (1 : ℚ) ∈ γ.capital []) (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q) :
    ∀ x, (∀ y, y <+: x → (γ.capital y).Dom) → (∀ y, y <+: x → y ≠ x → (γ.next y).Dom) →
      ∀ g ∈ γ.capital x,
        ∃ a ∈ isKLRandom_iff_total_parity_cap γ true x,
        ∃ b ∈ isKLRandom_iff_total_parity_cap γ false x, g = a * b := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro _ _ g hg
    have : g = 1 := Part.mem_unique hg h1
    subst this
    exact ⟨1, by rw [isKLRandom_iff_total_parity_cap_nil]; exact Part.mem_some _,
      1, by rw [isKLRandom_iff_total_parity_cap_nil]; exact Part.mem_some _,
      by norm_num⟩
  | append_singleton y c ih =>
    intro hdomc hdomn g hg
    have hpre : y <+: y ++ [c] := List.prefix_append y [c]
    have hdy : (γ.capital y).Dom := hdomc y hpre
    have hgy := Part.get_mem hdy
    have hdomn' : ∀ y', y' <+: y → y' ≠ y → (γ.next y').Dom := by
      intro y' h hne
      refine hdomn y' (h.trans hpre) ?_
      intro heq
      have := h.length_le
      rw [heq] at this
      simp at this
    obtain ⟨a, ha, b, hb, hab⟩ :=
      ih (fun y' h => hdomc y' (h.trans hpre)) hdomn' _ hgy
    have hdm : (γ.next y).Dom := hdomn y hpre (by simp)
    have hmm := Part.get_mem hdm
    set gy := (γ.capital y).get hdy
    set m := (γ.next y).get hdm
    have hgy0 := hpos _ gy hgy
    refine ⟨a * (if Nat.bodd m = true then
        isKLRandom_iff_total_parity_divd g gy else 1),
      (isKLRandom_iff_total_parity_cap_snoc_mem γ true y c _).2
        ⟨a, ha, m, hmm, g, hg, gy, hgy, rfl⟩,
      b * (if Nat.bodd m = false then
        isKLRandom_iff_total_parity_divd g gy else 1),
      (isKLRandom_iff_total_parity_cap_snoc_mem γ false y c _).2
        ⟨b, hb, m, hmm, g, hg, gy, hgy, rfl⟩, ?_⟩
    rw [isKLRandom_iff_total_parity_divd_of_pos hgy0]
    have hab0 : a * b ≠ 0 := by rw [← hab]; exact hgy0.ne'
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
    rcases h : Nat.bodd m
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      rw [hab] at *
      field_simp
    · simp only [Bool.true_eq_false, ↓reduceIte, mul_one]
      rw [hab] at *
      field_simp

/-- Step 2 of the proof of `isKLRandom_iff_total_split` (Stage B: parity split).
Given a strategy `γ` with partial computable `next` and `capital`, `γ([]) = 1`, strictly positive
and
non-overbetting, put `b_p.capital([]) = 1` and, for the child `x ++ [c]` of `x`,
`b_p.capital(x ++ [c]) = b_p.capital(x) * (γ(x ++ [c]) / γ(x))` if `γ.next x` has parity `p`, and
`b_p.capital(x ++ [c]) = b_p.capital(x)` otherwise (defined iff `b_p.capital x`, `γ.next x`, `γ x`,
`γ (x ++ [c])` are defined; a fold, computable by `Partrec.nat_rec`/`computable_of_num_den`).
Each step factor is in `(0, 2]` and the factors of the two children sum to `2` by fairness of `γ`,
so `b_p` is fair, nonnegative, non-overbetting and `p`-parity-restricted, with `b_p.next = γ.next`.
Along every string `x` whose prefixes all have `γ` defined and `next` defined on its proper
prefixes,
`γ(x) = b_true(x) * b_false(x)` (telescoping product, initial capital `1`). -/
private lemma isKLRandom_iff_total_parity (γ : KLBetting) (hnext : Partrec γ.next)
    (hcap : Partrec γ.capital) (h1 : (1 : ℚ) ∈ γ.capital []) (hpos : ∀ x, ∀ q ∈ γ.capital x, 0 < q)
    (hnobet : isKLRandom_iff_total_NoOverBet γ) :
    ∃ betas : Bool → KLBetting,
      (∀ p, (betas p).next = γ.next ∧ Partrec (betas p).capital ∧
        isKLRandom_iff_total_OnlyBetsOnParity (betas p) p ∧
        isKLRandom_iff_total_NoOverBet (betas p)) ∧
      ∀ x, (∀ y, y <+: x → (γ.capital y).Dom) → (∀ y, y <+: x → y ≠ x → (γ.next y).Dom) →
        ∀ g ∈ γ.capital x, ∃ a ∈ (betas true).capital x, ∃ b ∈ (betas false).capital x, g = a * b :=
            by
  refine ⟨fun p => isKLRandom_iff_total_parity_bet γ hpos p,
    fun p => ⟨rfl, isKLRandom_iff_total_parity_cap_partrec γ hnext hcap p,
      isKLRandom_iff_total_parity_bet_parity γ hpos p,
      isKLRandom_iff_total_parity_bet_nobet γ hpos hnobet p⟩,
    fun x hc hn g hg =>
      isKLRandom_iff_total_parity_cap_prod γ h1 hpos x hc hn g hg⟩

/-- The revealed bits of a rule depend only on its scan function. -/
private lemma isKLRandom_iff_total_split_revealed_congr (ρ ρ' : KLRule) (h : ρ.next = ρ'.next)
    (w : CantorSeq) (t : ℕ) : ρ.revealed w t = ρ'.revealed w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [KLRule.revealed, KLRule.revealed, ← ih]
    generalize ρ.revealed w t = x
    by_cases hd : (ρ'.next x).Dom
    · have hd' : (ρ.next x).Dom := by rw [h]; exact hd
      rw [dite_eq_left hd', dite_eq_left hd]
      have hm : (ρ.next x).get hd' ∈ ρ'.next x := by
        rw [← h]; exact Part.get_mem hd'
      rw [Part.mem_unique hm (Part.get_mem hd)]
    · have hd' : ¬ (ρ.next x).Dom := by rw [h]; exact hd
      rw [dite_eq_right hd', dite_eq_right hd]

private lemma isKLRandom_iff_total_split_revealed_succ_of_not_dom (ρ : KLRule) (w : CantorSeq)
    (t : ℕ) (h : ¬ (ρ.next (ρ.revealed w t)).Dom) : ρ.revealed w (t + 1) = ρ.revealed w t := by
  rw [KLRule.revealed]
  exact dite_eq_right h

private lemma isKLRandom_iff_total_split_revealed_length_le (ρ : KLRule) (w : CantorSeq)
    (t : ℕ) :
    (ρ.revealed w t).length ≤ t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    rw [KLRule.revealed]
    split_ifs
    · simp; omega
    · omega

private lemma isKLRandom_iff_total_split_revealed_prefix_le (ρ : KLRule) (w : CantorSeq)
    {s t : ℕ}
    (h : s ≤ t) : ρ.revealed w s <+: ρ.revealed w t := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ t _ ih => exact ih.trans (ρ.revealed_prefix w t)

/-- Step 3 of the proof of `isKLRandom_iff_total_split`: if `γ` wins on `w` and
`γ = b_true * b_false` along the run (with `b_p` nonnegative and the same scan function), then
some `b_p` wins on `w`: otherwise both capitals would be bounded and so would be their product. -/
private lemma isKLRandom_iff_total_split_wins (γ : KLBetting) (betas : Bool → KLBetting)
    (hnext : ∀ p, (betas p).next = γ.next)
    (hprod : ∀ x, (∀ y, y <+: x → (γ.capital y).Dom) → (∀ y, y <+: x → y ≠ x → (γ.next y).Dom) →
      ∀ g ∈ γ.capital x, ∃ a ∈ (betas true).capital x, ∃ b ∈ (betas false).capital x, g = a * b)
    (w : CantorSeq) (hw : γ.Wins w) : ∃ p, (betas p).Wins w := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hcong : ∀ p t, (betas p).toRule.revealed w t = γ.toRule.revealed w t := fun p t =>
    isKLRandom_iff_total_split_revealed_congr _ _ (hnext p) w t
  set σ : ℕ → BitString := γ.toRule.revealed w with hσ
  have hlen : ∀ t, (σ t).length = t := fun t =>
    le_antisymm (isKLRandom_iff_total_split_revealed_length_le _ w t) (h1 t)
  have hdom : ∀ t, (γ.next (σ t)).Dom := by
    intro t
    by_contra hnd
    have : σ (t + 1) = σ t :=
      isKLRandom_iff_total_split_revealed_succ_of_not_dom γ.toRule w t hnd
    have h' := hlen (t + 1)
    rw [this, hlen t] at h'
    omega
  have hpre : ∀ y t, y <+: σ t → y = σ y.length := by
    intro y t hy
    have hl : y.length ≤ t := by
      have := hy.length_le
      rwa [hlen t] at this
    have h2' : σ y.length <+: σ t :=
      isKLRandom_iff_total_split_revealed_prefix_le _ w hl
    have := List.prefix_of_prefix_length_le hy h2' (by rw [hlen])
    exact this.eq_of_length (by rw [hlen])
  have hP : ∀ t, ∀ g ∈ γ.capital (σ t), ∃ a ∈ (betas true).capital (σ t),
      ∃ b ∈ (betas false).capital (σ t), g = a * b := by
    intro t g hg
    refine hprod _ ?_ ?_ g hg
    · intro y hy
      rw [hpre y t hy]
      exact h2 _
    · intro y hy _
      rw [hpre y t hy]
      exact hdom _
  by_contra hno
  push Not at hno
  have hbdd : ∀ p, BddAbove {r : ℝ | ∃ t, ∃ q ∈ (betas p).capital ((betas p).toRule.revealed w t),
      (q : ℝ) = r} := by
    intro p
    by_contra hnb
    refine hno p ⟨fun t => ?_, fun t => ?_, hnb⟩
    · rw [hcong]; exact h1 t
    · rw [hcong]
      obtain ⟨a, ha, b, hb, _⟩ := hP t _ (Part.get_mem (h2 t))
      cases p
      · exact Part.dom_iff_mem.2 ⟨_, hb⟩
      · exact Part.dom_iff_mem.2 ⟨_, ha⟩
  obtain ⟨Mt, hMt⟩ := hbdd true
  obtain ⟨Mf, hMf⟩ := hbdd false
  apply h3
  refine ⟨Mt * Mf, ?_⟩
  rintro r ⟨t, q, hq, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hP t q hq
  have ha' : (a : ℝ) ≤ Mt := hMt ⟨t, a, by rw [hcong]; exact ha, rfl⟩
  have hb' : (b : ℝ) ≤ Mf := hMf ⟨t, b, by rw [hcong]; exact hb, rfl⟩
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (betas true).nonneg _ a ha
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast (betas false).nonneg _ b hb
  rw [hab]
  push_cast
  exact mul_le_mul ha' hb' hb0 (ha0.trans ha')

/-- Step 1 of the proof of `isKLRandom_iff_total`: decompose the betting strategy into two
strategies that bet only on odd and even parities respectively, and that do not overbet. -/
private lemma isKLRandom_iff_total_split (β : KLBetting) (hnext : Partrec β.next)
    (hcap : Partrec β.capital) :
  ∃ betas : Bool → KLBetting, (∀ p, Partrec (betas p).next ∧ Partrec (betas p).capital ∧
      isKLRandom_iff_total_OnlyBetsOnParity (betas p) p ∧ isKLRandom_iff_total_NoOverBet
      (betas p)) ∧ ∀ w, β.Wins w → ∃ p, (betas p).Wins w := by
  obtain ⟨γ, hγn, hγc, hγ1, hγpos, hγnb, hγw⟩ :=
    isKLRandom_iff_total_normalize β hcap
  obtain ⟨betas, hbetas, hprod⟩ :=
    isKLRandom_iff_total_parity γ (hγn ▸ hnext) hγc hγ1 hγpos hγnb
  refine ⟨betas, fun p => ⟨?_, (hbetas p).2⟩, fun w hw => ?_⟩
  · rw [(hbetas p).1, hγn]; exact hnext
  · exact isKLRandom_iff_total_split_wins γ betas (fun p => (hbetas p).1) hprod w
      (hγw w hw)

/-- The simulator state of the totalization: the simulated `β`-history, the cards read so far with
their bits, and the current capital. -/
private abbrev isKLRandom_iff_total_totalize_State :=
  BitString × List (ℕ × Bool) × ℚ

/-- An instruction: the physical card to request, whether to append the revealed bit to the
simulated history, an optional stored bit to append instead (skipping an already read card), and
the capital multipliers for the revealed bit `false` / `true`. -/
private abbrev isKLRandom_iff_total_totalize_Action :=
  ℕ × Bool × Option Bool × ℚ × ℚ

/-- One instruction of the totalizing machine; the budget is the number of bits read so far. All
unsound or degenerate situations (zero capital, a child outside `[0, 2q]`, a parity-`p` card read
twice) are answered by an idle step, so the multipliers are always nonnegative with sum `2`. -/
private def isKLRandom_iff_total_totalize_plan
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) :
    isKLRandom_iff_total_totalize_Action :=
  let idle : isKLRandom_iff_total_totalize_Action :=
    (isMisesKLRandomAt_iff_total_totalize_filler p st.2.1, false, none, 1, 1)
  match Fs st.2.1.length st.1 with
  | none => idle
  | some n =>
    match st.2.1.lookup n with
    | some c => if (n % 2 == 1) == p then idle else (idle.1, false, some c, 1, 1)
    | none =>
      if (n % 2 == 1) == p then
        match Cs st.2.1.length st.1 with
        | none => idle
        | some q =>
          match Cs st.2.1.length (st.1 ++ [false]), Cs st.2.1.length (st.1 ++ [true]) with
          | some v, _ =>
            if 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q then (n, true, none, v / q, 2 - v / q) else idle
          | none, some v =>
            if 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q then (n, true, none, 2 - v / q, v / q) else idle
          | none, none => idle
      else (n, true, none, 1, 1)

/-- Execute an instruction on the revealed bit `c`. -/
private def isKLRandom_iff_total_totalize_step
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) (c : Bool) :
    isKLRandom_iff_total_totalize_State :=
  let a := isKLRandom_iff_total_totalize_plan Fs Cs p st
  ((if a.2.1 then st.1 ++ [c] else
      match a.2.2.1 with
      | some d => st.1 ++ [d]
      | none => st.1),
    st.2.1 ++ [(a.1, c)], st.2.2 * (if c then a.2.2.2.2 else a.2.2.2.1))

/-- Replay a finite physical history. -/
private def isKLRandom_iff_total_totalize_replay
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) : isKLRandom_iff_total_totalize_State :=
  y.foldl (isKLRandom_iff_total_totalize_step Fs Cs p) ([], [], 1)

/-- The card requested by the totalized strategy after the history `y`. -/
private def isKLRandom_iff_total_totalize_nextCard
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) : ℕ :=
  (isKLRandom_iff_total_totalize_plan Fs Cs p
    (isKLRandom_iff_total_totalize_replay Fs Cs p y)).1

/-- The capital of the totalized strategy after the history `y`. -/
private def isKLRandom_iff_total_totalize_cap
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) : ℚ :=
  (isKLRandom_iff_total_totalize_replay Fs Cs p y).2.2

/-- Sound, complete and monotone fuel approximations of a partial function. -/
private def isKLRandom_iff_total_totalize_FuelSpec {α : Type}
    (F : BitString →. α) (Fs : ℕ → BitString → Option α) : Prop :=
  (∀ s x n, Fs s x = some n → n ∈ F x) ∧ (∀ x n, n ∈ F x → ∃ s, Fs s x = some n) ∧
    (∀ s x n, Fs s x = some n → ∀ t ≥ s, Fs t x = some n)

/-- Simulation invariant along the run of `β'` on `w`: the simulated history is always a stage of
the run of `β` on `w`, every stored (card, bit) pair is correct for `w`, and the simulated capital
is
the capital of that stage of `β` divided by its initial capital. -/
private def isKLRandom_iff_total_totalize_Invariant (p : Bool) (β β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (w : CantorSeq) : Prop :=
  ∀ t, ∃ k, (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w t)).1 =
      β.toRule.revealed w k ∧
    (∀ e ∈ (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w t)).2.1,
      e.2 = w e.1) ∧
    ∀ q0 ∈ β.capital [], ∀ qk ∈ β.capital (β.toRule.revealed w k),
      (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w t)).2.2 * q0 = qk

/-- The simulated history passes through every stage of the run of `β` on `w`. -/
private def isKLRandom_iff_total_totalize_Progress (p : Bool) (β β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (w : CantorSeq) : Prop :=
  ∀ k, ∃ t, (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w t)).1 =
    β.toRule.revealed w k

/-- Every instruction of the totalizing machine requests a card absent from the record. -/
private lemma isKLRandom_iff_total_totalize_plan_fresh
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) :
    (isKLRandom_iff_total_totalize_plan Fs Cs p st).1 ∉ st.2.1.map Prod.fst := by
  have hf := (isMisesKLRandomAt_iff_total_filler p st.2.1).1
  unfold isKLRandom_iff_total_totalize_plan
  split
  · exact hf
  · rename_i n hn
    split
    · rename_i c hc
      split <;> exact hf
    · rename_i hnK
      have hmem := (isMisesKLRandomAt_iff_total_totalize_lookup_none st.2.1 n).mp hnK
      split
      · split
        · exact hf
        · split
          · split <;> first | exact hf | exact hmem
          · split <;> first | exact hf | exact hmem
          · exact hf
      · exact hmem

/-- Executing any finite history only extends the record of read cards. -/
private lemma isKLRandom_iff_total_totalize_record_prefix
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (z : BitString) (st : isKLRandom_iff_total_totalize_State) :
    st.2.1 <+: (z.foldl (isKLRandom_iff_total_totalize_step Fs Cs p) st).2.1 := by
  induction z generalizing st with
  | nil => exact List.prefix_rfl
  | cons c z ih =>
    exact (List.prefix_append _ _).trans
      (ih (isKLRandom_iff_total_totalize_step Fs Cs p st c))

/-- Step 1 of the proof of `isKLRandom_iff_total_totalize`: the totalizing machine
never requests a card already requested on a shorter compatible history (freshness against the
record, for arbitrary fuel functions). -/
private lemma isKLRandom_iff_total_noRepeat
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (x y : BitString) (hxy : x <+: y) (hne : x ≠ y) :
    isKLRandom_iff_total_totalize_nextCard Fs Cs p x ≠
      isKLRandom_iff_total_totalize_nextCard Fs Cs p y := by
  obtain ⟨z, rfl⟩ := hxy
  cases z with
  | nil => simp at hne
  | cons c z =>
    let st := isKLRandom_iff_total_totalize_replay Fs Cs p x
    have hp := isKLRandom_iff_total_totalize_record_prefix Fs Cs p z
      (isKLRandom_iff_total_totalize_step Fs Cs p st c)
    have hmem : (isKLRandom_iff_total_totalize_nextCard Fs Cs p x, c) ∈
        (isKLRandom_iff_total_totalize_replay Fs Cs p (x ++ c :: z)).2.1 := by
      rw [isKLRandom_iff_total_totalize_replay, List.foldl_append, List.foldl_cons]
      change _ ∈ (z.foldl (isKLRandom_iff_total_totalize_step Fs Cs p)
        (isKLRandom_iff_total_totalize_step Fs Cs p st c)).2.1
      exact hp.subset (by simp [isKLRandom_iff_total_totalize_step,
        isKLRandom_iff_total_totalize_nextCard, st])
    intro heq
    have hf := isKLRandom_iff_total_totalize_plan_fresh Fs Cs p
      (isKLRandom_iff_total_totalize_replay Fs Cs p (x ++ c :: z))
    apply hf
    exact List.mem_map.mpr ⟨_, hmem, heq⟩

/-- The two multipliers of any instruction are nonnegative and sum to `2`. -/
private lemma isKLRandom_iff_total_totalize_plan_mult
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) :
    0 ≤ (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.2.1 ∧
      0 ≤ (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.2.2 ∧
      (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.2.1 +
        (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.2.2 = 2 := by
  have key : ∀ q v : ℚ, 0 < q → 0 ≤ v → v ≤ 2 * q →
      0 ≤ v / q ∧ 0 ≤ 2 - v / q := by
    intro q v hq hv hvq
    refine ⟨div_nonneg hv hq.le, ?_⟩
    have : v / q ≤ 2 := by rw [div_le_iff₀ hq]; linarith
    linarith
  unfold isKLRandom_iff_total_totalize_plan
  split
  · norm_num
  · split
    · split <;> norm_num
    · split
      · split
        · norm_num
        · split
          · split
            · rename_i hh
              obtain ⟨h1, h2⟩ := key _ _ hh.1 hh.2.1 hh.2.2
              exact ⟨h1, h2, by ring⟩
            · norm_num
          · split
            · rename_i hh
              obtain ⟨h1, h2⟩ := key _ _ hh.1 hh.2.1 hh.2.2
              exact ⟨h2, h1, by ring⟩
            · norm_num
          · norm_num
      · norm_num

/-- The capital after one more revealed bit. -/
private lemma isKLRandom_iff_total_totalize_cap_snoc
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) (c : Bool) :
    isKLRandom_iff_total_totalize_cap Fs Cs p (y ++ [c]) =
      isKLRandom_iff_total_totalize_cap Fs Cs p y *
      (if c then (isKLRandom_iff_total_totalize_plan Fs Cs p
          (isKLRandom_iff_total_totalize_replay Fs Cs p y)).2.2.2.2
        else (isKLRandom_iff_total_totalize_plan Fs Cs p
          (isKLRandom_iff_total_totalize_replay Fs Cs p y)).2.2.2.1) := by
  simp [isKLRandom_iff_total_totalize_cap, isKLRandom_iff_total_totalize_replay,
    List.foldl_append, isKLRandom_iff_total_totalize_step]

/-- Step 2 of the proof of `isKLRandom_iff_total_totalize`: the simulated capital is
nonnegative and fair on all strings (every instruction has nonnegative multipliers with sum `2`),
for arbitrary fuel functions. -/
private lemma isKLRandom_iff_total_nonneg_fair
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) :
    0 ≤ isKLRandom_iff_total_totalize_cap Fs Cs p y ∧
      isKLRandom_iff_total_totalize_cap Fs Cs p y =
        (isKLRandom_iff_total_totalize_cap Fs Cs p (y ++ [false]) +
          isKLRandom_iff_total_totalize_cap Fs Cs p (y ++ [true])) / 2 := by
  constructor
  · induction y using List.reverseRecOn with
    | nil => simp [isKLRandom_iff_total_totalize_cap,
        isKLRandom_iff_total_totalize_replay]
    | append_singleton y c ih =>
      rw [isKLRandom_iff_total_totalize_cap_snoc]
      obtain ⟨h0, h1, _⟩ := isKLRandom_iff_total_totalize_plan_mult Fs Cs p
        (isKLRandom_iff_total_totalize_replay Fs Cs p y)
      cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> positivity
  · rw [isKLRandom_iff_total_totalize_cap_snoc, isKLRandom_iff_total_totalize_cap_snoc]
    obtain ⟨_, _, h2⟩ := isKLRandom_iff_total_totalize_plan_mult Fs Cs p
      (isKLRandom_iff_total_totalize_replay Fs Cs p y)
    simp only [Bool.false_eq_true, ite_false, ite_true]
    linear_combination (-(isKLRandom_iff_total_totalize_cap Fs Cs p y) / 2) * h2

private lemma isKLRandom_iff_total_computable_aux_div :
    Computable (fun p : ℚ × ℚ => if 0 < p.2 then p.1 / p.2 else 0) := by
  have hn : Computable (fun p : ℚ × ℚ => p.2.num.toNat) :=
    ComputableReals.primrec_intToNat.to_comp.comp (computable_ratNum.comp Computable.snd)
  have hb : Computable (fun p : ℚ × ℚ => decide (0 < p.2.num.toNat)) :=
    (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide.to_comp.comp hn
  have hN : Computable (fun p : ℚ × ℚ =>
      cond (decide (0 < p.2.num.toNat)) (p.1.num * (p.2.den : ℤ)) 0) :=
    Computable.cond hb
      (Computable₂.comp primrec_intMul.to_comp (computable_ratNum.comp Computable.fst)
        (ComputableReals.primrec_natCastInt.to_comp.comp (computable_ratDen.comp Computable.snd)))
      (Computable.const 0)
  have hD : Computable (fun p : ℚ × ℚ =>
      cond (decide (0 < p.2.num.toNat)) (p.1.den * p.2.num.toNat) 1) :=
    Computable.cond hb
      (Computable₂.comp Primrec.nat_mul.to_comp (computable_ratDen.comp Computable.fst) hn)
      (Computable.const 1)
  refine computable_of_num_den hN hD (fun p => ?_) (fun p => ?_)
  · by_cases h : 0 < p.2.num.toNat
    · simpa [h] using Nat.mul_pos p.1.pos h
    · simp [h]
  · by_cases h : 0 < p.2
    · have hnum : 0 < p.2.num := Rat.num_pos.mpr h
      have h' : 0 < p.2.num.toNat := by omega
      have hd1 : ((p.1.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.1.den_nz
      have hd2 : ((p.2.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.den_nz
      have hq : (p.2.num.toNat : ℚ) = p.2 * (p.2.den : ℚ) := by
        have : ((p.2.num.toNat : ℤ) : ℚ) = (p.2.num : ℚ) := by
          rw [Int.toNat_of_nonneg hnum.le]
        rw [Rat.mul_den_eq_num p.2]
        exact_mod_cast this
      have h1 : (p.1.num : ℚ) = p.1 * (p.1.den : ℚ) := (Rat.mul_den_eq_num p.1).symm
      have hp0 : p.2 ≠ 0 := h.ne'
      simp only [h, h', decide_true, Bool.cond_true, ite_true]
      push_cast
      rw [hq, h1]
      field_simp
    · have h' : ¬ 0 < p.2.num.toNat := by
        intro h'
        apply h
        exact Rat.num_pos.mp (by omega)
      simp [h, h']

private lemma isKLRandom_iff_total_computable_aux_ok :
    Computable (fun p : ℚ × ℚ => decide (0 < p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 * p.1)) := by
  have hnn : Computable (fun x : ℚ => decide (0 ≤ x)) := by
    have h := Computable₂.comp (Primrec.eq (α := ℤ)).decide.to_comp
      (ComputableReals.primrec_natCastInt.to_comp.comp
        (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum)) computable_ratNum
    refine h.of_eq (fun x => ?_)
    refine decide_eq_decide.mpr ?_
    rw [← Rat.num_nonneg]
    omega
  have hpos : Computable (fun x : ℚ => decide (0 < x)) := by
    have h := (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide.to_comp.comp
      (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum)
    refine h.of_eq (fun x => ?_)
    refine decide_eq_decide.mpr ?_
    rw [← Rat.num_pos]
    change 0 < x.num.toNat ↔ 0 < x.num
    omega
  have h2q : Computable (fun p : ℚ × ℚ => 2 * p.1) :=
    (computable₂_ratAdd.comp Computable.fst Computable.fst).of_eq (fun p => by simp [two_mul])
  have hsub : Computable (fun p : ℚ × ℚ => 2 * p.1 - p.2) :=
    computable₂_ratSub.comp h2q Computable.snd
  have hand : ∀ {f g : ℚ × ℚ → Bool}, Computable f → Computable g →
      Computable (fun p => f p && g p) :=
    fun hf hg => Computable₂.comp ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp) hf hg
  refine (hand (hpos.comp Computable.fst)
    (hand (hnn.comp Computable.snd) (hnn.comp hsub))).of_eq (fun p => ?_)
  simp [sub_nonneg]


private lemma isKLRandom_iff_total_computable_aux_idle (p : Bool) :
    Computable (fun st : isKLRandom_iff_total_totalize_State =>
      ((isMisesKLRandomAt_iff_total_totalize_filler p st.2.1, false, none, 1, 1) :
        isKLRandom_iff_total_totalize_Action)) :=
  (((isMisesKLRandomAt_iff_total_filler_primrec p).to_comp).comp
    (Computable.fst.comp Computable.snd)).pair
      (Computable.const ((false, none, 1, 1) : Bool × Option Bool × ℚ × ℚ))

/-- The ratio `v / q`, set to `0` unless `q > 0`. -/
private def isKLRandom_iff_total_computable_dv (v q : ℚ) : ℚ :=
  if 0 < q then v / q else 0

/-- The test `0 < q ∧ 0 ≤ v ∧ v ≤ 2 q`. -/
private def isKLRandom_iff_total_computable_okb (q v : ℚ) : Bool :=
  decide (0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q)

private lemma isKLRandom_iff_total_computable_aux_dv_comp :
    Computable₂ (fun v q : ℚ =>
      isKLRandom_iff_total_computable_dv v q) :=
  isKLRandom_iff_total_computable_aux_div

private lemma isKLRandom_iff_total_computable_aux_okb_comp :
    Computable₂ (fun q v : ℚ =>
      isKLRandom_iff_total_computable_okb q v) :=
  isKLRandom_iff_total_computable_aux_ok

private lemma isKLRandom_iff_total_computable_aux_g1
    {α : Type} [Primcodable α] {n : α → ℕ} {q v : α → ℚ}
    {idl : α → isKLRandom_iff_total_totalize_Action}
    (hn : Computable n) (hq : Computable q) (hv : Computable v) (hidl : Computable idl) :
    Computable (fun a : α =>
      cond (isKLRandom_iff_total_computable_okb (q a) (v a))
        ((n a, true, none,
          isKLRandom_iff_total_computable_dv (v a) (q a),
          2 - isKLRandom_iff_total_computable_dv (v a) (q a)) :
          isKLRandom_iff_total_totalize_Action) (idl a)) := by
  have hd : Computable (fun a : α =>
      isKLRandom_iff_total_computable_dv (v a) (q a)) :=
    isKLRandom_iff_total_computable_aux_dv_comp.comp hv hq
  have hA : Computable (fun a : α =>
      isKLRandom_iff_total_computable_okb (q a) (v a)) :=
    isKLRandom_iff_total_computable_aux_okb_comp.comp hq hv
  have hs : Computable (fun a : α => 2 -
      isKLRandom_iff_total_computable_dv (v a) (q a)) :=
    computable₂_ratSub.comp (Computable.const (2 : ℚ)) hd
  exact Computable.cond hA
    (hn.pair ((Computable.const true).pair ((Computable.const (none : Option Bool)).pair
      (hd.pair hs)))) hidl

private lemma isKLRandom_iff_total_computable_aux_g2
    {α : Type} [Primcodable α] {n : α → ℕ} {q v : α → ℚ}
    {idl : α → isKLRandom_iff_total_totalize_Action}
    (hn : Computable n) (hq : Computable q) (hv : Computable v) (hidl : Computable idl) :
    Computable (fun a : α =>
      cond (isKLRandom_iff_total_computable_okb (q a) (v a))
        ((n a, true, none,
          2 - isKLRandom_iff_total_computable_dv (v a) (q a),
          isKLRandom_iff_total_computable_dv (v a) (q a)) :
          isKLRandom_iff_total_totalize_Action) (idl a)) := by
  have hd : Computable (fun a : α =>
      isKLRandom_iff_total_computable_dv (v a) (q a)) :=
    isKLRandom_iff_total_computable_aux_dv_comp.comp hv hq
  have hA : Computable (fun a : α =>
      isKLRandom_iff_total_computable_okb (q a) (v a)) :=
    isKLRandom_iff_total_computable_aux_okb_comp.comp hq hv
  have hs : Computable (fun a : α => 2 -
      isKLRandom_iff_total_computable_dv (v a) (q a)) :=
    computable₂_ratSub.comp (Computable.const (2 : ℚ)) hd
  exact Computable.cond hA
    (hn.pair ((Computable.const true).pair ((Computable.const (none : Option Bool)).pair
      (hs.pair hd)))) hidl

private lemma isKLRandom_iff_total_computable_aux_plan
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (hFs : Primrec₂ Fs) (hCs : Primrec₂ Cs) :
    Computable (isKLRandom_iff_total_totalize_plan Fs Cs p) := by
  have hF : Computable₂ Fs := hFs.to_comp
  have hC : Computable₂ Cs := hCs.to_comp
  have hidle := isKLRandom_iff_total_computable_aux_idle p
  have hfill := (isMisesKLRandomAt_iff_total_filler_primrec p).to_comp
  have hpar : Computable (fun n : ℕ => ((n % 2 == 1) == p)) :=
    (Primrec.beq.comp
      (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
        (Primrec.const 1)) (Primrec.const p)).to_comp
  -- level 4: the state, the card and the capital are known
  have h4a : Computable (fun r : (isKLRandom_iff_total_totalize_State × ℕ) × ℚ => r.1.1) :=
    Computable.fst.comp Computable.fst
  have h4len : Computable
      (fun r : (isKLRandom_iff_total_totalize_State × ℕ) × ℚ => r.1.1.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp h4a))
  have h4s : Computable
      (fun r : (isKLRandom_iff_total_totalize_State × ℕ) × ℚ => r.1.1.1) :=
    Computable.fst.comp h4a
  have h4c : ∀ b : Bool, Computable
      (fun r : (isKLRandom_iff_total_totalize_State × ℕ) × ℚ =>
        Cs r.1.1.2.1.length (r.1.1.1 ++ [b])) :=
    fun b => hC.comp h4len (Computable.list_append.comp h4s (Computable.const [b]))
  have h5a : Computable
      (fun pr : ((isKLRandom_iff_total_totalize_State × ℕ) × ℚ) × ℚ => pr.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have h5n : Computable
      (fun pr : ((isKLRandom_iff_total_totalize_State × ℕ) × ℚ) × ℚ => pr.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have h5q : Computable
      (fun pr : ((isKLRandom_iff_total_totalize_State × ℕ) × ℚ) × ℚ => pr.1.2) :=
    Computable.snd.comp Computable.fst
  have h5v : Computable
      (fun pr : ((isKLRandom_iff_total_totalize_State × ℕ) × ℚ) × ℚ => pr.2) :=
    Computable.snd
  have h5i := hidle.comp h5a
  have hg1 := isKLRandom_iff_total_computable_aux_g1 h5n h5q h5v h5i
  have hg2 := isKLRandom_iff_total_computable_aux_g2 h5n h5q h5v h5i
  have hL4 := Computable.option_casesOn (h4c false)
    (Computable.option_casesOn (h4c true) (hidle.comp h4a) hg2.to₂) hg1.to₂
  -- level 3: the state and the card are known
  have h3a : Computable (fun r : isKLRandom_iff_total_totalize_State × ℕ => r.1) :=
    Computable.fst
  have h3n : Computable (fun r : isKLRandom_iff_total_totalize_State × ℕ => r.2) :=
    Computable.snd
  have h3len : Computable
      (fun r : isKLRandom_iff_total_totalize_State × ℕ => r.1.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp h3a))
  have h3s : Computable (fun r : isKLRandom_iff_total_totalize_State × ℕ => r.1.1) :=
    Computable.fst.comp h3a
  have h3c : Computable
      (fun r : isKLRandom_iff_total_totalize_State × ℕ => Cs r.1.2.1.length r.1.1) :=
    hC.comp h3len h3s
  have hL3 := Computable.option_casesOn h3c (hidle.comp h3a) hL4.to₂
  -- level 2: parity test
  have hd2 : Computable (fun r : isKLRandom_iff_total_totalize_State × ℕ =>
      ((r.2, true, none, 1, 1) : isKLRandom_iff_total_totalize_Action)) :=
    h3n.pair (Computable.const ((true, none, 1, 1) : Bool × Option Bool × ℚ × ℚ))
  have hL2 := Computable.cond (hpar.comp h3n) hL3 hd2
  -- level 2': stored card
  have hlk : Computable
      (fun r : isKLRandom_iff_total_totalize_State × ℕ => r.1.2.1.lookup r.2) :=
    (Primrec.listLookup.comp (Primrec.snd : Primrec fun r :
        isKLRandom_iff_total_totalize_State × ℕ => r.2)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to_comp
  have hsome : Computable
      (fun pr : (isKLRandom_iff_total_totalize_State × ℕ) × Bool =>
        cond ((pr.1.2 % 2 == 1) == p)
          ((isMisesKLRandomAt_iff_total_totalize_filler p pr.1.1.2.1, false, none, 1, 1) :
            isKLRandom_iff_total_totalize_Action)
          ((isMisesKLRandomAt_iff_total_totalize_filler p pr.1.1.2.1, false, some pr.2, 1, 1)
              :
            isKLRandom_iff_total_totalize_Action)) := by
    have e1 : Computable (fun pr : (isKLRandom_iff_total_totalize_State × ℕ) × Bool =>
        isMisesKLRandomAt_iff_total_totalize_filler p pr.1.1.2.1) :=
      hfill.comp (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
    have e2 : Computable (fun pr : (isKLRandom_iff_total_totalize_State × ℕ) × Bool =>
        ((pr.1.2 % 2 == 1) == p)) := hpar.comp (Computable.snd.comp Computable.fst)
    exact Computable.cond e2
      (e1.pair (Computable.const ((false, none, 1, 1) : Bool × Option Bool × ℚ × ℚ)))
      (e1.pair ((Computable.const false).pair
        ((Computable.option_some.comp Computable.snd).pair
          (Computable.const ((1, 1) : ℚ × ℚ)))))
  have hL2' := Computable.option_casesOn hlk hL2 hsome.to₂
  -- level 1
  have h1 : Computable (fun st : isKLRandom_iff_total_totalize_State =>
      Fs st.2.1.length st.1) :=
    hF.comp (Computable.list_length.comp (Computable.fst.comp Computable.snd)) Computable.fst
  have hP := Computable.option_casesOn h1 hidle hL2'.to₂
  refine hP.of_eq (fun st => ?_)
  unfold isKLRandom_iff_total_totalize_plan
  cases hF1 : Fs st.2.1.length st.1 with
  | none => rfl
  | some n =>
    dsimp only
    cases hl : st.2.1.lookup n with
    | some c =>
      cases hb : ((n % 2 == 1) == p) <;> simp
    | none =>
      cases hb : ((n % 2 == 1) == p)
      · simp
      · cases hq : Cs st.2.1.length st.1 with
        | none => simp
        | some q =>
          cases h0 : Cs st.2.1.length (st.1 ++ [false]) with
          | some v =>
            by_cases hc : 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q
            · simp [hc, isKLRandom_iff_total_computable_okb,
                isKLRandom_iff_total_computable_dv]
            · simp [hc, isKLRandom_iff_total_computable_okb]
          | none =>
            cases h1 : Cs st.2.1.length (st.1 ++ [true]) with
            | none => simp
            | some v =>
              by_cases hc : 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q
              · simp [hc, isKLRandom_iff_total_computable_okb,
                  isKLRandom_iff_total_computable_dv]
              · simp [hc, isKLRandom_iff_total_computable_okb]


/-- Step 3 of the proof of `isKLRandom_iff_total_totalize`: for primitive recursive
fuel functions the card and capital functions of the machine are computable (a left fold of a
primitive recursive step with rational arithmetic). -/
private lemma isKLRandom_iff_total_computable
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (hFs : Primrec₂ Fs) (hCs : Primrec₂ Cs) :
    Computable (isKLRandom_iff_total_totalize_nextCard Fs Cs p) ∧
      Computable (isKLRandom_iff_total_totalize_cap Fs Cs p) := by
  have hplan := isKLRandom_iff_total_computable_aux_plan Fs Cs p hFs hCs
  have hstep : Computable (fun q : isKLRandom_iff_total_totalize_State × Bool =>
      isKLRandom_iff_total_totalize_step Fs Cs p q.1 q.2) := by
    have ha := hplan.comp
      (Computable.fst : Computable fun q : isKLRandom_iff_total_totalize_State × Bool => q.1)
    have hs1 : Computable (fun q : isKLRandom_iff_total_totalize_State × Bool => q.1.1) :=
      Computable.fst.comp Computable.fst
    have hc : Computable (fun q : isKLRandom_iff_total_totalize_State × Bool => q.2) :=
      Computable.snd
    have hrec : Computable
        (fun q : isKLRandom_iff_total_totalize_State × Bool => q.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hcap : Computable
        (fun q : isKLRandom_iff_total_totalize_State × Bool => q.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have a1 := Computable.fst.comp ha
    have a2 := Computable.fst.comp (Computable.snd.comp ha)
    have a3 := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp ha))
    have a4 := Computable.fst.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp ha)))
    have a5 := Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp ha)))
    have c1 := Computable.cond a2 (Computable.list_concat.comp hs1 hc)
      (Computable.option_casesOn a3 hs1
        (Computable.list_concat.comp (hs1.comp Computable.fst) Computable.snd).to₂)
    have c2 := Computable.list_concat.comp hrec (a1.pair hc)
    have c3 := computable₂_ratMul.comp hcap (Computable.cond hc a5 a4)
    refine (c1.pair (c2.pair c3)).of_eq (fun q => ?_)
    simp only [isKLRandom_iff_total_totalize_step, Bool.cond_eq_ite]
    cases ho : (isKLRandom_iff_total_totalize_plan Fs Cs p q.1).2.2.1 <;> simp
  have hr : Computable (isKLRandom_iff_total_totalize_replay Fs Cs p) :=
    Computable.list_foldl (l := fun y : BitString => y)
      (g := fun _ : BitString => (([], [], 1) : isKLRandom_iff_total_totalize_State))
      (h := fun (_ : BitString) (pb : isKLRandom_iff_total_totalize_State × Bool) =>
        isKLRandom_iff_total_totalize_step Fs Cs p pb.1 pb.2)
      Computable.id (Computable.const _)
      (hstep.to₂.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
  exact ⟨(Computable.fst.comp (hplan.comp hr)).of_eq (fun _ => rfl),
    (Computable.snd.comp (Computable.snd.comp hr)).of_eq (fun _ => rfl)⟩

/-- A simulator state is good for `β` on `w`: its simulated history is a stage `σ_k` of the run of
`β` on `w`, its stored (card, bit) pairs are correct for `w`, and its capital is `c(σ_k) / c([])`.
-/
private def isKLRandom_iff_total_totalize_Good (β : KLBetting) (w : CantorSeq)
    (st : isKLRandom_iff_total_totalize_State) : Prop :=
  ∃ k, st.1 = β.toRule.revealed w k ∧ (∀ e ∈ st.2.1, e.2 = w e.1) ∧
    ∀ q0 ∈ β.capital [], ∀ qk ∈ β.capital (β.toRule.revealed w k), st.2.2 * q0 = qk

/-- Step 4 of the proof of `isKLRandom_iff_total_totalize`: one step of the machine
preserves goodness when it is fed the true bit `w n` of the requested card `n`. A free request, a
skip
or a parity-`p` request moves the simulated history from `σ_k` to `σ_{k+1}` (using fuel
soundness, `OnlyBetsOnParity`, fairness of `β.capital` for the sibling child, `NoOverBet` for the
guard and the definedness of the capital along the run), a padding or defensive idle step changes
nothing. -/
private lemma isKLRandom_iff_total_totalize_onestep (p : Bool) (β : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hFs : isKLRandom_iff_total_totalize_FuelSpec β.next Fs)
    (hCs : isKLRandom_iff_total_totalize_FuelSpec β.capital Cs)
    (hparity : isKLRandom_iff_total_OnlyBetsOnParity β p)
    (w : CantorSeq) (hw : β.Wins w) (st : isKLRandom_iff_total_totalize_State)
    (hst : isKLRandom_iff_total_totalize_Good β w st) :
    isKLRandom_iff_total_totalize_Good β w
      (isKLRandom_iff_total_totalize_step Fs Cs p st
        (w (isKLRandom_iff_total_totalize_plan Fs Cs p st).1)) := by
  obtain ⟨k, hk1, hk2, hk3⟩ := hst
  obtain ⟨hFs1, -, -⟩ := hFs
  obtain ⟨hCs1, -, -⟩ := hCs
  obtain ⟨-, hdom, -⟩ := hw
  have hb : ∀ n : ℕ, (n % 2 == 1) = Nat.bodd n := by
    intro n; rw [Nat.mod_two_of_bodd]; cases Nat.bodd n <;> simp
  -- advancing one step of the run of `β`
  have hadv : ∀ n ∈ β.next (β.toRule.revealed w k),
      β.toRule.revealed w (k + 1) = β.toRule.revealed w k ++ [w n] := by
    intro n hn
    have hd : (β.next (β.toRule.revealed w k)).Dom := Part.dom_iff_mem.mpr ⟨n, hn⟩
    have hd' : (β.toRule.next (β.toRule.revealed w k)).Dom := hd
    rw [KLRule.revealed, dite_eq_left hd']
    have : (β.toRule.next (β.toRule.revealed w k)).get hd' = n :=
      Part.get_eq_of_mem hn hd'
    rw [this]
  -- an idle step
  have hidle : ∀ m : ℕ, isKLRandom_iff_total_totalize_Good β w
      (st.1, st.2.1 ++ [(m, w m)], st.2.2 * 1) := by
    intro m
    refine ⟨k, hk1, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hk2 e h
      · rw [List.mem_singleton] at h; subst h; rfl
    · intro q0 hq0 qk hqk
      simpa using hk3 q0 hq0 qk hqk
  -- a step that moves from `σ_k` to `σ_{k+1}` with the same capital
  have hmove : ∀ n ∈ β.next (β.toRule.revealed w k), ∀ m : ℕ, (n % 2 == 1) ≠ p →
      isKLRandom_iff_total_totalize_Good β w
        (st.1 ++ [w n], st.2.1 ++ [(m, w m)], st.2.2 * 1) := by
    intro n hn m hnp
    refine ⟨k + 1, by rw [hk1, hadv n hn], ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hk2 e h
      · rw [List.mem_singleton] at h; subst h; rfl
    · intro q0 hq0 qk1 hqk1
      obtain ⟨qk, hqk⟩ : ∃ qk, qk ∈ β.capital (β.toRule.revealed w k) :=
        Part.dom_iff_mem.mp (hdom k)
      rw [hadv n hn] at hqk1
      have := hparity _ n hn (by rw [← hb]; exact hnp) qk hqk (w n) qk1 hqk1
      have h3 := hk3 q0 hq0 qk hqk
      rw [this, ← h3]; ring
  -- a bet step
  have hbet : ∀ n ∈ β.next (β.toRule.revealed w k), ∀ q ∈ β.capital (β.toRule.revealed w k),
      ∀ (b : Bool) (v : ℚ), v ∈ β.capital (β.toRule.revealed w k ++ [b]) → 0 < q →
      ∀ M : ℚ, M = (if w n = b then v / q else 2 - v / q) →
      isKLRandom_iff_total_totalize_Good β w
        (st.1 ++ [w n], st.2.1 ++ [(n, w n)], st.2.2 * M) := by
    intro n hn q hq b v hv hq0 M hM
    refine ⟨k + 1, by rw [hk1, hadv n hn], ?_, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hk2 e h
      · rw [List.mem_singleton] at h; subst h; rfl
    · intro q0 hq0' qk1 hqk1
      rw [hadv n hn] at hqk1
      have h3 := hk3 q0 hq0' q hq
      subst hM
      by_cases hwb : w n = b
      · rw [ite_eq_left hwb]
        rw [hwb] at hqk1
        have : qk1 = v := Part.mem_unique hqk1 hv
        rw [this]
        calc st.2.2 * (v / q) * q0 = (st.2.2 * q0) * v / q := by ring
          _ = v := by rw [h3]; field_simp
      · rw [ite_eq_right hwb]
        have hwb' : w n = !b := by cases b <;> simpa using hwb
        rw [hwb'] at hqk1
        have hfair : q = (v + qk1) / 2 := by
          cases b
          · exact β.fair _ q v qk1 hq hv hqk1
          · have := β.fair _ q qk1 v hq hqk1 hv
            linarith
        have hq1 : qk1 = 2 * q - v := by linarith
        rw [hq1]
        calc st.2.2 * (2 - v / q) * q0 = (st.2.2 * q0) * (2 - v / q) := by ring
          _ = 2 * q - v := by rw [h3]; field_simp
  unfold isKLRandom_iff_total_totalize_step
  dsimp only
  generalize hA : isKLRandom_iff_total_totalize_plan Fs Cs p st = a
  unfold isKLRandom_iff_total_totalize_plan at hA
  dsimp only at hA
  rcases hF : Fs st.2.1.length st.1 with _ | n
  · rw [hF] at hA
    dsimp only at hA
    subst hA
    simpa using hidle _
  · have hn : n ∈ β.next (β.toRule.revealed w k) := by
      rw [← hk1]; exact hFs1 _ _ _ hF
    rw [hF] at hA
    dsimp only at hA
    rcases hL : st.2.1.lookup n with _ | c'
    · rw [hL] at hA
      dsimp only at hA
      by_cases hpar : ((n % 2 == 1) == p) = true
      · rw [ite_eq_left hpar] at hA
        rcases hC : Cs st.2.1.length st.1 with _ | q
        · rw [hC] at hA
          dsimp only at hA
          subst hA
          simpa using hidle _
        · have hq : q ∈ β.capital (β.toRule.revealed w k) := by
            rw [← hk1]; exact hCs1 _ _ _ hC
          rw [hC] at hA
          dsimp only at hA
          rcases hC0 : Cs st.2.1.length (st.1 ++ [false]) with _ | v
          · rcases hC1 : Cs st.2.1.length (st.1 ++ [true]) with _ | v
            · rw [hC0, hC1] at hA
              dsimp only at hA
              subst hA
              simpa using hidle _
            · have hv := hCs1 _ _ _ hC1
              rw [hk1] at hv
              rw [hC0, hC1] at hA
              dsimp only at hA
              by_cases hg : 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q
              · rw [ite_eq_left hg] at hA
                subst hA
                have := hbet n hn q hq true v hv hg.1
                  (if w n = true then v / q else 2 - v / q) rfl
                simpa using this
              · rw [ite_eq_right hg] at hA
                subst hA
                simpa using hidle _
          · have hv := hCs1 _ _ _ hC0
            rw [hk1] at hv
            rw [hC0] at hA
            dsimp only at hA
            by_cases hg : 0 < q ∧ 0 ≤ v ∧ v ≤ 2 * q
            · rw [ite_eq_left hg] at hA
              subst hA
              have := hbet n hn q hq false v hv hg.1
                (if w n = true then 2 - v / q else v / q) (by cases w n <;> simp)
              simpa using this
            · rw [ite_eq_right hg] at hA
              subst hA
              simpa using hidle _
      · rw [ite_eq_right hpar] at hA
        subst hA
        have := hmove n hn n (fun h => hpar (beq_iff_eq.mpr h))
        simpa using this
    · have hc' : c' = w n := by
        have hlk : ∀ (K : List (ℕ × Bool)) (n : ℕ) (c : Bool), K.lookup n = some c →
            (n, c) ∈ K := by
          intro K n c
          induction K with
          | nil => simp [List.lookup]
          | cons q K ih =>
            rcases q with ⟨m, d⟩
            intro hl
            by_cases h : n = m
            · subst h
              have hl' : d = c := by simpa [List.lookup] using hl
              subst hl'
              simp
            · have hnm : (n == m) = false := by simpa using h
              simp only [List.lookup, hnm] at hl
              exact List.mem_cons_of_mem _ (ih hl)
        exact hk2 _ (hlk _ _ _ hL)
      rw [hL] at hA
      dsimp only at hA
      by_cases hpar : ((n % 2 == 1) == p) = true
      · rw [ite_eq_left hpar] at hA
        subst hA
        simpa using hidle _
      · rw [ite_eq_right hpar] at hA
        subst hA
        have := hmove n hn (isMisesKLRandomAt_iff_total_totalize_filler p st.2.1)
          (fun h => hpar (beq_iff_eq.mpr h))
        simpa [hc'] using this

/-- Step 4' of the proof of `isKLRandom_iff_total_totalize`: the simulation
invariant, by induction on the time from the one-step lemma. -/
private lemma isKLRandom_iff_total_invariant (p : Bool) (β β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hFs : isKLRandom_iff_total_totalize_FuelSpec β.next Fs)
    (hCs : isKLRandom_iff_total_totalize_FuelSpec β.capital Cs)
    (hparity : isKLRandom_iff_total_OnlyBetsOnParity β p)
    (hn' : ∀ x, β'.next x = Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p x))
    (w : CantorSeq) (hw : β.Wins w) :
    isKLRandom_iff_total_totalize_Invariant p β β' Fs Cs w := by
  intro t
  suffices h : isKLRandom_iff_total_totalize_Good β w
      (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w t)) from h
  induction t with
  | zero =>
    refine ⟨0, rfl, by simp [isKLRandom_iff_total_totalize_replay, KLRule.revealed], ?_⟩
    intro q0 hq0 qk hqk
    have h0 : β.toRule.revealed w 0 = [] := rfl
    rw [h0] at hqk
    have := Part.mem_unique hq0 hqk
    simp [isKLRandom_iff_total_totalize_replay, KLRule.revealed, this]
  | succ t ih =>
    have hdom : (β'.toRule.next (β'.toRule.revealed w t)).Dom := by
      change (β'.next _).Dom
      rw [hn']; exact Part.some_dom _
    have hget : (β'.toRule.next (β'.toRule.revealed w t)).get hdom =
        isKLRandom_iff_total_totalize_nextCard Fs Cs p (β'.toRule.revealed w t) := by
      have hm := Part.get_mem hdom
      have hm' : (β'.toRule.next (β'.toRule.revealed w t)).get hdom ∈
          Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p
            (β'.toRule.revealed w t)) := by
        rw [← hn']; exact hm
      simpa using hm'
    rw [KLRule.revealed, dite_eq_left hdom, hget]
    have := isKLRandom_iff_total_totalize_onestep p β Fs Cs hFs hCs hparity w hw
        _
      ih
    simpa [isKLRandom_iff_total_totalize_replay, List.foldl_append,
      isKLRandom_iff_total_totalize_nextCard] using this

/-- Step 5a of the proof of `isKLRandom_iff_total_progress`: one
instruction either keeps the simulated history or extends it by exactly one bit. -/
private lemma isKLRandom_iff_total_progress_hist
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) (c : Bool) :
    (isKLRandom_iff_total_totalize_step Fs Cs p st c).1 = st.1 ∨
      ∃ b, (isKLRandom_iff_total_totalize_step Fs Cs p st c).1 = st.1 ++ [b] := by
  unfold isKLRandom_iff_total_totalize_step
  dsimp only
  split_ifs
  · exact Or.inr ⟨c, rfl⟩
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

private lemma isKLRandom_iff_total_progress_replay_snoc
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) (c : Bool) :
    isKLRandom_iff_total_totalize_replay Fs Cs p (y ++ [c]) =
      isKLRandom_iff_total_totalize_step Fs Cs p
        (isKLRandom_iff_total_totalize_replay Fs Cs p y) c := by
  simp [isKLRandom_iff_total_totalize_replay, List.foldl_append]

private lemma isKLRandom_iff_total_progress_reclen
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (y : BitString) :
    (isKLRandom_iff_total_totalize_replay Fs Cs p y).2.1.length = y.length := by
  induction y using List.reverseRecOn with
  | nil => simp [isKLRandom_iff_total_totalize_replay]
  | append_singleton y c ih =>
    rw [isKLRandom_iff_total_progress_replay_snoc]
    simp [isKLRandom_iff_total_totalize_step, ih]

private lemma isKLRandom_iff_total_progress_revealed_succ
    (p : Bool) (β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hn' : ∀ x, β'.next x = Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p x))
    (w : CantorSeq) (t : ℕ) :
    β'.toRule.revealed w (t + 1) = β'.toRule.revealed w t ++
      [w (isKLRandom_iff_total_totalize_nextCard Fs Cs p (β'.toRule.revealed w t))] := by
  have hdom : (β'.toRule.next (β'.toRule.revealed w t)).Dom := by
    change (β'.next _).Dom
    rw [hn']; exact Part.some_dom _
  have hget : (β'.toRule.next (β'.toRule.revealed w t)).get hdom =
      isKLRandom_iff_total_totalize_nextCard Fs Cs p (β'.toRule.revealed w t) := by
    have hm := Part.get_mem hdom
    have hm' : (β'.toRule.next (β'.toRule.revealed w t)).get hdom ∈
        Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p
          (β'.toRule.revealed w t)) := by
      rw [← hn']; exact hm
    simpa using hm'
  rw [KLRule.revealed, dite_eq_left hdom, hget]

private lemma isKLRandom_iff_total_progress_revealed_len
    (p : Bool) (β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hn' : ∀ x, β'.next x = Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p x))
    (w : CantorSeq) (t : ℕ) : (β'.toRule.revealed w t).length = t := by
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    rw [isKLRandom_iff_total_progress_revealed_succ p β' Fs Cs hn']
    simp [ih]

private lemma isKLRandom_iff_total_progress_revealed_cases
    (ρ : KLRule) (w : CantorSeq) (t : ℕ) :
    ρ.revealed w (t + 1) = ρ.revealed w t ∨
      ∃ c, ρ.revealed w (t + 1) = ρ.revealed w t ++ [c] := by
  rw [KLRule.revealed]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- Parity-`p` cards of the record were requested at a proper prefix of the simulated history. -/
private def isKLRandom_iff_total_progress_ParInv (β : KLBetting) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) : Prop :=
  ∀ e ∈ st.2.1, (e.1 % 2 == 1) = p → ∃ j, j < st.1.length ∧ e.1 ∈ β.next (st.1.take j)

private lemma isKLRandom_iff_total_progress_plan_spec
    (β : KLBetting) (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ β.next x)
    (st : isKLRandom_iff_total_totalize_State) :
    ((isKLRandom_iff_total_totalize_plan Fs Cs p st).1 % 2 == 1) ≠ p ∨
      ((isKLRandom_iff_total_totalize_plan Fs Cs p st).2.1 = true ∧
        (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.1 = none ∧
        (isKLRandom_iff_total_totalize_plan Fs Cs p st).1 ∈ β.next st.1) := by
  have hf := (isMisesKLRandomAt_iff_total_filler p st.2.1).2
  unfold isKLRandom_iff_total_totalize_plan
  split
  · exact Or.inl hf
  · rename_i n hn
    have hnmem : n ∈ β.next st.1 := hFs _ _ _ hn
    split
    · rename_i c hc
      split
      · exact Or.inl hf
      · exact Or.inl hf
    · split
      · split
        · exact Or.inl hf
        · split
          · split
            · exact Or.inr ⟨rfl, rfl, hnmem⟩
            · exact Or.inl hf
          · split
            · exact Or.inr ⟨rfl, rfl, hnmem⟩
            · exact Or.inl hf
          · exact Or.inl hf
      · rename_i hpar
        left
        simpa using hpar

private lemma isKLRandom_iff_total_progress_parinv_step
    (β : KLBetting) (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (hFs : ∀ s x n, Fs s x = some n → n ∈ β.next x)
    (st : isKLRandom_iff_total_totalize_State)
    (hst : isKLRandom_iff_total_progress_ParInv β p st) (c : Bool) :
    isKLRandom_iff_total_progress_ParInv β p
      (isKLRandom_iff_total_totalize_step Fs Cs p st c) := by
  intro e he hpar
  have hpre : st.1 <+: (isKLRandom_iff_total_totalize_step Fs Cs p st c).1 := by
    rcases isKLRandom_iff_total_progress_hist Fs Cs p st c with h | ⟨b, h⟩
    · rw [h]
    · rw [h]; exact List.prefix_append _ _
  have he' : e ∈ st.2.1 ++ [((isKLRandom_iff_total_totalize_plan Fs Cs p st).1, c)] := by
    simpa [isKLRandom_iff_total_totalize_step] using he
  rcases List.mem_append.1 he' with h | h
  · obtain ⟨j, hj, hjn⟩ := hst e h hpar
    refine ⟨j, lt_of_lt_of_le hj hpre.length_le, ?_⟩
    obtain ⟨z, hz⟩ := hpre
    rw [← hz, List.take_append_of_le_length hj.le]
    exact hjn
  · rw [List.mem_singleton] at h
    subst h
    rcases isKLRandom_iff_total_progress_plan_spec β Fs Cs p hFs st with
      h1 | ⟨h2, h3, h4⟩
    · exact absurd hpar h1
    · have hh : (isKLRandom_iff_total_totalize_step Fs Cs p st c).1 = st.1 ++ [c] := by
        simp [isKLRandom_iff_total_totalize_step, h2]
      refine ⟨st.1.length, ?_, ?_⟩
      · rw [hh]; simp
      · rw [hh, List.take_left]; exact h4

/-- Step 5b of the proof of `isKLRandom_iff_total_progress`: a
positive capital along the run (a zero capital stays zero by `NoOverBet`, contradicting
unboundedness). -/
private lemma isKLRandom_iff_total_progress_cap_pos
    (β : KLBetting) (hnobet : isKLRandom_iff_total_NoOverBet β) (w : CantorSeq)
    (hw : β.Wins w) (k : ℕ) (q : ℚ) (hq : q ∈ β.capital (β.toRule.revealed w k)) : 0 < q := by
  by_contra hle
  have hq0 : q = 0 := le_antisymm (not_lt.1 hle) (β.nonneg _ _ hq)
  have hzero : ∀ j, k ≤ j → ∀ q' ∈ β.capital (β.toRule.revealed w j), q' = 0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro q' hq'; rw [Part.mem_unique hq' hq, hq0]
    | succ j hj ih =>
      intro q' hq'
      obtain ⟨g, hg⟩ := Part.dom_iff_mem.1 (hw.2.1 j)
      have hg0 := ih g hg
      rcases isKLRandom_iff_total_progress_revealed_cases β.toRule w j with
        h | ⟨c, h⟩
      · rw [h] at hq'; exact ih q' hq'
      · rw [h] at hq'
        have h1 := hnobet _ g hg c q' hq'
        have h2 := β.nonneg _ _ hq'
        rw [hg0] at h1
        linarith
  apply hw.2.2
  have hnn : ∀ i, (0 : ℝ) ≤
      (((β.capital (β.toRule.revealed w i)).get (hw.2.1 i) : ℚ) : ℝ) := fun i => by
    exact_mod_cast β.nonneg _ _ (Part.get_mem _)
  refine ⟨∑ i ∈ Finset.range (k + 1),
    (((β.capital (β.toRule.revealed w i)).get (hw.2.1 i) : ℚ) : ℝ), ?_⟩
  rintro r ⟨j, q', hq', rfl⟩
  by_cases hjk : j ≤ k
  · have : q' = (β.capital (β.toRule.revealed w j)).get (hw.2.1 j) :=
      Part.mem_unique hq' (Part.get_mem _)
    rw [this]
    exact Finset.single_le_sum (f := fun i =>
      (((β.capital (β.toRule.revealed w i)).get (hw.2.1 i) : ℚ) : ℝ)) (fun i _ => hnn i)
      (Finset.mem_range.2 (by omega))
  · rw [hzero j (by omega) q' hq']
    simpa using Finset.sum_nonneg (fun i _ => hnn i)

/-- Step 5c of the proof of `isKLRandom_iff_total_progress`: under
the stated halting hypotheses, the instruction appends a bit to the simulated history. -/
private lemma isKLRandom_iff_total_progress_plan_flag
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) (n : ℕ)
    (hF : Fs st.2.1.length st.1 = some n)
    (hnot : (n % 2 == 1) = p → st.2.1.lookup n = none)
    (hbet : (n % 2 == 1) = p → ∃ q, Cs st.2.1.length st.1 = some q ∧ 0 < q ∧
      (∃ b v, Cs st.2.1.length (st.1 ++ [b]) = some v) ∧
      ∀ b v, Cs st.2.1.length (st.1 ++ [b]) = some v → 0 ≤ v ∧ v ≤ 2 * q) :
    (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.1 = true ∨
      ∃ d, (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.1 = some d := by
  unfold isKLRandom_iff_total_totalize_plan
  split
  · rename_i h; rw [hF] at h; cases h
  · rename_i n' hn'
    rw [hF] at hn'
    obtain rfl := Option.some.inj hn'
    split
    · rename_i c hc
      split
      · rename_i h
        have := hnot (by simpa using h)
        rw [hc] at this; cases this
      · exact Or.inr ⟨c, rfl⟩
    · rename_i hnK
      split
      · rename_i hp
        have hp' : (n % 2 == 1) = p := by simpa using hp
        obtain ⟨q, hq, hq0, ⟨b0, v0, hv0⟩, hall⟩ := hbet hp'
        split
        · rename_i h; rw [hq] at h; cases h
        · rename_i q' hq'
          rw [hq] at hq'
          obtain rfl := Option.some.inj hq'
          split
          · rename_i v h0
            split
            · exact Or.inl rfl
            · rename_i hg
              exact absurd ⟨hq0, hall _ _ h0⟩ hg
          · rename_i _ v h1
            split
            · exact Or.inl rfl
            · rename_i hg
              exact absurd ⟨hq0, hall _ _ h1⟩ hg
          · rename_i h0 h1
            cases b0
            · rw [h0] at hv0; cases hv0
            · rw [h1] at hv0; cases hv0
      · exact Or.inl rfl

/-- Step 5d of the proof of `isKLRandom_iff_total_progress`: an
instruction with the flag or a stored bit appends exactly one bit. -/
private lemma isKLRandom_iff_total_progress_grow
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ) (p : Bool)
    (st : isKLRandom_iff_total_totalize_State) (c : Bool)
    (h : (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.1 = true ∨
      ∃ d, (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.2.1 = some d) :
    ∃ b, (isKLRandom_iff_total_totalize_step Fs Cs p st c).1 = st.1 ++ [b] := by
  unfold isKLRandom_iff_total_totalize_step
  dsimp only
  rcases h with h | ⟨d, hd⟩
  · exact ⟨c, by rw [ite_eq_left h]⟩
  · by_cases h' : (isKLRandom_iff_total_totalize_plan Fs Cs p st).2.1 = true
    · exact ⟨c, by rw [ite_eq_left h']⟩
    · exact ⟨d, by rw [ite_eq_right h', hd]⟩

/-- Step 5e of the proof of `isKLRandom_iff_total_progress`: the
simulation cannot stay at a stage `σ_k` forever. -/
private lemma isKLRandom_iff_total_progress_stuck (p : Bool) (β : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hFs : isKLRandom_iff_total_totalize_FuelSpec β.next Fs)
    (hCs : isKLRandom_iff_total_totalize_FuelSpec β.capital Cs)
    (hnobet : isKLRandom_iff_total_NoOverBet β)
    (w : CantorSeq) (hw : β.Wins w)
    (st : ℕ → isKLRandom_iff_total_totalize_State)
    (hlen : ∀ s, (st s).2.1.length = s)
    (hsucc : ∀ s, st (s + 1) = isKLRandom_iff_total_totalize_step Fs Cs p (st s)
      (w (isKLRandom_iff_total_totalize_plan Fs Cs p (st s)).1))
    (hpar : ∀ s, isKLRandom_iff_total_progress_ParInv β p (st s))
    (k t : ℕ) (H : ∀ s, t ≤ s → (st s).1 = β.toRule.revealed w k) : False := by
  have hXlen : (β.toRule.revealed w k).length ≤ k :=
    isKLRandom_iff_total_split_revealed_length_le _ w k
  have hdomN : (β.next (β.toRule.revealed w k)).Dom := by
    by_contra hnd
    have h2 : β.toRule.revealed w (k + 1) = β.toRule.revealed w k := by
      rw [KLRule.revealed]
      exact dite_eq_right (show ¬ (β.toRule.next (β.toRule.revealed w k)).Dom from hnd)
    have h1 := hw.1 (k + 1)
    rw [h2] at h1
    omega
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 hdomN
  have hs1 : β.toRule.revealed w (k + 1) = β.toRule.revealed w k ++ [w n] := by
    have hd' : (β.toRule.next (β.toRule.revealed w k)).Dom := hdomN
    have hget : (β.toRule.next (β.toRule.revealed w k)).get hd' = n :=
      Part.get_eq_of_mem hn hd'
    rw [KLRule.revealed, dite_eq_left hd', hget]
  obtain ⟨q, hq⟩ := Part.dom_iff_mem.1 (hw.2.1 k)
  have hq0 := isKLRandom_iff_total_progress_cap_pos β hnobet w hw k q hq
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 (hw.2.1 (k + 1))
  rw [hs1] at hv
  obtain ⟨s0, h0⟩ := hFs.2.1 _ _ hn
  obtain ⟨s1, h1⟩ := hCs.2.1 _ _ hq
  obtain ⟨s2, h2⟩ := hCs.2.1 _ _ hv
  set X := β.toRule.revealed w k with hX
  set s := max (max t s0) (max s1 s2) with hs
  have hXs : (st s).1 = X := H s (by omega)
  have hL : (st s).2.1.length = s := hlen s
  have hFX : Fs (st s).2.1.length (st s).1 = some n := by
    rw [hL, hXs]; exact hFs.2.2 _ _ _ h0 s (by omega)
  have hflag := isKLRandom_iff_total_progress_plan_flag Fs Cs p (st s) n hFX
    (by
      intro hp
      cases hlk : (st s).2.1.lookup n with
      | none => rfl
      | some c =>
        exfalso
        have hmem := isMisesKLRandomAt_iff_total_totalize_lookup_mem _ _ _ hlk
        obtain ⟨j, hj, hjn⟩ := hpar s _ hmem hp
        rw [hXs] at hj hjn
        have hne : X.take j ≠ X := by
          intro heq
          have hlength := congrArg List.length heq
          simp only [List.length_take, Nat.min_eq_left hj.le] at hlength
          omega
        exact (β.noRepeat _ _ (List.take_prefix _ _) hne n hjn n hn) rfl)
    (by
      intro _
      refine ⟨q, ?_, hq0, ⟨w n, v, ?_⟩, ?_⟩
      · rw [hL, hXs]; exact hCs.2.2 _ _ _ h1 s (by omega)
      · rw [hL, hXs]; exact hCs.2.2 _ _ _ h2 s (by omega)
      · intro b v' hv'
        rw [hL, hXs] at hv'
        have hm := hCs.1 _ _ _ hv'
        exact ⟨β.nonneg _ _ hm, hnobet X q hq b v' hm⟩)
  obtain ⟨b, hb⟩ := isKLRandom_iff_total_progress_grow Fs Cs p (st s)
    (w (isKLRandom_iff_total_totalize_plan Fs Cs p (st s)).1) hflag
  have hnext : (st (s + 1)).1 = X := H (s + 1) (by omega)
  rw [hsucc, hb, hXs] at hnext
  have := congrArg List.length hnext
  simp at this

/-- Step 5 of the proof of `isKLRandom_iff_total_totalize`: progress. Given the
invariant, the budget (the number of bits read) grows by one per step, padding cards never run out,
and the finitely many computations needed for the next stage (`next σ_k`, `c σ_k`, one child) halt
within a finite budget, so the simulated history reaches every stage `σ_k` of the run of `β`. -/
private lemma isKLRandom_iff_total_progress (p : Bool) (β β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hFs : isKLRandom_iff_total_totalize_FuelSpec β.next Fs)
    (hCs : isKLRandom_iff_total_totalize_FuelSpec β.capital Cs)
    (hnobet : isKLRandom_iff_total_NoOverBet β)
    (hn' : ∀ x, β'.next x = Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p x))
    (w : CantorSeq) (hw : β.Wins w)
    (hinv : isKLRandom_iff_total_totalize_Invariant p β β' Fs Cs w) :
    isKLRandom_iff_total_totalize_Progress p β β' Fs Cs w := by
  let st : ℕ → isKLRandom_iff_total_totalize_State := fun s =>
    isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w s)
  have hlen : ∀ s, (st s).2.1.length = s := fun s => by
    change (isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w s)).2.1.length
        = s
    rw [isKLRandom_iff_total_progress_reclen,
      isKLRandom_iff_total_progress_revealed_len p β' Fs Cs hn']
  have hsucc : ∀ s, st (s + 1) = isKLRandom_iff_total_totalize_step Fs Cs p (st s)
      (w (isKLRandom_iff_total_totalize_plan Fs Cs p (st s)).1) := fun s => by
    change isKLRandom_iff_total_totalize_replay Fs Cs p (β'.toRule.revealed w (s + 1)) = _
    rw [isKLRandom_iff_total_progress_revealed_succ p β' Fs Cs hn',
      isKLRandom_iff_total_progress_replay_snoc]
    rfl
  have hpar : ∀ s, isKLRandom_iff_total_progress_ParInv β p (st s) := by
    intro s
    induction s with
    | zero =>
      intro e he
      simp [st, isKLRandom_iff_total_totalize_replay, KLRule.revealed] at he
    | succ s ih =>
      rw [hsucc s]
      exact isKLRandom_iff_total_progress_parinv_step β Fs Cs p hFs.1 _ ih _
  have hσlen : ∀ j, (β.toRule.revealed w j).length = j := fun j =>
    le_antisymm (isKLRandom_iff_total_split_revealed_length_le _ w j) (hw.1 j)
  intro k
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    by_contra hno
    push Not at hno
    have hall : ∀ s, t ≤ s → (st s).1 = β.toRule.revealed w k := by
      intro s hs
      induction s, hs using Nat.le_induction with
      | base => exact ht
      | succ s hs ih =>
        rcases isKLRandom_iff_total_progress_hist Fs Cs p (st s)
          (w (isKLRandom_iff_total_totalize_plan Fs Cs p (st s)).1) with h | ⟨b, h⟩
        · rw [hsucc s, h]; exact ih
        · exfalso
          obtain ⟨k', hk', _⟩ := hinv (s + 1)
          have hl : (st (s + 1)).1.length = k + 1 := by
            rw [hsucc s, h]; simp [ih, hσlen]
          have hl' : (st (s + 1)).1.length = k' := by
            rw [show (st (s + 1)).1 = β.toRule.revealed w k' from hk', hσlen]
          have : k' = k + 1 := by omega
          subst this
          exact hno (s + 1) hk'
    exact isKLRandom_iff_total_progress_stuck p β Fs Cs hFs hCs hnobet w hw
      st hlen hsucc hpar k t hall

/-- Step 6 of the proof of `isKLRandom_iff_total_totalize`: unboundedness. By the
invariant and progress the simulated capital takes every value `c(σ_k) / c([])`, so a bound on it
gives a bound on the capital of `β` along its run. -/
private lemma isKLRandom_iff_total_unbounded (p : Bool) (β β' : KLBetting)
    (Fs : ℕ → BitString → Option ℕ) (Cs : ℕ → BitString → Option ℚ)
    (hc' : ∀ x, β'.capital x = Part.some (isKLRandom_iff_total_totalize_cap Fs Cs p x))
    (w : CantorSeq) (hw : β.Wins w)
    (hinv : isKLRandom_iff_total_totalize_Invariant p β β' Fs Cs w)
    (hprog : isKLRandom_iff_total_totalize_Progress p β β' Fs Cs w) :
    ¬ BddAbove {r : ℝ | ∃ t, ∃ q ∈ β'.capital (β'.toRule.revealed w t), (q : ℝ) = r} := by
  rintro ⟨M, hM⟩
  have h0 : β.toRule.revealed w 0 = [] := rfl
  have hd0 : (β.capital []).Dom := by
    have := hw.2.1 0
    rw [h0] at this
    exact this
  have hq0 : (β.capital []).get hd0 ∈ β.capital [] := Part.get_mem _
  have hq0nn : 0 ≤ (β.capital []).get hd0 := β.nonneg _ _ hq0
  apply hw.2.2
  refine ⟨M * ((β.capital []).get hd0 : ℚ), ?_⟩
  rintro r ⟨k, qk, hqk, rfl⟩
  obtain ⟨t, ht⟩ := hprog k
  obtain ⟨k', h1, _, h3⟩ := hinv t
  have hkk : β.toRule.revealed w k' = β.toRule.revealed w k := h1.symm.trans ht
  rw [← hkk] at hqk
  have h4 : isKLRandom_iff_total_totalize_cap Fs Cs p (β'.toRule.revealed w t) *
      (β.capital []).get hd0 = qk := h3 _ hq0 qk hqk
  have hle : ((isKLRandom_iff_total_totalize_cap Fs Cs p (β'.toRule.revealed w t) : ℚ) : ℝ)
      ≤ M :=
    hM ⟨t, _, by rw [hc']; exact Part.mem_some _, rfl⟩
  have h5 : (qk : ℝ) = ((isKLRandom_iff_total_totalize_cap Fs Cs p
      (β'.toRule.revealed w t) : ℚ) : ℝ) * (((β.capital []).get hd0 : ℚ) : ℝ) := by
    rw [← h4]; push_cast; ring
  rw [h5]
  exact mul_le_mul_of_nonneg_right hle (by exact_mod_cast hq0nn)

/-- Step 2 of the proof of `isKLRandom_iff_total`: totalize a strategy that bets only on
one parity and does not overbet, into a total winning strategy. -/
private lemma isKLRandom_iff_total_totalize (p : Bool) (β : KLBetting)
    (hnext : Partrec β.next) (hcap : Partrec β.capital)
  (hparity : isKLRandom_iff_total_OnlyBetsOnParity β p)
      (hnobet : isKLRandom_iff_total_NoOverBet β) :
  ∃ β' : KLBetting, Partrec β'.next ∧ Partrec β'.capital ∧ (∀ x, (β'.next x).Dom) ∧
      (∀ x, (β'.capital x).Dom) ∧ ∀ w, β.Wins w → β'.Wins w := by
  obtain ⟨Fs, hFsP, hFs1, hFs2, hFs3⟩ :=
    isMisesKLRandomAt_iff_total_fuel (β := ℕ) hnext
  obtain ⟨Cs, hCsP, hCs1, hCs2, hCs3⟩ :=
    isMisesKLRandomAt_iff_total_fuel (β := ℚ) hcap
  obtain ⟨hcn, hcc⟩ := isKLRandom_iff_total_computable Fs Cs p hFsP hCsP
  let β' : KLBetting :=
    { next := fun y => Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p y)
      capital := fun y => Part.some (isKLRandom_iff_total_totalize_cap Fs Cs p y)
      noRepeat := by
        intro x y hxy hne a ha b hb
        simp only [Part.mem_some_iff] at ha hb
        subst ha hb
        exact isKLRandom_iff_total_noRepeat Fs Cs p x y hxy hne
      nonneg := by
        intro x q hq
        simp only [Part.mem_some_iff] at hq
        subst hq
        exact (isKLRandom_iff_total_nonneg_fair Fs Cs p x).1
      fair := by
        intro x q q₀ q₁ hq h0 h1
        simp only [Part.mem_some_iff] at hq h0 h1
        subst hq h0 h1
        exact (isKLRandom_iff_total_nonneg_fair Fs Cs p x).2 }
  refine ⟨β', hcn.partrec, hcc.partrec, fun _ => Part.some_dom _, fun _ => Part.some_dom _, ?_⟩
  intro w hw
  have hn' : ∀ x, β'.next x = Part.some (isKLRandom_iff_total_totalize_nextCard Fs Cs p x) :=
    fun _ => rfl
  have hc' : ∀ x, β'.capital x = Part.some (isKLRandom_iff_total_totalize_cap Fs Cs p x) :=
    fun _ => rfl
  have hFs : isKLRandom_iff_total_totalize_FuelSpec β.next Fs := ⟨hFs1, hFs2, hFs3⟩
  have hCs : isKLRandom_iff_total_totalize_FuelSpec β.capital Cs := ⟨hCs1, hCs2, hCs3⟩
  have hinv := isKLRandom_iff_total_invariant p β β' Fs Cs hFs hCs hparity hn' w hw
  have hprog := isKLRandom_iff_total_progress p β β' Fs Cs hFs hCs hnobet hn' w hw hinv
  refine ⟨?_, fun t => Part.some_dom _,
    isKLRandom_iff_total_unbounded p β β' Fs Cs hc' w hw hinv hprog⟩
  intro t
  induction t with
  | zero => simp [KLRule.revealed]
  | succ t ih =>
    have hdom : (β'.toRule.next (β'.toRule.revealed w t)).Dom := Part.some_dom _
    rw [KLRule.revealed, dite_eq_left hdom]
    simp only [List.length_append, List.length_singleton]
    omega

/-- **SUV p. 309.**  For non-monotonic martingales it does not matter whether they are total or not,
by the argument of Theorem 191. -/
theorem isKLRandom_iff_total (w : CantorSeq) :
    IsKLRandom w ↔ ∀ β : KLBetting, Partrec β.next → Partrec β.capital →
      (∀ x, (β.next x).Dom) → (∀ x, (β.capital x).Dom) → ¬ β.Wins w := by
  constructor
  · intro h β hnext hcap _ _ hwins
    exact h β hnext hcap hwins
  · intro h β hnext hcap hwins
    rcases isKLRandom_iff_total_split β hnext hcap with ⟨betas, hbetas, hwins_imp⟩
    rcases hwins_imp w hwins with ⟨p, hwins_p⟩
    have ⟨hnext_p, hcap_p, hparity_p, hnobet_p⟩ := hbetas p
    rcases isKLRandom_iff_total_totalize p (betas p) hnext_p hcap_p hparity_p hnobet_p with
        ⟨β', hnext', hcap', hdom_next, hdom_cap, hwins_imp'⟩
    exact h β' hnext' hcap' hdom_next hdom_cap (hwins_imp' w hwins_p)

/-- **SUV p. 309: an open question, not a theorem.**  "It is not known now (2013) whether these two
classes coincide."  This `Prop` names the question; nothing in the library asserts it or its
negation. -/
def KLRandomnessEqualsMartinLofQuestion : Prop :=
  ∀ w, IsKLRandom w ↔ IsMartinLofRandom uniformMeasure w

end Kolmogorov.FrequencyGames
