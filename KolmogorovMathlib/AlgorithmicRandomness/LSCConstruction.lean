import KolmogorovMathlib.AlgorithmicRandomness.LSCAux

/-!
# From an enumerator to a monotone dyadic approximation

Given an enumerator witnessing that `f : CantorSeq → ℝ≥0∞` is lower
semicomputable, we build a computable table of dyadic lower approximations
`lscApprox` which is monotone along the prefixes of a sequence and whose
supremum recovers `f`.
-/

namespace Kolmogorov

open Encodable Denumerable
open scoped ENNReal NNReal

/-- Stage-`s` search: the level-`s` dyadic threshold `k / 2 ^ s` has already been
enumerated, within `s` steps, together with a cylinder that is a prefix of `x`. -/
def lscFound (enum : ℚ → ℕ → Option BitString) (s : ℕ) (x : BitString) (k : ℕ) : Bool :=
  lscBExists (fun i => (enum ((k : ℚ) / 2 ^ s) i).elim false (fun y => lscIsPrefixB y x)) s

/-- The dyadic lower approximation of a lower semicomputable function extracted
from an enumerator: the largest level-`s` dyadic threshold below `s` that has
been found by stage `s`. -/
def lscApprox (enum : ℚ → ℕ → Option BitString) (s : ℕ) (x : BitString) : ℕ :=
  lscBMax (fun k => if lscFound enum s x k then k else 0) (s * 2 ^ s + 1)

/-- If the search test succeeds then one of the first `s` enumerated strings for the threshold
`k / 2^s` is a prefix of `x`. -/
lemma lscFound_spec {enum : ℚ → ℕ → Option BitString} {s : ℕ} {x : BitString} {k : ℕ}
    (h : lscFound enum s x k = true) :
    ∃ i < s, ∃ y, enum ((k : ℚ) / 2 ^ s) i = some y ∧ y <+: x := by
  rw [lscFound, lscBExists_iff] at h
  obtain ⟨i, hi, hval⟩ := h
  cases hy : enum ((k : ℚ) / 2 ^ s) i with
  | none => rw [hy] at hval; simp at hval
  | some y =>
    rw [hy] at hval
    exact ⟨i, hi, y, hy, (lscIsPrefixB_iff y x).1 (by simpa using hval)⟩

/-- The search test succeeds as soon as some enumerated string below stage `s` is a prefix
of `x`. -/
lemma lscFound_of {enum : ℚ → ℕ → Option BitString} {s : ℕ} {x : BitString} {k i : ℕ}
    {y : BitString} (hi : i < s) (h : enum ((k : ℚ) / 2 ^ s) i = some y) (hp : y <+: x) :
    lscFound enum s x k = true := by
  rw [lscFound, lscBExists_iff]
  refine ⟨i, hi, ?_⟩
  rw [h]
  simpa using (lscIsPrefixB_iff y x).2 hp

/-- The search test is computable whenever the enumeration of the superlevel sets is. -/
lemma lscComputable_found {enum : ℚ → ℕ → Option BitString}
    (hcomp : Computable (fun p : ℚ × ℕ => enum p.1 p.2)) :
    Computable (fun p : (ℕ × BitString) × ℕ => lscFound enum p.1.1 p.1.2 p.2) := by
  have hq : Computable (fun c : ((ℕ × BitString) × ℕ) × ℕ => ((c.1.2 : ℚ) / 2 ^ c.1.1.1)) := by
    have hpair : Computable (fun c : ((ℕ × BitString) × ℕ) × ℕ => (c.1.2, c.1.1.1)) :=
      (Computable.snd.comp Computable.fst).pair
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
    exact (lscComputable_dyadicRat.comp hpair).of_eq (fun _ => rfl)
  have ho : Computable
      (fun c : ((ℕ × BitString) × ℕ) × ℕ => enum ((c.1.2 : ℚ) / 2 ^ c.1.1.1) c.2) :=
    (hcomp.comp (hq.pair Computable.snd)).of_eq (fun _ => rfl)
  have hg : Computable₂ (fun (c : ((ℕ × BitString) × ℕ) × ℕ) (y : BitString) =>
      lscIsPrefixB y c.1.1.2) :=
    Computable₂.comp (f := fun (y x : BitString) => lscIsPrefixB y x)
      lscPrimrec₂_isPrefixB.to_comp Computable.snd
      (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
  have hG : Computable₂ (fun (a : (ℕ × BitString) × ℕ) (i : ℕ) =>
      (enum ((a.2 : ℚ) / 2 ^ a.1.1) i).elim false (fun y => lscIsPrefixB y a.1.2)) := by
    have hmain := Computable.option_casesOn ho (Computable.const false) hg
    refine hmain.of_eq (fun c => ?_)
    change Option.casesOn (enum ((c.1.2 : ℚ) / 2 ^ c.1.1.1) c.2) false
        (fun y => lscIsPrefixB y c.1.1.2)
      = (enum ((c.1.2 : ℚ) / 2 ^ c.1.1.1) c.2).elim false (fun y => lscIsPrefixB y c.1.1.2)
    cases enum ((c.1.2 : ℚ) / 2 ^ c.1.1.1) c.2 <;> rfl
  have hbe := lscComputable_bExists (G := fun (a : (ℕ × BitString) × ℕ) (i : ℕ) =>
    (enum ((a.2 : ℚ) / 2 ^ a.1.1) i).elim false (fun y => lscIsPrefixB y a.1.2))
    (N := fun a : (ℕ × BitString) × ℕ => a.1.1) hG (Computable.fst.comp Computable.fst)
  exact hbe.of_eq (fun a => rfl)

/-- The dyadic approximation built from a computable enumeration of superlevel sets is
computable. -/
lemma lscComputable_approx {enum : ℚ → ℕ → Option BitString}
    (hcomp : Computable (fun p : ℚ × ℕ => enum p.1 p.2)) :
    Computable (fun p : ℕ × BitString => lscApprox enum p.1 p.2) := by
  have hfound := lscComputable_found hcomp
  have hF : Computable₂ (fun (a : ℕ × BitString) (k : ℕ) =>
      if lscFound enum a.1 a.2 k then k else 0) := by
    have hc := Computable.cond hfound Computable.snd (Computable.const 0)
    refine hc.of_eq (fun c => ?_)
    cases h : lscFound enum c.1.1 c.1.2 c.2 <;> simp [h]
  have hN : Computable (fun a : ℕ × BitString => a.1 * 2 ^ a.1 + 1) := by
    have hpow : Primrec (fun a : ℕ × BitString => 2 ^ a.1) :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst
    have hmul : Primrec (fun a : ℕ × BitString => a.1 * 2 ^ a.1) :=
      Primrec₂.comp Primrec.nat_mul Primrec.fst hpow
    exact (Primrec₂.comp Primrec.nat_add hmul (Primrec.const 1)).to_comp
  exact lscComputable_bMax hF hN

/-! ### The approximation recovers the function -/

variable {f : CantorSeq → ℝ≥0∞} {enum : ℚ → ℕ → Option BitString}

/-- A successful search at threshold `k / 2^s` certifies that the value of `f` at the point
exceeds that threshold. -/
lemma lscDyadicValue_lt_of_found
    (hspec : ∀ q : ℚ, {w | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} =
      ⋃ i, (enum q i).elim ∅ cantorCylinder)
    {s k : ℕ} {w : CantorSeq} (h : lscFound enum s (cantorPrefix w s) k = true) :
    dyadicValue k s < f w := by
  obtain ⟨i, _, y, hy, hp⟩ := lscFound_spec h
  have hwy : w ∈ cantorCylinder y :=
    cantorCylinder_subset_of_prefix hp (mem_cantorCylinder_cantorPrefix w s)
  have hq0 : (0 : ℚ) ≤ (k : ℚ) / 2 ^ s := by positivity
  have hmem : w ∈ ⋃ i, (enum ((k : ℚ) / 2 ^ s) i).elim ∅ cantorCylinder :=
    Set.mem_iUnion.2 ⟨i, by rw [hy]; exact hwy⟩
  rw [← hspec ((k : ℚ) / 2 ^ s), Set.mem_setOf_eq] at hmem
  rcases hmem with hneg | hlt
  · exact absurd hneg (not_lt.2 (by exact_mod_cast hq0))
  · rw [lscDyadicValue_eq_ofReal]
    exact hlt

/-- The dyadic approximations built from an enumeration of the superlevel sets never exceed the
function they approximate. -/
lemma lscApprox_le
    (hspec : ∀ q : ℚ, {w | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} =
      ⋃ i, (enum q i).elim ∅ cantorCylinder)
    (w : CantorSeq) (s : ℕ) :
    dyadicValue (lscApprox enum s (cantorPrefix w s)) s ≤ f w := by
  rcases lscBMax_spec (fun k => if lscFound enum s (cantorPrefix w s) k then k else 0)
      (s * 2 ^ s + 1) with h0 | ⟨k, _, hkv⟩
  · rw [show lscApprox enum s (cantorPrefix w s) = 0 from h0, dyadicValue_zero]
    exact zero_le _
  · by_cases hfound : lscFound enum s (cantorPrefix w s) k = true
    · have hkeq : k = lscApprox enum s (cantorPrefix w s) := by
        rw [lscApprox]; simpa [hfound] using hkv
      rw [← hkeq]
      exact le_of_lt (lscDyadicValue_lt_of_found hspec hfound)
    · have h0 : lscApprox enum s (cantorPrefix w s) = 0 := by
        rw [lscApprox]; simpa [hfound] using hkv.symm
      rw [h0, dyadicValue_zero]
      exact zero_le _

/-- The dyadic approximations increase with the stage along a fixed sequence. -/
lemma lscApprox_prefix_mono (enum : ℚ → ℕ → Option BitString) (w : CantorSeq) (s : ℕ) :
    dyadicValue (lscApprox enum s (cantorPrefix w s)) s
      ≤ dyadicValue (lscApprox enum (s + 1) (cantorPrefix w (s + 1))) (s + 1) := by
  rcases lscBMax_spec (fun k => if lscFound enum s (cantorPrefix w s) k then k else 0)
      (s * 2 ^ s + 1) with h0 | ⟨k, hk, hkv⟩
  · rw [show lscApprox enum s (cantorPrefix w s) = 0 from h0, dyadicValue_zero]
    exact zero_le _
  · by_cases hfound : lscFound enum s (cantorPrefix w s) k = true
    · have hkeq : k = lscApprox enum s (cantorPrefix w s) := by
        rw [lscApprox]; simpa [hfound] using hkv
      obtain ⟨i, hi, y, hy, hp⟩ := lscFound_spec hfound
      have hrat : ((2 * k : ℕ) : ℚ) / 2 ^ (s + 1) = (k : ℚ) / 2 ^ s := by
        push_cast; ring
      have hfound' : lscFound enum (s + 1) (cantorPrefix w (s + 1)) (2 * k) = true := by
        refine lscFound_of (i := i) (y := y) (by omega) ?_ ?_
        · rw [hrat]; exact hy
        · exact hp.trans (cantorPrefix_mono w (Nat.le_succ s))
      have hk' : k ≤ s * 2 ^ s := by omega
      have hb : 2 * k < (s + 1) * 2 ^ (s + 1) + 1 := by
        have h1 : 2 * k ≤ 2 * (s * 2 ^ s) := by omega
        have h2 : 2 * (s * 2 ^ s) = s * 2 ^ (s + 1) := by ring
        have h3 : s * 2 ^ (s + 1) ≤ (s + 1) * 2 ^ (s + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hle : 2 * k ≤ lscApprox enum (s + 1) (cantorPrefix w (s + 1)) := by
        have hmax := lscLe_bMax
          (fun k' => if lscFound enum (s + 1) (cantorPrefix w (s + 1)) k' then k' else 0) hb
        simp only [hfound', if_true] at hmax
        exact hmax
      calc dyadicValue (lscApprox enum s (cantorPrefix w s)) s
          = dyadicValue (2 * k) (s + 1) := by rw [← hkeq, dyadicValue_two_mul_succ]
        _ ≤ _ := lscDyadicValue_mono _ hle
    · have h0 : lscApprox enum s (cantorPrefix w s) = 0 := by
        rw [lscApprox]; simpa [hfound] using hkv.symm
      rw [h0, dyadicValue_zero]
      exact zero_le _

/-- The supremum of the dyadic approximations is at least the value of the function. -/
lemma lscLe_iSup_approx
    (hspec : ∀ q : ℚ, {w | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} =
      ⋃ i, (enum q i).elim ∅ cantorCylinder)
    (w : CantorSeq) :
    f w ≤ ⨆ s, dyadicValue (lscApprox enum s (cantorPrefix w s)) s := by
  by_contra hcon
  have hlt : (⨆ s, dyadicValue (lscApprox enum s (cantorPrefix w s)) s) < f w := not_le.1 hcon
  obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  obtain ⟨q', hq'0, hq'1, hq'2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hq2
  have hqq' : q < q' := by
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hq0)).1 hq'1
    exact_mod_cast h
  have hpos : (0 : ℚ) < q' - q := sub_pos.2 hqq'
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (1 : ℚ) / 2 ^ t < q' - q := by
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 : ℚ) / 2 < 1)
    refine ⟨t, ?_⟩
    calc (1 : ℚ) / 2 ^ t = ((1 : ℚ) / 2) ^ t := by rw [div_pow]; norm_num
      _ < q' - q := ht
  have h2t : (0 : ℚ) < 2 ^ t := by positivity
  set j : ℕ := ⌊q * 2 ^ t⌋₊ + 1 with hj
  set d : ℚ := (j : ℚ) / 2 ^ t with hd
  have hqd : q < d := by
    have h1 : q * 2 ^ t < (j : ℚ) := by
      push_cast [hj]
      exact Nat.lt_floor_add_one (q * 2 ^ t)
    rw [hd, lt_div_iff₀ h2t]
    exact h1
  have hdq' : d < q' := by
    have hfl : (⌊q * 2 ^ t⌋₊ : ℚ) ≤ q * 2 ^ t :=
      Nat.floor_le (by positivity)
    have h1 : (j : ℚ) ≤ q * 2 ^ t + 1 := by push_cast [hj]; linarith
    have h2 : d ≤ q + 1 / 2 ^ t := by
      rw [hd, div_le_iff₀ h2t]
      field_simp
      linarith
    linarith
  have hd0 : (0 : ℚ) ≤ d := by positivity
  have hdf : ENNReal.ofReal ((d : ℝ)) < f w := by
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hq'2
    exact_mod_cast hdq'.le
  have hmemset : w ∈ {v : CantorSeq | (d : ℝ) < 0 ∨ ENNReal.ofReal (d : ℝ) < f v} :=
    Or.inr hdf
  rw [hspec d] at hmemset
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmemset
  cases hy : enum d i with
  | none =>
    rw [hy] at hi
    exact absurd hi (Set.notMem_empty w)
  | some y =>
    rw [hy] at hi
    have hyp : cantorPrefix w y.length = y :=
      (isCantorPrefix_iff_cantorPrefix_eq y w).1 hi
    set s : ℕ := max (max t (i + 1)) (max y.length j) with hs
    have hts : t ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
    have his : i < s := lt_of_lt_of_le (Nat.lt_succ_self i)
      (le_trans (le_max_right _ _) (le_max_left _ _))
    have hys : y.length ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
    have hjs : j ≤ s := le_trans (le_max_right _ _) (le_max_right _ _)
    set k : ℕ := j * 2 ^ (s - t) with hk
    have hpowsplit : (2 : ℚ) ^ s = 2 ^ (s - t) * 2 ^ t := by
      rw [← pow_add]
      congr 1
      omega
    have hrat : ((k : ℕ) : ℚ) / 2 ^ s = d := by
      have h1 : ((2 : ℚ) ^ (s - t)) ≠ 0 := by positivity
      have h2 : ((2 : ℚ) ^ t) ≠ 0 := by positivity
      rw [hk, hd, hpowsplit]
      push_cast
      field_simp
    have hfound : lscFound enum s (cantorPrefix w s) k = true := by
      refine lscFound_of (i := i) (y := y) his ?_ ?_
      · rw [hrat]; exact hy
      · rw [← hyp]; exact cantorPrefix_mono w hys
    have hkbound : k < s * 2 ^ s + 1 := by
      have h1 : (2 : ℕ) ^ (s - t) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : k ≤ s * 2 ^ s := by
        calc k = j * 2 ^ (s - t) := hk
          _ ≤ s * 2 ^ s := Nat.mul_le_mul hjs h1
      omega
    have hle : k ≤ lscApprox enum s (cantorPrefix w s) := by
      have hmax := lscLe_bMax
        (fun k' => if lscFound enum s (cantorPrefix w s) k' then k' else 0) hkbound
      simp only [hfound, if_true] at hmax
      exact hmax
    have hchain : ENNReal.ofReal ((d : ℝ)) ≤
        ⨆ s, dyadicValue (lscApprox enum s (cantorPrefix w s)) s := by
      calc ENNReal.ofReal ((d : ℝ)) = dyadicValue k s := by
            rw [lscDyadicValue_eq_ofReal]
            exact congrArg (fun r : ℚ => ENNReal.ofReal (r : ℝ)) hrat.symm
        _ ≤ dyadicValue (lscApprox enum s (cantorPrefix w s)) s := lscDyadicValue_mono _ hle
        _ ≤ _ := le_iSup (fun n => dyadicValue (lscApprox enum n (cantorPrefix w n)) n) s
    have hqd' : ENNReal.ofReal ((q : ℝ)) < ENNReal.ofReal ((d : ℝ)) := by
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hq0)).2 ?_
      exact_mod_cast hqd
    exact absurd (lt_of_lt_of_le (lt_trans hq1 hqd') hchain) (lt_irrefl _)

/-- A function enumerated by its rational superlevel sets is the pointwise supremum of the
dyadic approximations built from that enumeration. -/
lemma lscISup_approx_eq
    (hspec : ∀ q : ℚ, {w | (q : ℝ) < 0 ∨ ENNReal.ofReal (q : ℝ) < f w} =
      ⋃ i, (enum q i).elim ∅ cantorCylinder)
    (w : CantorSeq) :
    f w = ⨆ s, dyadicValue (lscApprox enum s (cantorPrefix w s)) s :=
  le_antisymm (lscLe_iSup_approx hspec w) (iSup_le fun s => lscApprox_le hspec w s)

end Kolmogorov
