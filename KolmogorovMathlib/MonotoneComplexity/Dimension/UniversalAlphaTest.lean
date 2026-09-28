/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.Dimension.AlphaTrim
import KolmogorovMathlib.AlgorithmicRandomness.Enumeration

/-!
# The universal effective `α`-test (SUV §5.8, p. 173, proof of Theorem 117)

> "if `α` is a rational number (or even a computable real), we can enumerate all
> effectively `α`-null sets (or, better, the algorithms that serve these sets) by
> enumerating all algorithms and changing them when too large intervals are
> generated." (p. 173)

Chapter 3's numbering of algorithms (`AlgorithmicRandomness/Enumeration.lean`)
enumerates each candidate cover *with repetitions*: the value of the index `i`
reappears at every simulation budget `t` beyond the one at which the simulation
converges.  For `α = 1` Chapter 3 removes the repetitions by disjointifying and
appealing to additivity of the measure (`Disjointify.tsum_measure_disjEnum`),
which is unavailable for `α ≠ 1`.  This module removes them directly: `firstCand`
emits the value of the index `i` only at the *first* budget at which it appears
(`Code.evaln_mono` makes convergence monotone in the budget), so the map "index
of the emission" is injective on the emissions and the `α`-weight of `firstCand`
never exceeds the `α`-weight of the enumeration the code serves, while the union
is unchanged.

`exists_code_candEnum_faithful` is the index-faithful reading of Chapter 3's
`exists_code_candEnum`; its proof is Chapter 3's, with the two directions kept
apart instead of being merged into an equality of unions.
-/

namespace Kolmogorov

open MeasureTheory Encodable Nat.Partrec
open scoped ENNReal

/-! ## The index-faithful reading of the numbering of algorithms -/

/-- Chapter 3's `exists_code_candEnum`, keeping the index: the code `c` produces
exactly the values of `h (n+1)`, the emission at `s` carrying the value of the
index `(unpair s).1`, and every value of `h (n+1)` being emitted at some budget. -/
theorem exists_code_candEnum_faithful {h : ℕ → ℕ → Option BitString} (hh : Computable₂ h) :
    ∃ c : ℕ,
      (∀ (n s : ℕ) (u : BitString), candEnum (Nat.pair c n) s = some u →
        h (n + 1) (Nat.unpair s).1 = some u) ∧
      (∀ (n i : ℕ) (u : BitString), h (n + 1) i = some u →
        ∃ t : ℕ, candEnum (Nat.pair c n) (Nat.pair i t) = some u) := by
  set G : ℕ → ℕ := fun x => Encodable.encode (h ((Nat.unpair x).1 + 1) (Nat.unpair x).2) with hG
  have hGcomp : Computable G := by
    have h1 : Computable (fun x : ℕ => h ((Nat.unpair x).1 + 1) (Nat.unpair x).2) :=
      hh.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp
    exact Primrec.encode.to_comp.comp h1
  have hpart : Nat.Partrec (fun x => Part.some (G x)) :=
    Partrec.nat_iff.mp (Computable.partrec hGcomp)
  obtain ⟨c₀, hc₀⟩ := Code.exists_code.mp hpart
  have hofNat : ∀ n : ℕ,
      Denumerable.ofNat Code (Nat.unpair (Nat.pair (Encodable.encode c₀) n)).1 = c₀ := by
    intro n
    rw [Nat.unpair_pair]
    exact Denumerable.ofNat_encode c₀
  have hlevel : ∀ n : ℕ, (Nat.unpair (Nat.pair (Encodable.encode c₀) n)).2 = n := by
    intro n
    rw [Nat.unpair_pair]
  refine ⟨Encodable.encode c₀, ?_, ?_⟩
  · intro n s u hcs0
    have hcs := hcs0
    unfold candEnum at hcs
    rw [hofNat n, hlevel n] at hcs
    cases hev : Code.evaln (Nat.unpair s).2 c₀ (Nat.pair n (Nat.unpair s).1) with
    | none => rw [hev] at hcs; simp at hcs
    | some v =>
      rw [hev] at hcs
      simp only [Option.bind_some] at hcs
      have hmem : v ∈ Code.eval c₀ (Nat.pair n (Nat.unpair s).1) :=
        Code.evaln_sound (by rw [hev]; rfl)
      rw [hc₀] at hmem
      have hveq : v = G (Nat.pair n (Nat.unpair s).1) := by simpa [eq_comm] using hmem
      rw [hveq, hG] at hcs
      simpa only [Nat.unpair_pair, Encodable.encodek₂, Option.getD_some] using hcs
  · intro n i u hhi
    have hmem : Encodable.encode (some u) ∈ Code.eval c₀ (Nat.pair n i) := by
      rw [hc₀]
      simp [hG, hhi]
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp hmem
    refine ⟨t, ?_⟩
    have ht' : Code.evaln t c₀ (Nat.pair n i) = some (Encodable.encode (some u)) := by
      simpa [eq_comm] using ht
    unfold candEnum
    rw [hofNat n, hlevel n]
    simp only [Nat.unpair_pair, ht', Option.bind_some, Encodable.encodek₂, Option.getD_some]

/-! ## Removing the repetitions -/

/-- The emission of `candEnum m` at the index `i = (unpair s).1` is monotone in
the simulation budget `t = (unpair s).2`. -/
lemma candEnum_mono (m i : ℕ) {t t' : ℕ} (htt' : t ≤ t') {u : BitString}
    (h : candEnum m (Nat.pair i t) = some u) : candEnum m (Nat.pair i t') = some u := by
  unfold candEnum at h ⊢
  simp only [Nat.unpair_pair] at h ⊢
  cases hev : Code.evaln t (Denumerable.ofNat Code (Nat.unpair m).1)
      (Nat.pair (Nat.unpair m).2 i) with
  | none => rw [hev] at h; simp at h
  | some v =>
    have hev' : Code.evaln t' (Denumerable.ofNat Code (Nat.unpair m).1)
        (Nat.pair (Nat.unpair m).2 i) = some v :=
      Code.evaln_mono htt' (by rw [hev]; rfl)
    rw [hev']
    rw [hev] at h
    exact h

/-- `candSeen m i t` records whether the code has already emitted the value of
the index `i` within the budget `t`. -/
def candSeen (m i t : ℕ) : Bool :=
  ((candEnum m (Nat.pair i t)).map fun _ => true).getD false

/-- If the enumeration of candidate strings produces a value at index `⟨i, t⟩` then the seen-flag at
`(i, t)` is set. -/
lemma candSeen_eq_true {m i t : ℕ} {u : BitString} (h : candEnum m (Nat.pair i t) = some u) :
    candSeen m i t = true := by
  unfold candSeen
  rw [h]
  rfl

/-- If the enumeration of candidate strings produces nothing at index `⟨i, t⟩` then the seen-flag at
`(i, t)` is clear. -/
lemma candSeen_eq_false {m i t : ℕ} (h : candEnum m (Nat.pair i t) = (none : Option BitString)) :
    candSeen m i t = false := by
  unfold candSeen
  rw [h]
  rfl

/-- The seen-flag of the candidate enumeration is computable in the machine index, the row and the
stage. -/
lemma computable_candSeen : Computable (fun p : (ℕ × ℕ) × ℕ => candSeen p.1.1 p.1.2 p.2) := by
  have hpair : Computable (fun p : (ℕ × ℕ) × ℕ => Nat.pair p.1.2 p.2) :=
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp
  have hcand : Computable (fun p : (ℕ × ℕ) × ℕ => candEnum p.1.1 (Nat.pair p.1.2 p.2)) :=
    computable₂_candEnum.comp (Computable.fst.comp Computable.fst) hpair
  exact Computable.option_getD (Computable.option_map hcand (Computable.const true))
    (Computable.const false)

/-- The test "this is the first budget at which the index `(unpair s).1` is
emitted". -/
def firstCondition (m s : ℕ) : Bool :=
  decide ((Nat.unpair s).2 = 0) || !candSeen m (Nat.unpair s).1 ((Nat.unpair s).2 - 1)

/-- The test selecting the first stage at which a candidate appears is computable. -/
lemma computable₂_firstCondition : Computable₂ firstCondition := by
  have hzero : Computable (fun p : ℕ × ℕ => decide ((Nat.unpair p.2).2 = 0)) :=
    ((PrimrecRel.comp Primrec.eq (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.const 0)).decide).to_comp
  have harg : Computable (fun p : ℕ × ℕ => ((p.1, (Nat.unpair p.2).1), (Nat.unpair p.2).2 - 1)) :=
    Computable.pair
      (Computable.pair Computable.fst
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp))
      ((Primrec.nat_sub.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.const 1)).to_comp)
  have hseen : Computable (fun p : ℕ × ℕ =>
      candSeen p.1 (Nat.unpair p.2).1 ((Nat.unpair p.2).2 - 1)) :=
    (computable_candSeen.comp harg).of_eq fun _ => rfl
  have hnot : Computable (fun p : ℕ × ℕ =>
      !candSeen p.1 (Nat.unpair p.2).1 ((Nat.unpair p.2).2 - 1)) :=
    (((Primrec.dom_bool (fun b : Bool => !b)).to_comp).comp hseen).of_eq fun _ => rfl
  exact (Computable₂.comp ((Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp)
    hzero hnot).of_eq fun _ => rfl

/-- The multiplicity-faithful version of `candEnum`: the value of the index
`(unpair s).1` is emitted only at the *first* budget at which it appears. -/
def firstCand (m s : ℕ) : Option BitString :=
  bif firstCondition m s then candEnum m s else none

/-- The candidate enumeration restricted to first appearances is computable. -/
lemma computable₂_firstCand : Computable₂ firstCand :=
  Computable.cond computable₂_firstCondition computable₂_candEnum (Computable.const none)

/-- Whenever the first-appearance enumeration outputs a string, the underlying candidate enumeration
outputs the same string. -/
lemma firstCand_eq_candEnum_of_ne_none {m s : ℕ} {u : BitString}
    (h : firstCand m s = some u) : candEnum m s = some u := by
  unfold firstCand at h
  cases hb : firstCondition m s with
  | false => rw [hb] at h; simp at h
  | true => rwa [hb, cond_true] at h

/-- On the emissions of `firstCand`, the index `(unpair s).1` determines `s`. -/
lemma firstCand_injOn_index {m s s' : ℕ} {u u' : BitString}
    (hs : firstCand m s = some u) (hs' : firstCand m s' = some u')
    (hidx : (Nat.unpair s).1 = (Nat.unpair s').1) : s = s' := by
  have key : ∀ a b : ℕ, ∀ v v' : BitString, firstCand m a = some v → firstCand m b = some v' →
      (Nat.unpair a).1 = (Nat.unpair b).1 → (Nat.unpair a).2 ≤ (Nat.unpair b).2 →
      (Nat.unpair a).2 = (Nat.unpair b).2 := by
    intro a b v v' ha hb hidx' hle
    by_contra hne
    have hlt : (Nat.unpair a).2 < (Nat.unpair b).2 := lt_of_le_of_ne hle hne
    have hpos : (Nat.unpair b).2 ≠ 0 := by omega
    have hbase : candEnum m (Nat.pair (Nat.unpair b).1 (Nat.unpair a).2) = some v := by
      rw [← hidx', Nat.pair_unpair]
      exact firstCand_eq_candEnum_of_ne_none ha
    have hprev : candEnum m (Nat.pair (Nat.unpair b).1 ((Nat.unpair b).2 - 1)) = some v :=
      candEnum_mono m (Nat.unpair b).1 (by omega) hbase
    have hseen : candSeen m (Nat.unpair b).1 ((Nat.unpair b).2 - 1) = true :=
      candSeen_eq_true hprev
    have hz : decide ((Nat.unpair b).2 = 0) = false := by simp [hpos]
    have hcond : firstCondition m b = false := by
      unfold firstCondition
      rw [hseen, hz]
      simp
    unfold firstCand at hb
    rw [hcond] at hb
    simp at hb
  rcases le_total (Nat.unpair s).2 (Nat.unpair s').2 with hle | hle
  · have h2 := key s s' u u' hs hs' hidx hle
    calc s = Nat.pair (Nat.unpair s).1 (Nat.unpair s).2 := (Nat.pair_unpair s).symm
      _ = Nat.pair (Nat.unpair s').1 (Nat.unpair s').2 := by rw [hidx, h2]
      _ = s' := Nat.pair_unpair s'
  · have h2 := key s' s u' u hs' hs hidx.symm hle
    calc s = Nat.pair (Nat.unpair s).1 (Nat.unpair s).2 := (Nat.pair_unpair s).symm
      _ = Nat.pair (Nat.unpair s').1 (Nat.unpair s').2 := by rw [hidx, h2.symm]
      _ = s' := Nat.pair_unpair s'

/-- Removing the repetitions does not change the covered set. -/
lemma iUnion_firstCand (m : ℕ) :
    (⋃ s, (firstCand m s).elim ∅ cantorCylinder) = ⋃ s, (candEnum m s).elim ∅ cantorCylinder := by
  classical
  refine Set.Subset.antisymm (Set.iUnion_subset fun s => ?_) (Set.iUnion_subset fun s => ?_)
  · cases hf : firstCand m s with
    | none => simp
    | some u =>
      refine Set.subset_iUnion_of_subset s ?_
      rw [firstCand_eq_candEnum_of_ne_none hf]
  · cases hc : candEnum m s with
    | none => simp
    | some u =>
      have hex : ∃ t : ℕ, (candEnum m (Nat.pair (Nat.unpair s).1 t)).isSome = true := by
        refine ⟨(Nat.unpair s).2, ?_⟩
        rw [Nat.pair_unpair, hc]
        rfl
      have hsome : (candEnum m (Nat.pair (Nat.unpair s).1 (Nat.find hex))).isSome = true :=
        Nat.find_spec hex
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
      have hle : Nat.find hex ≤ (Nat.unpair s).2 :=
        Nat.find_le (by rw [Nat.pair_unpair, hc]; rfl)
      have hvu : v = u := by
        have h' := candEnum_mono m (Nat.unpair s).1 hle hv
        rw [Nat.pair_unpair, hc] at h'
        exact (Option.some_inj.mp h').symm
      have hfirst : firstCand m (Nat.pair (Nat.unpair s).1 (Nat.find hex)) = some v := by
        unfold firstCand
        have hcond : firstCondition m (Nat.pair (Nat.unpair s).1 (Nat.find hex)) = true := by
          unfold firstCondition
          rw [Nat.unpair_pair]
          rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hz
          · simp [hz]
          · have hmin : candEnum m (Nat.pair (Nat.unpair s).1 (Nat.find hex - 1))
                = (none : Option BitString) := by
              by_contra hne
              obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
              exact Nat.find_min hex (m := Nat.find hex - 1) (by omega) (by rw [hw]; rfl)
            rw [candSeen_eq_false hmin]
            simp
        rw [hcond, cond_true]
        exact hv
      refine Set.subset_iUnion_of_subset (Nat.pair (Nat.unpair s).1 (Nat.find hex)) ?_
      rw [hfirst, hvu]

/-- The completeness half: every interval of the enumeration served by the code
is covered by `firstCand`. -/
lemma iUnion_subset_iUnion_firstCand {h : ℕ → ℕ → Option BitString} {c n : ℕ}
    (hcomplete : ∀ (i : ℕ) (u : BitString), h (n + 1) i = some u →
      ∃ t : ℕ, candEnum (Nat.pair c n) (Nat.pair i t) = some u) :
    (⋃ i, (h (n + 1) i).elim ∅ cantorCylinder)
      ⊆ ⋃ s, (firstCand (Nat.pair c n) s).elim ∅ cantorCylinder := by
  rw [iUnion_firstCand]
  refine Set.iUnion_subset fun i => ?_
  cases hi : h (n + 1) i with
  | none => simp
  | some u =>
    obtain ⟨t, ht⟩ := hcomplete i u hi
    refine Set.subset_iUnion_of_subset (Nat.pair i t) ?_
    rw [ht]

/-- The `α`-weight of `firstCand` never exceeds the `α`-weight of the
enumeration the code serves: the index of the emission is injective on the
emissions (`firstCand_injOn_index`), and by faithfulness the emitted interval is
the one that enumeration has at that index. -/
lemma tsum_firstCand_le (α : ℝ) {h : ℕ → ℕ → Option BitString} {c n : ℕ}
    (hfaith : ∀ (s : ℕ) (u : BitString), candEnum (Nat.pair c n) s = some u →
      h (n + 1) (Nat.unpair s).1 = some u) :
    (∑' s, (firstCand (Nat.pair c n) s).elim 0
        (fun x => uniformMeasure (cantorCylinder x) ^ α))
      ≤ ∑' i, (h (n + 1) i).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) := by
  classical
  set g : ℕ → ℝ≥0∞ :=
    fun i => (h (n + 1) i).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ α) with hgdef
  set f : ℕ → ℝ≥0∞ :=
    fun s => (firstCand (Nat.pair c n) s).elim 0
      (fun x => uniformMeasure (cantorCylinder x) ^ α) with hfdef
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  set F' := F.filter (fun s => (firstCand (Nat.pair c n) s).isSome = true) with hF'
  have hsub : F' ⊆ F := Finset.filter_subset _ _
  have hzero : ∀ s ∈ F, s ∉ F' → f s = 0 := by
    intro s hsF hsF'
    have hns : ¬ ((firstCand (Nat.pair c n) s).isSome = true) := fun hcon =>
      hsF' (Finset.mem_filter.2 ⟨hsF, hcon⟩)
    cases hfs : firstCand (Nat.pair c n) s with
    | none => simp [hfdef, hfs]
    | some u => exact absurd (by rw [hfs]; rfl) hns
  have hfg : ∀ s ∈ F', f s = g ((Nat.unpair s).1) := by
    intro s hs
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hs).2
    have hh := hfaith s u (firstCand_eq_candEnum_of_ne_none hu)
    simp [hfdef, hgdef, hu, hh]
  have hinj : ∀ s ∈ F', ∀ s' ∈ F', (Nat.unpair s).1 = (Nat.unpair s').1 → s = s' := by
    intro s hs s' hs' hidx
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hs).2
    obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hs').2
    exact firstCand_injOn_index hu hu' hidx
  calc ∑ s ∈ F, f s = ∑ s ∈ F', f s := (Finset.sum_subset hsub hzero).symm
    _ = ∑ s ∈ F', g ((Nat.unpair s).1) := Finset.sum_congr rfl hfg
    _ = ∑ i ∈ F'.image (fun s => (Nat.unpair s).1), g i := (Finset.sum_image hinj).symm
    _ ≤ ∑' i, g i := ENNReal.sum_le_tsum _

/-! ## The universal effective `α`-test -/

/-- The powers `2 ^ (-n)` decrease as `n` grows. -/
lemma inv_two_pow_antitone {n m : ℕ} (h : n ≤ m) :
    (2 : ℝ≥0∞)⁻¹ ^ m ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [show m = n + (m - n) from (Nat.add_sub_cancel' h).symm, pow_add]
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞)⁻¹ ^ (m - n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n * 1 := by
        gcongr
        exact inv_two_pow_le_one _
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := mul_one _

/-- The row `m = ⟨code of `ε`, code `c`⟩` of the universal test: the
multiplicity-faithful enumeration produced by the code `c` at the level
`den ε + c + 4`. -/
def uaRow (m : ℕ) : ℕ → Option BitString :=
  firstCand (Nat.pair (Nat.unpair m).2
    ((ratOfCode (Nat.unpair m).1).den + (Nat.unpair m).2 + 4))

/-- The `α`-trimming level of the row `m`, so that the budgets of the rows sum to
`2^{-den ε} ≤ ε`. -/
def uaLevel (m : ℕ) : ℕ := (ratOfCode (Nat.unpair m).1).den + (Nat.unpair m).2 + 1

/-- The row of the universal test, `α`-trimmed. -/
def uaEnum (α : ℚ) (m k : ℕ) : Option BitString :=
  trimEnum (uaRow m) (trimWeight (alphaApprox α) (uaRow m) (uaLevel m)) k

/-- The universal effective `α`-test: at accuracy `ε` the index `j = ⟨c, k⟩`
yields the `k`-th interval of the trimmed row of the code `c`. -/
def uaTest (α ε : ℚ) (j : ℕ) : Option BitString :=
  uaEnum α (Nat.pair (ratCode ε) (Nat.unpair j).1) (Nat.unpair j).2

/-- The level attached to the code of the pair `(ε, c)` is `ε.den + c + 1`. -/
@[simp] lemma uaLevel_pair (ε : ℚ) (c : ℕ) :
    uaLevel (Nat.pair (ratCode ε) c) = ε.den + c + 1 := by
  simp [uaLevel, ratOfCode_ratCode]

/-- The row attached to the code of the pair `(ε, c)` enumerates the first appearances of the
candidates of machine `⟨c, ε.den + c + 4⟩`. -/
@[simp] lemma uaRow_pair (ε : ℚ) (c : ℕ) :
    uaRow (Nat.pair (ratCode ε) c) = firstCand (Nat.pair c (ε.den + c + 4)) := by
  simp [uaRow, ratOfCode_ratCode]

/-- The level function of the universal `α`-test is computable. -/
lemma computable_uaLevel : Computable uaLevel := by
  have h1 : Computable (fun m : ℕ => (ratOfCode (Nat.unpair m).1).den) :=
    computable_ratDen.comp (computable_ratOfCode.comp (Primrec.fst.comp Primrec.unpair).to_comp)
  exact (Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp h1 (Primrec.snd.comp Primrec.unpair).to_comp)
    (Computable.const 1)).of_eq fun _ => rfl

/-- The row enumeration of the universal `α`-test is computable in the row index and the stage. -/
lemma computable₂_uaRow : Computable₂ uaRow := by
  have hden : Computable (fun p : ℕ × ℕ => (ratOfCode (Nat.unpair p.1).1).den) :=
    computable_ratDen.comp (computable_ratOfCode.comp
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to_comp))
  have hc : Computable (fun p : ℕ × ℕ => (Nat.unpair p.1).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hlev : Computable (fun p : ℕ × ℕ =>
      (ratOfCode (Nat.unpair p.1).1).den + (Nat.unpair p.1).2 + 4) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hden hc) (Computable.const 4)
  have hidx : Computable (fun p : ℕ × ℕ => Nat.pair (Nat.unpair p.1).2
      ((ratOfCode (Nat.unpair p.1).1).den + (Nat.unpair p.1).2 + 4)) :=
    Computable₂.comp Primrec₂.natPair.to_comp hc hlev
  exact (computable₂_firstCand.comp hidx Computable.snd).of_eq fun _ => rfl

/-- The enumeration underlying the universal `α`-test is computable. -/
lemma computable₂_uaEnum (α : ℚ) : Computable₂ (uaEnum α) :=
  computable_trimEnum computable₂_uaRow
    (computable_trimWeight (computable₂_alphaApprox α) computable₂_uaRow computable_uaLevel)

/-- The universal `α`-test is computable in its level and stage indices. -/
lemma computable₂_uaTest (α : ℚ) : Computable₂ (uaTest α) := by
  have hm : Computable (fun p : ℚ × ℕ => Nat.pair (ratCode p.1) (Nat.unpair p.2).1) :=
    Computable₂.comp Primrec₂.natPair.to_comp (computable_ratCode.comp Computable.fst)
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
  exact (((computable₂_uaEnum α).comp hm
    ((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)).of_eq fun _ => rfl)

/-- **SUV Theorem 117, the enumeration step (§5.8, p. 173)**, in the unfolded
form used by `Dimension/Basic.lean`. -/
theorem exists_universal_alphaTest_raw (α : ℚ) (hα : 0 < α) :
    ∃ I : ℚ → ℕ → Option BitString, Computable₂ I ∧
      (∀ ε : ℚ, 0 < ε →
        (∑' k, (I ε k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
          ≤ ENNReal.ofReal (ε : ℝ)) ∧
      (∀ B : Set CantorSeq,
        (∃ J : ℚ → ℕ → Option BitString, Computable₂ J ∧ ∀ δ : ℚ, 0 < δ →
          B ⊆ (⋃ k, (J δ k).elim ∅ cantorCylinder) ∧
            (∑' k, (J δ k).elim 0 (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
              < ENNReal.ofReal (δ : ℝ)) →
        ∀ ε : ℚ, 0 < ε → B ⊆ ⋃ k, (I ε k).elim ∅ cantorCylinder) := by
  refine ⟨uaTest α, computable₂_uaTest α, fun ε hε => ?_, ?_⟩
  · -- the total `α`-weight of the test at accuracy `ε`
    have hre : (∑' j, (uaTest α ε j).elim 0
          (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
        = ∑' p : ℕ × ℕ, (uaEnum α (Nat.pair (ratCode ε) p.1) p.2).elim 0
            (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)) := by
      rw [← Equiv.tsum_eq Nat.pairEquiv (fun j : ℕ => (uaTest α ε j).elim 0
        (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))]
      exact tsum_congr fun p => by simp [uaTest, Nat.pairEquiv, Function.uncurry]
    rw [hre, show (∑' p : ℕ × ℕ, (uaEnum α (Nat.pair (ratCode ε) p.1) p.2).elim 0
            (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
          = ∑' (c : ℕ) (k : ℕ), (uaEnum α (Nat.pair (ratCode ε) c) k).elim 0
              (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)) from
        ENNReal.tsum_prod (f := fun c k => (uaEnum α (Nat.pair (ratCode ε) c) k).elim 0
          (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))]
    calc (∑' (c : ℕ) (k : ℕ), (uaEnum α (Nat.pair (ratCode ε) c) k).elim 0
            (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
        ≤ ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (ε.den + c + 1) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          have h1 : (∑' k, (uaEnum α (Nat.pair (ratCode ε) c) k).elim 0
              (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
              ≤ (2 : ℝ≥0∞)⁻¹ ^ (uaLevel (Nat.pair (ratCode ε) c)) :=
            tsum_alphaTrim_le α hα (uaRow (Nat.pair (ratCode ε) c))
              (uaLevel (Nat.pair (ratCode ε) c))
          rwa [uaLevel_pair] at h1
      _ = (2 : ℝ≥0∞)⁻¹ ^ ε.den := tsum_inv_two_pow_shift ε.den
      _ ≤ ENNReal.ofReal (ε : ℝ) := by
          rw [← dyadicValue_one_eq_inv_two_pow']
          exact dyadicValue_den_le_rat hε
  · -- every effective `α`-null set is covered
    rintro B ⟨J, hJcomp, hJ⟩ ε hε
    set hB : ℕ → ℕ → Option BitString := fun m k => J ((2 : ℚ)⁻¹ ^ m) k with hBdef
    have hBcomp : Computable₂ hB :=
      hJcomp.comp (computable_pow_half.comp Computable.fst) Computable.snd
    obtain ⟨c, hfaith, hcomplete⟩ := exists_code_candEnum_faithful hBcomp
    set L : ℕ := ε.den + c + 5 with hLdef
    set N : ℕ := ε.den + c + 1 with hNdef
    have hlev : ε.den + c + 4 + 1 = L := by rw [hLdef]
    have hδpos : (0 : ℚ) < (2 : ℚ)⁻¹ ^ L := by positivity
    have hδR : ENNReal.ofReal (((2 : ℚ)⁻¹ ^ L : ℚ) : ℝ) = (2 : ℝ≥0∞)⁻¹ ^ L := by
      rw [ofReal_pow_half_eq_dyadicValue, dyadicValue_one_eq_inv_two_pow']
    -- the row is small, hence untouched by the trimming
    have hrowsmall : (∑' s, (firstCand (Nat.pair c (ε.den + c + 4)) s).elim 0
        (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ))) ≤ (2 : ℝ≥0∞)⁻¹ ^ (N + 3) := by
      have hbound := tsum_firstCand_le (α : ℝ) (h := hB) (c := c) (n := ε.den + c + 4)
        (fun s u hs => hfaith (ε.den + c + 4) s u hs)
      rw [hlev] at hbound
      refine hbound.trans ?_
      have := (hJ ((2 : ℚ)⁻¹ ^ L) hδpos).2
      rw [hδR] at this
      refine le_trans (le_of_lt this) (inv_two_pow_antitone ?_)
      omega
    have huntouched : ∀ k, uaEnum α (Nat.pair (ratCode ε) c) k
        = uaRow (Nat.pair (ratCode ε) c) k := by
      intro k
      have hsmall : (∑' j, (uaRow (Nat.pair (ratCode ε) c) j).elim 0
          (fun x => uniformMeasure (cantorCylinder x) ^ (α : ℝ)))
          ≤ (2 : ℝ≥0∞)⁻¹ ^ (uaLevel (Nat.pair (ratCode ε) c) + 3) := by
        rw [uaLevel_pair, uaRow_pair, ← hNdef]
        exact hrowsmall
      exact alphaTrim_eq_self α hα hsmall k
    -- the covering
    have hBsub : B ⊆ ⋃ i, (hB L i).elim ∅ cantorCylinder := by
      have := (hJ ((2 : ℚ)⁻¹ ^ L) hδpos).1
      simpa [hBdef] using this
    have hcov : B ⊆ ⋃ s, (firstCand (Nat.pair c (ε.den + c + 4)) s).elim ∅ cantorCylinder := by
      refine hBsub.trans ?_
      have := iUnion_subset_iUnion_firstCand (h := hB) (c := c) (n := ε.den + c + 4)
        (fun i u hu => hcomplete (ε.den + c + 4) i u (by rwa [hlev]))
      rwa [hlev] at this
    intro w hw
    obtain ⟨s, hwS⟩ := Set.mem_iUnion.1 (hcov hw)
    refine Set.mem_iUnion.2 ⟨Nat.pair c s, ?_⟩
    have : uaTest α ε (Nat.pair c s) = firstCand (Nat.pair c (ε.den + c + 4)) s := by
      rw [uaTest, Nat.unpair_pair, huntouched s, uaRow_pair]
    rw [this]
    exact hwS

end Kolmogorov
