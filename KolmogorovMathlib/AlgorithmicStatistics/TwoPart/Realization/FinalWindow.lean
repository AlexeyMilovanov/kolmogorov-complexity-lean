import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Part01
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.TemporalBadSets

/-!
# The final window and its decoder input

The model that realizes a curve is the temporal window at the end of the run, and it is named
by the version number.  `finalWindowInput` packs the parameters the decoder reads — `n`, the
level `i`, the complexity `m`, the generator constant, the version and the curve code — with
the field readers `fwNatN`, `fwNatI`, `fwNatM`, `fwNatCGen`, `fwNatVersion`, `fwCurveCode` and
their round-trip lemmas.

`temporalWindow_contains_survivor` is the mathematical content: the stabilized window contains
the shared lex-least survivor.  `setComplexity_le_of_partrec_code` turns a partial-recursive
encoder into a set-complexity bound, and `greedyWindowFoldList`, `temporalRefreshCountList`
and `temporalWindowList` are the computable list mirrors whose agreement with the abstract
notions is proved in `Realization/Computability`.
-/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The stabilized temporal window contains the shared lex-least survivor. -/
theorem temporalWindow_contains_survivor (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (m c_gen kx i T : ℕ)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h
        m c_gen kx).length).Nonempty)
    (h_stable : ∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = temporalRefreshCount c_U
        n h m c_gen i T) :
    lexLeastSurvivor U n h m c_gen kx ∈ temporalWindow c_U n h m c_gen i T := by
  obtain ⟨t₀, _hstab, hmax0⟩ := exists_simultaneous_stable_countHalts c_U n
  set T_full := max T t₀ with hTfull
  have hmaxF : ∀ j < n, ∀ t', countHalts c_U j t' ≤ countHalts c_U j T_full := by
    intro j hj t'
    exact le_trans (hmax0 j hj t') (countHalts_mono c_U j (le_max_right T t₀))
  obtain ⟨L_rest, h_append⟩ :=
    temporalBadEnumList_append_of_le c_U n h m c_gen (le_max_left T t₀)
  have h_no_refresh :
      temporalRefreshCount c_U n h m c_gen i T_full = temporalRefreshCount c_U n h m c_gen i T
          :=
    h_stable T_full (le_max_left T t₀)
  have hmem := lexLeastSurvivor_mem_rem U n h m c_gen kx hrem
  have h_surv : ∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full,
      lexLeastSurvivor U n h m c_gen kx ∉ d := by
    intro d hd hxd
    have hsub :=
      temporalBadEnumList_subset_fullBadUnion U c_U hc_code n h m c_gen kx (T := T_full) hd
    exact (Finset.mem_sdiff.mp hmem).2 (hsub hxd)
  have h_min : ∀ y, y ∈ stringsOfLength n →
      (∀ d ∈ temporalBadEnumList c_U n h m c_gen T_full, y ∉ d) →
        Encodable.encode (lexLeastSurvivor U n h m c_gen kx) ≤ Encodable.encode y := by
    intro y hyG hy_avoid
    have hy_rem : y ∈ stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
        (badEnumList U n h m c_gen kx).length := by
      rw [Finset.mem_sdiff]
      refine ⟨hyG, fun hy_bad => ?_⟩
      have hcov := badUnion_subset_temporal_of_max U c_U hc_code n h m c_gen kx T_full hmaxF
          hy_bad
      rw [mem_badUnionUpTo_full] at hcov
      obtain ⟨d, hd, hyd⟩ := hcov
      exact hy_avoid d hd hyd
    exact lexLeastSurvivor_encode_le U n h m c_gen kx hrem hy_rem
  exact temporalWindow_contains_survivor_of_append_no_refresh c_U n h m c_gen i T T_full
    (lexLeastSurvivor U n h m c_gen kx) (Finset.mem_sdiff.mp hmem).1 L_rest h_append
    h_no_refresh h_surv h_min

/-- Set complexity from a partial-recursive code.
If a partrec `enc` maps a code `w` to the canonical uniform-set code of `A`,
then `setComplexity U A ≤ KPPlain U w + O(1)`. -/
theorem setComplexity_le_of_partrec_code (U : Map) (hU : IsOptimalPrefixConditional U)
    (enc : BitString →. BitString) (henc : Partrec enc) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (w : BitString),
      (codedUniformOn A hA).code ∈ enc w →
      setComplexity U A hA ≤ KPPlain U w + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU enc henc
  refine ⟨c, fun A hA w hw => ?_⟩
  unfold setComplexity
  exact hc w ((codedUniformOn A hA).code) hw

/-- Extract `n` from the decoder input tuple. -/
def fwNatN (s : BitString) : ℕ := decodeNatCode (decodeFirst s)

/-- Extract `i` from the decoder input tuple. -/
def fwNatI (s : BitString) : ℕ := decodeNatCode (decodeFirst (decodeSecond s))

/-- Extract `m` from the decoder input tuple. -/
def fwNatM (s : BitString) : ℕ := decodeNatCode (decodeFirst (decodeSecond (decodeSecond s)))

/-- Extract `c_gen` from the decoder input tuple. -/
def fwNatCGen (s : BitString) : ℕ :=
    decodeNatCode (decodeFirst (decodeSecond (decodeSecond (decodeSecond s))))

/-- Extract `version` from the decoder input tuple. -/
def fwNatVersion (s : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond (decodeSecond s)))))

/-- Extract `curve code` from the decoder input tuple. -/
def fwCurveCode (s : BitString) : BitString :=
    decodeSecond (decodeSecond (decodeSecond (decodeSecond (decodeSecond s))))

/-- Pack the parameters used by the final-window decoder. -/
def finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) : BitString :=
  pairCode (natCode n) (pairCode (natCode i) (pairCode (natCode m)
    (pairCode (natCode c_gen) (pairCode (Nat.bits version) curve))))

/-- The length parameter is read back from a final-window input. -/
@[simp] theorem fwNat_n_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNatN (finalWindowInput n i m c_gen version curve) = n := by
  simp [finalWindowInput, fwNatN, decodeFirst_pairCode, decodeNatCode_natCode]

/-- The level parameter is read back from a final-window input. -/
@[simp] theorem fwNat_i_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNatI (finalWindowInput n i m c_gen version curve) = i := by
  simp [finalWindowInput, fwNatI, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

/-- The complexity parameter is read back from a final-window input. -/
@[simp] theorem fwNat_m_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNatM (finalWindowInput n i m c_gen version curve) = m := by
  simp [finalWindowInput, fwNatM, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

/-- The slack constant is read back from a final-window input. -/
@[simp] theorem fwNat_c_gen_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNatCGen (finalWindowInput n i m c_gen version curve) = c_gen := by
  simp [finalWindowInput, fwNatCGen, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

/-- The version number is read back from a final-window input. -/
@[simp] theorem fwNat_version_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwNatVersion (finalWindowInput n i m c_gen version curve) = version := by
  simp [finalWindowInput, fwNatVersion, decodeFirst_pairCode, decodeSecond_pairCode,
    bitsToNat_bits]

/-- The curve code is read back from a final-window input. -/
@[simp] theorem fwCurveCode_finalWindowInput (n i m c_gen version : ℕ) (curve : BitString) :
    fwCurveCode (finalWindowInput n i m c_gen version curve) = curve := by
  simp [finalWindowInput, fwCurveCode, decodeSecond_pairCode]

/-- Named decoder shape: rfind the first time `P s t` holds, then emit the canonical
uniform code of the held window `W s t` (or diverge if empty).  Naming this (rather than
inlining the `dite`) lets `finalWindowFn` be *definitionally* `codedWindowDecoder _ _`, so
matching `finalWindowFn` against the skeleton lemma is a delta step on `codedWindowDecoder`
and never exposes the heavy `temporalWindow` `Decidable`-nonempty instance to `whnf`. -/
noncomputable def codedWindowDecoder {α : Type} [Primcodable α]
    (P : α → ℕ → Bool) (W : α → ℕ → Finset BitString) : α →. BitString := fun s
        =>
  (Nat.rfind (fun t => Part.some (P s t))).bind
    (fun t => if hne : (W s t).Nonempty then Part.some (codedUniformOn (W s t) hne).code
      else Part.none)

/-- The machine-model decoder for the held temporal window: it waits for the first stage whose
refresh count equals the requested version and emits the canonical uniform code of the window
held at that stage. -/
noncomputable def finalWindowFn (c : Nat.Partrec.Code) : BitString →. BitString :=
  codedWindowDecoder
    (fun s t => decide (temporalRefreshCount c (fwNatN s) (decodeCurve (fwCurveCode s))
      (fwNatM s) (fwNatCGen s) (fwNatI s) t = fwNatVersion s))
    (fun s t => temporalWindow c (fwNatN s) (decodeCurve (fwCurveCode s))
      (fwNatM s) (fwNatCGen s) (fwNatI s) t)

/-- The bad sets up to a time depend on the curve only through which values exceed
the threshold and what those values are. -/
theorem badSetsUpToTime_congr (c : Nat.Partrec.Code) (n m c_gen t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    badSetsUpToTime c n h1 m c_gen t = badSetsUpToTime c n h2 m c_gen t := by
  unfold badSetsUpToTime
  congr 1
  have filter_eq : (List.range n).filter (fun j => m + logSlack c_gen n < h1 j) =
      (List.range n).filter (fun j => m + logSlack c_gen n < h2 j) := by
    have h_congr : ∀ l : List ℕ, (∀ j ∈ l, j < n) → l.filter (fun j => m + logSlack
        c_gen n < h1 j)
        = l.filter (fun j => m + logSlack c_gen n < h2 j) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro hl
        have hl_a : a < n := hl a (by simp)
        have hl_l : ∀ j ∈ l, j < n := fun j hj => hl j (by simp [hj])
        have ih_l := ih hl_l
        simp only [List.filter_cons]
        have heq_a : (m + logSlack c_gen n < h1 a) ↔ (m + logSlack c_gen n < h2 a) := heq a
            hl_a
        have dec_eq : decide (m + logSlack c_gen n < h1 a) = decide (m + logSlack c_gen n < h2
            a) := decide_eq_decide.mpr heq_a
        rw [dec_eq, ih_l]
    apply h_congr
    intro j hj
    exact List.mem_range.mp hj
  rw [filter_eq]
  apply List.flatMap_congr_loc
  intro j hj
  rw [List.mem_filter, List.mem_range] at hj
  have hj_h2 : m + logSlack c_gen n < h2 j := of_decide_eq_true hj.2
  have hj_h1 : m + logSlack c_gen n < h1 j := (heq j hj.1).mpr hj_h2
  have h_eq : h1 j = h2 j := heq2 j hj.1 hj_h1
  rw [h_eq]

/-- The new bad sets at a time depend on the curve only through the same data. -/
theorem newBadSetsAtTime_congr (c : Nat.Partrec.Code) (n m c_gen t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    newBadSetsAtTime c n h1 m c_gen t = newBadSetsAtTime c n h2 m c_gen t := by
  unfold newBadSetsAtTime
  cases t
  · exact badSetsUpToTime_congr c n m c_gen 0 heq heq2
  · simp only
    rw [badSetsUpToTime_congr c n m c_gen _ heq heq2, badSetsUpToTime_congr c n m c_gen _ heq
        heq2]

/-- The temporal bad-set enumeration depends on the curve only through the same
data. -/
theorem temporalBadEnumList_congr (c : Nat.Partrec.Code) (n m c_gen t_max : ℕ) {h1 h2 : ℕ
    → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j) :
    temporalBadEnumList c n h1 m c_gen t_max = temporalBadEnumList c n h2 m c_gen t_max := by
  unfold temporalBadEnumList
  apply List.flatMap_congr_loc
  intro t _
  exact newBadSetsAtTime_congr c n m c_gen t heq heq2

/-- Congruence for temporal refresh count over the curve function. -/
theorem temporalRefreshCount_congr (c : Nat.Partrec.Code) (n m c_gen i t : ℕ) {h1 h2 : ℕ →
    ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j)
    (heqi : h1 i = h2 i) :
    temporalRefreshCount c n h1 m c_gen i t = temporalRefreshCount c n h2 m c_gen i t := by
  unfold temporalRefreshCount
  rw [heqi]
  rw [temporalBadEnumList_congr c n m c_gen t heq heq2]

/-- Congruence for temporal window over the curve function. -/
theorem temporalWindow_congr (c : Nat.Partrec.Code) (n m c_gen i t : ℕ) {h1 h2 : ℕ → ℕ}
    (heq : ∀ j < n, m + logSlack c_gen n < h1 j ↔ m + logSlack c_gen n < h2 j)
    (heq2 : ∀ j < n, m + logSlack c_gen n < h1 j → h1 j = h2 j)
    (heqi : h1 i = h2 i) :
    temporalWindow c n h1 m c_gen i t = temporalWindow c n h2 m c_gen i t := by
  unfold temporalWindow
  rw [heqi]
  rw [temporalBadEnumList_congr c n m c_gen t heq heq2]

/-- Computable list mirror of `badSetsUpToTime`. -/
def badSetsUpToTimeList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t
    : ℕ) :
    List (List BitString) :=
  List.dedup (((List.range n).filter (fun j => decide (m + logSlack c_gen n < decodeCurve curve
      j))).flatMap (fun j =>
    snapshotDescList c j (decodeCurve curve j - (m + logSlack c_gen n)) t))

/-- Computable list mirror of `newBadSetsAtTime`. -/
def newBadSetsAtTimeList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ) (t
    : ℕ) :
    List (List BitString) :=
  let all_at_t := badSetsUpToTimeList c n curve m c_gen t
  match t with
  | 0 => all_at_t
  | t_minus_1 + 1 =>
    let all_at_t_minus_1 := badSetsUpToTimeList c n curve m c_gen t_minus_1
    all_at_t.filter (fun S => ! (all_at_t_minus_1.elem S))

/-- Computable list mirror of `temporalBadEnumList`. -/
def temporalBadEnumListList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen : ℕ)
    (t_max : ℕ) : List (List BitString) :=
  (List.range (t_max + 1)).flatMap (fun t => newBadSetsAtTimeList c n curve m c_gen t)

/-- Computable list mirror of `GreedyWindow.step`. -/
def greedyWindowStepList (G : List BitString) (size : ℕ) (st : List BitString × List
    BitString × ℕ)
    (d : List BitString) : List BitString × List BitString × ℕ :=
  let deleted := List.dedup (st.1 ++ (d.filter (fun x => G.elem x)))
  if st.2.1.all (fun x => deleted.elem x) then
    let new_window_full := G.filter (fun x => ! (deleted.elem x))
    (deleted, new_window_full.take size, st.2.2 + 1)
  else
    (deleted, st.2.1, st.2.2)

/-- Computable list mirror of `GreedyWindow.fold`. -/
def greedyWindowFoldList (G : List BitString) (size : ℕ) (L : List (List BitString)) : List
    BitString × List BitString × ℕ :=
  L.foldl (greedyWindowStepList G size) ([], G.take size, 0)

/-- Computable list mirror of `temporalRefreshCount`. -/
def temporalRefreshCountList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t :
    ℕ) :
    ℕ :=
  let G := canonicalFinsetList (allStrings n).toFinset
  greedyWindowFoldList G (2 ^ (decodeCurve curve i)) (temporalBadEnumListList c n curve m c_gen
      t) |>.2.2

/-- Computable list mirror of `temporalWindow`. -/
def temporalWindowList (c : Nat.Partrec.Code) (n : ℕ) (curve : BitString) (m c_gen i t : ℕ)
    : List
    BitString :=
  let G := canonicalFinsetList (allStrings n).toFinset
  greedyWindowFoldList G (2 ^ (decodeCurve curve i)) (temporalBadEnumListList c n curve m c_gen
      t) |>.2.1

/-
List↔Finset correspondence chain.  These discharge the `*_eq` lemmas that bridge
the computable list mirrors (`badSetsUpToTimeList`, `greedyWindowFoldList`, …)
with their abstract `Finset`-valued counterparts.
-/

/-- Injective image commutes with `List.dedup`. -/
theorem dedup_map_injOn {α β} [DecidableEq α] [DecidableEq β] (f : α → β) (l : List α)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    List.map f (List.dedup l) = List.dedup (List.map f l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hft : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y :=
      fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])
    have iht := ih hft
    have hmemA : a ∈ List.dedup t ↔ a ∈ t := mem_List.dedup t a
    have hmemB : f a ∈ List.dedup (List.map f t) ↔ f a ∈ List.map f t :=
      mem_List.dedup (List.map f t) (f a)
    change List.map f (if a ∈ List.dedup t then List.dedup t else a :: List.dedup t)
      = (if f a ∈ List.dedup (List.map f t) then List.dedup (List.map f t)
          else f a :: List.dedup (List.map f t))
    by_cases h : a ∈ t
    · rw [if_pos (hmemA.mpr h), if_pos (hmemB.mpr (List.mem_map_of_mem h)), iht]
    · have hfa : f a ∉ List.dedup (List.map f t) := by
        intro hd
        rw [hmemB, List.mem_map] at hd
        obtain ⟨x, hx, hfx⟩ := hd
        exact h (hf x (by simp [hx]) a (by simp) hfx ▸ hx)
      rw [if_neg (fun hd => h (hmemA.mp hd)), if_neg hfa, List.map_cons, iht]

/-- Every description list produced by `snapshotDescList` is in canonical form,
i.e. it is a fixed point of `canonicalFinsetList ∘ List.toFinset`.  This is the
injectivity input needed to swap `List.dedup` past `List.toFinset`. -/
theorem snapshotDescList_canonical (c : Nat.Partrec.Code) (i j t : ℕ) :
    ∀ x ∈ snapshotDescList c i j t, canonicalFinsetList x.toFinset = x := by
  intro x hx
  unfold snapshotDescList at hx
  rw [List.mem_filter] at hx
  rw [List.mem_map] at hx
  obtain ⟨⟨w, _, rfl⟩, _⟩ := hx
  rw [canonicalFinsetList_toFinset]

end Kolmogorov
