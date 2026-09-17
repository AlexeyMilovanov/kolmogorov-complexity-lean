import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GreedyWindow
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization.Computability

/-! # Curve realization: every admissible `ProfileCurve` is realized up to logarithmic slack. -/
namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- Abstract decoder skeleton: for any computable step predicate `P` and any window
family `W` whose canonical list and nonemptiness test are computable, the map that
rfind-searches for the first time `P s t` holds and then emits the canonical uniform
code of the held window `W s t` (or diverges if empty) is partial recursive.  This is
the general shape of `finalWindowFn`, isolated so the partial-recursiveness proof does
not force `whnf` to unfold the heavy `temporalRefreshCount`/`temporalWindow` defs. -/
theorem partrec_codedWindow_decoder {α : Type} [Primcodable α]
    (P : α → ℕ → Bool) (W : α → ℕ → Finset BitString)
    (hP : Computable (fun x : α × ℕ => P x.1 x.2))
    (hWlist : Computable (fun x : α × ℕ => canonicalFinsetList (W x.1 x.2))) :
    Partrec (codedWindowDecoder P W) := by
  unfold codedWindowDecoder
  -- The nonemptiness guard is derived from the (computable) canonical list: a finset is
  -- nonempty iff its sorted list has positive length.  Deriving it here (rather than taking
  -- it as a hypothesis) keeps `decide (·.Nonempty)` out of the caller's unification problem.
  have hlt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨inst, hpl⟩ := (Primrec.nat_lt : PrimrecRel (· < ·))
    exact (hpl.of_eq (fun p => by congr 1)).to_comp
  have hpos : Computable (fun n : ℕ => decide (0 < n)) :=
    hlt.comp (Computable.pair (Computable.const 0) Computable.id)
  have hWne : Computable (fun x : α × ℕ => decide (W x.1 x.2).Nonempty) := by
    refine Computable.of_eq (hpos.comp (Computable.list_length.comp hWlist)) (fun x => ?_)
    simp [canonicalFinsetList, Finset.length_sort, Finset.card_pos]
  apply Partrec.bind
  · exact Partrec.rfind (Computable₂.partrec₂ hP)
  · refine Partrec.of_eq (Partrec.cond hWne
      ((canonicalUniformCodeOfList_computable.comp hWlist).partrec) Partrec.none) ?_
    intro x
    by_cases h : (W x.1 x.2).Nonempty
    · have hd : decide (W x.1 x.2).Nonempty = true := by simp [h]
      simp only [hd, cond_true, dif_pos h, PFun.coe_val]
      rw [canonicalUniformCodeOfList_canonicalFinsetList _ h]
    · have hd : decide (W x.1 x.2).Nonempty = false := by simp [h]
      simp only [hd, cond_false, dif_neg h]

/- G3: The decoder is partial recursive.

The genuine content is fully discharged by the reusable, proved skeleton
`partrec_codedWindow_decoder` together with the proved computable primitives
`finalWindowFn_refreshCount_computable`, `finalWindowFn_version_computable`, and
`finalWindowFn_window_computable`.  `finalWindowFn c` is now *definitionally*
`codedWindowDecoder P W` with
`P s t = decide (temporalRefreshCount c (fwNatN s) … t = fwNatVersion s)` and
`W s t = temporalWindow c (fwNatN s) … t`, so it matches the skeleton by a delta step
on `codedWindowDecoder`.

Historical note.  The earlier formulation inlined the `rfind`/`dite` shape directly into
`finalWindowFn`, and matching it against the skeleton drove `isDefEq` to `whnf`-reduce the
`decide (· = ·)` / `Decidable (·.Nonempty)` guards, unfolding the heavy `GreedyWindow.fold`
bodies of `temporalRefreshCount`/`temporalWindow` and timing out.  Two changes remove that
obstacle: (i) naming the decoder shape (`codedWindowDecoder`) so the caller unifies at the
named application rather than the raw guards, and (ii) `seal`-ing the two heavy defs for the
duration of this proof so no residual `whnf` can unfold them. -/
/-- G3: The decoder `finalWindowFn c` is partial recursive. -/
theorem partrec_finalWindowFn (c : Nat.Partrec.Code) :
    Partrec (finalWindowFn c) := by
  -- The step predicate is `Nat`-equality of the (computable) refresh count and version.
  -- Building it with `Computable₂.comp` (rather than `comp` with a `Computable.pair`) keeps
  -- the guard in the clean `decide (· = ·)` shape, so unifying it against the skeleton's
  -- predicate is a beta step and never forces `whnf` to evaluate the heavy `decide`.
  have heq2 : Computable₂ (fun a b : ℕ => decide (a = b)) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst Primrec.snd)).to_comp
  have hP := heq2.comp (finalWindowFn_refreshCount_computable c)
      finalWindowFn_version_computable
  -- `finalWindowFn c` is *definitionally* `codedWindowDecoder P W`; unfolding exposes only the
  -- named decoder application, so matching the skeleton is structural.
  unfold finalWindowFn
  exact partrec_codedWindow_decoder _ _ hP (finalWindowFn_window_computable c)

/-- G4: The decoder correctness (evaluation matches the window). -/
theorem finalWindowFn_eval_decoded (c_U : Nat.Partrec.Code)
    (n m c_gen i T version : ℕ) (curve : BitString)
    (hne : (temporalWindow c_U n (decodeCurve curve) m c_gen i T).Nonempty)
    (hfind : Nat.rfind (fun t => Part.some
      (decide (temporalRefreshCount c_U n (decodeCurve curve) m c_gen i t = version))) =
          Part.some T) :
    (codedUniformOn (temporalWindow c_U n (decodeCurve curve) m c_gen i T) hne).code ∈
      finalWindowFn c_U (finalWindowInput n i m c_gen version curve) := by
  unfold finalWindowFn codedWindowDecoder
  simp only [fwNat_n_finalWindowInput, fwCurveCode_finalWindowInput,
    fwNat_m_finalWindowInput, fwNat_c_gen_finalWindowInput, fwNat_i_finalWindowInput,
    fwNat_version_finalWindowInput]
  rw [hfind]
  simp only [Part.bind_some]
  simp [hne]

/-- Coding a uniform distribution respects equality of its nonempty supporting finset. -/
lemma codedUniformOn_congr {W1 W2 : Finset BitString} (hW : W1 = W2) (h1 : W1.Nonempty)
    (h2 : W2.Nonempty) :
    (codedUniformOn W1 h1).code = (codedUniformOn W2 h2).code := by
  cases hW
  rfl

/-- If `T` is the first stage at which the temporal refresh counter reaches `version`, the final
window function on the corresponding input outputs the code of the uniform distribution on the
temporal window at stage `T`. -/
theorem finalWindowFn_eval (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U)
    (c n kx m c_gen i T version : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h)
    (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h
        m c_gen kx).length).Nonempty)
    (_hT : temporalRefreshCount c_U n h m c_gen i T = version)
    (hfind : Nat.rfind (fun t => Part.some
      (decide (temporalRefreshCount c_U n h m c_gen i t = version))) = Part.some T) :
    (codedUniformOn (temporalWindow c_U n h m c_gen i T) (temporalWindow_nonempty U c_U hc_code
        n h m c_gen kx i T hrem)).code ∈
      finalWindowFn c_U (finalWindowInput n i m c_gen version hc.code) := by
  have h_decode : decodeCurve hc.code = h := funext hc.curveDecodes
  have hfind' : Nat.rfind
      (fun t => Part.some (decide (temporalRefreshCount c_U n (decodeCurve hc.code) m c_gen i t
          = version)))
      = Part.some T := by
    have hR : (fun t => Part.some (decide (temporalRefreshCount c_U n (decodeCurve hc.code) m
        c_gen i t = version))) =
        (fun t => Part.some (decide (temporalRefreshCount c_U n h m c_gen i t = version))) := by
      rw [h_decode]
    rwa [hR]
  have hne : (temporalWindow c_U n (decodeCurve hc.code) m c_gen i T).Nonempty := by
    have hW : temporalWindow c_U n (decodeCurve hc.code) m c_gen i T = temporalWindow c_U n h m
        c_gen i T := by rw [h_decode]
    rw [hW]
    exact temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem
  have heval := finalWindowFn_eval_decoded c_U n m c_gen i T version hc.code hne hfind'
  have heq : (codedUniformOn (temporalWindow c_U n (decodeCurve hc.code) m c_gen i T) hne).code =
        (codedUniformOn (temporalWindow c_U n h m c_gen i T) (temporalWindow_nonempty U c_U
            hc_code n h m c_gen kx i T hrem)).code := by
    apply codedUniformOn_congr
    rw [h_decode]
  rwa [heq] at heval

/-- Appending further deletions can only increase the number of window refreshes. -/
theorem GreedyWindow_fold_count_mono {α : Type} [DecidableEq α] (G : Finset α)
    (first : Finset α → Finset α)
    (L : List (Finset α)) (st : Finset α × Finset α × ℕ) (L_suffix : List (Finset α)) :
    (L.foldl (GreedyWindow.step G first) st).2.2 ≤
        ((L ++ L_suffix).foldl (GreedyWindow.step G first) st).2.2 := by
  rw [List.foldl_append]
  generalize (L.foldl (GreedyWindow.step G first) st) = st'
  induction L_suffix generalizing st' with
  | nil => rfl
  | cons hd tl ih =>
    exact (GreedyWindow.step_count_mono G first st' hd).trans (ih (GreedyWindow.step G first st'
        hd))

/-- The temporal enumeration of bad sets grows only by appending, so an earlier stage is a prefix of
a later one. -/
theorem temporalBadEnumList_prefix (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen
    t1 t2 : ℕ)
    (ht : t1 ≤ t2) :
    ∃ L_suffix, temporalBadEnumList c n h m c_gen t2 = temporalBadEnumList c n h m c_gen t1 ++
        L_suffix := by
  unfold temporalBadEnumList
  have h_range : List.range (t2 + 1) = List.range (t1 + 1) ++ (List.range (t2 + 1)).drop (t1 +
      1) :=
      by
    have h1 := List.take_append_drop (t1 + 1) (List.range (t2 + 1))
    have h2 : List.take (t1 + 1) (List.range (t2 + 1)) = List.range (t1 + 1) := by
      rw [List.take_range]
      exact congr_arg List.range (Nat.min_eq_left (Nat.succ_le_succ ht))
    rw [h2] at h1
    exact h1.symm
  rw [h_range, List.flatMap_append]
  exact ⟨_, rfl⟩

/-- The temporal refresh counter is nondecreasing in the stage. -/
theorem temporalRefreshCount_mono (c : Nat.Partrec.Code) (n : ℕ) (h : ℕ → ℕ) (m c_gen i
    t1 t2 : ℕ)
    (ht : t1 ≤ t2) :
    temporalRefreshCount c n h m c_gen i t1 ≤ temporalRefreshCount c n h m c_gen i t2 := by
  unfold temporalRefreshCount
  obtain ⟨L_suffix, h_suffix⟩ := temporalBadEnumList_prefix c n h m c_gen t1 t2 ht
  rw [h_suffix]
  exact GreedyWindow_fold_count_mono _ _ _ _ L_suffix

/-- There is a partial recursive encoder and a code for `U` such that every temporal window of
the bad enumeration is held by a version number bounded by `2 ^ (i + 1) * (n + 1) + 1`, and the
window is decodable from that version. -/
theorem exists_temporalWindowDecoder (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ enc : BitString →. BitString, Partrec enc ∧
      ∃ (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U),
      ∀ (c n kx m c_gen : ℕ) (h : ℕ → ℕ) (hc : ProfileCurve U c n kx m h) (i : ℕ)
        (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
            (badEnumList U n h m c_gen kx).length).Nonempty),
        ∃ version : ℕ, version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1 ∧
        ∃ T : ℕ, (temporalRefreshCount c_U n h m c_gen i T = version) ∧
        (∀ t ≥ T, temporalRefreshCount c_U n h m c_gen i t = version) ∧
        (codedUniformOn
            (temporalWindow c_U n h m c_gen i T)
            (temporalWindow_nonempty U c_U hc_code n h m c_gen kx i T hrem)).code
          ∈ enc (finalWindowInput n i m c_gen version hc.code) := by
  obtain ⟨c_U, hc_raw⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hc_code : IsCodeFor c_U U := by
    simpa only [IsCodeFor] using hc_raw
  refine ⟨finalWindowFn c_U, partrec_finalWindowFn c_U, c_U, hc_code, ?_⟩
  intro c n kx m c_gen h hc i hrem
  obtain ⟨T, version, hbound, hT, hstable⟩ := temporalRefreshCount_stabilizes U c_U hc_code
      c n kx m c_gen i h hc hrem
  have hrfind : ∃ t, temporalRefreshCount c_U n h m c_gen i t = version := ⟨T, hT⟩
  set T_find := Nat.find hrfind
  have hT_find : temporalRefreshCount c_U n h m c_gen i T_find = version := Nat.find_spec hrfind
  have hfind : Nat.rfind
      ((fun t : ℕ =>
        Part.some
          (decide (temporalRefreshCount c_U n h m c_gen i t = version))) :
        ℕ →. Bool) = Part.some T_find := by
    have h_mem : T_find ∈ Nat.rfind
        ((fun t : ℕ =>
          Part.some
            (decide (temporalRefreshCount c_U n h m c_gen i t = version))) :
          ℕ →. Bool) := by
      rw [@Nat.mem_rfind
        ((fun t : ℕ =>
          Part.some
            (decide (temporalRefreshCount c_U n h m c_gen i t = version))) :
          ℕ →. Bool)
        T_find]
      constructor
      · simp [hT_find]
      · intro m hm
        simp [Nat.find_min hrfind hm]
    exact Part.eq_some_iff.mpr h_mem
  have hstable_find : ∀ t ≥ T_find, temporalRefreshCount c_U n h m c_gen i t = version := by
    intro t ht
    by_cases h_le_T : t ≤ T
    · have h1 : version ≤ temporalRefreshCount c_U n h m c_gen i t := by
        rw [←hT_find]
        exact temporalRefreshCount_mono _ _ _ _ _ _ _ _ ht
      have h2 : temporalRefreshCount c_U n h m c_gen i t ≤ version := by
        rw [←hT]
        exact temporalRefreshCount_mono _ _ _ _ _ _ _ _ h_le_T
      exact le_antisymm h2 h1
    · exact hstable t (le_of_not_ge h_le_T)
  refine ⟨version, hbound, T_find, hT_find, hstable_find, ?_⟩
  exact finalWindowFn_eval U c_U hc_code c n kx m c_gen i T_find version h hc hrem hT_find hfind

/- **Gate B5-core (the Vereshchagin–Vitányi machine-model coding gate).**

This is the set-complexity content of the VV coding step: the final greedy window
— a set of size `≤ 2^{h i}` — has set-complexity at most `i + m + O(log n)`.

Proof idea (VV): the final window is `firstElements (survivors r) (2^{h i})` where
`r` is the version number reached by the running-window process.  That window is
recoverable by a computable, dove-tailed simulation of the greedy process from the
inputs `(n, i, curve code of h, version number r)`; feeding this computable decoder
to `setComplexity_le_of_computable_code` gives
`setComplexity ≤ KPPlain(n) + KPPlain(i) + KPPlain(curve) + KPPlain(r) + O(1)`.
Here `KPPlain(curve) ≤ m` (`hc.curveComplexity`), `KPPlain(n), KPPlain(i) = O(log n)`
(with `i ≤ kx ≤ n` on the positive region), and the *version number is bounded* by
`r ≤ 2^{i+1} + n·2^{i+1}` (via the already-proved `bucket1_bound` and
`bucket2_bound_of_curve`), so `KPPlain(r) = O(log r) = i + O(log n)`.  Summing gives
the `i + m + O(log n)` bound.

The `O(log n)` coding overhead is an absolute constant `c_code` coming from the fixed
computable decoder.  It depends only on `U`, not on the construction slack `c_gen`
used to build `badEnumList`.  The caller can therefore choose
`c_gen ≥ max 3 c_code`; the counting estimate continues to hold for this larger
parameter by `sum_badSetsUnion_card_lt_of_le`.

The hypotheses match the VV proof: `hc : ProfileCurve` supplies both the
curve budget `m` and the diagonal descent that bounds the version count; `hrem`
supplies nonemptiness of the window.  The implementation uses the concrete temporal
simulation. -/
lemma ENat_add_five_mul (A B C D E F c_pair : ENat) :
  A + (B + (C + (D + (E + F + c_pair) + c_pair) + c_pair) + c_pair) + c_pair =
  A + B + C + D + E + F + (c_pair + c_pair + c_pair + c_pair + c_pair) := by
  ac_rfl

/-- Five copies of `c` added in `ENat` equal the cast of `5 * c`. -/
lemma ENat_five_mul (c : ℕ) : (c + c + c + c + c : ENat) = (5 * c : ℕ) := by
  rw [←ENat.natCast_add, ←ENat.natCast_add, ←ENat.natCast_add, ←ENat.natCast_add]
  congr 1
  omega

/-- A small arithmetic consequence of the VV refresh-count bound: if the version
number is at most `(n + 1) * 2^(i+1) + 1`, then its binary representation has
`i + O(log n)` bits.  The extra `+2` absorbs the final `+1` and the strict
`Nat.size` bound. -/
theorem version_bits_length_le (n i version : ℕ)
    (hversion : version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1) :
    (Nat.bits version).length ≤ i + (Nat.bits (n + 1)).length + 2 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hpow_pos : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow (i + 1) 2 (by norm_num)
  have hnlt : n + 1 < 2 ^ (Nat.bits (n + 1)).length := by
    simpa [Nat.size_eq_bits_len] using Nat.lt_size_self (n + 1)
  have hversion' : version ≤ (n + 1) * 2 ^ (i + 1) + 1 := by
    nlinarith
  have hlt1 : (n + 1) * 2 ^ (i + 1) + 1 <
      (2 ^ (Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) := by
    nlinarith
  have hlt2 : (2 ^ (Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) ≤
      2 ^ ((Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) := by
    gcongr
    calc 2 ^ (Nat.bits (n + 1)).length + 1
        ≤ 2 ^ (Nat.bits (n + 1)).length + 2 ^ (Nat.bits (n + 1)).length := by
            gcongr
            exact Nat.one_le_pow (Nat.bits (n + 1)).length 2 (by norm_num)
      _ = 2 ^ ((Nat.bits (n + 1)).length + 1) := by
            rw [pow_succ]
            ring
  have hpow_eq : 2 ^ ((Nat.bits (n + 1)).length + 1) * 2 ^ (i + 1) =
      2 ^ (i + (Nat.bits (n + 1)).length + 2) := by
    rw [← pow_add]
    congr 1
    omega
  exact lt_of_le_of_lt hversion' (lt_of_lt_of_le hlt1 (by simpa [hpow_eq] using hlt2))

/-- **Set-complexity of the `m`-free first block.**  The window
`firstElements (stringsOfLength n) (2^s)` is computable from `(n, s)` alone: by
`firstElements_eq_take` it is the `toFinset` of the first `2^s` entries of the canonical
enumeration of the length-`n` cube, and that enumeration is itself computable from `n`
(`canonicalFinsetList_toFinset_primrec` composed with `allStrings`).  Hence, feeding the
computable encoder
`w ↦ canonicalUniformCodeOfList ((canonicalFinsetList (stringsOfLength …)).take (2^…))`
to `setComplexity_le_of_computable_code`, its set-complexity is
`≤ KPPlain (pairCode (natCode n) (natCode s)) + O(1) ≤ 2·log n + 2·log s + O(1)`.  When
`s ≤ n` this collapses to a single `logSlack c_fe n`.  This is the `m`-independent coding
step for the `m > n` regime of the final greedy window, where `badEnumList` is empty and the
window collapses to this block. -/
theorem firstElementsCube_setComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_fe : ℕ, 3 ≤ c_fe ∧ ∀ (n s : ℕ)
      (hne : (firstElements (stringsOfLength n) (2 ^ s)).Nonempty),
      s ≤ n →
      setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
        ≤ ((logSlack c_fe n : ℕ) : ENat) := by
  -- The computable `(n, s)`-encoder producing the code of the first block.
  have henc : Computable (fun w : BitString => canonicalUniformCodeOfList
      ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
        (2 ^ decodeNatCode (decodeSecond w)))) := by
    refine canonicalUniformCodeOfList_computable.comp (Primrec.to_comp ?_)
    refine KraftChaitin.take_primrec.comp ?_ ?_
    · exact canonicalFinsetList_toFinset_primrec.comp
        (allStrings_primrec.comp (decodeNatCode_primrec.comp decodeFirst_primrec))
    · exact natPow_primrec.comp (Primrec.const 2)
        (decodeNatCode_primrec.comp decodeSecond_primrec)
  obtain ⟨c, hc⟩ := setComplexity_le_of_partrec_code U hU _ henc.partrec
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨cNat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  refine ⟨4 + 2 * cNat + c_pair + c + 3, by omega, ?_⟩
  intro n s hne hs
  -- Code identity: the encoder on `pairCode (natCode n) (natCode s)` yields the window code.
  have hid : (fun w : BitString => canonicalUniformCodeOfList
      ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
        (2 ^ decodeNatCode (decodeSecond w)))) (pairCode (natCode n) (natCode s))
      = (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code := by
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]
    set L := (canonicalFinsetList (stringsOfLength n)).take (2 ^ s) with hL
    have hnd : L.Nodup := (canonicalFinsetList_nodup _).sublist (List.take_sublist _ _)
    have hpw : L.Pairwise bitStringLE :=
      (Finset.pairwise_sort _ bitStringLE).sublist (List.take_sublist _ _)
    have hLtf : L.toFinset = firstElements (stringsOfLength n) (2 ^ s) :=
      (firstElements_eq_take _ _).symm
    have hcanon : canonicalFinsetList L.toFinset = L := canonicalFinsetList_of_sorted L hnd hpw
    have hne' : L.toFinset.Nonempty := by rw [hLtf]; exact hne
    calc canonicalUniformCodeOfList L
        = canonicalUniformCodeOfList (canonicalFinsetList L.toFinset) := by rw [hcanon]
      _ = (codedUniformOn L.toFinset hne').code :=
            canonicalUniformCodeOfList_canonicalFinsetList _ _
      _ = (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code :=
            codedUniformOn_code_congr _ _ hLtf
  -- Complexity bound and arithmetic.
  have hmem : (codedUniformOn (firstElements (stringsOfLength n) (2 ^ s)) hne).code
      ∈ (fun w : BitString => Part.some (canonicalUniformCodeOfList
          ((canonicalFinsetList (stringsOfLength (decodeNatCode (decodeFirst w)))).take
            (2 ^ decodeNatCode (decodeSecond w))))) (pairCode (natCode n) (natCode s)) :=
    Part.mem_some_iff.mpr hid.symm
  have hstep := hc (firstElements (stringsOfLength n) (2 ^ s)) hne
    (pairCode (natCode n) (natCode s)) hmem
  have hpairbd : KPPlain U (pairCode (natCode n) (natCode s))
      ≤ KPPlain U (natCode n) + KPPlain U (natCode s) + (c_pair : ENat) :=
    hc_pair (natCode n) (natCode s)
  have hsize : (Nat.bits s).length ≤ (Nat.bits n).length := by
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size hs
  have hbound : setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
      ≤ ((4 * (Nat.bits n).length + 2 * cNat + c_pair + c : ℕ) : ENat) := by
    calc setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
        ≤ KPPlain U (pairCode (natCode n) (natCode s)) + (c : ENat) := hstep
      _ ≤ (KPPlain U (natCode n) + KPPlain U (natCode s) + (c_pair : ENat)) + (c : ENat) := by
            gcongr
      _ ≤ ((2 * (Nat.bits n).length + cNat : ℕ) + (2 * (Nat.bits s).length + cNat : ℕ)
            + (c_pair : ENat)) + (c : ENat) := by
            gcongr <;> [exact hc_nat n; exact hc_nat s]
      _ ≤ ((4 * (Nat.bits n).length + 2 * cNat + c_pair + c : ℕ) : ENat) := by
            push_cast
            have : (Nat.bits s).length ≤ (Nat.bits n).length := hsize
            have hb : (0 : ℕ) ≤ (Nat.bits n).length := Nat.zero_le _
            calc ((2 * (Nat.bits n).length + cNat : ℕ) : ENat)
                  + ((2 * (Nat.bits s).length + cNat : ℕ) : ENat) + (c_pair : ENat) + (c :
                      ENat)
                ≤ ((2 * (Nat.bits n).length + cNat : ℕ) : ENat)
                  + ((2 * (Nat.bits n).length + cNat : ℕ) : ENat) + (c_pair : ENat) + (c :
                      ENat) :=
                      by
                    gcongr
              _ = ((4 * (Nat.bits n).length + 2 * cNat + c_pair + c : ℕ) : ENat) := by
                    push_cast; ring
  refine hbound.trans ?_
  have : 4 * (Nat.bits n).length + 2 * cNat + c_pair + c
      ≤ logSlack (4 + 2 * cNat + c_pair + c + 3) n := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  exact_mod_cast this

/-
The decoder input `finalWindowInput` contains `natCode m`, whose plain-complexity
cost is logarithmic in `m`.  The hypothesis `m ≤ n` lets `logSlack c_work n`
absorb this cost.  In the main theorem this lemma is used only in the `m ≤ n`
branch; the `m > n` branch uses the `m`-free first-elements decoder.
-/
/-- Bounding the plain Kolmogorov complexity of `finalWindowInput` by the sum of plain
complexities of its individual components plus five pairing constants. -/
private lemma finalWindowInput_kp_bound (U : Map) (c_pair : ℕ)
    (hc_pair : ∀ x y, KPPair U x y ≤ KPPlain U x + KPPlain U y + (c_pair : ENat))
    (n i m c_work version : ℕ) (curve_code : BitString) :
    KPPlain U (finalWindowInput n i m c_work version curve_code) ≤
      KPPlain U (natCode n) + KPPlain U (natCode i) + KPPlain U (natCode m) +
        KPPlain U (natCode c_work) + KPPlain U (Nat.bits version) + KPPlain U curve_code +
        (5 * c_pair : ℕ) := by
  have h_pair1 := hc_pair (natCode n) (pairCode (natCode i) (pairCode (natCode m) (pairCode
      (natCode c_work) (pairCode (Nat.bits version) curve_code))))
  have h_pair2 := hc_pair (natCode i) (pairCode (natCode m) (pairCode (natCode c_work) (pairCode
      (Nat.bits version) curve_code)))
  have h_pair3 := hc_pair (natCode m) (pairCode (natCode c_work) (pairCode (Nat.bits version)
      curve_code))
  have h_pair4 := hc_pair (natCode c_work) (pairCode (Nat.bits version) curve_code)
  have h_pair5 := hc_pair (Nat.bits version) curve_code
  calc
    KPPlain U (finalWindowInput n i m c_work version curve_code)
      ≤ KPPlain U (natCode n) +
          KPPlain U (pairCode (natCode i) (pairCode (natCode m) (pairCode (natCode c_work)
            (pairCode (Nat.bits version) curve_code)))) + (c_pair : ENat) := h_pair1
    _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) +
          KPPlain U (pairCode (natCode m) (pairCode (natCode c_work)
            (pairCode (Nat.bits version) curve_code))) + (c_pair : ENat)) + (c_pair : ENat) := by
        gcongr; exact h_pair2
    _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) +
          KPPlain U (pairCode (natCode c_work) (pairCode (Nat.bits version) curve_code)) +
            (c_pair : ENat)) + (c_pair : ENat)) + (c_pair : ENat) := by
        gcongr; exact h_pair3
    _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) +
          (KPPlain U (natCode c_work) + KPPlain U (pairCode (Nat.bits version) curve_code) +
            (c_pair : ENat)) + (c_pair : ENat)) + (c_pair : ENat)) + (c_pair : ENat) := by
        gcongr; exact h_pair4
    _ ≤ KPPlain U (natCode n) + (KPPlain U (natCode i) + (KPPlain U (natCode m) +
          (KPPlain U (natCode c_work) + (KPPlain U (Nat.bits version) + KPPlain U curve_code +
            (c_pair : ENat)) + (c_pair : ENat)) + (c_pair : ENat)) + (c_pair : ENat)) +
            (c_pair : ENat) := by
        gcongr; exact h_pair5
    _ = KPPlain U (natCode n) + KPPlain U (natCode i) + KPPlain U (natCode m) +
        KPPlain U (natCode c_work) + KPPlain U (Nat.bits version) + KPPlain U curve_code +
        (5 * c_pair : ℕ) := by rw [ENat_add_five_mul, ENat_five_mul]

/-- Bounding the plain complexity of `Nat.bits version` in terms of version bit length. -/
private lemma version_kp_bound (U : Map) (c_len n i version : ℕ)
    (hc_len : ∀ w : BitString, KPPlain U w ≤ w.length + 2 * (Nat.bits w.length).length + c_len)
    (h_version_bound : version ≤ 2 ^ (i + 1) + n * 2 ^ (i + 1) + 1) :
    (KPPlain U (Nat.bits version) : ENat) ≤
      (i + (Nat.bits (n + 1)).length + 2 + 2 * (Nat.bits (Nat.bits version).length).length +
        c_len : ℕ) := by
  have _h_version_bits := version_bits_length_le n i version h_version_bound
  calc (KPPlain U (Nat.bits version) : ENat)
    _ ≤ ((Nat.bits version).length + 2 * (Nat.bits (Nat.bits version).length).length + c_len
        : ℕ) := hc_len _
    _ ≤
        (i + (Nat.bits (n + 1)).length + 2 + 2 * (Nat.bits (Nat.bits version).length).length +
            c_len : ℕ)
        := by gcongr

/-- The temporal final window has complexity at most `i + m + O(log n)`, uniformly in
the profile curve and construction parameters. -/
theorem temporalWindow_setComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ _c_code c_work : ℕ, 3 ≤ c_work ∧
    (∀ (n s : ℕ) (hne : (firstElements (stringsOfLength n) (2 ^ s)).Nonempty),
        s ≤ n → setComplexity U (firstElements (stringsOfLength n) (2 ^ s)) hne
          ≤ ((logSlack c_work n : ℕ) : ENat)) ∧
    ∀ (c n kx m : ℕ) (h : ℕ → ℕ) (_hc : ProfileCurve U c n kx m h) (i : ℕ)
      (_hi : i ≤ n) (_hmn : m ≤ n)
      (hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx)
        (badEnumList U n h m c_work kx).length).Nonempty),
      ∃ (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U U) (T : ℕ),
        (∀ t ≥ T, temporalRefreshCount c_U n h m c_work i t = temporalRefreshCount c_U n h m
            c_work i T) ∧
        setComplexity U (temporalWindow c_U n h m c_work i T)
          (temporalWindow_nonempty U c_U hc_code n h m c_work kx i T hrem)
        ≤ ((i + m + logSlack c_work n : ℕ) : ENat) := by
  obtain ⟨enc, hpartrec, c_U, hc_code, h_enc⟩ := exists_temporalWindowDecoder U hU
  obtain ⟨c_sim, hc_map⟩ := setComplexity_le_of_partrec_code U hU enc hpartrec
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨cNat, hc_nat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_fe, _hc_fe3, hc_fe⟩ := firstElementsCube_setComplexity_le U hU
  -- `c_work` must be large enough to absorb the *self-encoding* cost of `c_work` itself:
  -- the decoder input `finalWindowInput` contains `natCode c_work`, costing `≈ 2·log c_work`
  -- bits, and this must fit inside `logSlack c_work n` even when `n` is small (`B = 0, 1`).
  -- Taking `c_work = base + 2·size base + 300` guarantees `2·size c_work ≤ 2·size base +
  -- O(1)`,
  -- which the `+300` slack covers.
  let base := 5 * c_pair + 4 * cNat + c_len + c_sim + c_fe
  let c_work := base + 2 * Nat.size base + 300
  use base + 10, c_work
  refine ⟨by unfold c_work; omega, ?_, ?_⟩
  · -- The `m`-free first-block bound, transported to `c_work` via monotonicity of `logSlack`.
    intro n' s hne hsn
    refine (hc_fe n' s hne hsn).trans ?_
    have hle : c_fe ≤ c_work := by unfold c_work base; omega
    have hmono : logSlack c_fe n' ≤ logSlack c_work n' := by
      unfold logSlack; nlinarith [Nat.zero_le ((Nat.bits n').length), hle]
    exact_mod_cast hmono
  intro c n kx m h hc i hi hmn hrem
  use c_U, hc_code
  obtain ⟨version, h_version_bound, T, hT, hstable, h_enc_eval⟩ :=
    h_enc c n kx m c_work h hc i hrem
  use T
  have hstable' : ∀ t ≥ T, temporalRefreshCount c_U n h m c_work i t = temporalRefreshCount
      c_U n h
      m c_work i T := by
    intro t ht
    rw [hstable t ht, hT]
  refine ⟨hstable', ?_⟩
  have h_comp := hc_map _ (temporalWindow_nonempty U c_U hc_code n h m c_work kx i T hrem) _
      h_enc_eval
  -- Now we bound the complexity.
  have h_tuple_bound := finalWindowInput_kp_bound U c_pair hc_pair n i m c_work version hc.code
  -- Convert the version bound into a binary-length bound.
  have h_version_bits := version_bits_length_le n i version h_version_bound
  have h_len_version := version_kp_bound U c_len n i version hc_len h_version_bound
  have h_m : KPPlain U hc.code ≤ m := hc.curveComplexity
  have h_n : KPPlain U (natCode n) ≤ 2 * (Nat.bits n).length + cNat := hc_nat n
  have h_i : KPPlain U (natCode i) ≤ 2 * (Nat.bits i).length + cNat := hc_nat i
  have h_m_code : KPPlain U (natCode m) ≤ 2 * (Nat.bits m).length + cNat := hc_nat m
  have h_c_work : KPPlain U (natCode c_work) ≤ 2 * (Nat.bits c_work).length + cNat := hc_nat
      c_work
  -- Final absorption: under `hmn : m ≤ n` every non-`i`, non-`m` term is `O(log n)`, and the
  -- self-referential `natCode c_work` cost `2·log c_work` is covered by the `+300` slack in
  -- `c_work`.  The bit-length arithmetic is packaged in the `have`s below.
  have h_2size : ∀ k : ℕ, 2 * Nat.size k ≤ k + 6 := by
    intro k
    by_cases hk : k < 16;
    · interval_cases k <;> decide;
    · have := Nat.size_le.mp ( show Nat.size k ≤ k / 2 + 3 from ?_ );
      · have := Nat.size_le.mpr this; omega;
      · rw [ Nat.size_le ];
        rw [ ← Nat.mod_add_div k 2 ] ; have := Nat.mod_lt k two_pos; interval_cases k % 2 <;>
            norm_num at hk ⊢;
        · exact Nat.recOn (k / 2) (by norm_num) fun n ihn => by
            norm_num [Nat.pow_succ'] at ihn ⊢
            linarith
        · norm_num [ Nat.add_div ];
          exact Nat.recOn (k / 2) (by norm_num) fun n ihn => by
            norm_num [Nat.pow_succ'] at ihn ⊢
            linarith
  simp +arith +decide only [Nat.cast_add, ge_iff_le, Nat.size_eq_bits_len] at *;
  have h_2size_c_work : 2 * Nat.size c_work ≤ 2 * Nat.size base + 20 := by
    have h_2size_c_work : Nat.size c_work ≤ Nat.size base + 10 := by
      rw [ Nat.size_le ];
      have h_2size_c_work : base < 2 ^ Nat.size base := Nat.lt_size_self base
      grind +locals;
    linarith;
  have h_2size_version : 2 * Nat.size (Nat.size version) ≤ 2 * Nat.size n + 4 := by
    have h_2size_version : Nat.size (Nat.size version) ≤ Nat.size (i + Nat.size n + 3) := by
      apply Nat.size_le_size;
      linarith [ show Nat.size ( n + 1 ) ≤ Nat.size n + 1 from Nat.size_le.mpr ( by
                  exact Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.lt_size_self _ ) ) (
                      pow_lt_pow_right₀ ( by decide ) ( Nat.lt_succ_self _ ) ) ) ];
    have h_2size_version : Nat.size (i + Nat.size n + 3) ≤ Nat.size n + 2 := by
      rw [ Nat.size_le ];
      have := Nat.lt_size_self n;
      by_cases hn : n < 16;
      · interval_cases n <;> interval_cases i <;> trivial;
      · grind +qlia;
    linarith;
  refine le_trans ( hc_map _ _ _ h_enc_eval ) ?_;
  refine le_trans ( add_le_add h_tuple_bound le_rfl ) ?_;
  unfold logSlack
  norm_cast
  simp +arith +decide only [KPPlain_eq_KP, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_add] at h_n h_i h_m_code h_c_work h_len_version h_m ⊢
  refine le_trans
    (add_le_add
      (add_le_add
        (add_le_add
          (add_le_add (add_le_add (add_le_add (add_le_add h_n h_i) h_m_code)
            h_c_work) h_len_version) h_m) le_rfl) le_rfl) ?_
  norm_cast
  have h_size_i_m : Nat.size i ≤ Nat.size n ∧ Nat.size m ≤ Nat.size n := by
    exact ⟨ Nat.size_le_size hi, Nat.size_le_size hmn ⟩;
  have h_size_succ : (n + 1).size ≤ n.size + 1 := by
    rw [ Nat.size_le ];
    exact Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt ( Nat.lt_size_self _ ) ) ( by norm_num [
        pow_succ' ] );
  rw [Nat.size_eq_bits_len]
  have h_base_part : c_sim + 5 * c_pair + 4 * cNat + c_len ≤ base := by
    dsimp only [base]
    omega
  have hc_work_eq : c_work = base + 2 * base.size + 300 := rfl
  have h_fixed :
      c_sim + 5 * c_pair + 4 * cNat + c_len + 2 * c_work.size + 7 ≤ c_work := by
    omega
  have hc_work_ge : 9 ≤ c_work := by
    omega
  have h_scaled : 9 * n.size ≤ c_work * n.size :=
    Nat.mul_le_mul_right n.size hc_work_ge
  omega

/- Gate B5: The final visited window is an `(i + m + O(log n), h i)`-description.
This is the machine-model coding step of Vereshchagin-Vitányi.  The window is coded
by its visited version number, bounded by `poly(n) * 2^i`, together with `n`, `i`,
and the curve.  A computable dovetailed simulation maps this bounded version number
back to the window.  The `ProfileCurve` hypothesis supplies the curve-description
budget through `hc.curveComplexity`. -/

/-- When the size parameter equals the string length `n`, the enumeration of bad sets is empty. -/
theorem badEnumList_nil_of_m_eq_n (U : Map) (n : ℕ) (h : ℕ → ℕ) (c_gen kx : ℕ)
    (h_top : h 0 ≤ n) (h_antitone : Antitone h) :
    badEnumList U n h n c_gen kx = [] := by
  unfold badEnumList
  have h_empty : (Finset.range n).filter (fun j => n + logSlack c_gen n < h j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    have h_le : h j ≤ n := by
      calc h j ≤ h 0 := h_antitone (Nat.zero_le j)
        _ ≤ n := h_top
    omega
  rw [h_empty]
  simp

/-- When the enumeration of bad sets is empty, so is its temporal version at every stage. -/
theorem temporalBadEnumList_eq_nil_of_m_eq_n (U : Map) (c_U : Nat.Partrec.Code)
    (hc_code : IsCodeFor c_U U)
    (n : ℕ) (h : ℕ → ℕ) (c_gen kx t : ℕ) (h_empty : badEnumList U n h n c_gen kx = [])
        :
    temporalBadEnumList c_U n h n c_gen t = [] := by
  have h_sub := temporalBadEnumList_sublist_badEnumList U c_U hc_code n h n c_gen kx t
  cases h_temp : temporalBadEnumList c_U n h n c_gen t with
  | nil => rfl
  | cons head tail =>
    have h_in : head ∈ temporalBadEnumList c_U n h n c_gen t := by rw [h_temp]; simp
    have h_bad := h_sub head h_in
    rw [h_empty] at h_bad
    contradiction

/-- With no bad sets to delete, the initial temporal window is the first `2 ^ h i` strings of length
`n`. -/
theorem temporalWindow_zero_m_eq_n (U : Map) (c_U : Nat.Partrec.Code) (hc_code : IsCodeFor c_U
    U)
    (n : ℕ) (h : ℕ → ℕ) (c_work kx i : ℕ) (h_empty : badEnumList U n h n c_work kx =
        []) :
    temporalWindow c_U n h n c_work i 0 = firstElements (stringsOfLength n) (2 ^ h i) := by
  unfold temporalWindow
  have h_temp := temporalBadEnumList_eq_nil_of_m_eq_n U c_U hc_code n h c_work kx 0 h_empty
  rw [h_temp]
  simp [GreedyWindow.fold]

/-- When the size parameter exceeds the string length `n`, the enumeration of bad sets is empty. -/
theorem badEnumList_nil_of_m_gt_n (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (h_top : h 0 ≤ n) (h_antitone : Antitone h) (hmn : n < m) :
    badEnumList U n h m c_gen kx = [] := by
  unfold badEnumList
  have h_empty : (Finset.range n).filter (fun j => m + logSlack c_gen n < h j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _
    have h_le : h j ≤ n := by
      calc h j ≤ h 0 := h_antitone (Nat.zero_le j)
        _ ≤ n := h_top
    omega
  rw [h_empty]
  simp

/-- The lexicographically least survivor lies in a set of complexity at most
`i + m + logSlack c_work n` and size at most `2 ^ h i`, for every level `i` of the curve. -/
theorem finalWindow_mem_coverableSet (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_work : ℕ, 3 ≤ c_work ∧
    ∀ (c n kx m : ℕ) (h : ℕ → ℕ) (_hc : ProfileCurve U c n kx m h) (i : ℕ)
      (_hi : i ≤ n)
      (_hrem : (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx)
        (badEnumList U n h m c_work kx).length).Nonempty),
      ∃ S, lexLeastSurvivor U n h m c_work kx ∈ S ∧
           S ∈ descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
  -- Use the temporal decoder code (`temporalWindow_setComplexity_le`) to bypass the static
  -- greedy
  -- window entirely. The coded temporal window maintains the required set complexity, and
  -- `temporalWindow_contains_survivor` ensures the realizing point is within the output.
  obtain ⟨c_code, c_work, hc_work, h_firstEl, h_temp⟩ := temporalWindow_setComplexity_le U
      hU
  refine ⟨c_work, hc_work, fun c n kx m h hc i hi hrem => ?_⟩
  by_cases hmn : m ≤ n
  · obtain ⟨c_U, hc_code_U, T, h_stable, h_comp⟩ := h_temp c n kx m h hc i hi hmn hrem
    have hne := temporalWindow_nonempty U c_U hc_code_U n h m c_work kx i T hrem
    have h_mem_S := temporalWindow_contains_survivor U c_U hc_code_U n h m c_work kx i T hrem
        h_stable
    have h_S_code : temporalWindow c_U n h m c_work i T ∈
        descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
      rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
      exact ⟨mem_descriptionsWithComplexityLe_of_complexity hne h_comp,
        temporalWindow_card_le c_U n h m c_work i T⟩
    exact ⟨temporalWindow c_U n h m c_work i T, h_mem_S, h_S_code⟩
  · push Not at hmn
    have h_badEnum_nil : badEnumList U n h m c_work kx = [] :=
      badEnumList_nil_of_m_gt_n U n h m c_work kx hc.top hc.antitone hmn
    have h_hi : h i ≤ n := le_trans (hc.antitone (Nat.zero_le i)) hc.top
    have heq : stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_work kx)
        (badEnumList U n h m c_work kx).length = stringsOfLength n := by
      rw [h_badEnum_nil]
      simp [badUnionUpTo]
    have hne2 : (firstElements (stringsOfLength n) (2 ^ h i)).Nonempty := by
      exact Finset.card_pos.mp ( by rw [ firstElements_card ] ; exact lt_min ( by norm_num ) (
          Finset.card_pos.mpr (by rwa [heq] at hrem) ) )
    have h_mem_S : lexLeastSurvivor U n h m c_work kx ∈ firstElements (stringsOfLength n) (2 ^
        h i)
        := by
      unfold lexLeastSurvivor
      simp only [heq]
      split_ifs with h_ne h_ne2
      · exact firstElements_mono_size (stringsOfLength n) Nat.one_le_two_pow
          (Finset.mem_toList.mp (List.head_mem h_ne2))
      · exfalso
        have h_eq_nil : (firstElements (stringsOfLength n) 1).toList = [] := by
          by_contra h_not_nil
          exact h_ne2 h_not_nil
        have h_empty : firstElements (stringsOfLength n) 1 = ∅ := Finset.toList_eq_nil.mp
            h_eq_nil
        have h_card := firstElements_card (stringsOfLength n) 1
        rw [h_empty] at h_card
        have h_pos : 0 < (stringsOfLength n).card := Finset.card_pos.mpr h_ne
        have h_min : min 1 (stringsOfLength n).card = 1 := min_eq_left h_pos
        rw [h_min] at h_card
        simp at h_card
      · exfalso
        exact h_ne (by rwa [heq] at hrem)
    have h_S_code : firstElements (stringsOfLength n) (2 ^ h i) ∈
        descriptionsWithComplexityLeAndSizeLe U (i + m + logSlack c_work n) (h i) := by
      rw [descriptionsWithComplexityLeAndSizeLe, Finset.mem_filter]
      have hcomp := h_firstEl n (h i) hne2 h_hi
      have hcomp2 : setComplexity U (firstElements (stringsOfLength n) (2 ^ h i)) hne2 ≤
          ((i + m + logSlack c_work n : ℕ) : ENat) := by
        refine hcomp.trans ?_
        exact_mod_cast Nat.le_add_left (logSlack c_work n) (i + m)
      exact ⟨mem_descriptionsWithComplexityLe_of_complexity hne2 hcomp2,
        by rw [firstElements_card]; exact min_le_left _ _⟩
    exact ⟨firstElements (stringsOfLength n) (2 ^ h i), h_mem_S, h_S_code⟩

/-
Auxiliary: the full running bad-union (deleting every set of the enumeration) equals
the level-indexed union of `badSetsUnion`.  `badEnumList` is the `toList` of the finset
`((range n).filter …).biUnion (fun j => descriptions j)`, and `badUnionUpTo … L.length`
folds `∪` over that whole list; flattening the two `biUnion`s gives the level union.
-/
theorem badUnionUpTo_full_eq (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ) :
    badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length =
      ((Finset.range n).filter (fun j => m + logSlack c_gen n < h j)).biUnion
        (fun j => badSetsUnion U n h m c_gen j) := by
  apply Finset.ext
  intro x
  rw [mem_badUnionUpTo_full]
  unfold badEnumList badSetsUnion
  simp only [Finset.mem_toList, Finset.mem_biUnion, id_eq]
  exact ⟨fun ⟨d, ⟨j, hj, hd_j⟩, hx⟩ => ⟨j, hj, d, hd_j, hx⟩,
    fun ⟨j, hj, d, hd_j, hx⟩ => ⟨d, ⟨j, hj, hd_j⟩, hx⟩⟩

/-
Descent consequence: on the positive region an index is `< n`.  If `0 < h i` then
`i < i + h i ≤ h 0 ≤ n` by the `slope`/`antitone`/`top` fields of `ProfileCurve`.
-/
theorem profileCurve_pos_index_lt (U : Map) (c n kx m : ℕ) (h : ℕ → ℕ)
    (hc : ProfileCurve U c n kx m h) {i : ℕ} (hpos : 0 < h i) : i < n := by
  have hdesc : ∀ j, 0 < h j → j + h j ≤ h 0 := by
    intro j hj_pos
    induction j with
    | zero => norm_num;
    | succ j ih => cases hc.slope j <;> linarith [ ih ( by linarith [ hc.antitone ( Nat.le_succ
        j ) ] ), hc.antitone ( Nat.le_succ j ) ];
  linarith [ hdesc i hpos, hc.top ]

/-
Auxiliary: the survivor set is nonempty once the counting bound holds.  The full
bad-union has cardinality `≤ ∑ card (badSetsUnion j) < 2 ^ n = (stringsOfLength n).card`,
so some length-`n` string escapes it.
-/
theorem survivor_set_nonempty (U : Map) (n : ℕ) (h : ℕ → ℕ) (m c_gen kx : ℕ)
    (hsum : ((Finset.range n).filter (fun i => m + logSlack c_gen n < h i)).sum
        (fun i => (badSetsUnion U n h m c_gen i).card) < 2 ^ n) :
    (stringsOfLength n \ badUnionUpTo (badEnumList U n h m c_gen kx)
      (badEnumList U n h m c_gen kx).length).Nonempty := by
  contrapose! hsum;
  rw [ Finset.ext_iff ] at hsum;
  have h_card : (stringsOfLength n).card ≤
      (badUnionUpTo (badEnumList U n h m c_gen kx) (badEnumList U n h m c_gen kx).length).card
          := by
    exact Finset.card_le_card fun x hx => by specialize hsum x; aesop;
  refine le_trans ?_ ( h_card.trans ?_ );
  · rw [ card_stringsOfLength ];
  · rw [ badUnionUpTo_full_eq ];
    exact Finset.card_biUnion_le

/-- Existence of a string in all coverable sets avoiding all bad sets.
This is the joint counting/greedy heart of Vereshchagin–Vitányi.

The lower/avoidance half comes from `exists_string_avoiding_curve`, via
`sum_badSetsUnion_card_lt`.  The greedy construction supplies the membership clause
`x ∈ coverableSet U i (h i)` for every budget `i ≤ kx + logSlack c n`.

That clause genuinely requires the Vereshchagin–Vitányi greedy/staircase
construction of nested realizing sets and cannot be obtained by counting the
complement: by `coverableSet_card_le`, `coverableSet U i (h i)` has only
`≤ 2^{i+1+h i}` elements, so at low budgets *most* length-`n` strings are not
coverable and the union over levels of the non-coverable strings already fills
almost the whole cube.  Hence a purely enumerative existence argument (as used for
the avoidance half) is provably insufficient here; the proof below uses the
temporal greedy-window construction (each held window has `|A_i| ≤ 2^{h i}` and
complexity `≤ i + O(log n)`) to provide the upper half of the profile-realization
theorem `stat-any-curve`.

Why the obvious sub-cube construction does *not* suffice: fixing an `(n-h i)`-bit
prefix of `x` gives a set of size `2^{h i}` containing `x`, but its set complexity is
`≈ n - h i`, and along an admissible curve `i + h i ≤ h 0 ≤ n` (descent), so
`n - h i ≥ i` — the sub-cube is generally an `(n-h i, h i)`-description, *not* the
required `(i, h i)`-description (equality only for the exact slope `-1` diagonal).
The gate-free diagonal upper bound realizable this way is exactly
`structureFunction_prefix_upper_of_optimal` (`h_x(i) ≤ n - i + O(log n)`).  Reaching
complexity `≤ i` on the *interior* of the curve therefore forces the genuine VV
construction, whose `≈ i` "address" bits selecting the held window must be chosen
jointly with `x` (via the survival/greedy argument), not read off `x`'s prefix. -/
theorem exists_point_in_all_coverableSets (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_gen, ∀ c n kx m h, ProfileCurve U c n kx m h →
      ∃ x : BitString, x.length = n ∧
        (∀ i, i ≤ kx + logSlack c n → x ∈ coverableSet U (i + m + logSlack c_gen n) (h
            i)) ∧
        (∀ i, x ∉ badSetsUnion U n h m c_gen i ∨ h i ≤ m + logSlack c_gen n) := by
  -- Use the single construction slack chosen by the final-window coding gate; it is
  -- large enough for both counting (`≥ 3`) and machine-model coding overhead.
  obtain ⟨c_gen, hge3, hcode⟩ := finalWindow_mem_coverableSet U hU
  refine ⟨c_gen, fun c n kx m h hcurve => ?_⟩
  have hsum := sum_badSetsUnion_card_lt_of_le U c_gen hge3 c n kx m h hcurve
  have hrem := survivor_set_nonempty U n h m c_gen kx hsum
  have hxrem := lexLeastSurvivor_mem_rem U n h m c_gen kx hrem
  rw [Finset.mem_sdiff] at hxrem
  obtain ⟨hxlen0, hxnotbad⟩ := hxrem
  have hxlen : (lexLeastSurvivor U n h m c_gen kx).length = n :=
    (mem_stringsOfLength n _).mp hxlen0
  refine ⟨lexLeastSurvivor U n h m c_gen kx, hxlen, ?_, ?_⟩
  · -- Upper/membership half: the lex-least survivor lies in some coded window
    -- which is an `(i + m + O(log n), h i)`-description, hence in the coverable set.
    intro i _hi
    by_cases hi_le_n : i ≤ n
    · obtain ⟨S, h_mem_S, h_S_code⟩ := hcode c n kx m h hcurve i hi_le_n hrem
      unfold coverableSet
      rw [Finset.mem_biUnion]
      exact ⟨S, h_S_code, h_mem_S⟩
    · have h_zero : h i = 0 := by
        by_contra hpos
        have h_lt_n := profileCurve_pos_index_lt U c n kx m h hcurve (Nat.pos_of_ne_zero hpos)
        omega
      have hn_le_n : n ≤ n := le_rfl
      obtain ⟨S_n, h_mem_Sn, h_Sn_code⟩ := hcode c n kx m h hcurve n hn_le_n hrem
      have hile_n : n + m + logSlack c_gen n ≤ i + m + logSlack c_gen n := by
        have : n ≤ i := le_of_not_ge hi_le_n
        omega
      have hn_zero : h n = 0 := by
        by_contra hpos
        have h_lt_n := profileCurve_pos_index_lt U c n kx m h hcurve (Nat.pos_of_ne_zero hpos)
        omega
      rw [hn_zero] at h_Sn_code
      rw [h_zero]
      have hmem_n := descriptionsWithComplexityLeAndSizeLe_subset_of_le_left U 0 hile_n
          h_Sn_code
      unfold coverableSet
      rw [Finset.mem_biUnion]
      exact ⟨S_n, hmem_n, h_mem_Sn⟩
  · -- Lower/avoidance half: the survivor escapes the full bad-union, hence every
    -- level-`i` bad set (for the levels that actually appear in the enumeration).
    intro i
    by_cases hle : h i ≤ m + logSlack c_gen n
    · exact Or.inr hle
    · refine Or.inl (fun hxbad => hxnotbad ?_)
      rw [badUnionUpTo_full_eq]
      rw [Finset.mem_biUnion]
      refine ⟨i, ?_, hxbad⟩
      rw [Finset.mem_filter, Finset.mem_range]
      have hlt : m + logSlack c_gen n < h i := by omega
      refine ⟨profileCurve_pos_index_lt U c n kx m h hcurve (by omega), hlt⟩

/-- Set complexity from a computable code.
If a computable `enc` maps a code `w` to the canonical uniform-set code of `A`,
then `setComplexity U A ≤ KPPlain U w + O(1)`. -/
theorem setComplexity_le_of_computable_code (U : Map) (hU : IsOptimalPrefixConditional U)
    (enc : BitString → BitString) (henc : Computable enc) :
    ∃ c, ∀ (A : Finset BitString) (hA : A.Nonempty) (w : BitString),
      enc w = (codedUniformOn A hA).code →
      setComplexity U A hA ≤ KPPlain U w + c := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU enc henc
  refine ⟨c, fun A hA w hw => ?_⟩
  unfold setComplexity
  rw [← hw]
  exact hc w

/-- Upper half of the realization theorem.  A string lying in every coverable set
`coverableSet U i (h i)` inherits, for each budget `i`, an `(i + O(1), h i)`-description,
so its profile contains the curve up to logarithmic slack. -/
theorem realization_upper (U : Map) :
    ∃ c_up, ∀ c_in c n kx m h, ProfileCurve U c n kx m h → ∀ x,
      (∀ i, i ≤ kx + logSlack c n → x ∈ coverableSet U (i + m + logSlack c_in n) (h i))
          →
      ∀ i, i ≤ kx + logSlack c n → InDescriptionProfile U x (i + m + logSlack (c_in +
          c_up) n)
          (h i + logSlack (c_in + c_up) n) := by
  obtain ⟨c_fam, hc_fam⟩ := inDescriptionProfile_of_mem_coverableSet U
  use c_fam
  intro c_in c n kx m h hcurve x hxmem i hi_le
  have h_in := hc_fam (i + m + logSlack c_in n) (h i) x (hxmem i hi_le)
  have h1 : i + m + logSlack c_in n + c_fam ≤ i + m + logSlack (c_in + c_fam) n := by
    unfold logSlack
    have : c_in * (Nat.bits n).length + c_in + c_fam ≤ (c_in + c_fam) * (Nat.bits n).length +
        (c_in + c_fam) := by
      rw [Nat.add_mul]
      omega
    omega
  have h2 : h i ≤ h i + logSlack (c_in + c_fam) n := by
    unfold logSlack
    have : h i ≤ h i + ((c_in + c_fam) * (Nat.bits n).length + (c_in + c_fam)) := by omega
    exact this
  exact (h_in.mono_i h1).mono_j h2

end Kolmogorov
