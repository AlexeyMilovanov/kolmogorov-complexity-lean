import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.FiniteSetModel
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Prefix.TwoStage

/-!
# Models to Sets 2 (Section 3)

This module shows that distribution models can be replaced by uniform finite-set
models with logarithmic slack in optimality deficiency (P-MS2).
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/--
If `x` has mass at least `2^{-k}`, then the `k`-th level set is nonempty.
-/
theorem levelSet_nonempty_of_mass_ge (P : CodedFiniteDistribution) (x : BitString) (k : ℕ)
    (hx_support : x ∈ P.support) (hx_mass : (2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass x) :
    (levelSet P k).Nonempty :=
  ⟨x, mem_levelSet hx_support hx_mass⟩

/-- The explicit encoder behind P-MS2.  Given the pair code `(P.code, natCode k)`,
it decodes the finite rational distribution data of `P`, keeps the points whose
combined mass passes the `k`-th level-set threshold (`levelSetMemBool`), and
re-encodes the uniform distribution on the resulting finite set using the
canonical *computable* enumeration `canonicalFinsetList`.  This is a genuine
computable function (no `Finset.toList`/choice). -/
def levelSetUniformCode (s : BitString) : BitString :=
  let w := decodeFirst s
  let k := decodeNatCode (decodeSecond s)
  let pts := ((decodeDistributionData w).map CodedDistributionEntry.point).filter
      (fun x => levelSetMemBool w k x)
  let S := pts.toFinset
  codedDistributionDataCode ((canonicalFinsetList S).map fun x =>
    { point := x, mass := ratMassInvNat (max 1 S.card) (by positivity) })

/-- `decodeDistributionData` is a left inverse of the canonical code. -/
theorem decodeDistributionData_of_code (P : CodedFiniteDistribution) :
    decodeDistributionData P.code = P.data := by
  have := decodeCodedFiniteDistribution_code P
  unfold decodeCodedFiniteDistribution at this
  exact congrArg CodedFiniteDistribution.data this

/-- The computable level-set filter on `P.code` recovers exactly `levelSet P k`. -/
theorem levelSetFilter_toFinset (P : CodedFiniteDistribution) (k : ℕ) :
    (((decodeDistributionData P.code).map CodedDistributionEntry.point).filter
      (fun x => levelSetMemBool P.code k x)).toFinset = levelSet P k := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, List.mem_map]
  rw [decodeDistributionData_of_code]
  constructor
  · rintro ⟨_, hmem⟩
    have hx : x ∈ levelSet (decodeCodedFiniteDistribution P.code) k :=
      (levelSetMemBool_iff _ _ _).mp hmem
    rwa [decodeCodedFiniteDistribution_code] at hx
  · intro hx
    refine ⟨?_, ?_⟩
    · have hxsupp : x ∈ P.support :=
        Finset.mem_filter.mp (by rw [levelSet] at hx; exact hx) |>.1
      exact List.mem_map.mp ((mem_support_iff P x).mp hxsupp)
    · rw [levelSetMemBool_iff, decodeCodedFiniteDistribution_code]; exact hx

/-- Correctness of the explicit encoder: on `(P.code, natCode k)` it produces the
canonical code of the uniform distribution on `levelSet P k`. -/
theorem levelSetUniformCode_eq (P : CodedFiniteDistribution) (k : ℕ)
    (h : (levelSet P k).Nonempty) :
    levelSetUniformCode (pairCode P.code (natCode k)) = (codedUniformOn (levelSet P k) h).code := by
  have hSeq := levelSetFilter_toFinset P k
  have hSne : (((decodeDistributionData P.code).map CodedDistributionEntry.point).filter
      (fun x => levelSetMemBool P.code k x)).toFinset.Nonempty := hSeq ▸ h
  unfold levelSetUniformCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]
  rw [← codedUniformOn_code_congr hSne h hSeq, codedUniformOn_code_eq]
  have hc : max 1 (((decodeDistributionData P.code).map CodedDistributionEntry.point).filter
      (fun x => levelSetMemBool P.code k x)).toFinset.card
      = (((decodeDistributionData P.code).map CodedDistributionEntry.point).filter
      (fun x => levelSetMemBool P.code k x)).toFinset.card :=
    max_eq_right (Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hSne))
  refine congrArg codedDistributionDataCode ?_
  apply List.map_congr_left
  intro x _
  refine congrArg (fun m => ({point := x, mass := m} : CodedDistributionEntry)) ?_
  apply RatMass.code_injective
  simp only [RatMass.code, ratMassInvNat, hc]

/-! ### Primitive recursion of the sorting / dedup step

The only genuinely new computability content of P-MS2 compared with the
description-shift encoder is that the canonical sorted enumeration
`canonicalFinsetList l.toFinset` of (the finite set spanned by) a list `l` is a
primitive recursive function of `l`.  We isolate this as a handful of small,
reusable `Primrec` facts about `List.orderedInsert`, `List.insertionSort` and
`List.dedup` for the canonical order `bitStringLE`. -/

/-
A general `filter` combinator is primitive recursive.
-/
theorem list_filter_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).filter (p a)) := by
  convert Primrec.list_foldr hf ( Primrec.const List.nil ) _ using 1;
  rotate_left;
  · exact fun a b => if p a b.1 then b.1 :: b.2 else b.2;
  · convert Primrec.ite _ _ _ using 1;
    · exact Primrec.eq.comp ( hp.comp ( Primrec.fst ) ( Primrec.fst.comp ( Primrec.snd ) ) )
        ( Primrec.const true );
    · exact Primrec.list_cons.comp ( Primrec.fst.comp ( Primrec.snd ) )
        ( Primrec.snd.comp ( Primrec.snd ) );
    · exact Primrec.snd.comp Primrec.snd;
  · exact funext fun a => by induction ( f a ) <;> aesop;

/-
Membership of a `BitString` in a `BitString` list is a primitive recursive
predicate.
-/
theorem bitString_mem_primrec :
    Primrec₂ (fun (a : BitString) (l : List BitString) => decide (a ∈ l)) := by
  have h_eq : Primrec₂ (fun (a b : BitString) => decide (a = b)) := by
    convert Primrec.eq;
    any_goals exact BitString;
    · convert Iff.rfl
      exact primrecRel_iff_primrec_decide
  convert list_any_primrec ( show Primrec ( fun x : BitString × List BitString => x.2 ) from ?_ )
      ( show Primrec₂ ( fun p : BitString × List BitString => fun b => decide ( p.1 = b ) ) from ?_
          ) using 1;
  · simp +decide [ Primrec₂, List.any_eq ];
  · exact Primrec.snd;
  · convert h_eq.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.snd ) using 1

/-
Ordered insertion at the canonical (`Encodable`-code) order is primitive
recursive in the inserted element and the list.
-/
theorem orderedInsert_primrec :
    Primrec₂ (fun (a : BitString) (l : List BitString) =>
      List.orderedInsert bitStringLE a l) := by
  simp only [Primrec₂];
  apply Primrec.of_eq;
  · convert Primrec.list_rec ( show Primrec ( fun x : BitString × List BitString => x.2 ) from ?_ )
      ( show Primrec ( fun x : BitString × List BitString => [ x.1 ] ) from ?_ )
          ( show Primrec₂ ( fun p : BitString × List BitString => fun b : BitString × List
                            BitString × List BitString =>
                                if decide ( bitStringLE p.1 b.1 ) then p.1 :: b.1 :: b.2.1 else b.1
                                    :: b.2.2 ) from ?_ ) using 1
    · exact Primrec.snd
    · exact Primrec.list_cons.comp ( Primrec.fst ) ( Primrec.const [ ] )
    · convert Primrec.ite _ _ _ using 1
      · convert Primrec.nat_le.comp ( Primrec.encode.comp ( Primrec.fst.comp ( Primrec.fst ) ) )
          ( Primrec.encode.comp ( Primrec.fst.comp ( Primrec.snd ) ) ) using 1
        exact funext fun x => by simp only [bitStringLE, decide_eq_true_eq]
      · convert Primrec.list_cons.comp ( Primrec.fst.comp ( Primrec.fst ) )
          ( Primrec.list_cons.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.fst.comp
                                                                          ( Primrec.snd.comp
                                                                              ( Primrec.snd )
                                                                                  ) ) ) using 1
      · exact Primrec.list_cons.comp ( Primrec.fst.comp ( Primrec.snd ) )
          ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) )
  · intro n; induction n.2 <;> simp only [*, List.orderedInsert] ;
    aesop

/-
Insertion sort by the canonical order is primitive recursive.
-/
theorem insertionSort_primrec :
    Primrec (fun l : List BitString => List.insertionSort bitStringLE l) := by
  convert Primrec.list_foldr ( show Primrec ( fun l : List BitString => l ) from ?_ )
      ( show Primrec ( fun _ : List BitString => [ ] ) from ?_ )
          ( show Primrec₂ ( fun p : List BitString => fun b : BitString × List BitString =>
                            List.orderedInsert bitStringLE b.1 b.2 ) from ?_ ) using 1;
  · exact Primrec.id;
  · exact Primrec.const [ ];
  · convert orderedInsert_primrec.comp ( Primrec.fst.comp ( Primrec.snd ) )
      ( Primrec.snd.comp ( Primrec.snd ) ) using 1

/-
Deduplication of a `BitString` list is primitive recursive.
-/
theorem dedup_primrec :
    Primrec (fun l : List BitString => l.dedup) := by
  have h_foldr : ∀ l : List BitString,
      l.dedup = List.foldr (fun a acc => if a ∈ acc then acc else a :: acc) [] l := by
        intro l; induction l <;> simp +decide [ * ] ;
        grind +suggestions;
  convert Primrec.list_foldr ( show Primrec ( fun l : List BitString => l ) from ?_ )
      ( show Primrec ( fun _ : List BitString => [ ] ) from ?_ )
          ( show Primrec₂ ( fun p : List BitString => fun b : BitString × List BitString => if b.1
                            ∈ b.2 then b.2 else b.1 :: b.2 ) from ?_ ) using 1;
  · exact funext h_foldr;
  · exact Primrec.id;
  · exact Primrec.const [ ];
  · convert Primrec.ite _ _ _ using 1;
    · convert bitString_mem_primrec.comp ( Primrec.fst.comp ( Primrec.snd ) )
        ( Primrec.snd.comp ( Primrec.snd ) ) using 1;
      rotate_left;
      · exact List BitString;
      · infer_instance;
      exact primrecPred_iff_primrec_decide;
    · exact Primrec.snd.comp ( Primrec.snd );
    · exact Primrec.list_cons.comp ( Primrec.fst.comp ( Primrec.snd ) )
        ( Primrec.snd.comp ( Primrec.snd ) )

/-
The canonical sorted enumeration of `l.toFinset` is the insertion sort of the
deduplicated list `l.dedup`.
-/
theorem canonicalFinsetList_toFinset_eq (l : List BitString) :
    canonicalFinsetList l.toFinset = List.insertionSort bitStringLE l.dedup := by
  have h_perm : List.Perm (canonicalFinsetList l.toFinset) (l.dedup) ∧ List.Perm
      (List.insertionSort bitStringLE l.dedup) (l.dedup) := by
    have h_perm : Multiset.ofList (canonicalFinsetList l.toFinset) = Multiset.ofList l.dedup := by
      convert Finset.sort_eq ( s := l.toFinset ) ( r := bitStringLE ) using 1;
    exact ⟨ Multiset.coe_eq_coe.mp h_perm, List.perm_insertionSort _ _ ⟩;
  apply List.Perm.eq_of_pairwise;
  case le => exact fun a b => bitStringLE a b;
  · exact fun a b ha hb hab hba => Std.Antisymm.antisymm _ _ hab hba;
  · exact Finset.pairwise_sort _ _;
  · apply List.pairwise_insertionSort;
  · exact h_perm.1.trans h_perm.2.symm

/-- The canonical sorted enumeration of `l.toFinset` is a primitive recursive
function of `l`. -/
theorem canonicalFinsetList_toFinset_primrec :
    Primrec (fun l : List BitString => canonicalFinsetList l.toFinset) :=
  (insertionSort_primrec.comp dedup_primrec).of_eq
    (fun l => (canonicalFinsetList_toFinset_eq l).symm)

/-
`codedDistributionDataCode` of the uniform map on a list, as a `foldr` that
only ever builds `BitString`s (convenient for the computability proof).
-/
theorem codedUniform_data_foldr (l : List BitString) (n : ℕ) (hn : 0 < n) :
    codedDistributionDataCode
        (l.map (fun x => ({point := x, mass := ratMassInvNat n hn} : CodedDistributionEntry)))
      = l.foldr (fun x acc =>
          true :: pairCode (pairCode x (pairCode (natCode 1) (natCode n))) acc) [false] := by
  induction l <;> simp +decide [ *, codedDistributionDataCode ];
  congr

/-
The uniform-distribution encoder on a list of points is primitive recursive.
-/
theorem codedUniformEncoder_primrec :
    Primrec (fun t : List BitString =>
      codedDistributionDataCode (t.map fun x =>
        ({point := x, mass := ratMassInvNat (max 1 t.length) (by positivity)} :
          CodedDistributionEntry))) := by
  convert Primrec.list_foldr _ _ _ using 1;
  rotate_left;
  · exact BitString;
  · infer_instance;
  · exact fun t => t;
  · exact fun _ => [ false ];
  · exact fun t p =>
      true :: pairCode ( pairCode p.1 ( pairCode ( natCode 1 ) ( natCode ( max 1 t.length ) ) ) )
          p.2;
  · exact Primrec.id;
  · exact Primrec.const [ false ];
  · apply Primrec.list_cons.comp ( Primrec.const true )
      ( pairCode_primrec.comp ( pairCode_primrec.comp ( Primrec.fst.comp ( Primrec.snd ) )
                                ( pairCode_primrec.comp ( natCode_primrec.comp ( Primrec.const 1 )
                                                          ) ( natCode_primrec.comp
                                                              ( Primrec.nat_max.comp
                                                                  ( Primrec.const 1 )
                                                                      ( Primrec.list_length.comp
                                                                          ( Primrec.fst )
                                                                              ) ) ) ) )
          ( Primrec.snd.comp ( Primrec.snd ) ) );
  · exact funext fun t => codedUniform_data_foldr t ( max 1 t.length ) ( by positivity )

/-
The remaining genuine computability content of P-MS2, isolated as a single local
obligation: the explicit encoder `levelSetUniformCode` is computable.  It is a
composition of computable decoders (`decodeFirst`, `decodeSecond`,
`decodeNatCode`, `decodeDistributionData`), the computable level-set test
(`levelSetMemBool`, see `levelSetMemBool_primrec`), the canonical computable
enumeration `canonicalFinsetList` (`Finset.sort`, see
`canonicalFinsetList_toFinset_primrec`), and the computable encoder
`codedDistributionDataCode`.
-/
theorem levelSetUniformCode_computable : Computable levelSetUniformCode := by
  convert Primrec.to_comp _;
  convert Primrec.comp ( codedUniformEncoder_primrec )
      ( canonicalFinsetList_toFinset_primrec.comp ( list_filter_primrec _ _ ) ) using 1;
  rotate_left;
  · exact fun s => ( decodeDistributionData ( decodeFirst s ) ).map CodedDistributionEntry.point;
  · exact fun s x => levelSetMemBool ( decodeFirst s ) ( decodeNatCode ( decodeSecond s ) ) x;
  · exact Primrec.list_map ( decodeDistributionData_primrec.comp decodeFirst_primrec )
      ( entry_point_primrec.comp Primrec.snd );
  · convert Primrec.comp levelSetMemBool_primrec
      ( Primrec.pair ( Primrec.pair ( decodeFirst_primrec.comp ( Primrec.fst ) )
                       ( decodeNatCode_primrec.comp ( decodeSecond_primrec.comp ( Primrec.fst ) ) )
                           ) ( Primrec.snd ) ) using 1;
  · ext; simp [levelSetUniformCode]

/--
P-MS2 computable-encoder existence: there is a fixed computable map sending
`(P.code, natCode k)` to the canonical code of the uniform distribution on
`levelSet P k`.  Assembled from the explicit encoder `levelSetUniformCode`, its
computability `levelSetUniformCode_computable`, and its correctness
`levelSetUniformCode_eq`.
-/
theorem exists_levelSetUniformCode_computable :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ (P : CodedFiniteDistribution) (k : ℕ) (h : (levelSet P k).Nonempty),
        f (pairCode P.code (natCode k)) = (codedUniformOn (levelSet P k) h).code :=
  ⟨levelSetUniformCode, levelSetUniformCode_computable, levelSetUniformCode_eq⟩

/-
The main coding bridge: the complexity of the uniform distribution on the level
set is bounded by the complexity of `P` plus `O(log k)`.

This is now fully reduced to the computable-encoder existence
`exists_levelSetUniformCode_computable`: the `O(log k)` slack is the explicit
complexity accounting `KPPair ≤ KPPlain P.code + KPPlain (natCode k) + O(1)` and
`KPPlain (natCode k) ≤ 2 * |bits k| + O(1)`.
-/
theorem levelSetModel_setComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : CodedFiniteDistribution) (k : ℕ) (h_nonempty : (levelSet P k).Nonempty),
      setComplexity U (levelSet P k) h_nonempty ≤ P.complexity U + (logSlack c k : ENat) := by
  obtain ⟨f, hf_computable, hf_eq⟩ := exists_levelSetUniformCode_computable
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU f hf_computable
  obtain ⟨c_pair, h_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_nat, h_nat⟩ := KPPlain_natCode_le_log U hU
  use c_nat + c_pair + c_map + 2
  intro P k h_nonempty
  have hpair_eq : KPPlain U (pairCode P.code (natCode k)) = KPPair U P.code (natCode k) := by
    rw [KPPair_eq_KP_pairCode, KPPlain_eq_KP]
  have h_complexity : KPPlain U (f (pairCode P.code (natCode k))) ≤
      KPPlain U P.code + 2 * (Nat.bits k).length + c_nat + c_pair + c_map := by
    refine le_trans (h_map _) ?_
    rw [hpair_eq]
    calc KPPair U P.code (natCode k) + (c_map : ENat)
        ≤ (KPPlain U P.code + KPPlain U (natCode k) + c_pair) + c_map := by
          gcongr
          exact h_pair P.code (natCode k)
      _ ≤ (KPPlain U P.code + (2 * (Nat.bits k).length + c_nat) + c_pair) + c_map := by
          gcongr
          exact h_nat k
      _ = KPPlain U P.code + 2 * (Nat.bits k).length + c_nat + c_pair + c_map := by abel
  convert h_complexity.trans ?_ using 1
  · exact hf_eq P k h_nonempty ▸ rfl
  · unfold logSlack
    norm_cast
    simp only [KPPlain_eq_KP, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, add_assoc]
    exact add_le_add (by rfl) (by norm_cast; nlinarith)

/-
The original P-MS2 assembly statement quantified `k` only with the *lower*
threshold `2^{-k} ≤ P.mass x`.  That statement is FALSE with the `+ 1` slack:
without an upper bound on `P.mass x`, the level set `levelSet P k` can be much
larger than `1 / P.mass x` (e.g. `P` with `P.mass x = 1/2` but `2^k` further
points of mass `2^{-k}`), so the uniform mass `1 / |S|` of `x` can be far below
`P.mass x` and the set optimality deficiency exceeds `beta + logSlack c k + 1`.

The faithful statement (matching the tight level set `k ≈ -log P(x)` used by
Vereshchagin–Shen) additionally requires the *upper* threshold
`P.mass x ≤ 2 * 2^{-k}`, which pins `k` to `-log P(x)` up to one bit.  The
corrected, proved version is `exists_setModel_optimalityDeficiencyLe_of_distribution`
below.  In Lean syntax the old conclusion only assumed
`(2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass x` (no upper threshold), which is exactly what made
it unprovable with the `+ 1` slack.
-/

/--
Final theorem for P-MS2: `exists_set_optimalityDeficiencyLe_of_distribution`.
This assembles the threshold helper and the coding bridge.

Corrected statement: in addition to the lower threshold `2^{-k} ≤ P.mass x` we
require the matching upper threshold `P.mass x ≤ 2 * 2^{-k}`, i.e. `k` is the
tight level `-log P(x)` (up to one bit).  This is exactly the level used in
Vereshchagin–Shen and is necessary for the `+ 1` deficiency slack: it guarantees
`P.mass x ≤ 2 / |levelSet P k|`, since `|levelSet P k| ≤ 2^k`.
-/
theorem exists_setModel_optimalityDeficiencyLe_of_distribution
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ P : CodedFiniteDistribution, ∀ x : BitString, ∀ k : ℕ,
      P.IsProbability → x ∈ P.support →
      (2 : ℝ≥0∞)⁻¹ ^ k ≤ P.mass x →
      P.mass x ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k →
      ∀ beta : ℕ, OptimalityDeficiencyLe U P x beta →
      ∃ S hS, x ∈ S ∧
        setComplexity U S hS ≤ P.complexity U + (logSlack c k : ENat) ∧
        SetOptimalityDeficiencyLe U S hS x (beta + logSlack c k + 1) := by
  obtain ⟨ c, hc ⟩ := levelSetModel_setComplexity_le U hU;
  refine ⟨ c, fun P x k hP hx hk₁ hk₂ beta hbeta => ?_ ⟩;
  refine ⟨ levelSet P k, levelSet_nonempty_of_mass_ge P x k hx hk₁, mem_levelSet hx hk₁,
           hc P k ( levelSet_nonempty_of_mass_ge P x k hx hk₁ ), ?_ ⟩;
  rw [ setOptimalityDeficiencyLe_iff_of_mem ( mem_levelSet hx hk₁ ) ];
  refine le_trans hbeta ?_;
  -- Apply the bounds from hc and the properties of the level set.
  have h_bounds : complexityWeight (KPPlain U P.code) ≤ complexityWeight
      (setComplexity U (levelSet P k) (levelSet_nonempty_of_mass_ge P x k hx hk₁)) * (2 : ℝ≥0∞) ^
          (logSlack c k) ∧ P.mass x ≤ 2 * (↑(levelSet P k).card)⁻¹ := by
    constructor;
    · have h_complexity_weight : complexityWeight (KPPlain U P.code + (logSlack c k : ENat)) ≤
        complexityWeight
            (setComplexity U (levelSet P k) (levelSet_nonempty_of_mass_ge P x k hx hk₁)) := by
        exact complexityWeight_le_of_le ( hc P k ( levelSet_nonempty_of_mass_ge P x k hx hk₁ ) );
      convert mul_le_mul' h_complexity_weight (le_refl ((2 : ℝ≥0∞) ^ logSlack c k)) using 1
      rw [ complexityWeight_add_nat ]
      rw [ mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel ] <;> norm_num
    · refine le_trans hk₂ ?_
      rw [ ← ENNReal.inv_pow ]
      gcongr
      convert levelSet_card_le P k hP using 1
  convert mul_le_mul' ( le_refl ( 2 ^ beta ) ) ( mul_le_mul' h_bounds.1 h_bounds.2 ) using 1
  ring

end Kolmogorov
