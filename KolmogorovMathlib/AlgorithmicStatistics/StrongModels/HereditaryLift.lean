import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Partition
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic

/-!
# G → L model lifting (S8, hereditary chain)

The first step of the hereditary-theorem chain (`thm:hereditary` sketch in VS40
§7).  Given a family `G` of set-codes containing the canonical code of a model
`A ∋ x`, we build the model

  `L = ⋃ { A' ∈ G : log #A' = log #A }`

for `x`.  By construction `x ∈ L`, `log #L ≤ log #G + log #A`, and — the point
of the construction — `C(L) ≤ C(G) + O(log log #A)`, because the canonical code
of `L` is a computable function of the canonical code of `G` and the single
number `r = log #A`, which is self-delimitingly describable in `O(log r)` bits.

The plain (ordinary) complexity bound is obtained by an explicit decompressor
that reads a self-delimiting code of `r`, then runs the optimal machine `V` on
the *suffix* to recover `G`'s code; because `V`'s program is the suffix, no
`O(log C(G))` composition tax is incurred and the slack is exactly
`logSlack c (finiteSetLogCard A) = O(log log #A)`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The lift `L = ⋃ { A' ∈ G : log #A' = r }`, decoding each member of `G` as a
finite set of strings. -/
noncomputable def hereditaryLift (G : Finset BitString) (r : Nat) : Finset BitString :=
  (G.filter (fun w =>
    finiteSetLogCard (canonicalPointListOfCode w).toFinset = r)).biUnion
    (fun w => (canonicalPointListOfCode w).toFinset)

/-- Membership: if `A ∋ x` and the canonical code of `A` lies in `G`, then `x`
lands in the lift at radius `finiteSetLogCard A`. -/
theorem hereditaryLift_mem (x : BitString) (A G : Finset BitString) (hA : A.Nonempty)
    (_hG : G.Nonempty)
    (hxA : x ∈ A) (hcode : (codedUniformOn A hA).code ∈ G) :
    x ∈ hereditaryLift G (finiteSetLogCard A) := by
  unfold hereditaryLift
  rw [Finset.mem_biUnion]
  refine ⟨(codedUniformOn A hA).code, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨hcode, ?_⟩
    rw [canonicalPointListOfCode_codedUniformOn, canonicalFinsetList_toFinset]
  · rw [canonicalPointListOfCode_codedUniformOn, canonicalFinsetList_toFinset]
    exact hxA

/-- Cardinality: the lift has at most `#G · 2^r` elements. -/
theorem hereditaryLift_card_le (G : Finset BitString) (r : Nat) :
    (hereditaryLift G r).card ≤ G.card * 2 ^ r := by
  unfold hereditaryLift
  refine le_trans Finset.card_biUnion_le ?_
  calc
    ∑ w ∈ G.filter (fun w =>
          finiteSetLogCard (canonicalPointListOfCode w).toFinset = r),
        (canonicalPointListOfCode w).toFinset.card
        ≤ ∑ _w ∈ G.filter (fun w =>
              finiteSetLogCard (canonicalPointListOfCode w).toFinset = r), 2 ^ r := by
          apply Finset.sum_le_sum
          intro w hw
          rw [Finset.mem_filter] at hw
          have hspec := finiteSetLogCard_spec (canonicalPointListOfCode w).toFinset
          rw [hw.2] at hspec
          exact hspec
    _ = (G.filter (fun w =>
          finiteSetLogCard (canonicalPointListOfCode w).toFinset = r)).card * 2 ^ r := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ G.card * 2 ^ r := by
          exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

/-! ### List-level reformulation (for computability) -/

/-- Boolean test `Nat.clog 2 m = r`, expressed via the dyadic bracket so that it
is primitive recursive. -/
def clogEqBool (m r : Nat) : Bool :=
  decide (m ≤ 2 ^ r ∧ (r = 0 ∨ 2 ^ (r - 1) < m))

theorem clogEqBool_iff (m r : Nat) :
    clogEqBool m r = true ↔ Nat.clog 2 m = r := by
  unfold clogEqBool
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hle, hlow⟩
    have hclog_le : Nat.clog 2 m ≤ r := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hle
    rcases hlow with hr0 | hlt
    · subst hr0; omega
    · have hgt : r - 1 < Nat.clog 2 m := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
      omega
  · intro hclog
    subst hclog
    refine ⟨(Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.clog 2 m) with h0 | hpos
    · exact Or.inl h0
    · exact Or.inr ((Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega))

theorem clogEqBool_primrec : Primrec₂ clogEqBool := by
  have h : PrimrecPred (fun p : ℕ × ℕ =>
      p.1 ≤ 2 ^ p.2 ∧ (p.2 = 0 ∨ 2 ^ (p.2 - 1) < p.1)) :=
    PrimrecPred.and
      (Primrec.nat_le.comp Primrec.fst (twoPow_primrec.comp Primrec.snd))
      (PrimrecPred.or
        (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.nat_lt.comp
          (twoPow_primrec.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
          Primrec.fst))
  exact h.decide

/-- The list-level lift: the concatenation (with later deduplication via
`toFinset`) of the decoded members of `G` whose decoded set has log-cardinality
`r`.  Everything here is a computable list operation. -/
noncomputable def hereditaryLiftList (Gcode : BitString) (r : Nat) : List BitString :=
  ((canonicalPointListOfCode Gcode).filter
    (fun w => clogEqBool (canonicalPointListOfCode w).length r)).flatMap
    (fun w => canonicalPointListOfCode w)

theorem hereditaryLiftList_primrec :
    Primrec (fun p : BitString × Nat => hereditaryLiftList p.1 p.2) := by
  have hfilter : Primrec (fun p : BitString × Nat =>
      (canonicalPointListOfCode p.1).filter
        (fun w => clogEqBool (canonicalPointListOfCode w).length p.2)) := by
    refine list_filter_primrec (canonicalPointListOfCode_primrec.comp Primrec.fst) ?_
    exact clogEqBool_primrec.comp
      (Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_flatMap hfilter
    (canonicalPointListOfCode_primrec.comp Primrec.snd)

/-- Canonical code of the lift, computed from a set-code `Gcode` and radius `r`. -/
noncomputable def hereditaryLiftCode (Gcode : BitString) (r : Nat) : BitString :=
  canonicalFiniteSetCode (hereditaryLift (canonicalPointListOfCode Gcode).toFinset r)

/-- The decoded members of `w` form a duplicate-free list. -/
theorem canonicalPointListOfCode_nodup (w : BitString) :
    (canonicalPointListOfCode w).Nodup := by
  unfold canonicalPointListOfCode
  exact canonicalFinsetList_nodup _

/-- The two filter predicates (Finset-level `finiteSetLogCard` and list-level
`clogEqBool ∘ length`) agree. -/
theorem finiteSetLogCard_toFinset_eq_clog (w : BitString) :
    finiteSetLogCard (canonicalPointListOfCode w).toFinset =
      Nat.clog 2 (canonicalPointListOfCode w).length := by
  unfold finiteSetLogCard
  rw [List.toFinset_card_of_nodup (canonicalPointListOfCode_nodup w)]

theorem hereditaryLift_filter_pred (w : BitString) (r : Nat) :
    (finiteSetLogCard (canonicalPointListOfCode w).toFinset = r) ↔
      (clogEqBool (canonicalPointListOfCode w).length r = true) := by
  rw [clogEqBool_iff, finiteSetLogCard_toFinset_eq_clog]

/-- The Finset lift of a decoded code equals the `toFinset` of the list lift. -/
theorem hereditaryLift_toFinset_eq (Gcode : BitString) (r : Nat) :
    hereditaryLift (canonicalPointListOfCode Gcode).toFinset r
      = (hereditaryLiftList Gcode r).toFinset := by
  ext x
  simp only [hereditaryLift, hereditaryLiftList, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset, List.mem_flatMap, List.mem_filter]
  constructor
  · rintro ⟨w, ⟨hwG, hwpred⟩, hxw⟩
    exact ⟨w, ⟨hwG, (hereditaryLift_filter_pred w r).mp hwpred⟩, hxw⟩
  · rintro ⟨w, ⟨hwG, hwpred⟩, hxw⟩
    exact ⟨w, ⟨hwG, (hereditaryLift_filter_pred w r).mpr hwpred⟩, hxw⟩

/-- `hereditaryLiftCode` is exactly the canonical image code of the list lift. -/
theorem hereditaryLiftCode_eq_image (Gcode : BitString) (r : Nat) :
    hereditaryLiftCode Gcode r = canonicalImageCodeOfList (hereditaryLiftList Gcode r) := by
  unfold hereditaryLiftCode canonicalImageCodeOfList canonicalFiniteSetCode
  rw [hereditaryLift_toFinset_eq]

theorem hereditaryLiftCode_computable :
    Computable₂ hereditaryLiftCode := by
  refine (canonicalImageCodeOfList_primrec.comp hereditaryLiftList_primrec).to_comp.of_eq ?_
  intro p
  exact (hereditaryLiftCode_eq_image p.1 p.2).symm

/-- On canonical set codes, the lift-code produces exactly the canonical code of
the (nonempty) lift. -/
theorem hereditaryLiftCode_eq (G : Finset BitString) (hG : G.Nonempty) (r : Nat)
    (hL : (hereditaryLift G r).Nonempty) :
    hereditaryLiftCode (codedUniformOn G hG).code r =
      (codedUniformOn (hereditaryLift G r) hL).code := by
  unfold hereditaryLiftCode canonicalFiniteSetCode
  rw [canonicalPointListOfCode_codedUniformOn, canonicalFinsetList_toFinset]
  exact canonicalUniformCodeOfList_canonicalFinsetList (hereditaryLift G r) hL

/-! ### Plain-complexity bound via a suffix-running decompressor -/

/-- Reads a self-delimiting code of the radius `r` from the *first* component of
the program, runs `V` on the *second* component to recover the set-code, and
returns the lift-code.  Because `V`'s program is the (unbounded) suffix, the
composition costs only the self-delimiting description of `r`. -/
noncomputable def hereditaryLiftPlainDecompressor (V : Map) : Map := fun pr =>
  (V (decodeSecond pr.1, [])).map (fun Gcode =>
    hereditaryLiftCode Gcode (bitsToNat (decodeFirst pr.1)))

theorem hereditaryLiftPlainDecompressor_partrec (V : Map) (hV : isDecompressor V) :
    isDecompressor (hereditaryLiftPlainDecompressor V) := by
  unfold hereditaryLiftPlainDecompressor
  refine Partrec.map ?_ ?_
  · exact Partrec.comp hV
      (Computable.pair (decodeSecond_computable.comp Computable.fst)
        (Computable.const []))
  · exact hereditaryLiftCode_computable.comp Computable.snd
      (bitsToNat_computable.comp
        (decodeFirst_computable.comp (Computable.fst.comp Computable.fst)))

theorem hereditaryLiftPlainDecompressor_produces (V : Map) (Gcode p : BitString) (r : Nat)
    (h : produces V p [] Gcode) :
    produces (hereditaryLiftPlainDecompressor V) (pairCode (Nat.bits r) p) []
      (hereditaryLiftCode Gcode r) := by
  unfold produces hereditaryLiftPlainDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode, bitsToNat_bits]
  exact (Part.mem_map_iff _).2 ⟨Gcode, h, rfl⟩

/-- The plain-complexity bound: `C(L-code) ≤ C(G-code) + O(log r)`. -/
theorem plainK_hereditaryLiftCode_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (Gcode : BitString) (r : Nat),
      plainK V (hereditaryLiftCode Gcode r) ≤
        plainK V Gcode + (logSlack c r : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (hereditaryLiftPlainDecompressor V)
    (hereditaryLiftPlainDecompressor_partrec V hV.1)
  refine ⟨cSim + 2, fun Gcode r => ?_⟩
  set M : Nat := 2 * (Nat.bits r).length + 1 with hM
  clear_value M
  have hbound : condK (hereditaryLiftPlainDecompressor V)
      (hereditaryLiftCode Gcode r) [] ≤ condK V Gcode [] + (M : ENat) := by
    apply sInfLeSInfAdd
    rintro s₂ ⟨p, hp, rfl⟩
    refine ⟨(programLength (pairCode (Nat.bits r) p) : ENat),
      ⟨pairCode (Nat.bits r) p,
        hereditaryLiftPlainDecompressor_produces V Gcode p r hp, rfl⟩, ?_⟩
    have hlen : (pairCode (Nat.bits r) p).length ≤ p.length + M := by
      rw [length_pairCode, hM]; omega
    exact_mod_cast hlen
  calc
    plainK V (hereditaryLiftCode Gcode r)
        ≤ condK (hereditaryLiftPlainDecompressor V) (hereditaryLiftCode Gcode r) []
            + (cSim : ENat) := hSim _ _
    _ ≤ (condK V Gcode [] + (M : ENat)) + (cSim : ENat) := by gcongr
    _ = plainK V Gcode + ((M : ENat) + (cSim : ENat)) := by
        change (condK V Gcode [] + (M : ENat)) + (cSim : ENat)
          = condK V Gcode [] + ((M : ENat) + (cSim : ENat))
        rw [add_assoc]
    _ ≤ plainK V Gcode + (logSlack (cSim + 2) r : ENat) := by
        gcongr
        have hle : M + cSim ≤ logSlack (cSim + 2) r := by
          rw [hM]; unfold logSlack
          nlinarith [Nat.zero_le (cSim * (Nat.bits r).length)]
        calc (M : ENat) + (cSim : ENat) = ((M + cSim : Nat) : ENat) := by norm_cast
          _ ≤ (logSlack (cSim + 2) r : ENat) := by exact_mod_cast hle

/-! ### The G → L model-lifting theorem -/

/-- **G → L model lifting.**  Given a family `G` of set-codes containing the
canonical code of a model `A ∋ x`, there is a model `L ∋ x` whose plain
complexity exceeds that of `G` by at most `O(log log #A)` and whose
log-cardinality is at most `log #G + log #A`. -/
theorem hereditary_lift_model
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ x A (hA : A.Nonempty) G (hG : G.Nonempty),
      x ∈ A →
      (codedUniformOn A hA).code ∈ G →
      ∃ L, ∃ hL : L.Nonempty,
        x ∈ L ∧
        plainSetComplexity V L hL ≤
          plainSetComplexity V G hG +
            (logSlack c (finiteSetLogCard A) : ENat) ∧
        finiteSetLogCard L ≤
          finiteSetLogCard G + finiteSetLogCard A := by
  obtain ⟨c, hc⟩ := plainK_hereditaryLiftCode_le V hV
  refine ⟨c, fun x A hA G hG hxA hcode => ?_⟩
  have hxL : x ∈ hereditaryLift G (finiteSetLogCard A) :=
    hereditaryLift_mem x A G hA hG hxA hcode
  have hLne : (hereditaryLift G (finiteSetLogCard A)).Nonempty := ⟨x, hxL⟩
  refine ⟨hereditaryLift G (finiteSetLogCard A), hLne, hxL, ?_, ?_⟩
  · unfold plainSetComplexity
    rw [← hereditaryLiftCode_eq G hG (finiteSetLogCard A) hLne]
    exact hc (codedUniformOn G hG).code (finiteSetLogCard A)
  · rw [finiteSetLogCard_le_iff]
    calc
      (hereditaryLift G (finiteSetLogCard A)).card
          ≤ G.card * 2 ^ (finiteSetLogCard A) :=
            hereditaryLift_card_le G (finiteSetLogCard A)
      _ ≤ 2 ^ (finiteSetLogCard G) * 2 ^ (finiteSetLogCard A) := by
            gcongr; exact finiteSetLogCard_spec G
      _ = 2 ^ (finiteSetLogCard G + finiteSetLogCard A) := by rw [pow_add]

end Kolmogorov
