import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRaw
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailRawComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayChargeComputable
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# Computability of the erased charged spend layout

Every mirror introduced in `GacsDayChargedRaw.lean` for the *spend* layout and
for the displayed charged move is shown here to be computable, jointly in all
its arguments.  Each mirror is first packed into a single-argument definition
so that the composition lemmas stay cheap to elaborate; a `..._eq` shape lemma
records the packed unfolding.

The proofs reuse the erased ingredients of
`GacsDayLadderTailRawComputable.lean`.
-/


namespace Kolmogorov

/-- Strict rational comparison from the available non-strict test. -/
theorem decide_rat_lt_eq (u v : ℚ) : (!decide (v ≤ u)) = decide (u < v) := by
  by_cases h : u < v
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-! ### The spare and spend pair layout -/

/-- The raw spare pairs are computable in the branching and the source count. -/
theorem computable_rawSparePairs :
    Computable fun x : ℕ × ℕ => rawSparePairs x.1 x.2 := by
  have hbody : Primrec₂ fun (x : ℕ × ℕ) (c : ℕ) =>
      (List.range x.1).map fun d => ((c, d) : ℕ × ℕ) := by
    have hm : Primrec fun z : (ℕ × ℕ) × ℕ =>
        (List.range z.1.1).map fun d => ((z.2, d) : ℕ × ℕ) := by
      refine Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) ?_
      exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
    exact hm
  have hdrop : Primrec fun x : ℕ × ℕ => (List.range x.1).drop x.2 :=
    (Primrec.list_drop (α := ℕ)).comp Primrec.snd (Primrec.list_range.comp Primrec.fst)
  exact (Primrec.list_flatMap hdrop hbody).to_comp

/-- The spend pairs of a pass, as a function of the tuple of branching, source count, pass count
and pass index. -/
def spendPairsP (x : (ℕ × ℕ) × ℕ × ℕ) : List (ℕ × ℕ) :=
  rawSpendPairs x.1.1 x.1.2 x.2.1 x.2.2

/-- The spend pairs of a pass are computable in their parameters. -/
theorem computable_spendPairsP : Computable spendPairsP := by
  have hspare : Computable fun x : (ℕ × ℕ) × ℕ × ℕ => rawSparePairs x.1.1 x.1.2 :=
    computable_rawSparePairs.comp Computable.fst
  have hmul : Computable fun x : (ℕ × ℕ) × ℕ × ℕ => x.2.2 * x.2.1 :=
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)).to_comp
  have hdrop : Computable fun x : (ℕ × ℕ) × ℕ × ℕ =>
      (rawSparePairs x.1.1 x.1.2).drop (x.2.2 * x.2.1) :=
    (Primrec.list_drop (α := ℕ × ℕ)).to_comp.comp hmul hspare
  exact (Primrec.list_take (α := ℕ × ℕ)).to_comp.comp (Computable.fst.comp Computable.snd) hdrop

/-! ### The charged son request -/

/-- Packed arguments of the charged son request:
`(source, (threshold, eps), entries, i, c)`. -/
abbrev CSonArg := ℕ × (ℚ × ℚ) × List (RawSlot × ClientMove) × ℕ × ℕ

/-- Packed charged son request. -/
def chargedSonReq (x : CSonArg) : ℚ :=
  rawChargedSonRequest x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The charged son request is the raw son request on the source children and the raw son base on
the spare ones. -/
theorem chargedSonReq_eq_cond (x : CSonArg) :
    chargedSonReq x =
      cond (decide (x.2.2.2.2 < x.1))
        (rawSonRequest x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
        (rawSonBase x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  rw [chargedSonReq, rawChargedSonRequest]
  by_cases h : x.2.2.2.2 < x.1 <;> simp [h]

/-- The charged son request is computable in its arguments. -/
theorem computable_chargedSonReq : Computable chargedSonReq := by
  have hbase : Computable fun x : CSonArg => rawSonBase x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
    computable_rawSonBase.comp (Computable.snd.comp Computable.snd)
  have hreq : Computable fun x : CSonArg =>
      rawSonRequest x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
    computable_rawSonRequest.comp Computable.snd
  have hlt : Computable fun x : CSonArg => decide (x.2.2.2.2 < x.1) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
      Computable.fst
  exact (Computable.cond hlt hreq hbase).of_eq fun x => (chargedSonReq_eq_cond x).symm

/-! ### The charged root request -/

/-- Packed arguments of the charged root request:
`((source, threshold, eps), b, entries, i)`. -/
abbrev CRootArg := (ℕ × ℚ × ℚ) × ℕ × List (RawSlot × ClientMove) × ℕ

/-- Packed charged root request. -/
def chargedRootReq (x : CRootArg) : ℚ :=
  rawChargedRootRequest x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2

/-- The charged root request is the sum of the son requests over all children. -/
theorem chargedRootReq_eq_sum (x : CRootArg) :
    chargedRootReq x =
      ((List.range x.2.1).map fun c =>
        chargedSonReq (x.1.1, (x.1.2.1, x.1.2.2), x.2.2.1, x.2.2.2, c)).sum := rfl

/-- Reshape a root argument into a son argument. -/
theorem computable_chargedSonOfRoot :
    Computable fun z : CRootArg × ℕ =>
      chargedSonReq (z.1.1.1, (z.1.1.2.1, z.1.1.2.2), z.1.2.2.1, z.1.2.2.2, z.2) := by
  have h1 : Computable fun z : CRootArg × ℕ => z.1.1 :=
    Computable.fst.comp Computable.fst
  have h2 : Computable fun z : CRootArg × ℕ => z.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have harg : Computable fun z : CRootArg × ℕ =>
      ((z.1.1.1, (z.1.1.2.1, z.1.1.2.2), z.1.2.2.1, z.1.2.2.2, z.2) : CSonArg) :=
    (Computable.fst.comp h1).pair
      ((Computable.snd.comp h1).pair
        ((Computable.fst.comp h2).pair
          ((Computable.snd.comp h2).pair Computable.snd)))
  exact computable_chargedSonReq.comp harg

/-- The charged root request is computable in its arguments. -/
theorem computable_chargedRootReq : Computable chargedRootReq := by
  have hb : Computable fun x : CRootArg => x.2.1 := Computable.fst.comp Computable.snd
  have hlist : Computable fun x : CRootArg =>
      (List.range x.2.1).map fun c =>
        chargedSonReq (x.1.1, (x.1.2.1, x.1.2.2), x.2.2.1, x.2.2.2, c) :=
    Computable.list_map (Primrec.list_range.to_comp.comp hb)
      computable_chargedSonOfRoot.to₂
  have hadd : Computable₂ fun (_ : CRootArg) (u : ℚ × ℚ) => u.1 + u.2 :=
    (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hlist (Computable.const 0) hadd).of_eq fun x => ?_
  rw [chargedRootReq_eq_sum]
  exact (list_sum_rat_eq_foldr _).symm

/-! ### Deficient roots -/

/-- Packed arguments of the deficient-root scan:
`((n, b, source), (threshold, eps, alpha), frozen)`. -/
abbrev CDefArg := (ℕ × ℕ × ℕ) × (ℚ × ℚ × ℚ) × List RawRound

/-- Packed deficient-root scan. -/
def chargedDefRoots (x : CDefArg) : List ℕ :=
  rawChargedDeficientRoots x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2

/-- The deficient roots are the clients whose root request is below half the target. -/
theorem chargedDefRoots_eq_filter (x : CDefArg) :
    chargedDefRoots x =
      (List.range x.1.1).filter fun i =>
        decide (chargedRootReq ((x.1.2.2, x.2.1.1, x.2.1.2.1), x.1.2.1,
          rawFrozenEntries x.2.2, i) < x.2.1.2.2 / 2) := rfl

/-- The list of deficient roots is computable in its arguments. -/
theorem computable_chargedDefRoots : Computable chargedDefRoots := by
  have hn : Computable fun x : CDefArg => x.1.1 := Computable.fst.comp Computable.fst
  have hhalf : Computable fun x : CDefArg => x.2.1.2.2 / 2 :=
    (computable₂_ratMul.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd)))
      (Computable.const ((1 : ℚ) / 2))).of_eq fun _ => by ring
  have hroot : Computable fun z : CDefArg × ℕ =>
      chargedRootReq ((z.1.1.2.2, z.1.2.1.1, z.1.2.1.2.1), z.1.1.2.1,
        rawFrozenEntries z.1.2.2, z.2) := by
    have hsource : Computable fun z : CDefArg × ℕ => z.1.1.2.2 :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hthr : Computable fun z : CDefArg × ℕ => z.1.2.1.1 :=
      Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have heps : Computable fun z : CDefArg × ℕ => z.1.2.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
    have hb : Computable fun z : CDefArg × ℕ => z.1.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hentries : Computable fun z : CDefArg × ℕ => rawFrozenEntries z.1.2.2 :=
      computable_rawFrozenEntries.comp
        (Computable.snd.comp (Computable.snd.comp Computable.fst))
    have harg : Computable fun z : CDefArg × ℕ =>
        (((z.1.1.2.2, z.1.2.1.1, z.1.2.1.2.1), z.1.1.2.1,
          rawFrozenEntries z.1.2.2, z.2) : CRootArg) :=
      (hsource.pair (hthr.pair heps)).pair (hb.pair (hentries.pair Computable.snd))
    exact computable_chargedRootReq.comp harg
  have hpred : Computable₂ fun (x : CDefArg) (i : ℕ) =>
      decide (chargedRootReq ((x.1.2.2, x.2.1.1, x.2.1.2.1), x.1.2.1,
        rawFrozenEntries x.2.2, i) < x.2.1.2.2 / 2) :=
    ((Primrec.not.to_comp.comp
      (computable_ratLe.comp (hhalf.comp Computable.fst) hroot)).of_eq fun _ =>
        decide_rat_lt_eq _ _).to₂
  refine (computable_list_filter (Primrec.list_range.to_comp.comp hn) hpred).of_eq fun x => ?_
  exact (chargedDefRoots_eq_filter x).symm

/-! ### Spend slots -/

/-- Packed arguments of the spend-slot selection:
`((n, b, source, count, pass), (threshold, eps, alpha), frozen)`. -/
abbrev CSpendArg := (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℚ × ℚ × ℚ) × List RawRound

/-- Packed spend-slot selection. -/
def chargedSpendSlotsP (x : CSpendArg) : List RawSlot :=
  rawChargedSpendSlots x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2
    x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2

/-- The spend slots are the spend pairs of the pass, taken at every deficient root. -/
theorem chargedSpendSlotsP_eq_flatMap (x : CSpendArg) :
    chargedSpendSlotsP x =
      (chargedDefRoots ((x.1.1, x.1.2.1, x.1.2.2.1), x.2.1, x.2.2)).flatMap fun i =>
        (spendPairsP ((x.1.2.1, x.1.2.2.1), x.1.2.2.2.1, x.1.2.2.2.2)).map
          fun p => ((i, p.1, p.2) : RawSlot) := rfl

/-- The spend slots are computable in their arguments. -/
theorem computable_chargedSpendSlotsP : Computable chargedSpendSlotsP := by
  have hn : Computable fun x : CSpendArg => x.1.1 := Computable.fst.comp Computable.fst
  have hb : Computable fun x : CSpendArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hsource : Computable fun x : CSpendArg => x.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hcount : Computable fun x : CSpendArg => x.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hpass : Computable fun x : CSpendArg => x.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hrootarg : Computable fun x : CSpendArg =>
      (((x.1.1, x.1.2.1, x.1.2.2.1), x.2.1, x.2.2) : CDefArg) :=
    (hn.pair (hb.pair hsource)).pair
      ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))
  have hroots : Computable fun x : CSpendArg =>
      chargedDefRoots ((x.1.1, x.1.2.1, x.1.2.2.1), x.2.1, x.2.2) :=
    computable_chargedDefRoots.comp hrootarg
  have hpairarg : Computable fun x : CSpendArg =>
      (((x.1.2.1, x.1.2.2.1), x.1.2.2.2.1, x.1.2.2.2.2) : (ℕ × ℕ) × ℕ × ℕ) :=
    (hb.pair hsource).pair (hcount.pair hpass)
  have hpairs : Computable fun x : CSpendArg =>
      spendPairsP ((x.1.2.1, x.1.2.2.1), x.1.2.2.2.1, x.1.2.2.2.2) :=
    computable_spendPairsP.comp hpairarg
  have hbody : Computable fun z : CSpendArg × ℕ =>
      (spendPairsP ((z.1.1.2.1, z.1.1.2.2.1), z.1.1.2.2.2.1, z.1.1.2.2.2.2)).map
        fun p => ((z.2, p.1, p.2) : RawSlot) := by
    refine Computable.list_map (hpairs.comp Computable.fst) ?_
    exact ((Computable.snd.comp Computable.fst).pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.snd.comp Computable.snd))).to₂
  refine (computable_list_flatMap hroots hbody.to₂).of_eq fun x => ?_
  exact (chargedSpendSlotsP_eq_flatMap x).symm

/-! ### The depths of a spend pass -/

/-- The spend anchor `max (a+3) (e − (pass+1)L)` is computable. -/
theorem computable_grayChargedSpendEps {X : Type} [Primcodable X]
    {fa fL fe fp : X → ℕ} (ha : Computable fa) (hL : Computable fL)
    (he : Computable fe) (hp : Computable fp) :
    Computable fun x : X => grayChargedSpendEps (fa x) (fL x) (fe x) (fp x) := by
  have hbase : Computable fun x : X => fa x + 3 :=
    Primrec.nat_add.to_comp.comp ha (Computable.const 3)
  have hraw : Computable fun x : X => fe x - (fp x + 1) * fL x :=
    Primrec.nat_sub.to_comp.comp he
      (Primrec.nat_mul.to_comp.comp (Primrec.succ.to_comp.comp hp) hL)
  refine (Primrec.nat_add.to_comp.comp hbase
    (Primrec.nat_sub.to_comp.comp hraw hbase)).of_eq fun x => ?_
  unfold grayChargedSpendEps grayChargedSpendAlphaDepth
  omega

/-- The spend window's fine end is computable. -/
theorem computable_grayChargedSpendDelta {X : Type} [Primcodable X]
    {fa fL fe fp : X → ℕ} (ha : Computable fa) (hL : Computable fL)
    (he : Computable fe) (hp : Computable fp) :
    Computable fun x : X => grayChargedSpendDelta (fa x) (fL x) (fe x) (fp x) :=
  (Primrec.nat_add.to_comp.comp
    (computable_grayChargedSpendEps ha hL he hp) hL).of_eq fun _ => rfl

/-! ### Slots of one spend pass -/

/-- Packed arguments of the pass-slot selection: `((q, a, e), (n, b, pass), frozen)`. -/
abbrev CPassArg := (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × List RawRound

/-- Packed pass-slot selection. -/
def chargedPassSlots (x : CPassArg) : List RawSlot :=
  rawChargedSlotsForPass x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2

/-- The slots of a pass are the spend slots taken with the source count, spend count, threshold
and scales of the charged construction. -/
theorem chargedPassSlots_eq (x : CPassArg) :
    chargedPassSlots x =
      chargedSpendSlotsP
        ((x.2.1.1, x.2.1.2.1, grayChargedSourceCount x.1.2.1 x.1.2.2,
            grayChargedSpendCount x.1.1 x.1.2.1 x.1.2.2, x.2.1.2.2),
          (grayChargedThreshold x.1.1 x.1.2.2, dyadicScale x.1.2.2, dyadicScale x.1.2.1),
          x.2.2) := rfl

/-- The slots of a pass are computable in their arguments. -/
theorem computable_chargedPassSlots : Computable chargedPassSlots := by
  have hq : Computable fun x : CPassArg => x.1.1 := Computable.fst.comp Computable.fst
  have ha : Computable fun x : CPassArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have he : Computable fun x : CPassArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hn : Computable fun x : CPassArg => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb : Computable fun x : CPassArg => x.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hpass : Computable fun x : CPassArg => x.2.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have hfrozen : Computable fun x : CPassArg => x.2.2 :=
    Computable.snd.comp Computable.snd
  have hsource : Computable fun x : CPassArg => grayChargedSourceCount x.1.2.1 x.1.2.2 :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha)).of_eq fun _ => rfl
  have hcount : Computable fun x : CPassArg => grayChargedSpendCount x.1.1 x.1.2.1 x.1.2.2 :=
    (Computable.const 1).of_eq fun _ => rfl
  have hthr : Computable fun x : CPassArg => grayChargedThreshold x.1.1 x.1.2.2 :=
    (computable₂_rawThreshold.comp hq he).of_eq fun _ => rfl
  have heps : Computable fun x : CPassArg => dyadicScale x.1.2.2 :=
    computable_dyadicScale.comp he
  have halpha : Computable fun x : CPassArg => dyadicScale x.1.2.1 :=
    computable_dyadicScale.comp ha
  have harg : Computable fun x : CPassArg =>
      (((x.2.1.1, x.2.1.2.1, grayChargedSourceCount x.1.2.1 x.1.2.2,
          grayChargedSpendCount x.1.1 x.1.2.1 x.1.2.2, x.2.1.2.2),
        (grayChargedThreshold x.1.1 x.1.2.2, dyadicScale x.1.2.2, dyadicScale x.1.2.1),
        x.2.2) : CSpendArg) :=
    (hn.pair (hb.pair (hsource.pair (hcount.pair hpass)))).pair
      ((hthr.pair (heps.pair halpha)).pair hfrozen)
  refine (computable_chargedSpendSlotsP.comp harg).of_eq fun x => ?_
  exact (chargedPassSlots_eq x).symm

/-! ### The displayed charged move -/

/-- One row of the erased charged family move. -/
def chargedRowMove (y : CRootArg) : ClientMove :=
  graftTwoLevel (chargedRootReq y) y.2.1
    (fun c => if c < y.2.1 then
      chargedSonReq (y.1.1, (y.1.2.1, y.1.2.2), y.2.2.1, y.2.2.2, c) else 0)
    (fun c c' => if c < y.2.1 then
      (if c' < y.2.1 then rawEntryMove y.2.2.1 (y.2.2.2, c, c') else []) else [])

/-- The row of the displayed family move belonging to one client is computable in its arguments. -/
theorem computable_chargedRowMove : Computable chargedRowMove := by
  have hb : Computable fun y : CRootArg => y.2.1 := Computable.fst.comp Computable.snd
  have hentries : Computable fun y : CRootArg => y.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable fun y : CRootArg => y.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hson : Computable fun z : CRootArg × ℕ =>
      if z.2 < z.1.2.1 then
        chargedSonReq (z.1.1.1, (z.1.1.2.1, z.1.1.2.2), z.1.2.2.1, z.1.2.2.2, z.2)
      else 0 := by
    have hlt : Computable fun z : CRootArg × ℕ => decide (z.2 < z.1.2.1) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.snd
        (hb.comp Computable.fst)
    refine (Computable.cond hlt computable_chargedSonOfRoot (Computable.const 0)).of_eq
      fun z => ?_
    by_cases h : z.2 < z.1.2.1 <;> simp [h]
  have hg : Computable fun w : (CRootArg × ℕ) × ℕ =>
      if w.1.2 < w.1.1.2.1 then
        (if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) else [])
      else [] := by
    have hlt1 : Computable fun w : (CRootArg × ℕ) × ℕ => decide (w.1.2 < w.1.1.2.1) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp
        (Computable.snd.comp Computable.fst)
        (hb.comp (Computable.fst.comp Computable.fst))
    have hlt2 : Computable fun w : (CRootArg × ℕ) × ℕ => decide (w.2 < w.1.1.2.1) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.snd
        (hb.comp (Computable.fst.comp Computable.fst))
    have hmovearg : Computable fun w : (CRootArg × ℕ) × ℕ =>
        ((w.1.1.2.2.1, w.1.1.2.2.2, w.1.2, w.2) :
          List (RawSlot × ClientMove) × RawSlot) :=
      (hentries.comp (Computable.fst.comp Computable.fst)).pair
        ((hi.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hmove : Computable fun w : (CRootArg × ℕ) × ℕ =>
        rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) :=
      (computable_rawEntryMove.comp hmovearg).of_eq fun _ => rfl
    have hinner : Computable fun w : (CRootArg × ℕ) × ℕ =>
        if w.2 < w.1.1.2.1 then
          rawEntryMove w.1.1.2.2.1 (w.1.1.2.2.2, w.1.2, w.2) else ([] : ClientMove) := by
      refine (Computable.cond hlt2 hmove (Computable.const [])).of_eq fun w => ?_
      by_cases h : w.2 < w.1.1.2.1 <;> simp [h]
    refine (Computable.cond hlt1 hinner (Computable.const [])).of_eq fun w => ?_
    by_cases h : w.1.2 < w.1.1.2.1 <;> simp [h]
  exact (computable_graftTwoLevel (X := CRootArg)
    (froot := chargedRootReq)
    (fb := fun y : CRootArg => y.2.1)
    (fson := fun (y : CRootArg) (c : ℕ) => if c < y.2.1 then
      chargedSonReq (y.1.1, (y.1.2.1, y.1.2.2), y.2.2.1, y.2.2.2, c) else 0)
    (fg := fun (y : CRootArg) (c c' : ℕ) => if c < y.2.1 then
      (if c' < y.2.1 then rawEntryMove y.2.2.1 (y.2.2.2, c, c') else []) else [])
    computable_chargedRootReq hb hson hg).of_eq fun _ => rfl

/-- Packed arguments of the erased charged family move:
`((source, threshold, eps), (n, b), frozen, slots, current)`. -/
abbrev CFamArg := (ℕ × ℚ × ℚ) × (ℕ × ℕ) × List RawRound × List RawSlot × FamilyClientMove

/-- Packed erased charged family move. -/
def chargedFamMoveP (x : CFamArg) : FamilyClientMove :=
  rawChargedFamilyMove x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The displayed family move is the list of the rows of its clients. -/
theorem chargedFamMoveP_eq_map (x : CFamArg) :
    chargedFamMoveP x =
      (List.range x.2.1.1).map fun i =>
        chargedRowMove (x.1, x.2.1.2, rawEntries x.2.2.1 x.2.2.2.1 x.2.2.2.2, i) := rfl

/-- The displayed family move is computable in its arguments. -/
theorem computable_chargedFamMoveP : Computable chargedFamMoveP := by
  have hn : Computable fun x : CFamArg => x.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hb : Computable fun x : CFamArg => x.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hentries : Computable fun x : CFamArg =>
      rawEntries x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
    computable_rawEntries.comp (Computable.snd.comp Computable.snd)
  have harg : Computable fun z : CFamArg × ℕ =>
      ((z.1.1, z.1.2.1.2, rawEntries z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2, z.2) : CRootArg) :=
    (Computable.fst.comp Computable.fst).pair
      ((hb.comp Computable.fst).pair
        ((hentries.comp Computable.fst).pair Computable.snd))
  have hbody : Computable₂ fun (x : CFamArg) (i : ℕ) =>
      chargedRowMove (x.1, x.2.1.2, rawEntries x.2.2.1 x.2.2.2.1 x.2.2.2.2, i) :=
    (computable_chargedRowMove.comp harg).to₂
  refine (Computable.list_map (Primrec.list_range.to_comp.comp hn) hbody).of_eq fun x => ?_
  exact (chargedFamMoveP_eq_map x).symm

/-! ### The displayed output -/

/-- Packed arguments of the erased charged output:
`((q, a, e), (n, b), tag, state, current)`. -/
abbrev COutArg := (ℕ × ℕ × ℕ) × (ℕ × ℕ) × ℕ × RawState × FamilyClientMove

/-- Packed erased charged output. -/
def chargedOutP (x : COutArg) : FamilyClientMove :=
  rawChargedOutput x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The raw charged output is the displayed family move built from the source count, threshold
and scale of the construction, with an empty current move in the `done` phase. -/
theorem chargedOutP_eq (x : COutArg) :
    chargedOutP x =
      chargedFamMoveP
        ((grayChargedSourceCount x.1.2.1 x.1.2.2, grayChargedThreshold x.1.1 x.1.2.2,
            dyadicScale x.1.2.2),
          x.2.1,
          x.2.2.2.1.2.1, x.2.2.2.1.2.2.2.1,
          (if x.2.2.1 = 1 then [] else
            if x.2.2.2.1.2.2.2.1.isEmpty then [] else x.2.2.2.2)) := rfl

/-- The raw charged output is computable in its arguments. -/
theorem computable_chargedOutP : Computable chargedOutP := by
  have hq : Computable fun x : COutArg => x.1.1 := Computable.fst.comp Computable.fst
  have ha : Computable fun x : COutArg => x.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have he : Computable fun x : COutArg => x.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have htag : Computable fun x : COutArg => x.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hst : Computable fun x : COutArg => x.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hcur : Computable fun x : COutArg => x.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hfrozen : Computable fun x : COutArg => x.2.2.2.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hst)
  have hslots : Computable fun x : COutArg => x.2.2.2.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp hst)))
  have hsource : Computable fun x : COutArg => grayChargedSourceCount x.1.2.1 x.1.2.2 :=
    (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
      (Primrec.nat_sub.to_comp.comp he ha)).of_eq fun _ => rfl
  have hthr : Computable fun x : COutArg => grayChargedThreshold x.1.1 x.1.2.2 :=
    (computable₂_rawThreshold.comp hq he).of_eq fun _ => rfl
  have heps : Computable fun x : COutArg => dyadicScale x.1.2.2 :=
    computable_dyadicScale.comp he
  have hemp : Computable fun x : COutArg => x.2.2.2.1.2.2.2.1.isEmpty := by
    have hz : Computable fun x : COutArg => decide (x.2.2.2.1.2.2.2.1.length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hisone : Computable fun x : COutArg => decide (x.2.2.1 = 1) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp htag (Computable.const 1)
  have hinner : Computable fun x : COutArg =>
      (if x.2.2.2.1.2.2.2.1.isEmpty then [] else x.2.2.2.2 : FamilyClientMove) := by
    refine (Computable.cond hemp (Computable.const []) hcur).of_eq fun x => ?_
    cases hx : x.2.2.2.1.2.2.2.1.isEmpty <;> simp
  have hcurrent : Computable fun x : COutArg =>
      (if x.2.2.1 = 1 then [] else
        if x.2.2.2.1.2.2.2.1.isEmpty then [] else x.2.2.2.2 : FamilyClientMove) := by
    refine (Computable.cond hisone (Computable.const []) hinner).of_eq fun x => ?_
    by_cases hx : x.2.2.1 = 1 <;> simp [hx]
  have harg : Computable fun x : COutArg =>
      (((grayChargedSourceCount x.1.2.1 x.1.2.2, grayChargedThreshold x.1.1 x.1.2.2,
          dyadicScale x.1.2.2),
        x.2.1,
        x.2.2.2.1.2.1, x.2.2.2.1.2.2.2.1,
        (if x.2.2.1 = 1 then [] else
          if x.2.2.2.1.2.2.2.1.isEmpty then [] else x.2.2.2.2)) : CFamArg) :=
    (hsource.pair (hthr.pair heps)).pair
      ((Computable.fst.comp Computable.snd).pair
        (hfrozen.pair (hslots.pair hcurrent)))
  refine (computable_chargedFamMoveP.comp harg).of_eq fun x => ?_
  exact (chargedOutP_eq x).symm


/-! ### Computability of the erased snapshot harvest -/

/-- `isPrefixOf` form of the erased foreign test. -/
lemma rawGrayNodeForeignB_eq_isPrefixOf (slots : List RawSlot) (i : ℕ)
    (x : GacsDayNode) :
    rawGrayNodeForeignB slots i x =
      slots.all fun s =>
        (!decide (i = s.1)) ||
          !(x.isPrefixOf [s.2.1, s.2.2] || [s.2.1, s.2.2].isPrefixOf x) := by
  unfold rawGrayNodeForeignB
  congr 1
  funext s
  rw [decide_not, isPrefixOf_eq_decide, isPrefixOf_eq_decide]
  simp

/-- The raw harvest is computable in any computable parameters. -/
theorem computable_rawGrayHarvest {X : Type} [Primcodable X]
    {fd fb : X → ℕ} {fs : X → List RawSlot} {fn : X → ℕ}
    {fm : X → FamilyServerMove}
    (hd : Computable fd) (hb : Computable fb) (hs : Computable fs)
    (hn : Computable fn) (hm : Computable fm) :
    Computable fun x : X => rawGrayHarvest (fd x) (fb x) (fs x) (fn x) (fm x) := by
  have hrange : Computable fun x : X => List.range (fn x) :=
    Primrec.list_range.to_comp.comp hn
  have hmove : Computable fun z : X × ℕ => familyServerMoveAt (fm z.1) z.2 :=
    (Primrec.list_getD ([] : ServerMove)).to_comp.comp (hm.comp Computable.fst)
      Computable.snd
  have htags : Computable fun z : X × ℕ =>
      (familyServerMoveAt (fm z.1) z.2).map Prod.fst :=
    Computable.list_map hmove (Computable.fst.comp Computable.snd).to₂
  have hx3 : Computable fun w : (X × ℕ) × GacsDayNode => w.1.1 :=
    Computable.fst.comp Computable.fst
  have hi3 : Computable fun w : (X × ℕ) × GacsDayNode => w.1.2 :=
    Computable.snd.comp Computable.fst
  have hnd3 : Computable fun w : (X × ℕ) × GacsDayNode => w.2 := Computable.snd
  have hvalid : Computable fun w : (X × ℕ) × GacsDayNode =>
      grayNodeValidB (fb w.1.1) w.2 := by
    have hp : Computable₂ fun (w : (X × ℕ) × GacsDayNode) (d : ℕ) =>
        decide (d < fb w.1.1) :=
      ((PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.snd
        ((hb.comp hx3).comp Computable.fst)).to₂
    exact (computable_list_all hnd3 hp).of_eq fun w => rfl
  have hforeign : Computable fun w : (X × ℕ) × GacsDayNode =>
      rawGrayNodeForeignB (fs w.1.1) w.1.2 w.2 := by
    have hnodeS : Computable fun r :
        (((X × ℕ) × GacsDayNode) × RawSlot) => ([r.2.2.1, r.2.2.2] : GacsDayNode) :=
      Computable.list_cons.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.list_cons.comp
          (Computable.snd.comp (Computable.snd.comp Computable.snd))
          (Computable.const []))
    have hp : Computable₂ fun (w : (X × ℕ) × GacsDayNode) (s : RawSlot) =>
        ((!decide (w.1.2 = s.1)) ||
          !(w.2.isPrefixOf [s.2.1, s.2.2] || [s.2.1, s.2.2].isPrefixOf w.2)) := by
      have hne : Computable fun r : (((X × ℕ) × GacsDayNode) × RawSlot) =>
          (!decide (r.1.1.2 = r.2.1)) :=
        Primrec.not.to_comp.comp
          ((PrimrecRel.decide Primrec.eq).to_comp.comp
            (hi3.comp Computable.fst) (Computable.fst.comp Computable.snd))
      have hpre1 : Computable fun r : (((X × ℕ) × GacsDayNode) × RawSlot) =>
          r.1.2.isPrefixOf [r.2.2.1, r.2.2.2] :=
        primrec₂_isPrefixOf_gen.to_comp.comp
          (hnd3.comp Computable.fst) hnodeS
      have hpre2 : Computable fun r : (((X × ℕ) × GacsDayNode) × RawSlot) =>
          ([r.2.2.1, r.2.2.2] : GacsDayNode).isPrefixOf r.1.2 :=
        primrec₂_isPrefixOf_gen.to_comp.comp hnodeS
          (hnd3.comp Computable.fst)
      exact (Primrec.or.to_comp.comp hne
        (Primrec.not.to_comp.comp
          (Primrec.or.to_comp.comp hpre1 hpre2))).to₂
    exact (computable_list_all (hs.comp hx3) hp).of_eq fun w =>
      (rawGrayNodeForeignB_eq_isPrefixOf (fs w.1.1) w.1.2 w.2).symm
  have htest : Computable fun w : (X × ℕ) × GacsDayNode =>
      (grayNodeValidB (fb w.1.1) w.2 &&
        rawGrayNodeForeignB (fs w.1.1) w.1.2 w.2) := by
    refine (Computable.cond hvalid hforeign (Computable.const false)).of_eq
      fun w => ?_
    cases h : grayNodeValidB (fb w.1.1) w.2 <;> simp
  have hmoveW : Computable fun w : (X × ℕ) × GacsDayNode =>
      familyServerMoveAt (fm w.1.1) w.1.2 :=
    hmove.comp Computable.fst
  have hallocW : Computable fun w : (X × ℕ) × GacsDayNode =>
      getAlloc (familyServerMoveAt (fm w.1.1) w.1.2) w.2 :=
    primrec₂_getAlloc.to_comp.comp hmoveW hnd3
  have hthen : Computable fun w : (X × ℕ) × GacsDayNode =>
      (getAlloc (familyServerMoveAt (fm w.1.1) w.1.2) w.2).map
        (fun c => c.take (fd w.1.1)) :=
    Computable.list_map hallocW
      (Primrec.list_take.to_comp.comp ((hd.comp hx3).comp Computable.fst) Computable.snd).to₂
  have hbody : Computable fun w : (X × ℕ) × GacsDayNode =>
      (if grayNodeValidB (fb w.1.1) w.2 &&
          rawGrayNodeForeignB (fs w.1.1) w.1.2 w.2 then
        (getAlloc (familyServerMoveAt (fm w.1.1) w.1.2) w.2).map
          (fun c => c.take (fd w.1.1))
      else ([] : Allocation)) := by
    refine (Computable.cond htest hthen (Computable.const [])).of_eq fun w => ?_
    cases h : (grayNodeValidB (fb w.1.1) w.2 &&
        rawGrayNodeForeignB (fs w.1.1) w.1.2 w.2) <;> simp
  have hinner : Computable fun z : X × ℕ =>
      ((familyServerMoveAt (fm z.1) z.2).map Prod.fst).flatMap fun nd =>
        (if grayNodeValidB (fb z.1) nd &&
            rawGrayNodeForeignB (fs z.1) z.2 nd then
          (getAlloc (familyServerMoveAt (fm z.1) z.2) nd).map
            (fun c => c.take (fd z.1))
        else ([] : Allocation)) :=
    computable_list_flatMap htags hbody.to₂
  refine (computable_list_flatMap hrange hinner.to₂).of_eq fun x => ?_
  rfl


end Kolmogorov
