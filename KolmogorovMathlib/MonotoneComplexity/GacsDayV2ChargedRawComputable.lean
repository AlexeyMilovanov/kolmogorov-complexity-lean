import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ChargedRaw
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedRawComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustGrayComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayTailReserveComputable

/-!
# Computability of the erased V2 controller components

Every mirror introduced in `GacsDayV2ChargedRaw.lean` is shown here to be
computable, jointly in all its arguments.  The V1 twins of this module are
`GacsDayChargedRawComputable.lean` (the erased spend layout) and the first
half of `GacsDayChargedStepComputable.lean` (the phase-tagged pieces); the
record-agnostic leaves (`rawGrayHarvest`, `rawFrozenSonBase`,
`rawChargedDeficientRoots`, `rawSparePairs`, `rawLocalServerMove`,
`rawGlobalQuarterB`, `rawNextSlots`) are reused from them unchanged.

What is genuinely new on the V2 side, and proved here:

* the **pinned footprint schedule** `grayFootprint` and the derived
  `graySpendSpan` — a four-case `Nat` recursion, turned into a plain
  `Nat.rec` exactly as `canonicalGrayLossRec` does for V1's
  `canonicalGrayLoss`;
* the **block multiplicities and cumulative offsets** `graySpendMult`,
  `grayBlockSpendOffset`, `grayAdvBlockMult`, `grayAdvBlockOffset` (two more
  `Nat.rec` accumulations);
* the **wide advantage slot geometry** `rawAdvBlockGrandsons`,
  `rawAdvBlockSlots`, `rawBlockNextSlots`;
* the **wide spend block geometry** `rawBlockSpendPairs`,
  `rawBlockSpendSlotsV2`, `rawChargedSlotsForPassV2`, together with the erased
  V1 view `rawFrozenV1OfV2` of a raw V2 ledger;
* the **v15.1 raised-service wait** `servesB`, `rawChargedRaisedServedB`,
  `rawChargedWaitServedB` — V1 has no analogue at all (its mirror of the wait
  test is the constant `rawWaitingB _ := false`);
* the two **block acceptance goals** `grayChargedBlockGoalAtB` and
  `grayChargedBlockSpendGoalAtB`, both instances of the joint charged-goal
  search `computable_familyChargedGrayGoalAtB_joint`;
* the phase entry points `rawChargedStartSpendV2`, `rawInitialStateV2` and the
  child query `rawChargedQueryV2`.

Statements are given in the open form `Computable fun x : X => …` with the
arguments supplied as computable functions of an arbitrary `Primcodable`
parameter `X` (the style of `computable_rawGrayHarvest`), so that the step
assembler of the next module can compose them without repacking.
-/


namespace Kolmogorov

/-! ### The pinned footprint schedule -/

/-- The plain `Nat.rec` presentation of the pinned footprint schedule (the V2
twin of `canonicalGrayLossRec`). -/
def grayFootprintRec : ℕ → ℕ := fun n =>
  Nat.rec 3 (fun k prev =>
    if k ≤ 1 then 3
    else (256 * (k + 1) ^ 2 + 8) * prev + 256 * (k + 1) + 3) n

/-- The recursive form of the gray footprint agrees with its definition. -/
theorem grayFootprintRec_eq (n : ℕ) : grayFootprintRec n = grayFootprint n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rcases k with _ | _ | k
      · rfl
      · rfl
      · simp only [grayFootprintRec] at ih ⊢
        rw [if_neg (by omega), ih]
        exact (grayFootprint_succ (by omega)).symm

/-- The pinned footprint schedule is primitive recursive. -/
theorem primrec_grayFootprint : Primrec grayFootprint := by
  have hk1 : Primrec fun p : ℕ × ℕ => p.1 + 1 := Primrec.succ.comp Primrec.fst
  have hsq : Primrec fun p : ℕ × ℕ => (p.1 + 1) * (p.1 + 1) :=
    Primrec.nat_mul.comp hk1 hk1
  have hbody : Primrec fun p : ℕ × ℕ =>
      (256 * (p.1 + 1) ^ 2 + 8) * p.2 + 256 * (p.1 + 1) + 3 := by
    refine (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 256) hsq) (Primrec.const 8))
          Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.const 256) hk1))
      (Primrec.const 3)).of_eq fun p => ?_
    ring
  have hstep : Primrec₂ fun (_ : ℕ) (p : ℕ × ℕ) =>
      if p.1 ≤ 1 then 3
      else (256 * (p.1 + 1) ^ 2 + 8) * p.2 + 256 * (p.1 + 1) + 3 :=
    (Primrec.ite (PrimrecRel.comp Primrec.nat_le Primrec.fst (Primrec.const 1))
      (Primrec.const 3) hbody).comp Primrec.snd
  exact (Primrec.nat_rec' Primrec.id (Primrec.const 3) hstep).of_eq grayFootprintRec_eq

/-- The spend span of a stage is primitive recursive. -/
theorem primrec_graySpendSpan : Primrec graySpendSpan :=
  (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8)
      (primrec_grayFootprint.comp
        (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))))
    (Primrec.const 3)).of_eq fun _ => rfl

/-! ### Block multiplicities and cumulative offsets -/

/-- The spend multiplicity `2^{(7−i)L}` is primitive recursive. -/
theorem primrec₂_graySpendMult : Primrec₂ graySpendMult :=
  (nat_pow_primrec₂.comp (Primrec.const 2)
    (Primrec.nat_mul.comp
      (Primrec.nat_sub.comp (Primrec.const 7) Primrec.snd) Primrec.fst)).of_eq
    fun _ => rfl

/-- The plain `Nat.rec` presentation of the cumulative spend offset. -/
def grayBlockSpendOffsetRec (L n : ℕ) : ℕ :=
  Nat.rec 0 (fun i prev => prev + graySpendMult L i) n

/-- The recursive form of the block spend offset agrees with its definition. -/
theorem grayBlockSpendOffsetRec_eq (L n : ℕ) :
    grayBlockSpendOffsetRec L n = grayBlockSpendOffset L n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [grayBlockSpendOffsetRec] at ih ⊢
      rw [ih]
      rfl

/-- The cumulative spend-block offset is primitive recursive. -/
theorem primrec₂_grayBlockSpendOffset : Primrec₂ grayBlockSpendOffset := by
  have hstep : Primrec₂ fun (a : ℕ × ℕ) (p : ℕ × ℕ) =>
      p.2 + graySpendMult a.1 p.1 := by
    have h1 : Primrec fun z : (ℕ × ℕ) × ℕ × ℕ => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have h2 : Primrec fun z : (ℕ × ℕ) × ℕ × ℕ => graySpendMult z.1.1 z.2.1 :=
      primrec₂_graySpendMult.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    exact Primrec.nat_add.comp h1 h2
  exact (Primrec.nat_rec' Primrec.snd (Primrec.const 0) hstep).of_eq fun p =>
    grayBlockSpendOffsetRec_eq p.1 p.2

/-- The advantage-block multiplicity `2^{(roundCount−1−r)L}` is primitive
recursive. -/
theorem primrec_grayAdvBlockMult :
    Primrec fun x : ℕ × ℕ × ℕ => grayAdvBlockMult x.1 x.2.1 x.2.2 :=
  (nat_pow_primrec₂.comp (Primrec.const 2)
    (Primrec.nat_mul.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          (primrec_grayTailRoundCount.comp Primrec.fst) (Primrec.const 1))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd))).of_eq fun _ => rfl

/-- The plain `Nat.rec` presentation of the cumulative advantage offset. -/
def grayAdvBlockOffsetRec (q L n : ℕ) : ℕ :=
  Nat.rec 0 (fun r prev => prev + grayAdvBlockMult q L r) n

/-- The recursive form of the adversary block offset agrees with its definition. -/
theorem grayAdvBlockOffsetRec_eq (q L n : ℕ) :
    grayAdvBlockOffsetRec q L n = grayAdvBlockOffset q L n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [grayAdvBlockOffsetRec] at ih ⊢
      rw [ih]
      rfl

/-- The cumulative advantage-block offset is primitive recursive. -/
theorem primrec_grayAdvBlockOffset :
    Primrec fun x : ℕ × ℕ × ℕ => grayAdvBlockOffset x.1 x.2.1 x.2.2 := by
  have hstep : Primrec₂ fun (a : ℕ × ℕ × ℕ) (p : ℕ × ℕ) =>
      p.2 + grayAdvBlockMult a.1 a.2.1 p.1 := by
    have h1 : Primrec fun z : (ℕ × ℕ × ℕ) × ℕ × ℕ => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have h2 : Primrec fun z : (ℕ × ℕ × ℕ) × ℕ × ℕ =>
        grayAdvBlockMult z.1.1 z.1.2.1 z.2.1 :=
      primrec_grayAdvBlockMult.comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
            (Primrec.fst.comp Primrec.snd)))
    exact Primrec.nat_add.comp h1 h2
  exact (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd) (Primrec.const 0)
    hstep).of_eq fun x => grayAdvBlockOffsetRec_eq x.1 x.2.1 x.2.2

/-! ### Numeric spend anchors -/

/-- The source-son count `2^{e−a}` is computable. -/
theorem computable_grayChargedSourceCount {X : Type} [Primcodable X]
    {fa fe : X → ℕ} (ha : Computable fa) (he : Computable fe) :
    Computable fun x : X => grayChargedSourceCount (fa x) (fe x) :=
  (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
    (Primrec.nat_sub.to_comp.comp he ha)).of_eq fun _ => rfl

/-- The round threshold is computable. -/
theorem computable_grayChargedThreshold {X : Type} [Primcodable X]
    {fq fe : X → ℕ} (hq : Computable fq) (he : Computable fe) :
    Computable fun x : X => grayChargedThreshold (fq x) (fe x) :=
  (computable₂_rawThreshold.comp hq he).of_eq fun _ => rfl

/-! ### The two V2 block acceptance goals -/

/-- The re-anchored advantage goal is computable jointly in its arguments. -/
theorem computable_grayChargedBlockGoalAtB {X : Type} [Primcodable X]
    {fq fL fe fr fn : X → ℕ} {fA : X → Allocation}
    {fc : X → FamilyClientMove} {fs : X → FamilyServerMove}
    (hq : Computable fq) (hL : Computable fL) (he : Computable fe)
    (hr : Computable fr) (hn : Computable fn) (hA : Computable fA)
    (hc : Computable fc) (hs : Computable fs) :
    Computable fun x : X =>
      grayChargedBlockGoalAtB (fq x) (fL x) (fe x) (fr x) (fn x) (fA x)
        (fc x) (fs x) := by
  have harg : Computable fun x : X =>
      ((fq x, fL x, fe x, fr x) : ℕ × ℕ × ℕ × ℕ) :=
    hq.pair (hL.pair (he.pair hr))
  have heps : Computable fun x : X =>
      grayTailRoundEps (fq x) (fL x) (fe x) (fr x) :=
    computable_grayTailRoundEps.comp harg
  -- `grayTailRoundDelta` is `grayTailRoundEps + L`: adding to the already
  -- established `heps` keeps the unifier away from a deep `whnf` on the
  -- unfolded round definition, which composing `computable_grayTailRoundDelta`
  -- with the packed argument would trigger.
  have hdelta : Computable fun x : X =>
      grayTailRoundDelta (fq x) (fL x) (fe x) (fr x) :=
    (Primrec.nat_add.to_comp.comp heps hL).of_eq fun _ => rfl
  have halpha : Computable fun x : X =>
      dyadicScale (grayTailRoundEps (fq x) (fL x) (fe x) (fr x)) :=
    computable_dyadicScale.comp heps
  have hbeta : Computable fun x : X =>
      (3 / 4 : ℚ) * dyadicScale (grayTailRoundEps (fq x) (fL x) (fe x) (fr x)) :=
    computable₂_ratMul.comp (Computable.const ((3 : ℚ) / 4)) halpha
  have hkappa : Computable fun x : X => halfAmplification (fq x) :=
    computable_halfAmplification.comp hq
  exact (computable_familyChargedGrayGoalAtB_joint.comp
    (((Computable.const (4 : ℚ)).pair (hkappa.pair (halpha.pair hbeta))).pair
      ((heps.pair (hdelta.pair hn)).pair
        (hA.pair (hc.pair hs))))).of_eq fun _ => rfl

/-- The V2 spend goal is computable jointly in its arguments. -/
theorem computable_grayChargedBlockSpendGoalAtB {X : Type} [Primcodable X]
    {fq fL fa fe fp fn : X → ℕ} {fA : X → Allocation}
    {fc : X → FamilyClientMove} {fs : X → FamilyServerMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hp : Computable fp) (hn : Computable fn)
    (hA : Computable fA) (hc : Computable fc) (hs : Computable fs) :
    Computable fun x : X =>
      grayChargedBlockSpendGoalAtB (fq x) (fL x) (fa x) (fe x) (fp x) (fn x)
        (fA x) (fc x) (fs x) := by
  have heps : Computable fun x : X =>
      grayChargedSpendEps (fa x) (fL x) (fe x) (fp x) :=
    computable_grayChargedSpendEps ha hL he hp
  have hdelta : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) (fp x) :=
    computable_grayChargedSpendDelta ha hL he hp
  have halpha : Computable fun x : X =>
      dyadicScale (grayChargedSpendEps (fa x) (fL x) (fe x) (fp x)) :=
    computable_dyadicScale.comp heps
  have hbeta : Computable fun x : X =>
      (3 / 4 : ℚ) *
        dyadicScale (grayChargedSpendEps (fa x) (fL x) (fe x) (fp x)) :=
    computable₂_ratMul.comp (Computable.const ((3 : ℚ) / 4)) halpha
  have hkappa : Computable fun x : X => halfAmplification (fq x) :=
    computable_halfAmplification.comp hq
  exact (computable_familyChargedGrayGoalAtB_joint.comp
    (((Computable.const (4 : ℚ)).pair (hkappa.pair (halpha.pair hbeta))).pair
      ((heps.pair (hdelta.pair hn)).pair
        (hA.pair (hc.pair hs))))).of_eq fun _ => rfl

/-! ### The erased V1 view of a raw V2 ledger -/

/-- Forgetting the block data of a raw V2 round is computable. -/
theorem computable_rawRoundV2ToV1 : Computable rawRoundV2ToV1 := by
  have hidx : Computable fun p : RawRoundV2 => p.1 := Computable.fst
  have h1 : Computable fun p : RawRoundV2 => p.1.1 := Computable.fst.comp hidx
  have h2 : Computable fun p : RawRoundV2 => p.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp hidx)
  have h3 : Computable fun p : RawRoundV2 => p.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hidx))
  exact ((h1.pair (h2.pair h3)).pair Computable.snd).of_eq fun _ => rfl

/-- Forgetting the block data of the raw V2 frozen rounds is computable. -/
theorem computable_rawFrozenV1OfV2 {X : Type} [Primcodable X]
    {ff : X → List RawRoundV2} (hf : Computable ff) :
    Computable fun x : X => rawFrozenV1OfV2 (ff x) :=
  (Computable.list_map hf
    (computable_rawRoundV2ToV1.comp Computable.snd).to₂).of_eq fun _ => rfl

/-! ### The wide advantage slot geometry -/

/-- The advantage-block multiplicity is computable jointly in its arguments
(built from primitives, so that the composition stays cheap). -/
theorem computable_grayAdvBlockMult {X : Type} [Primcodable X]
    {fq fL fr : X → ℕ} (hq : Computable fq) (hL : Computable fL)
    (hr : Computable fr) :
    Computable fun x : X => grayAdvBlockMult (fq x) (fL x) (fr x) :=
  (nat_pow_primrec₂.to_comp.comp (Computable.const 2)
    (Primrec.nat_mul.to_comp.comp
      (Primrec.nat_sub.to_comp.comp
        (Primrec.nat_sub.to_comp.comp
          (primrec_grayTailRoundCount.to_comp.comp hq) (Computable.const 1))
        hr)
      hL)).of_eq fun _ => rfl

/-- The cumulative advantage-block offset is computable jointly in its
arguments. -/
theorem computable_grayAdvBlockOffset {X : Type} [Primcodable X]
    {fq fL fr : X → ℕ} (hq : Computable fq) (hL : Computable fL)
    (hr : Computable fr) :
    Computable fun x : X => grayAdvBlockOffset (fq x) (fL x) (fr x) :=
  primrec_grayAdvBlockOffset.to_comp.comp (hq.pair (hL.pair hr))

/-- The grandchildren of an adversary block are computable in computable parameters. -/
theorem computable_rawAdvBlockGrandsons {X : Type} [Primcodable X]
    {fb fq fL fr : X → ℕ} (hb : Computable fb) (hq : Computable fq)
    (hL : Computable fL) (hr : Computable fr) :
    Computable fun x : X => rawAdvBlockGrandsons (fb x) (fq x) (fL x) (fr x) := by
  have hdrop : Computable fun x : X =>
      (List.range (fb x)).drop (grayAdvBlockOffset (fq x) (fL x) (fr x)) :=
    (Primrec.list_drop (α := ℕ)).to_comp.comp
      (Primrec.list_range.to_comp.comp hb) (computable_grayAdvBlockOffset hq hL hr)
  exact ((Primrec.list_take (α := ℕ)).to_comp.comp hdrop
    (computable_grayAdvBlockMult hq hL hr)).of_eq fun _ => rfl

/-- The slots of an adversary block are computable in computable parameters. -/
theorem computable_rawAdvBlockSlots {X : Type} [Primcodable X]
    {fn fb fused fq fL fr : X → ℕ} (hn : Computable fn) (hb : Computable fb)
    (hused : Computable fused) (hq : Computable fq) (hL : Computable fL)
    (hr : Computable fr) :
    Computable fun x : X =>
      rawAdvBlockSlots (fn x) (fb x) (fused x) (fq x) (fL x) (fr x) := by
  have hcols : Computable fun x : X =>
      (List.range (fb x)).filter fun c => decide (c < fused x) := by
    refine computable_list_filter (Primrec.list_range.to_comp.comp hb) ?_
    exact ((PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.snd
      (hused.comp Computable.fst)).to₂
  have hgrand : Computable fun x : X =>
      rawAdvBlockGrandsons (fb x) (fq x) (fL x) (fr x) :=
    computable_rawAdvBlockGrandsons hb hq hL hr
  have hinner : Computable fun w : (X × ℕ) × ℕ =>
      (rawAdvBlockGrandsons (fb w.1.1) (fq w.1.1) (fL w.1.1) (fr w.1.1)).map
        fun g => ((w.1.2, w.2, g) : RawSlot) := by
    refine Computable.list_map
      (hgrand.comp (Computable.fst.comp Computable.fst)) ?_
    exact ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  have hrow : Computable fun z : X × ℕ =>
      ((List.range (fb z.1)).filter fun c => decide (c < fused z.1)).flatMap
        fun c => (rawAdvBlockGrandsons (fb z.1) (fq z.1) (fL z.1) (fr z.1)).map
          fun g => ((z.2, c, g) : RawSlot) :=
    computable_list_flatMap (hcols.comp Computable.fst) hinner.to₂
  exact (computable_list_flatMap (Primrec.list_range.to_comp.comp hn)
    hrow.to₂).of_eq fun _ => rfl

/-! ### The wide spend block geometry -/

/-- The spend pairs of a block pass are computable in computable parameters. -/
theorem computable_rawBlockSpendPairs {X : Type} [Primcodable X]
    {fb fsource fL fp : X → ℕ} (hb : Computable fb) (hsource : Computable fsource)
    (hL : Computable fL) (hp : Computable fp) :
    Computable fun x : X =>
      rawBlockSpendPairs (fb x) (fsource x) (fL x) (fp x) := by
  have hspare : Computable fun x : X => rawSparePairs (fb x) (fsource x) :=
    computable_rawSparePairs.comp (hb.pair hsource)
  have hoff : Computable fun x : X => grayBlockSpendOffset (fL x) (fp x) :=
    primrec₂_grayBlockSpendOffset.to_comp.comp hL hp
  have hmult : Computable fun x : X => graySpendMult (fL x) (fp x) :=
    primrec₂_graySpendMult.to_comp.comp hL hp
  exact ((Primrec.list_take (α := ℕ × ℕ)).to_comp.comp
    ((Primrec.list_drop (α := ℕ × ℕ)).to_comp.comp hspare hoff) hmult).of_eq
    fun _ => rfl

/-- The spend slots of a block pass are computable in computable parameters. -/
theorem computable_rawBlockSpendSlotsV2 {X : Type} [Primcodable X]
    {fn fb fsource fL fp : X → ℕ} {fthr feps falpha : X → ℚ}
    {ffr : X → List RawRound}
    (hn : Computable fn) (hb : Computable fb) (hsource : Computable fsource)
    (hL : Computable fL) (hp : Computable fp) (hthr : Computable fthr)
    (heps : Computable feps) (halpha : Computable falpha)
    (hfr : Computable ffr) :
    Computable fun x : X =>
      rawBlockSpendSlotsV2 (fn x) (fb x) (fsource x) (fL x) (fp x)
        (fthr x) (feps x) (falpha x) (ffr x) := by
  have hroots : Computable fun x : X =>
      chargedDefRoots (((fn x, fb x, fsource x),
        (fthr x, feps x, falpha x), ffr x) : CDefArg) :=
    computable_chargedDefRoots.comp
      ((hn.pair (hb.pair hsource)).pair
        ((hthr.pair (heps.pair halpha)).pair hfr))
  have hpairs : Computable fun x : X =>
      rawBlockSpendPairs (fb x) (fsource x) (fL x) (fp x) :=
    computable_rawBlockSpendPairs hb hsource hL hp
  have hbody : Computable fun z : X × ℕ =>
      (rawBlockSpendPairs (fb z.1) (fsource z.1) (fL z.1) (fp z.1)).map
        fun p => ((z.2, p.1, p.2) : RawSlot) := by
    refine Computable.list_map (hpairs.comp Computable.fst) ?_
    exact ((Computable.snd.comp Computable.fst).pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.snd.comp Computable.snd))).to₂
  exact (computable_list_flatMap hroots hbody.to₂).of_eq fun _ => rfl

/-- The slots of a V2 pass are computable in computable parameters. -/
theorem computable_rawChargedSlotsForPassV2 {X : Type} [Primcodable X]
    {fq fL fa fe fn fb fp : X → ℕ} {ffr : X → List RawRoundV2}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (hp : Computable fp) (hfr : Computable ffr) :
    Computable fun x : X =>
      rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
        (fp x) (ffr x) :=
  (computable_rawBlockSpendSlotsV2 hn hb
    (computable_grayChargedSourceCount ha he) hL hp
    (computable_grayChargedThreshold hq he)
    (computable_dyadicScale.comp he) (computable_dyadicScale.comp ha)
    (computable_rawFrozenV1OfV2 hfr)).of_eq fun _ => rfl

/-! ### The v15.1 raised-service wait -/

/-- The Boolean service test is computable jointly in its arguments. -/
theorem computable_servesB {X : Type} [Primcodable X]
    {fa : X → Allocation} {fr : X → ℚ}
    (ha : Computable fa) (hr : Computable fr) :
    Computable fun x : X => servesB (fa x) (fr x) := by
  have hp : Computable₂ fun (x : X) (c : BitString) =>
      decide (fr x ≤ (1 / 2 : ℚ) ^ c.length) := by
    have h1 : Computable fun w : X × BitString => fr w.1 := hr.comp Computable.fst
    have h2 : Computable fun w : X × BitString => ((1 / 2 : ℚ)) ^ w.2.length :=
      (computable_dyadicScale.comp
        (Primrec.list_length.to_comp.comp Computable.snd)).of_eq fun _ => rfl
    exact (computable_ratLe.comp h1 h2).to₂
  exact (computable_list_any ha hp).of_eq fun _ => rfl

/-- The raised-service test as a `cond` on the conjunction of two decidable
Boolean tests (the shape the computability proof consumes). -/
theorem rawChargedRaisedServedB_eq_cond (n b e used : ℕ) (threshold : ℚ)
    (frozen : List RawRound) (sm : FamilyServerMove) :
    rawChargedRaisedServedB n b e used threshold frozen sm =
      (List.range n).all fun i => (List.range b).all fun j =>
        cond (decide (j < used) &&
            decide (threshold < rawFrozenSonBase frozen i j))
          (servesB (getFamilyAlloc sm i [j]) (dyadicScale e)) true := by
  unfold rawChargedRaisedServedB
  congr 1
  funext i
  congr 1
  funext j
  by_cases h1 : j < used <;> by_cases h2 : threshold < rawFrozenSonBase frozen i j <;>
    simp [h1, h2]

/-- The raised-service test is computable jointly in its arguments. -/
theorem computable_rawChargedRaisedServedB {X : Type} [Primcodable X]
    {fn fb fe fused : X → ℕ} {fthr : X → ℚ} {ffr : X → List RawRound}
    {fsm : X → FamilyServerMove}
    (hn : Computable fn) (hb : Computable fb) (he : Computable fe)
    (hused : Computable fused) (hthr : Computable fthr) (hfr : Computable ffr)
    (hsm : Computable fsm) :
    Computable fun x : X =>
      rawChargedRaisedServedB (fn x) (fb x) (fe x) (fused x) (fthr x) (ffr x)
        (fsm x) := by
  -- the inner test, as a function of `((x, i), j)`
  have hx : Computable fun w : (X × ℕ) × ℕ => w.1.1 :=
    Computable.fst.comp Computable.fst
  have hi : Computable fun w : (X × ℕ) × ℕ => w.1.2 :=
    Computable.snd.comp Computable.fst
  have hj : Computable fun w : (X × ℕ) × ℕ => w.2 := Computable.snd
  have ht1 : Computable fun w : (X × ℕ) × ℕ => decide (w.2 < fused w.1.1) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hj (hused.comp hx)
  have hbase : Computable fun w : (X × ℕ) × ℕ =>
      rawFrozenSonBase (ffr w.1.1) w.1.2 w.2 :=
    (computable_rawFrozenSonBase.comp ((hfr.comp hx).pair (hi.pair hj))).of_eq
      fun _ => rfl
  have ht2 : Computable fun w : (X × ℕ) × ℕ =>
      decide (fthr w.1.1 < rawFrozenSonBase (ffr w.1.1) w.1.2 w.2) := by
    refine (Primrec.not.to_comp.comp
      (computable_ratLe.comp hbase (hthr.comp hx))).of_eq fun w => ?_
    exact decide_rat_lt_eq _ _
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  have halloc : Computable fun w : (X × ℕ) × ℕ =>
      getFamilyAlloc (fsm w.1.1) w.1.2 [w.2] :=
    (primrec_getFamilyAlloc.to_comp.comp
      ((hsm.comp hx).pair
        (hi.pair (Computable.list_cons.comp hj (Computable.const []))))).of_eq
      fun _ => rfl
  have hserves : Computable fun w : (X × ℕ) × ℕ =>
      servesB (getFamilyAlloc (fsm w.1.1) w.1.2 [w.2]) (dyadicScale (fe w.1.1)) :=
    computable_servesB halloc (computable_dyadicScale.comp (he.comp hx))
  have hcond : Computable fun w : (X × ℕ) × ℕ =>
      cond (decide (w.2 < fused w.1.1) &&
          decide (fthr w.1.1 < rawFrozenSonBase (ffr w.1.1) w.1.2 w.2))
        (servesB (getFamilyAlloc (fsm w.1.1) w.1.2 [w.2])
          (dyadicScale (fe w.1.1))) true :=
    Computable.cond (hand.comp ht1 ht2) hserves (Computable.const true)
  have hrow : Computable fun z : X × ℕ =>
      (List.range (fb z.1)).all fun j =>
        cond (decide (j < fused z.1) &&
            decide (fthr z.1 < rawFrozenSonBase (ffr z.1) z.2 j))
          (servesB (getFamilyAlloc (fsm z.1) z.2 [j]) (dyadicScale (fe z.1)))
          true :=
    computable_list_all
      (Primrec.list_range.to_comp.comp (hb.comp Computable.fst)) hcond.to₂
  refine (computable_list_all (Primrec.list_range.to_comp.comp hn)
    hrow.to₂).of_eq fun x => ?_
  exact (rawChargedRaisedServedB_eq_cond (fn x) (fb x) (fe x) (fused x)
    (fthr x) (ffr x) (fsm x)).symm

/-- The V2 controller's wait test is computable jointly in its arguments. -/
theorem computable_rawChargedWaitServedB {X : Type} [Primcodable X]
    {fq fa fe fn fb : X → ℕ} {fcore : X → RawStateV2}
    {fsm : X → FamilyServerMove}
    (hq : Computable fq) (ha : Computable fa) (he : Computable fe)
    (hn : Computable fn) (hb : Computable fb) (hcore : Computable fcore)
    (hsm : Computable fsm) :
    Computable fun x : X =>
      rawChargedWaitServedB (fq x) (fa x) (fe x) (fn x) (fb x) (fcore x)
        (fsm x) :=
  (computable_rawChargedRaisedServedB hn hb he
    (computable_grayChargedSourceCount ha he)
    (computable_grayChargedThreshold hq he)
    (computable_rawFrozenV1OfV2
      (Computable.fst.comp (Computable.snd.comp hcore)))
    hsm).of_eq fun _ => rfl

/-! ### The V2 initial state and the child query -/

/-- The initial raw V2 state is computable in computable parameters. -/
theorem computable_rawInitialStateV2 {X : Type} [Primcodable X]
    {fn fb fa fe fq fL : X → ℕ} {fA : X → Allocation}
    (hn : Computable fn) (hb : Computable fb) (ha : Computable fa)
    (he : Computable fe) (hq : Computable fq) (hL : Computable fL)
    (hA : Computable fA) :
    Computable fun x : X =>
      rawInitialStateV2 (fn x) (fb x) (fa x) (fe x) (fq x) (fL x) (fA x) := by
  have hslots : Computable fun x : X =>
      rawAdvBlockSlots (fn x) (fb x) (grayChargedSourceCount (fa x) (fe x))
        (fq x) (fL x) 0 :=
    computable_rawAdvBlockSlots hn hb (computable_grayChargedSourceCount ha he)
      hq hL (Computable.const 0)
  exact ((((Computable.const 0).pair
      ((Computable.const 0).pair (Computable.const false))).pair
    ((Computable.const ([] : List RawRoundV2)).pair
      (hA.pair (hslots.pair
        ((Computable.const ([] : List RawSlot)).pair
          (Computable.const (([], []) : FamilyGameHistory))))))).of_eq
    fun _ => rfl)

/-- The raw V2 query is computable in computable parameters. -/
theorem computable_rawChargedQueryV2 {X : Type} [Primcodable X]
    {fq fL fa fe ftag : X → ℕ} {fst : X → RawStateV2}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (htag : Computable ftag) (hst : Computable fst) :
    Computable fun x : X =>
      rawChargedQueryV2 (fq x) (fL x) (fa x) (fe x) (ftag x) (fst x) := by
  have hbody : Computable fun x : X => (fst x).2 :=
    Computable.snd.comp hst
  have hfrozen : Computable fun x : X => (fst x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fst x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hslots : Computable fun x : X => (fst x).2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hbody))
  have hhist : Computable fun x : X => (fst x).2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody)))
  have htail : Computable fun x : X =>
      (((fst x).2.2.1, ((fst x).2.2.2.1.length, (fst x).2.2.2.2.2)) :
        Allocation × ℕ × FamilyGameHistory) :=
    hunav.pair ((Primrec.list_length.to_comp.comp hslots).pair hhist)
  have hspan : Computable fun x : X => graySpendSpan (fq x) :=
    primrec_graySpendSpan.to_comp.comp hq
  have hadv : Computable fun x : X =>
      grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length :=
    computable_grayTailRoundEps.comp
      (hq.pair (hL.pair (he.pair (Primrec.list_length.to_comp.comp hfrozen))))
  have hspend : Computable fun x : X =>
      grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2) :=
    computable_grayChargedSpendEps ha hL he
      (Primrec.nat_sub.to_comp.comp htag (Computable.const 2))
  have hthen : Computable fun x : X =>
      ((grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length,
          grayTailRoundEps (fq x) (fL x) (fe x) (fst x).2.1.length +
            graySpendSpan (fq x)),
        ((fst x).2.2.1, ((fst x).2.2.2.1.length, (fst x).2.2.2.2.2))) :=
    (hadv.pair (Primrec.nat_add.to_comp.comp hadv hspan)).pair htail
  have helse : Computable fun x : X =>
      ((grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2),
          grayChargedSpendEps (fa x) (fL x) (fe x) (ftag x - 2) +
            graySpendSpan (fq x)),
        ((fst x).2.2.1, ((fst x).2.2.2.1.length, (fst x).2.2.2.2.2))) :=
    (hspend.pair (Primrec.nat_add.to_comp.comp hspend hspan)).pair htail
  have hlt : Computable fun x : X => decide (ftag x < 2) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp htag (Computable.const 2)
  refine (Computable.cond hlt hthen helse).of_eq fun x => ?_
  unfold rawChargedQueryV2
  by_cases h : ftag x < 2 <;> simp [h]

/-! ### Starting the V2 spend phase -/

/-- Opening a raw V2 spend pass is computable in computable parameters. -/
theorem computable_rawChargedStartSpendV2 {X : Type} [Primcodable X]
    {fq fL fa fe fn fb : X → ℕ} {fA : X → Allocation}
    {fcore : X → RawStateV2} {fsm : X → FamilyServerMove}
    (hq : Computable fq) (hL : Computable fL) (ha : Computable fa)
    (he : Computable fe) (hn : Computable fn) (hb : Computable fb)
    (hA : Computable fA) (hcore : Computable fcore) (hsm : Computable fsm) :
    Computable fun x : X =>
      rawChargedStartSpendV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) (fA x)
        (fcore x) (fsm x) := by
  have hbody : Computable fun x : X => (fcore x).2 := Computable.snd.comp hcore
  have htime : Computable fun x : X => (fcore x).1.1 :=
    Computable.fst.comp (Computable.fst.comp hcore)
  have hstart : Computable fun x : X => (fcore x).1.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp hcore))
  have hfrozen : Computable fun x : X => (fcore x).2.1 := Computable.fst.comp hbody
  have hunav : Computable fun x : X => (fcore x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp hbody)
  have hanchors : Computable fun x : X => (fcore x).2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hbody)))
  have hslots : Computable fun x : X =>
      rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) 0
        (fcore x).2.1 :=
    computable_rawChargedSlotsForPassV2 hq hL ha he hn hb
      (Computable.const 0) hfrozen
  have hemp : Computable fun x : X =>
      (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) 0
        (fcore x).2.1).isEmpty := by
    have hz : Computable fun x : X =>
        decide ((rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x)
          (fb x) 0 (fcore x).2.1).length = 0) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Primrec.list_length.to_comp.comp hslots) (Computable.const 0)
    exact hz.of_eq fun x => (list_isEmpty_eq_decide _).symm
  have hdelta0 : Computable fun x : X =>
      grayChargedSpendDelta (fa x) (fL x) (fe x) 0 :=
    computable_grayChargedSpendDelta ha hL he (Computable.const 0)
  have hharv : Computable fun x : X =>
      fA x ++ rawGrayHarvest (grayChargedSpendDelta (fa x) (fL x) (fe x) 0)
        (fb x)
        (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) 0
          (fcore x).2.1) (fn x) (fsm x) :=
    Primrec.list_append.to_comp.comp hA
      (computable_rawGrayHarvest hdelta0 hb hslots hn hsm)
  have hthen : Computable fun x : X =>
      (((1 : ℕ), (((fcore x).1.1, (fcore x).1.2.1, true),
        ((fcore x).2.1, (fcore x).2.2.1, ([] : List RawSlot),
          (fcore x).2.2.2.2.1,
          (([], []) : FamilyGameHistory)))) : RawChargedStateV2) :=
    (Computable.const 1).pair
      ((htime.pair (hstart.pair (Computable.const true))).pair
        (hfrozen.pair (hunav.pair ((Computable.const []).pair
          (hanchors.pair
            (Computable.const (([], []) : FamilyGameHistory)))))))
  have helse : Computable fun x : X =>
      (((2 : ℕ), (((fcore x).1.1, (fcore x).1.1, false),
        ((fcore x).2.1,
          fA x ++ rawGrayHarvest (grayChargedSpendDelta (fa x) (fL x) (fe x) 0)
            (fb x)
            (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x)
              0 (fcore x).2.1) (fn x) (fsm x),
          rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x) (fb x) 0
            (fcore x).2.1,
          (fcore x).2.2.2.2.1,
          (([], []) : FamilyGameHistory)))) : RawChargedStateV2) :=
    (Computable.const 2).pair
      ((htime.pair (htime.pair (Computable.const false))).pair
        (hfrozen.pair (hharv.pair (hslots.pair
          (hanchors.pair
            (Computable.const (([], []) : FamilyGameHistory)))))))
  refine (Computable.cond hemp hthen helse).of_eq fun x => ?_
  unfold rawChargedStartSpendV2
  cases hx : (rawChargedSlotsForPassV2 (fq x) (fL x) (fa x) (fe x) (fn x)
      (fb x) 0 (fcore x).2.1).isEmpty <;> simp

/-! ### The wide advantage next-slots -/

/-- Selecting the raw slots of the next block round is computable in computable parameters. -/
theorem computable_rawBlockNextSlots {X : Type} [Primcodable X]
    {fn fb fq fL fe fused fround : X → ℕ} {fthr : X → ℚ}
    {fA : X → Allocation} {ffr : X → List RawRound}
    {fsm : X → FamilyServerMove}
    (hn : Computable fn) (hb : Computable fb) (hq : Computable fq)
    (hL : Computable fL) (he : Computable fe) (hused : Computable fused)
    (hround : Computable fround) (hthr : Computable fthr) (hA : Computable fA)
    (hfr : Computable ffr) (hsm : Computable fsm) :
    Computable fun x : X =>
      rawBlockNextSlots (fn x) (fb x) (fq x) (fL x) (fe x) (fused x)
        (fround x) (fthr x) (fA x) (ffr x) (fsm x) := by
  have hx : Computable fun w : (X × ℕ) × ℕ => w.1.1 :=
    Computable.fst.comp Computable.fst
  have hi : Computable fun w : (X × ℕ) × ℕ => w.1.2 :=
    Computable.snd.comp Computable.fst
  have hc : Computable fun w : (X × ℕ) × ℕ => w.2 := Computable.snd
  have ht1 : Computable fun w : (X × ℕ) × ℕ => decide (w.2 < fused w.1.1) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hc (hused.comp hx)
  have hbase : Computable fun w : (X × ℕ) × ℕ =>
      rawFrozenSonBase (ffr w.1.1) w.1.2 w.2 :=
    (computable_rawFrozenSonBase.comp ((hfr.comp hx).pair (hi.pair hc))).of_eq
      fun _ => rfl
  have ht2 : Computable fun w : (X × ℕ) × ℕ =>
      !(decide (fthr w.1.1 < rawFrozenSonBase (ffr w.1.1) w.1.2 w.2)) := by
    refine (computable_ratLe.comp hbase (hthr.comp hx)).of_eq fun w => ?_
    exact (not_decide_lt_rat _ _).symm
  have hresarg : Computable fun w : (X × ℕ) × ℕ =>
      (((fe w.1.1, fb w.1.1), fA w.1.1, (fn w.1.1, w.1.2), fsm w.1.1, [w.2]) :
        (ℕ × ℕ) × Allocation × (ℕ × ℕ) × FamilyServerMove × GacsDayNode) :=
    ((he.comp hx).pair (hb.comp hx)).pair
      ((hA.comp hx).pair
        (((hn.comp hx).pair hi).pair
          ((hsm.comp hx).pair
            (Computable.list_cons.comp hc (Computable.const [])))))
  have ht3 : Computable fun w : (X × ℕ) × ℕ =>
      !(getTailFamilyReserve (fe w.1.1) (fb w.1.1) (fA w.1.1) (fn w.1.1) w.1.2
        (fsm w.1.1) [w.2]).isSome :=
    Primrec.not.to_comp.comp
      (Primrec.option_isSome.to_comp.comp
        ((computable_getTailFamilyReserve_joint.comp hresarg).of_eq
          fun _ => rfl))
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  have hpred : Computable fun w : (X × ℕ) × ℕ =>
      (decide (w.2 < fused w.1.1) &&
        !(decide (fthr w.1.1 < rawFrozenSonBase (ffr w.1.1) w.1.2 w.2))) &&
      !(getTailFamilyReserve (fe w.1.1) (fb w.1.1) (fA w.1.1) (fn w.1.1) w.1.2
        (fsm w.1.1) [w.2]).isSome :=
    hand.comp (hand.comp ht1 ht2) ht3
  have hcols : Computable fun z : X × ℕ =>
      (List.range (fb z.1)).filter fun c =>
        (decide (c < fused z.1) &&
          !(decide (fthr z.1 < rawFrozenSonBase (ffr z.1) z.2 c))) &&
        !(getTailFamilyReserve (fe z.1) (fb z.1) (fA z.1) (fn z.1) z.2
          (fsm z.1) [c]).isSome :=
    computable_list_filter
      (Primrec.list_range.to_comp.comp (hb.comp Computable.fst)) hpred.to₂
  have hgrand : Computable fun x : X =>
      rawAdvBlockGrandsons (fb x) (fq x) (fL x) (fround x) :=
    computable_rawAdvBlockGrandsons hb hq hL hround
  have hinner : Computable fun w : (X × ℕ) × ℕ =>
      (rawAdvBlockGrandsons (fb w.1.1) (fq w.1.1) (fL w.1.1)
        (fround w.1.1)).map fun g => ((w.1.2, w.2, g) : RawSlot) := by
    refine Computable.list_map (hgrand.comp hx) ?_
    exact ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  have hrow : Computable fun z : X × ℕ =>
      ((List.range (fb z.1)).filter fun c =>
        (decide (c < fused z.1) &&
          !(decide (fthr z.1 < rawFrozenSonBase (ffr z.1) z.2 c))) &&
        !(getTailFamilyReserve (fe z.1) (fb z.1) (fA z.1) (fn z.1) z.2
          (fsm z.1) [c]).isSome).flatMap fun c =>
        (rawAdvBlockGrandsons (fb z.1) (fq z.1) (fL z.1) (fround z.1)).map
          fun g => ((z.2, c, g) : RawSlot) :=
    computable_list_flatMap hcols hinner.to₂
  exact (computable_list_flatMap (Primrec.list_range.to_comp.comp hn)
    hrow.to₂).of_eq fun _ => rfl

end Kolmogorov
