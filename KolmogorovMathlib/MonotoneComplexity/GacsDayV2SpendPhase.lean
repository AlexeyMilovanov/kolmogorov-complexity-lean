import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedController
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2BlockLayout
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Schedule
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Multiplicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2StateStrict
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedSpendArithmetic

/-!
# The V2 spend phase (blueprint C1/C2, spend side)

Blueprint C1 restores the spend multiplicities: pass `i` runs a block of
`2^{(7−i)L}` child roots per deficient outer root at request scale
`2^{-(a+3+(7−i)L)}` (aggregate `2^{-(a+3)}` per root).  At the pinned gap
`e = a + 8L + 3` the committed window anchor
`grayChargedSpendEps a L e i = max (a+3) (e−(i+1)L)` equals `a+3+(7−i)L` —
so the pass's request scale COINCIDES with its window anchor, exactly like
the advantage side (`α`-depth = block anchor = window anchor).  The V2 spend
goal therefore mirrors `grayChargedBlockGoalAtB` shape-for-shape: everything
at `grayChargedSpendEps`, window `(spendEps, spendEps + L]`.

Children are called `sigma blockAnchor childEps` with
`childEps = blockAnchor + graySpendSpan q` (blueprint C2 / A3, the same
schedule-correct child anchor as the advantage side).
-/

namespace Kolmogorov

/-- The V2 spend acceptance goal of pass `pass`: the charged gray goal at request scale `dyadicScale
(grayChargedSpendEps a L e pass)` over the window from that pass anchor to one per-round budget
above it. At the pinned gap the anchor is `a + 3 + (7 - pass) * L`. -/
def grayChargedBlockSpendGoalAtB (q L a e pass n : Nat)
    (A : Allocation) (c : FamilyClientMove) (s : FamilyServerMove) : Bool :=
  familyChargedGrayGoalAtB 4 (halfAmplification q)
    (dyadicScale (grayChargedSpendEps a L e pass))
    ((3 / 4 : Rat) * dyadicScale (grayChargedSpendEps a L e pass))
    (grayChargedSpendEps a L e pass) (grayChargedSpendDelta a L e pass) n A c s

/-- The V2 spend move of pass `pass`: `sigma` at the pass anchor and the
schedule-correct child anchor. -/
def grayBlockSpendMoveV2 {n b : Nat}
    (q L a e pass : Nat) (sigma : FamilyStrategyScheme)
    (st : GrayTailStateV2 n b) : FamilyClientMove :=
  sigma (grayChargedSpendEps a L e pass)
    (grayChargedSpendEps a L e pass + graySpendSpan q)
    st.unavailable st.slots.length st.history

/-- The V2 spend slots of pass `pass`: every deficient outer root receives
the pass's whole spare-pair block (`graySpendMult L pass` pairs). -/
def grayBlockSpendSlotsV2 {n b : Nat}
    (source L pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) : List (GrayTailSlot n b) :=
  (grayChargedDeficientRoots source threshold eps alpha frozen).flatMap fun i =>
    (grayBlockSpendPairs b source L pass).map fun p => (i, p.1, p.2)

/-- Per-root request bounds of an accepted V2 spend pass, at the pass anchor. -/
lemma grayChargedBlockSpendGoalAtB_root_bounds
    {q L a e pass n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass n A move server = true)
    (j : Fin n) :
    dyadicScale (grayChargedSpendEps a L e pass) / 2 ≤
        getFamilyReq move j.val [] ∧
      getFamilyReq move j.val [] ≤
        dyadicScale (grayChargedSpendEps a L e pass) := by
  unfold grayChargedBlockSpendGoalAtB at hgoal
  obtain ⟨G, _hGmem, hG⟩ := familyChargedGrayGoalAtB.exists_charge hgoal
  have hj := familyGrayChargeAtB.root hG j.isLt
  exact ⟨hj.1, hj.2.1⟩

/-- The V2 spend pass's total request lower bound, at the pass anchor. -/
lemma grayChargedBlockSpendGoal_totalRequest_lower
    {q L a e pass n : Nat} {A : Allocation}
    {move : FamilyClientMove} {server : FamilyServerMove}
    (hgoal : grayChargedBlockSpendGoalAtB q L a e pass n A move server = true) :
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale (grayChargedSpendEps a L e pass)) ≤
      halfAmplification q * totalRootRequest n move := by
  unfold grayChargedBlockSpendGoalAtB at hgoal
  have hweak := familyChargedGrayGoalAtB.to_familyGrayGoalAtB hgoal
  unfold familyGrayGoalAtB at hweak
  rw [Bool.and_eq_true] at hweak
  exact of_decide_eq_true hweak.2

/-- At the pinned gap `e = a + 8L + 3`, the spend window anchor equals the
C1 request depth `graySpendAnchor a L pass = a + 3 + (7 − pass)·L`. -/
lemma grayChargedSpendEps_pinned (a L pass : Nat) (hpass : pass < 8) :
    grayChargedSpendEps a L (a + 8 * L + 3) pass =
      graySpendAnchor a L pass := by
  unfold grayChargedSpendEps grayChargedSpendAlphaDepth graySpendAnchor
  have hL : (pass + 1) * L <= 8 * L := by
    apply Nat.mul_le_mul_right
    omega
  have h2 : 8 * L - (pass + 1) * L = (7 - pass) * L := by
    rw [← Nat.sub_mul]
    congr 1
    omega
  have h1 : a + 8 * L + 3 - (pass + 1) * L = a + 3 + (7 - pass) * L := by
    omega
  rw [h1]
  omega

/-- The pinned-gap spend aggregate (blueprint C1): the pass block of one
deficient root carries total request scale exactly `2^{-a}/8 = 2^{-(a+3)}`. -/
lemma graySpendBlock_pinned_mass (a L pass : Nat) (hpass : pass < 8) :
    (graySpendMult L pass : Rat) *
        dyadicScale (grayChargedSpendEps a L (a + 8 * L + 3) pass) =
      dyadicScale a / 8 := by
  rw [grayChargedSpendEps_pinned a L pass hpass]
  exact graySpendMult_mass a L pass

/-- Every pair of a spend block starts at or above the source region. -/
lemma grayBlockSpendPairs_first_ge
    {b source L pass : Nat} {p : Fin b × Fin b}
    (hp : p ∈ grayBlockSpendPairs b source L pass) : source <= p.1.val := by
  apply grayChargedSparePairs_first_ge
  exact List.mem_of_mem_drop (List.mem_of_mem_take hp)

/-- V2 spend slot lists are duplicate free. -/
lemma grayBlockSpendSlotsV2_nodup {n b : Nat}
    (source L pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) :
    (grayBlockSpendSlotsV2 source L pass threshold eps alpha frozen).Nodup := by
  rw [grayBlockSpendSlotsV2, List.nodup_flatMap]
  constructor
  · intro i hi
    exact (grayBlockSpendPairs_nodup b source L pass).map fun p p' h =>
      congrArg Prod.snd h
  · refine (grayChargedDeficientRoots_nodup source threshold eps alpha frozen).imp ?_
    intro i i' hne
    change (List.map (fun p => (i, p.1, p.2)) (grayBlockSpendPairs b source L pass)).Disjoint
      (List.map (fun p => (i', p.1, p.2)) (grayBlockSpendPairs b source L pass))
    rw [List.disjoint_iff_ne]
    intro x hx y hy heq
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    obtain ⟨p', hp', hpy⟩ := List.mem_map.mp hy
    have hslots : (i, p.1, p.2) = (i', p'.1, p'.2) :=
      hpx.trans (heq.trans hpy.symm)
    exact hne (congrArg Prod.fst hslots)

/-- V2 spend slots lie at or above the source region. -/
lemma grayBlockSpendSlotsV2_son_ge {n b : Nat}
    {source L pass : Nat} {threshold eps alpha : Rat}
    {frozen : GrayTailFrozen n b} {s : GrayTailSlot n b}
    (hs : s ∈ grayBlockSpendSlotsV2 source L pass
      threshold eps alpha frozen) : source <= s.2.1.val := by
  rw [grayBlockSpendSlotsV2, List.mem_flatMap] at hs
  obtain ⟨i, hi, hsi⟩ := hs
  rw [List.mem_map] at hsi
  obtain ⟨p, hp, hps⟩ := hsi
  have hge := grayBlockSpendPairs_first_ge hp
  have hson := congrArg (fun z => z.2.1.val) hps
  calc
    source <= p.1.val := hge
    _ = s.2.1.val := hson

/-- The two-level pair of a V2 spend slot lies in the pass's block. -/
lemma grayBlockSpendSlotsV2_pair {n b : Nat}
    {source L pass : Nat} {threshold eps alpha : Rat}
    {frozen : GrayTailFrozen n b} {s : GrayTailSlot n b}
    (hs : s ∈ grayBlockSpendSlotsV2 source L pass
      threshold eps alpha frozen) :
    (s.2.1, s.2.2) ∈ grayBlockSpendPairs b source L pass := by
  rw [grayBlockSpendSlotsV2, List.mem_flatMap] at hs
  obtain ⟨i, hi, hsi⟩ := hs
  rw [List.mem_map] at hsi
  obtain ⟨p, hp, hps⟩ := hsi
  have hpair := congrArg Prod.snd hps
  simpa using hpair ▸ hp

/-- Source-region slots are disjoint from V2 spend slots. -/
lemma grayBlockSource_disjoint_spendV2 {n b : Nat}
    {source L pass : Nat} {slots : List (GrayTailSlot n b)}
    {threshold eps alpha : Rat} {frozen : GrayTailFrozen n b}
    (hsource : forall s, s ∈ slots -> s.2.1.val < source) :
    slots.Disjoint (grayBlockSpendSlotsV2 source L pass
      threshold eps alpha frozen) := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  have hslt := hsource s hs
  have htge := grayBlockSpendSlotsV2_son_ge ht
  rw [heq] at hslt
  omega

/-- Distinct passes' V2 spend slots are disjoint. -/
lemma grayBlockSpendSlotsV2_disjoint {n b : Nat}
    {source L pass pass' : Nat}
    {threshold eps alpha threshold' eps' alpha' : Rat}
    {frozen frozen' : GrayTailFrozen n b} (hpass : pass < pass') :
    (grayBlockSpendSlotsV2 source L pass threshold eps alpha frozen).Disjoint
      (grayBlockSpendSlotsV2 source L pass'
        threshold' eps' alpha' frozen') := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  have hsp := grayBlockSpendSlotsV2_pair hs
  have htp := grayBlockSpendSlotsV2_pair ht
  have hdisj := grayBlockSpendPairs_disjoint
    (b := b) (source := source) (L := L) hpass
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj (s.2.1, s.2.2) hsp (t.2.1, t.2.2) htp
    (congrArg Prod.snd heq)

/-- At the pinned gap, the spend anchors take the explicit staircase form. -/
lemma grayChargedSpendEps_pinned_eq {a L pass : Nat} (hpass : pass < 8) :
    grayChargedSpendEps a L (a + 8 * L + 3) pass =
      a + 3 + (7 - pass) * L := by
  unfold grayChargedSpendEps grayChargedSpendAlphaDepth
  have h1 : a + 8 * L + 3 - (pass + 1) * L = a + 3 + (7 - pass) * L := by
    have hL : (pass + 1) * L <= 8 * L := Nat.mul_le_mul_right L (by omega)
    have h2 : (7 - pass) * L + (pass + 1) * L = 8 * L := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  rw [h1]
  omega

/-- Any shared spare pair pins the pass: distinct passes have disjoint
blocks. -/
lemma grayBlockSpendPairs_pass_eq {b source L p0 p1 : Nat}
    {x : Fin b × Fin b}
    (h0 : x ∈ grayBlockSpendPairs b source L p0)
    (h1 : x ∈ grayBlockSpendPairs b source L p1) : p0 = p1 := by
  by_contra hne
  rcases Nat.lt_or_ge p0 p1 with hlt | hge
  · exact (grayBlockSpendPairs_disjoint (b := b) (source := source)
      (L := L) hlt) h0 h1
  · have hlt : p1 < p0 := by omega
    exact (grayBlockSpendPairs_disjoint (b := b) (source := source)
      (L := L) hlt) h1 h0

end Kolmogorov
