import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailFloorArithmetic
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2OwnerComplement
import Mathlib.Tactic.NormNum.Prime
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ComplementFamily

/-!
# The all-reduced aggregate arithmetic (Phase 2C)

The corrected scalar ledger: every resolved source contributes a reduced
reserve `5ε/6`, and the raise residual is bounded separately, so one source
may pay both the owner overlap and the raise remainder.  This replaces the
refuted two-exclusive-classes theorem.
-/

namespace Kolmogorov

/-- **The all-reduced aggregate bounds** (blueprint 2C): with `c` resolved
sources at reduced reserve mass `5ε/6` each and the raise residual bounded
by the raised class, the final mass dominates both the coarse budget `m·ε`
and the amplified request `(κ + 1/2)·Q`. -/
theorem grayChargedV2_allReduced_aggregate
    {m c r : Nat} {kappa eps Q Qcalls R MS MR MF : Rat}
    (hkappa : 1 <= kappa) (heps : 0 < eps)
    (hcount : 3 * (m : Rat) <= 4 * (c : Rat))
    (hrc : (r : Rat) <= (c : Rat))
    (hQsplit : Q = Qcalls + R)
    (hR0 : 0 <= R)
    (hQcalls0 : 0 <= Qcalls)
    (hRr : R <= (r : Rat) * (eps / (6 * kappa)))
    (hQupper : Q <= (m : Rat) * eps)
    (hQlower : (m : Rat) * eps / 2 <= Q)
    (hMS : kappa * Qcalls <= MS)
    (hMR : (c : Rat) * (5 * eps / 6) <= MR)
    (hMF : MF = MS + MR) :
    (m : Rat) * eps <= MF ∧ (kappa + 1 / 2) * Q <= MF := by
  have hkpos : (0 : Rat) < kappa := lt_of_lt_of_le one_pos hkappa
  -- the amplified residual is at most one sixth of the resolved budget
  have hkR : kappa * R <= (c : Rat) * eps / 6 := by
    have h1 : kappa * R <= kappa * ((r : Rat) * (eps / (6 * kappa))) :=
      mul_le_mul_of_nonneg_left hRr hkpos.le
    have h2 : kappa * ((r : Rat) * (eps / (6 * kappa))) =
        (r : Rat) * eps / 6 := by
      field_simp
    have h3 : (r : Rat) * eps / 6 <= (c : Rat) * eps / 6 := by
      have := mul_le_mul_of_nonneg_right hrc heps.le
      linarith
    linarith
  -- the raw residual too, since `κ ≥ 1`
  have hR_le : R <= (c : Rat) * eps / 6 := by
    have h4 : 1 * R <= kappa * R := mul_le_mul_of_nonneg_right hkappa hR0
    linarith
  -- the source budget sits inside two thirds of the resolved budget
  have hcm : (m : Rat) * eps / 2 <= 2 * ((c : Rat) * eps) / 3 := by
    have := mul_le_mul_of_nonneg_right hcount heps.le
    linarith
  -- the recursive mass dominates the unamplified accepted request
  have hQc : Qcalls <= MS := by
    have h5 : 1 * Qcalls <= kappa * Qcalls :=
      mul_le_mul_of_nonneg_right hkappa hQcalls0
    linarith
  constructor
  · -- the coarse budget
    have h6 : Q - R <= MS := by
      rw [hQsplit]
      linarith
    have h7 : (m : Rat) * eps / 2 - (c : Rat) * eps / 6 +
        (c : Rat) * (5 * eps / 6) <= MF := by
      rw [hMF]
      have h8 : (m : Rat) * eps / 2 - (c : Rat) * eps / 6 <= MS := by
        linarith
      linarith
    have h9 : (m : Rat) * eps <=
        (m : Rat) * eps / 2 - (c : Rat) * eps / 6 +
          (c : Rat) * (5 * eps / 6) := by
      have h10 : (c : Rat) * (5 * eps / 6) =
          5 * ((c : Rat) * eps) / 6 := by ring
      rw [h10]
      linarith
    linarith
  · -- the amplified request
    have h11 : kappa * Q - kappa * R <= MS := by
      have h12 : kappa * Qcalls = kappa * Q - kappa * R := by
        rw [hQsplit]
        ring
      linarith
    have h13 : Q / 2 <= 2 * ((c : Rat) * eps) / 3 := by
      linarith
    have h14 : kappa * Q + Q / 2 <= MF := by
      rw [hMF]
      have h15 : (c : Rat) * (5 * eps / 6) =
          5 * ((c : Rat) * eps) / 6 := by ring
      have h16 : kappa * Q - (c : Rat) * eps / 6 <= MS := by
        linarith
      linarith
    have h17 : (kappa + 1 / 2) * Q = kappa * Q + Q / 2 := by ring
    linarith

/-- A uniform lower bound over a list sums to a count multiple. -/
lemma grayCharged_sum_le_of_forall_le {alpha : Type _} (l : List alpha)
    (f : alpha -> Rat) (x : Rat)
    (h : forall a, a ∈ l -> x <= f a) :
    (l.length : Rat) * x <= (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := h a List.mem_cons_self
      have h2 := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
      push_cast
      have h3 : ((rest.length : Rat) + 1) * x =
          (rest.length : Rat) * x + x := by ring
      rw [h3]
      linarith

/-- **The aggregate complement mass**: the family's reserve charge carries
at least `5ε/6` per resolved coordinate. -/
theorem grayChargedV2_complement_family_aggregate_mass
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm))
    (hmass : forall r, r ∈ reserves ->
      dyadicScale e - dyadicScale e / 6 <=
        grayChargeMass (e + grayTailNewLoss q L) r.cells) :
    (reserves.length : Rat) * (dyadicScale e - dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedReserveChargeV2 reserves) := by
  rw [grayChargedReserveChargeV2, grayChargeMass_flatMap]
  exact grayCharged_sum_le_of_forall_le reserves _ _ hmass

/-- Powers of two escape divisibility by three. -/
lemma grayCharged_three_not_dvd_two_pow (s : Nat) : ¬ (3 ∣ 2 ^ s) := by
  intro h
  have h3 : Nat.Prime 3 := by norm_num
  have h2 := h3.dvd_of_dvd_pow h
  norm_num at h2

/-- **The strict call-scale bound** (leaf-2 prerequisite): the call scale
sits STRICTLY below `ε/(24κ)`, because `3q+6` is never a power of two. -/
theorem grayCallDepth_scale_strict (q e : Nat) :
    dyadicScale (grayCallDepth q e) <
      dyadicScale e / (24 * halfAmplification q) := by
  set s := Nat.size (3 * q + 5) with hs
  have hD : (0 : Rat) < dyadicScale e := dyadicScale_pos e
  have heq : dyadicScale (grayCallDepth q e) =
      dyadicScale e / 2 ^ (s + 2) := by
    rw [grayCallDepth, dyadicScale_add]
  -- `3q+6 ≤ 2^s` and `3q+6 ≠ 2^s` give strictness
  have hlow : 3 * q + 6 <= 2 ^ s := two_pow_size_lower q
  have hne : 3 * q + 6 ≠ 2 ^ s := by
    intro hcontra
    exact grayCharged_three_not_dvd_two_pow s
      ⟨q + 2, by omega⟩
  have hstrict : 3 * q + 6 < 2 ^ s := lt_of_le_of_ne hlow hne
  -- convert to the rational inequality `24κ < 2^{s+2}`
  have hkappa : (24 : Rat) * halfAmplification q = 4 * (3 * q + 6) := by
    unfold halfAmplification
    ring
  have hpow : ((2 : Rat)) ^ (s + 2) = 4 * (2 ^ s : Nat) := by
    push_cast
    rw [pow_add]
    ring
  have hlt : (24 : Rat) * halfAmplification q < 2 ^ (s + 2) := by
    rw [hkappa, hpow]
    have : ((3 * q + 6 : Nat) : Rat) < ((2 ^ s : Nat) : Rat) := by
      exact_mod_cast hstrict
    push_cast at this ⊢
    linarith
  rw [heq]
  apply div_lt_div_of_pos_left hD ?_ hlt
  have hk : (0 : Rat) < halfAmplification q := halfAmplification_pos q
  positivity

/-- **The strict owner-window cap** (leaf-2 prerequisite): the owner fibre
carries STRICTLY less than `ε/6` — the strictness the bait-corner LP
needs. -/
theorem grayChargedOwnerFibreV2_mass_lt
    {q L a e n t : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove} (hae : a <= e)
    (p : GrayTailRoundV2 n (grayTailBranch q L a e))
    (hp : p ∈ (grayChargedRunStateV2 (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).core.frozen)
    (hadv : grayCallDepth q e <= p.blockAnchor)
    (z : Fin n × Fin (grayTailBranch q L a e)) :
    grayChargeMass (e + grayTailNewLoss q L)
        (grayChargedOwnerFibreV2 hae p hp z) <
      dyadicScale e / 6 := by
  classical
  have hsplit := grayChargedRunStateV2_frozen_phase_split q L a e sigma A
    sm t hp hae hadv
  have hgoal := hsplit.2.2.1
  have hnodup : p.slots.Nodup :=
    ((grayChargedRunStateV2_coreCertified q L a e sigma A sm
      t).round_valid p hp).2.2.2.2.1
  have hcount := grayInAdvBlock_fibre_count_le hnodup hsplit.2.2.2.1
  have hbase := grayChargedBlockRoundSonBase_le_callScale hgoal hcount
    z.1 z.2
  have hvalid := grayChargedLocalChargeOfBlockGoal_valid
    (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp hae
      hadv)
  have hfineEq : p.fineEnd = p.blockAnchor + L :=
    grayChargedRunStateV2_frozen_fineEnd q L a e sigma A sm t hp
  have hdeltaLe : grayTailRoundDelta q L e p.roundIndex <=
      e + grayTailNewLoss q L := by
    have hub := grayChargedRunStateV2_frozen_depth_ub hp hae
    have h2 := hsplit.2.1
    omega
  have hcharge : grayChargedRoundLocalChargeV2 hae p hp =
      grayChargedLocalChargeOfBlockGoal
        (grayChargedRunStateV2_frozen_adv_goal q L a e sigma A sm t hp
          hae hadv) := by
    rw [grayChargedRoundLocalChargeV2, dite_eq_left hadv]
  rw [grayChargedOwnerFibreV2, grayChargeMass_flatMap]
  have hstep : ((List.finRange p.slots.length).map fun j =>
      grayChargeMass (e + grayTailNewLoss q L)
        (if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
          grayChargedTransportRoot (e + grayTailNewLoss q L) z.1.val j.val
            (grayChargedRoundLocalChargeV2 hae p hp)
        else [])).sum <=
      ((List.finRange p.slots.length).map fun j =>
        if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
          4 * halfAmplification q * getFamilyReq p.move j.val [] else
          0).sum := by
    apply List.sum_le_sum
    intro j _
    by_cases hm : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2
    · rw [ite_eq_left hm, ite_eq_left hm, hcharge,
        grayChargedTransportRoot_mass_of_charge hdeltaLe hvalid]
      exact (familyGrayChargeAtB.root hvalid j.isLt).2.2
    · rw [ite_eq_right hm, ite_eq_right hm]
      simp [grayChargeMass, grayMassOfCount]
  refine lt_of_le_of_lt hstep ?_
  have hbridge : ((List.finRange p.slots.length).map fun j =>
      if (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2 then
        4 * halfAmplification q * getFamilyReq p.move j.val [] else
        0).sum =
      4 * halfAmplification q *
        grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 := by
    rw [grayTailSonBase_eq_sum_map, grayTailSlotEntries, List.map_ofFn,
      List.ofFn_eq_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    by_cases hm : (p.slots.get j).1 = z.1 ∧ (p.slots.get j).2.1 = z.2
    · rw [ite_eq_left hm]
      rw [ite_eq_left hm]
      rfl
    · rw [ite_eq_right hm]
      rw [ite_eq_right hm, mul_zero]
  rw [hbridge]
  have hcallStrict := grayCallDepth_scale_strict q e
  have hkpos : (0 : Rat) < halfAmplification q := halfAmplification_pos q
  calc 4 * halfAmplification q *
      grayTailSonBase (grayTailSlotEntries p.slots p.move) z.1 z.2 <=
      4 * halfAmplification q * dyadicScale (grayCallDepth q e) := by
        apply mul_le_mul_of_nonneg_left hbase
        positivity
    _ < 4 * halfAmplification q *
        (dyadicScale e / (24 * halfAmplification q)) := by
        apply mul_lt_mul_of_pos_left hcallStrict
        positivity
    _ = dyadicScale e / 6 := by
        field_simp
        ring

/-- **The abstract bait-corner sum** (leaf-2 LP core, §4.4): with at most a
quarter of the son slots active and every root's net bounded below by its
resolved slots at rate `S` minus half an active slot each, the family net
is at least the bait-corner value `nB(3S/4 − 1/8)`. -/
theorem grayChargedV2_bait_corner_sum
    {n B : Nat} {S : Rat} (a : Fin n -> Nat) (nets : Fin n -> Rat)
    (hSpos : 0 <= S)
    (hquarter : 4 * (∑ i : Fin n, ((a i : Nat) : Rat)) <=
      (n : Rat) * (B : Rat))
    (hnet : forall i, ((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2 <=
      nets i) :
    (n : Rat) * (B : Rat) * (3 * S / 4 - 1 / 8) <=
      ∑ i : Fin n, nets i := by
  have h1 : (∑ i : Fin n,
      (((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2)) <=
      ∑ i : Fin n, nets i :=
    Finset.sum_le_sum (fun i _ => hnet i)
  have hpt : forall i : Fin n,
      ((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2 =
      (B : Rat) * S - ((a i : Rat) * S + (a i : Rat) / 2) := by
    intro i
    ring
  have h2 : (∑ i : Fin n,
      (((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2)) =
      (n : Rat) * ((B : Rat) * S) -
        ((∑ i : Fin n, ((a i : Nat) : Rat)) * S +
          (∑ i : Fin n, ((a i : Nat) : Rat)) / 2) := by
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_div]
  have hA : (∑ i : Fin n, ((a i : Nat) : Rat)) <=
      (n : Rat) * (B : Rat) / 4 := by
    linarith
  have hA0 : (0 : Rat) <= ∑ i : Fin n, ((a i : Nat) : Rat) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have h3 : (∑ i : Fin n, ((a i : Nat) : Rat)) * S +
      (∑ i : Fin n, ((a i : Nat) : Rat)) / 2 <=
      ((n : Rat) * (B : Rat) / 4) * S +
        ((n : Rat) * (B : Rat) / 4) / 2 := by
    have hs := mul_le_mul_of_nonneg_right hA hSpos
    linarith
  have h4 : (n : Rat) * ((B : Rat) * S) -
      (((n : Rat) * (B : Rat) / 4) * S +
        ((n : Rat) * (B : Rat) / 4) / 2) =
      (n : Rat) * (B : Rat) * (3 * S / 4 - 1 / 8) := by
    ring
  linarith

/-- **The threshold-son net rate is strictly above one sixth** (leaf-2
constants): `S_thr = κ·threshold + K − κ′ > 1/6` whenever the kept reserve
mass strictly exceeds `5ε/6` — the exact form the strict owner cap
delivers. In `ε = 1` units. -/
theorem grayChargedV2_thr_net_rate_gt
    {q : Nat} {K : Rat}
    (hK : 5 / 6 < K) :
    (1 : Rat) / 6 <
      halfAmplification q * (1 - 1 / (6 * halfAmplification q)) + K -
        halfAmplification (q + 1) := by
  have hkpos : (0 : Rat) < halfAmplification q := halfAmplification_pos q
  have hexp : halfAmplification q *
      (1 - 1 / (6 * halfAmplification q)) =
      halfAmplification q - 1 / 6 := by
    field_simp
  rw [hexp, halfAmplification_succ]
  linarith

/-- **The abstract subfamily corner** (leaf-2 core, §4.4 in hereditary
form): for every subfamily `I`, the selected nets plus the amplified
displays of the complement are nonnegative — the adversary's optimum is
the all-in bait corner, which closes exactly when the net rate reaches one
sixth. -/
theorem grayChargedV2_subfamily_corner_sum
    {n B : Nat} {S kp : Rat} (a : Fin n -> Nat)
    (nets d : Fin n -> Rat) (I : Finset (Fin n))
    (hS16 : 1 / 6 <= S) (hS12 : S <= 1 / 2) (hkp : 1 <= kp)
    (hquarter : 4 * (∑ i : Fin n, ((a i : Nat) : Rat)) <=
      (n : Rat) * (B : Rat))
    (hnet : forall i, ((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2 <=
      nets i)
    (hd : forall i, (B : Rat) / 2 <= d i) :
    0 <= (∑ i ∈ I, nets i) + kp * ∑ i ∈ Finset.univ \ I, d i := by
  have hB0 : (0 : Rat) <= (B : Rat) := Nat.cast_nonneg B
  have hn0 : (0 : Rat) <= (n : Rat) := Nat.cast_nonneg n
  -- the selected nets
  have h1 : (∑ i ∈ I,
      (((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2)) <=
      ∑ i ∈ I, nets i :=
    Finset.sum_le_sum (fun i _ => hnet i)
  have hpt : forall i : Fin n,
      ((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2 =
      (B : Rat) * S - ((a i : Rat) * S + (a i : Rat) / 2) := by
    intro i
    ring
  have h2 : (∑ i ∈ I,
      (((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2)) =
      (I.card : Rat) * ((B : Rat) * S) -
        ((∑ i ∈ I, ((a i : Nat) : Rat)) * S +
          (∑ i ∈ I, ((a i : Nat) : Rat)) / 2) := by
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_div]
  -- the act budget restricted to `I` stays within the global quarter
  have hsub : (∑ i ∈ I, ((a i : Nat) : Rat)) <=
      ∑ i : Fin n, ((a i : Nat) : Rat) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun i _ _ => Nat.cast_nonneg _)
  have hA : (∑ i ∈ I, ((a i : Nat) : Rat)) <=
      (n : Rat) * (B : Rat) / 4 := by
    linarith
  have hA0 : (0 : Rat) <= ∑ i ∈ I, ((a i : Nat) : Rat) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  -- the complement displays
  have h3 : ((Finset.univ \ I).card : Rat) * ((B : Rat) / 2) <=
      ∑ i ∈ Finset.univ \ I, d i := by
    calc ((Finset.univ \ I).card : Rat) * ((B : Rat) / 2) =
        ∑ _i ∈ Finset.univ \ I, (B : Rat) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ∑ i ∈ Finset.univ \ I, d i :=
          Finset.sum_le_sum (fun i _ => hd i)
  have hdpos : (0 : Rat) <= ∑ i ∈ Finset.univ \ I, d i := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    have := hd i
    linarith
  have hk3 : (∑ i ∈ Finset.univ \ I, d i) <=
      kp * ∑ i ∈ Finset.univ \ I, d i := by
    have h4 : 1 * (∑ i ∈ Finset.univ \ I, d i) <=
        kp * ∑ i ∈ Finset.univ \ I, d i :=
      mul_le_mul_of_nonneg_right hkp hdpos
    linarith
  -- cardinalities
  have hcardSplit : ((Finset.univ \ I).card : Rat) =
      (n : Rat) - (I.card : Rat) := by
    have h5 : (Finset.univ \ I).card = n - I.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    rw [h5]
    have h6 : I.card <= n := by
      have := Finset.card_le_card (Finset.subset_univ I)
      simpa [Finset.card_univ] using this
    push_cast [Nat.cast_sub h6]
    ring
  have hIcard : (I.card : Rat) <= (n : Rat) := by
    have := Finset.card_le_card (Finset.subset_univ I)
    have h7 : I.card <= n := by simpa [Finset.card_univ] using this
    exact_mod_cast h7
  have hIcard0 : (0 : Rat) <= (I.card : Rat) := Nat.cast_nonneg _
  -- the linear optimum: worst at `I = univ`, closing at `S = 1/6`
  have hkey : 0 <= (I.card : Rat) * ((B : Rat) * S) -
      ((n : Rat) * (B : Rat) / 4) * S -
      ((n : Rat) * (B : Rat) / 4) / 2 +
      ((n : Rat) - (I.card : Rat)) * ((B : Rat) / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hIcard hB0,
      mul_nonneg hIcard0 hB0,
      mul_nonneg (mul_nonneg hn0 hB0) (by linarith : (0:Rat) <= S - 1/6),
      mul_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_right hIcard hB0))
        (by linarith : (0:Rat) <= 1/2 - S)]
  -- assemble
  have hAmul : (∑ i ∈ I, ((a i : Nat) : Rat)) * S +
      (∑ i ∈ I, ((a i : Nat) : Rat)) / 2 <=
      ((n : Rat) * (B : Rat) / 4) * S +
        ((n : Rat) * (B : Rat) / 4) / 2 := by
    have hs := mul_le_mul_of_nonneg_right hA (by linarith : (0:Rat) <= S)
    linarith
  calc (0 : Rat) <=
      (I.card : Rat) * ((B : Rat) * S) -
        ((n : Rat) * (B : Rat) / 4) * S -
        ((n : Rat) * (B : Rat) / 4) / 2 +
        ((n : Rat) - (I.card : Rat)) * ((B : Rat) / 2) := hkey
    _ <= (∑ i ∈ I, nets i) + kp * ∑ i ∈ Finset.univ \ I, d i := by
        have hstep : ((n : Rat) - (I.card : Rat)) * ((B : Rat) / 2) <=
            ∑ i ∈ Finset.univ \ I, d i := by
          rw [← hcardSplit]
          exact h3
        linarith

/-- **The hereditary bound in leaf-2 shape**: from per-root masses and
displays satisfying the net bounds, every subfamily's amplified surplus is
covered by its selected mass — the exact form of
`GrayChargedL5SubfamilyV2`, over finsets. -/
theorem grayChargedV2_subfamily_of_perRoot_nets
    {n B : Nat} {S kp : Rat} (a : Fin n -> Nat)
    (m d : Fin n -> Rat) (I : Finset (Fin n))
    (hS16 : 1 / 6 <= S) (hS12 : S <= 1 / 2) (hkp : 1 <= kp)
    (hquarter : 4 * (∑ i : Fin n, ((a i : Nat) : Rat)) <=
      (n : Rat) * (B : Rat))
    (hnet : forall i, ((B : Rat) - (a i : Rat)) * S - (a i : Rat) / 2 <=
      m i - kp * d i)
    (hd : forall i, (B : Rat) / 2 <= d i) :
    kp * (2 * (∑ i ∈ I, d i) - ∑ i : Fin n, d i) <= ∑ i ∈ I, m i := by
  have hcore := grayChargedV2_subfamily_corner_sum a
    (fun i => m i - kp * d i) d I hS16 hS12 hkp hquarter hnet hd
  have hsplit : (∑ i : Fin n, d i) =
      (∑ i ∈ I, d i) + ∑ i ∈ Finset.univ \ I, d i := by
    rw [add_comm]
    exact (Finset.sum_sdiff (Finset.subset_univ I)).symm
  have hsum : (∑ i ∈ I, (m i - kp * d i)) =
      (∑ i ∈ I, m i) - kp * ∑ i ∈ I, d i := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum] at hcore
  have hexp : kp * (2 * (∑ i ∈ I, d i) - ∑ i : Fin n, d i) =
      kp * (∑ i ∈ I, d i) - kp * ∑ i ∈ Finset.univ \ I, d i := by
    rw [hsplit]
    ring
  linarith

end Kolmogorov
