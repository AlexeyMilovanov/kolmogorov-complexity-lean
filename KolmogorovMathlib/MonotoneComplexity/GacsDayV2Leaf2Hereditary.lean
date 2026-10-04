import KolmogorovMathlib.MonotoneComplexity.GacsDayV2SubfamilyBridge

/-!
# Leaf 2 (D4), hereditary route — the abstract scalar core

The pointwise `hnet` bridge is unavailable (its all-active-root counterexample
is impossible: an active son contributes `0` to the displayed request while H1
forces `req i ≥ Bε/2` at every root), and H4 for `F = source ++ reserve` closes
instead via the **hereditary** decomposition

* `(S)`   `κ·(2·P_I − P) ≤ MS_I`   (source subfamily, from
  `familyGrayChargeAtB.subfamily` per frozen source; `P` = frozen request,
  `D = P + E`, `E` the raised remainder), and
* `(R_I)` `½·(2·P_I − P) + κ′·(2·E_I − E) ≤ MR_I`   (owner-restricted reserve
  deficit; `κ′ = κ + ½`),

whose sum is exactly `κ′·(2·D_I − D)`.  This module proves the two **scalar**
cores (independent of the transport/owner plumbing), matching the proven
aggregate `grayChargedV2_allReduced_aggregate` at `I = [n]`:

1. `grayChargedV2_h4_assemble` — `(S) + (R_I) ⟹ H4` (pure algebra), and
2. `grayChargedV2_reserve_deficit_closes` — `(R_I)` holds from the H1 window
   (`D_I ≤ m_I·ε`, `D_{Iᶜ} ≥ (m−m_I)·ε/2`), the per-`I` quarter
   `c_I ≥ m_I − m/4` (global three-quarters restricted), the strict owner cap
   (`2E_I − E ≤ c_I·ε/(6κ)`), and `MR_I ≥ c_I·(5ε/6)`.  The chain reduces to
   `m_I ≤ m`.
-/

namespace Kolmogorov

/-- **The H4 assembly (scalar).**  The source subfamily bound `(S)` and the
owner-restricted reserve deficit `(R_I)` sum to the hereditary H4 inequality,
using `D = P + E` and `κ′ = κ + 1/2`. -/
theorem grayChargedV2_h4_assemble
    {kappa P E PI EI MS MR : Rat}
    (hS : kappa * (2 * PI - P) <= MS)
    (hR : (1 / 2) * (2 * PI - P) + (kappa + 1 / 2) * (2 * EI - E) <= MR) :
    (kappa + 1 / 2) * (2 * (PI + EI) - (P + E)) <= MS + MR := by
  nlinarith [hS, hR]

/-- **The reserve deficit closes (scalar).**  Mirrors the proven aggregate
`grayChargedV2_allReduced_aggregate` at the subfamily level.  With `κ ≥ 1`,
`ε > 0`, the displayed split `D = P + E`, `D_I = P_I + E_I`; the H1 window
`D_I ≤ m_I·ε` and `D_{Iᶜ} = D − D_I ≥ (m − m_I)·ε/2`; the per-`I` quarter
`c_I ≥ m_I − m/4`; the strict owner cap `2E_I − E ≤ c_I·(ε/(6κ))`; the reserve
`c_I·(5ε/6) ≤ MR_I`; and `m_I ≤ m` — the deficit `(R_I)` holds. -/
theorem grayChargedV2_reserve_deficit_closes
    {kappa eps P E PI EI DI D MR mI m cI : Rat}
    (hkappa : 1 <= kappa) (heps : 0 < eps)
    (hDP : D = P + E) (hDPI : DI = PI + EI)
    (hMR : cI * (5 * eps / 6) <= MR)
    (hDI_up : DI <= mI * eps)
    (hDIc_lo : (m - mI) * eps / 2 <= D - DI)
    (hc_I_lo : mI - m / 4 <= cI)
    (hmI : mI <= m)
    (hEbound : 2 * EI - E <= cI * (eps / (6 * kappa))) :
    (1 / 2) * (2 * PI - P) + (kappa + 1 / 2) * (2 * EI - E) <= MR := by
  have hkpos : (0 : Rat) < kappa := lt_of_lt_of_le one_pos hkappa
  -- the amplified raised remainder is at most c_I·ε/6 (κ cancels the cap)
  have hcancel : kappa * (cI * (eps / (6 * kappa))) = cI * eps / 6 := by
    field_simp
  have hkE : kappa * (2 * EI - E) <= cI * eps / 6 :=
    le_of_le_of_eq
      (mul_le_mul_of_nonneg_left hEbound (by linarith)) hcancel
  -- rewrite (R_I) in displayed form: ½(2D_I−D) + κ(2E_I−E)
  have hconv : (1 / 2) * (2 * PI - P) + (kappa + 1 / 2) * (2 * EI - E) =
      (1 / 2) * (2 * DI - D) + kappa * (2 * EI - E) := by
    rw [hDP, hDPI]; ring
  rw [hconv]
  -- ε-scaled per-I quarter
  have hquarter : (mI - m / 4) * eps <= cI * eps :=
    mul_le_mul_of_nonneg_right hc_I_lo heps.le
  -- close: ½(2D_I−D) ≤ m_I·ε/2 − (m−m_I)·ε/4, + c_I·ε/6 ≤ c_I·5ε/6 ≤ MR (⟺ m_I ≤ m)
  nlinarith [hkE, hDI_up, hDIc_lo, hMR, hquarter, hmI, heps]

/-- **Per-root reserve lower bound** (the mirror of
`grayChargedReserveChargeV2_perRoot_mass_le_of_unit`): if every reserve record
carries mass at least `5ε/6`, the reserve charge at root `i` is at least the
number of records owned by `i` times `5ε/6`. -/
lemma grayChargedReserveChargeV2_perRoot_mass_ge_of_unit
    {q L a e n U : Nat} {A : Allocation} {sm : Nat -> FamilyServerMove}
    (reserves : List (GrayChargedReserveSourceV2 q L a e n U A sm)) (i : Nat)
    (hunit : forall r, r ∈ reserves ->
      5 * dyadicScale e / 6 <= grayChargeMass (e + grayTailNewLoss q L) r.cells) :
    ((reserves.countP fun r => decide (r.coordinate.1.val = i) : Nat) : Rat) *
        (5 * dyadicScale e / 6) <=
      grayChargeMass (e + grayTailNewLoss q L)
        (grayChargeAtRoot i (grayChargedReserveChargeV2 reserves)) := by
  classical
  rw [grayChargedReserveChargeV2, grayChargeAtRoot_flatMap,
    grayChargeMass_flatMap]
  rw [← sum_map_ite_const_rat reserves
    (fun r => decide (r.coordinate.1.val = i)) (5 * dyadicScale e / 6)]
  refine List.sum_le_sum ?_
  intro r hr
  by_cases h : r.coordinate.1.val = i
  · simp only [h, decide_true, ite_true]
    rw [grayChargeAtRoot_of_single_owner (fun z hz => r.cells_owner z hz),
      ite_eq_left h]
    exact hunit r hr
  · simp only [h, decide_false]
    rw [grayChargeAtRoot_of_single_owner (fun z hz => r.cells_owner z hz),
      ite_eq_right h, grayChargeMass_nil]
    simp

end Kolmogorov
