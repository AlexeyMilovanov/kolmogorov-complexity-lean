import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.SourceLedger
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport.Reserves
import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedClosureSupport

/-!
# v15 step 2: the computable raised-service test (controller-side)

Proof document v15.1, A3: after the advantage exit the client repeats its move
until every SUV-raised source son is served at scale `2^-e`, and only then
starts the spend passes.  This module defines the Boolean test the controller
runs on the frozen ledger (V1 shape `GrayTailFrozen`, the shape of the
classification `grayChargedRaisedSources`) and the current server move,
proves its specification against `grayChargedRaisedSources` and `Serves`, and
shows that it is monotone in the server time.  It sits below the V2
controller in the import graph; the run-level exit theorem is in
`GacsDayV2WaitTest`.
-/

namespace Kolmogorov

/-- Boolean form of `Serves`: some allocated cylinder has mass at least
`req`. -/
def servesB (alloc : Allocation) (req : ℚ) : Bool :=
  alloc.any fun c => decide (req ≤ (1 / 2 : ℚ) ^ c.length)

/-- The decidable service test agrees with `Serves`. -/
lemma servesB_eq_true_iff {alloc : Allocation} {req : ℚ} :
    servesB alloc req = true ↔ Serves alloc req := by
  unfold servesB Serves
  simp only [List.any_eq_true, decide_eq_true_eq]
  have hcast : ∀ k : ℕ, (((1 / 2 : ℚ) ^ k : ℚ) : ℝ) = (1 / 2 : ℝ) ^ k := by
    intro k
    simp
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    rw [← hcast]
    exact Rat.cast_le.mpr h
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    rw [← hcast] at h
    exact Rat.cast_le.mp h

/-- The raised-service test: every raised source son of the frozen ledger, that is every `(i, j)`
with `j < used` and frozen son base above `threshold`, is served at scale `2 ^ -e` by the server
move `sm`. -/
def grayChargedRaisedServedB {n b : ℕ} (e used : ℕ) (threshold : ℚ)
    (frozen : GrayTailFrozen n b) (sm : FamilyServerMove) : Bool :=
  (List.finRange n).all fun i => (List.finRange b).all fun j =>
    if j.val < used ∧ threshold < grayTailFrozenSonBase frozen i j then
      servesB (getFamilyAlloc sm i.val [j.val]) (dyadicScale e)
    else true

/-- Specification of the test against the classical raised class. -/
theorem grayChargedRaisedServedB_eq_true_iff {n b : ℕ} {e used : ℕ}
    {threshold : ℚ} {frozen : GrayTailFrozen n b} {sm : FamilyServerMove} :
    grayChargedRaisedServedB e used threshold frozen sm = true ↔
      ∀ z ∈ grayChargedRaisedSources used threshold frozen,
        Serves (getFamilyAlloc sm z.1.val [z.2.val]) (dyadicScale e) := by
  classical
  unfold grayChargedRaisedServedB
  simp only [List.all_eq_true]
  constructor
  · intro h z hz
    have hmem : z.2.val < used ∧ threshold < grayTailFrozenSonBase frozen z.1 z.2 :=
      (Finset.mem_filter.mp hz).2
    have hz' := h z.1 (List.mem_finRange _) z.2 (List.mem_finRange _)
    rw [ite_eq_left hmem] at hz'
    exact servesB_eq_true_iff.mp hz'
  · intro h i _ j _
    by_cases hij : j.val < used ∧ threshold < grayTailFrozenSonBase frozen i j
    · rw [ite_eq_left hij]
      exact servesB_eq_true_iff.mpr
        (h (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩))
    · rw [ite_eq_right hij]

/-- The test is monotone in the server time: service persists under legal
server play (`serves_mono_time`). -/
theorem grayChargedRaisedServedB_mono_time {n b : ℕ} {e used : ℕ} {threshold : ℚ}
    {frozen : GrayTailFrozen n b} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) {u v : ℕ} (huv : u ≤ v)
    (h : grayChargedRaisedServedB e used threshold frozen (sm u) = true) :
    grayChargedRaisedServedB e used threshold frozen (sm v) = true := by
  rw [grayChargedRaisedServedB_eq_true_iff] at h ⊢
  intro z hz
  exact serves_mono_time (hsm.1 z.1.val z.1.isLt) huv (h z hz)

end Kolmogorov
