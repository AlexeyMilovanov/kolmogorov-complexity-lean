import KolmogorovMathlib.MonotoneComplexity.GacsDayV2ReserveSupport
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderRelocation
import KolmogorovMathlib.MonotoneComplexity.GacsDayV2HarvestKill

/-!
# v15 support: reserve validity by coherence, and the raised-service wait exit

Two anchoring-free ingredients of the Gács-faithful repair (blueprint "v15
implementation spec", steps 2–3):

* a tail reserve at a son's node is comparable with a ROOT allocation by
  server coherence (`allocationSubset_getAlloc_cons`), so reserve-complement
  cells are valid new-gray cells at the reserve depth without any allocated
  prefix (`newGrayCell_of_reserve_prefix`);
* the exit of the raised-service wait: unless the V2 client wins the positive
  game, every displayed positive request on a finite list of son nodes is
  served at one common later time (`grayChargedV2_all_served_of_not_positive`),
  in particular every SUV-raised source son's ε-request after the advantage exit
  (`grayChargedReplayV2_raised_all_served_of_not_positive`).
-/

namespace Kolmogorov

/-- A tail reserve at a son's node is comparable with a root allocation. -/
lemma tailReserve_comparable_root {e b : Nat} {A : Allocation} {m : ServerMove}
    {c : Nat} {R : BitString}
    (hcoh : serverMoveCoherent b m) (hc : c < b)
    (hR : IsTailReserve e b A m [c] R) :
    ∃ y ∈ getAlloc m [], R <+: y ∨ y <+: R := by
  obtain ⟨-, ⟨v, hv, hRv⟩, -, -⟩ := hR
  obtain ⟨y, hy, hyv⟩ := allocationSubset_getAlloc_cons hcoh hc v hv
  refine ⟨y, hy, ?_⟩
  rcases hRv with hRv | hvR
  · exact List.prefix_or_prefix_of_prefix hRv hyv
  · exact Or.inr (hyv.trans hvR)

/-- A family tail reserve at a son's node is comparable with a root
allocation of its tree. -/
lemma tailFamilyReserve_comparable_root {e b n i c t : Nat} {A : Allocation}
    {sm : Nat -> FamilyServerMove} {R : BitString}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n) (hc : c < b)
    (hR : IsTailFamilyReserve e b A n i (sm t) [c] R) :
    ∃ y ∈ getFamilyAlloc (sm t) i [], R <+: y ∨ y <+: R :=
  tailReserve_comparable_root ((hsm.1 i hi).1 t) hc hR.1

/-- A cell of depth `D` extending a reserve cylinder `R` of length `e` that is
comparable with a root allocation, and fresh w.r.t. `A`, is a valid new-gray
cell at `(e, D]` — no allocated prefix needed. -/
lemma newGrayCell_of_reserve_prefix {e D : Nat} {S U : List BitString}
    {R z : BitString}
    (hRz : R <+: z) (hRlen : R.length = e) (hzlen : z.length = D)
    (hcmp : ∃ y ∈ S, R <+: y ∨ y <+: R)
    (hfresh : ¬ ∃ u ∈ U, z <+: u ∨ u <+: z) :
    z ∈ newGrayCellsList e D S U := by
  rw [mem_newGrayCellsList]
  refine ⟨hzlen, ?_, hfresh⟩
  obtain ⟨y, hy, hRy⟩ := hcmp
  have htake : z.take e = R := by
    have h := List.prefix_iff_eq_take.mp hRz
    rw [hRlen] at h
    exact h.symm
  exact ⟨y, hy, by rw [htake]; exact hRy⟩

/-- **Common service horizon**: unless the V2 client wins the positive game,
the displayed positive requests at finitely many son nodes are all served at
one later time. -/
theorem grayChargedV2_all_served_of_not_positive
    {q L a e n T : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (zs : List (Fin n × Fin (grayTailBranch q L a e)))
    (hpos : ∀ z ∈ zs, 0 < getFamilyReq
      (grayChargedRunMoveV2 q L a e n sigma A sm T) z.1.val [z.2.val]) :
    ∃ u, ∀ z ∈ zs, Serves (getFamilyAlloc (sm u) z.1.val [z.2.val])
      (getFamilyReq (grayChargedRunMoveV2 q L a e n sigma A sm T)
        z.1.val [z.2.val]) := by
  induction zs with
  | nil => exact ⟨0, by simp⟩
  | cons z zs ih =>
      obtain ⟨u1, hu1⟩ := ih (fun w hw => hpos w (List.mem_cons_of_mem _ hw))
      have hlen : [z.2.val].length <= 2 * (q + 1) := by
        simp only [List.length_singleton]
        omega
      have hx : ∀ d ∈ [z.2.val], d < grayTailBranch q L a e := by
        intro d hd
        rw [List.mem_singleton] at hd
        rw [hd]
        exact z.2.isLt
      obtain ⟨u2, hu2⟩ := grayChargedV2_exists_serves_of_not_positive hnotpos
        z.1.isLt T [z.2.val] hlen hx (hpos z List.mem_cons_self)
      refine ⟨max u1 u2, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with hwz | hw
      · subst hwz
        exact serves_mono_time (hsm.1 w.1.val w.1.isLt) (le_max_right u1 u2) hu2
      · exact serves_mono_time (hsm.1 w.1.val w.1.isLt) (le_max_left u1 u2)
          (hu1 w hw)

/-- **The raised-service wait exits**: unless the client wins the positive game,
all SUV-raised source sons of the final replay are served at scale `2^-e` at
one common time. -/
theorem grayChargedReplayV2_raised_all_served_of_not_positive
    {q L a e n T U : Nat} {sigma : FamilyStrategyScheme} {A : Allocation}
    {sm : Nat -> FamilyServerMove}
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hnotpos : ¬ GrayChargedPositiveV2 q L a e n sigma A sm)
    (replay : GrayChargedFinalReplayV2 q L a e n sigma A sm T)
    (hU : T + 1 <= U) :
    ∃ u, ∀ z ∈ grayChargedReplayV2RaisedSources replay,
      Serves (getFamilyAlloc (sm u) z.1.val [z.2.val]) (dyadicScale e) := by
  classical
  obtain ⟨u, hu⟩ := grayChargedV2_all_served_of_not_positive (T := U) hsm hnotpos
    (grayChargedReplayV2RaisedSources replay).toList
    (fun z hz => by
      rw [grayChargedReplayV2_raised_display_eq replay hU (Finset.mem_toList.mp hz)]
      exact dyadicScale_pos e)
  refine ⟨u, fun z hz => ?_⟩
  have hz' := hu z (Finset.mem_toList.mpr hz)
  rwa [grayChargedReplayV2_raised_display_eq replay hU hz] at hz'

end Kolmogorov
