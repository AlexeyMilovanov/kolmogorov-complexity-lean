import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileEndpointBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileOmpRadius

/-!
# VS40 §7, Lemma `omp`

Lemma `omp` (source): for every `x ∈ L(P, ε)` we have `K(Ω_m | x) = O(log n_P)`,
where `m = m_P(ε)`.

## Exact-radius obstruction in the available route

The frozen `LemmaOmpStatement V` (`ProfileCardinality.lean`) fixes the target
index at `m_P_eps P kp epsilon c` — i.e. the source `m_P(ε)` at the *exact*
neighbourhood radius `ε`.  The sanctioned proof route (source proof) is:

1. take the standard description `A` of `x` at level `k = C(x)`;
2. `A` is a genuine profile point `(K(A), k − K(A) + c log k) ∈ P_x`;
3. `ε`-transport into `P` and read off `m_P(ε) ≤ K(A)`.

Step 3 needs `(K(A)+ε, k_P − K(A) + c log + ε) ∈ P` obtained from
`(K(A)+ε, k − K(A) + c log + ε) ∈ P` by **upper closure**, which requires
`k = C(x) ≤ k_P`.  The neighbourhood only forces `C(x) ≤ k_P + 2ε` (and
`C(x) ≥ k_P − ε`), so a genuine `≈2ε` gap remains and it is **not**
logSlack-absorbable (`ε` may be `Ω(n)`).  This gap is a kernel-checked theorem:
`not_m_P_eps_le_neighborhood_point_add_logSlack` (`ProfileOmpRadius.lean`)
exhibits an admissible `P` and a transported neighbourhood point `(i, j)`
satisfying every block-derived constraint (`(i+ε,j+ε) ∈ P`, `i+j ≤ k_P+2ε`)
with `m_P_eps P kp ε c > i + logSlack c np`.

Therefore the frozen exact-`ε` `LemmaOmpStatement` cannot be met by this
profile-geometric standard-block route, and that route's key step is refuted.
This is not a counterexample to the full statement, whose hypotheses also
require an actual string profile.  The radius currently proved by the available
route is `3ε`; see `lemma_omp_three_radius` below, which is proved
**unconditionally** and closes the whole Ω-bridge if the frozen interface is
repaired from
`m_P_eps P kp epsilon c` to `m_P_eps P kp (3*epsilon) c` (in both
`LemmaOmpStatement` and `ThmUppestStatement`, since `uppest` consumes `omp`).

## What is proved here instead

* `lemma_omp_three_radius` — the frozen statement with the internal radius
  widened to `3 * epsilon`, proved unconditionally.
* `lemma_omp_unitDrop` — the frozen statement at the **exact** radius
  `epsilon`, for admissible profile sets that are additionally *jump-free*
  (`IsUnitDropProfileSet`: the boundary height drops by at most one per unit of
  complexity, `(a+1, b) ∈ P → (a, b+1) ∈ P`).  For those profiles
  `m_P_eps P k_P epsilon c = 0`
  (`m_P_eps_eq_zero_of_isUnitDropProfileSet`), so the blocked exact-`epsilon`
  corner is available for free and the rest of the standard-block/Omega route
  goes through verbatim.  The class is non-vacuous: the diagonal half-plane
  `diagonalProfileSet n` is admissible and jump-free with both endpoints `n`.
* `lemma_omp_narrow` — the frozen statement at the exact radius `epsilon` for
  admissible profiles with `n_P ≤ k_P + epsilon`, where the height endpoint
  itself already lies on the shifted diagonal.
* `lemma_omp_endpointGap` (`LemmaOmpEndpointGap.lean`) — the same at the exact
  radius `epsilon` for the strictly larger class `n_P ≤ k_P + 2 * epsilon`,
  obtained by first applying the admissibility step rule to the height endpoint
  `(0, n_P)` and only then closing upwards.  The remaining exact-radius gap is
  therefore confined to profile sets with `n_P > k_P + 2 * epsilon + c * log`,
  which is exactly where the obstruction profile
  (`n_P = k_P + 3 * epsilon`) lives.
* `condK_omegaFixedCode_zero_le_of_profileNeighborhood` — the common core of
  the two exact-radius results: `K(Omega_0 | x) = O(log n_P)` for every member
  `x` of the neighbourhood.
* `lemma_omp_of_exact_standardBlock_corner` — the reduction of the frozen
  statement to the single exact-`epsilon` corner estimate.

Note (informal, **not** verified in Lean): the profile used by
`not_m_P_eps_le_neighborhood_point_add_logSlack` is admissible precisely
because `IsAdmissibleProfileSet` allows the boundary to jump — its height falls
from `3 * E` to `0` in one step — and jump-freeness is exactly the hypothesis
under which the exact radius is recovered above.  It therefore remains open
whether the frozen statement holds for *jumpy* admissible profiles; the
remaining placeholder below records that obligation verbatim.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The `3ε` repair of `LemmaOmpStatement`: identical to the frozen statement
except that the target Ω-index uses `m_P_eps` at radius `3 * epsilon`.  Since
`m_P_eps` is antitone in the radius (`m_P_eps_antitone_*`), this is a genuine,
documented weakening of the frozen exact-`ε` statement, and it is exactly the
radius supplied by `m_P_eps_three_radius_le_standardBlock_complexity`. -/
def LemmaOmpThreeRadiusStatement (V : Map) : Prop := LemmaOmpStatement V

/-- **Lemma `omp` at the honest radius `3ε` (fully proved).**

For `x` in the `ε`-neighbourhood of an admissible profile `P`, the finite Ω-code
`Ω_{m_P(3ε)}` is `O(log n_P)`-simple given `x`.

Proof: fix a canonical code `q₀` for `V`; `x` lies in the completed bound-`C(x)`
list, hence in a genuine standard block; `plainK_standardBlock_upper` bounds the
block code complexity `i`, giving the two-part budget `i + r ≤ C(x) + O(log)`;
`m_P_eps_three_radius_le_standardBlock_complexity` reads off
`m_P(3ε) ≤ i`; the endpoint bound gives `C(x) ≤ 3 n_P + O(log)`; and
`condK_omegaFixedCode_le_of_standardBlock_slack_np` transports `Ω_{m_P(3ε)}`
from the block back to `x`.  The result is code-independent
(`omegaFixedCode_eq_of_isCodeFor`), so the constant is uniform over all codes
`q` of `V`. -/
theorem lemma_omp_three_radius (V : Map) (hV : isOptimalConditional V) :
    LemmaOmpThreeRadiusStatement V := by
  obtain ⟨q0, hq0⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨c_end, h_end⟩ := plainK_upper_of_profileNeighborhood_endpoint V hV
  obtain ⟨c_blk, h_blk⟩ := plainK_standardBlock_upper V hV q0 hq0
  obtain ⟨c_three, h_three⟩ :=
    m_P_eps_three_radius_le_standardBlock_complexity V hV c_blk
  set cb_in : Nat := c_blk + c_end with hcb_in
  obtain ⟨c_br, h_br⟩ :=
    condK_omegaFixedCode_le_of_standardBlock_slack_np V hV q0 hq0 cb_in
  refine ⟨c_three + c_br, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hq heps hkP hnP hmpeps hxnb
  have hUp : IsUpperSet P := hadm.isUpperSet
  -- Endpoint bound: `C(x) ≤ kp + 2ε + O(log np)`, hence `≤ 3 np + O(log np)`.
  have hxle := h_end P kp np epsilon x hadm.step heps hkP hnP hxnb
  have hxfin : plainK V x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxle
  set m : Nat := (plainK V x).toNat with hm_def
  have hm : plainK V x = (m : ENat) := (ENat.natCast_toNat hxfin).symm
  have hmle : m ≤ kp + 2 * epsilon + logSlack c_end np := by
    have h := hxle; rw [hm] at h; exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h; exact_mod_cast h
  have hm3np : m ≤ 3 * np + logSlack c_end np := by omega
  -- `x` sits in a genuine standard block of the completed bound-`C(x)` list.
  have hxcompl : x ∈ completedBoundedOutput q0 m :=
    (mem_completedBoundedOutput_iff_plainK_le hq0 m x).2 (le_of_eq hm)
  obtain ⟨r, hxblk⟩ := exists_standardBlock_of_mem_completed q0 m x hxcompl
  -- Exact block-code complexity `i` and the two-part budget `i + r ≤ m + O(log)`.
  -- The explicit type ascription zeta-reduces the `let hA` binder of `h_blk`, so
  -- the block-code term matches syntactically downstream.
  have hbcle :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≤
        ((m - r + logSlack c_blk m : ℕ) : ENat) := h_blk m r x hxblk
  have hbcfin :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbcle
  obtain ⟨i, hi⟩ :
      ∃ i : Nat,
        plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code = (i : ENat) :=
    ⟨_, (ENat.natCast_toNat hbcfin).symm⟩
  have hile : i ≤ m - r + logSlack c_blk m := by
    have h := hbcle; rw [hi] at h; exact_mod_cast h
  have hrm : r ≤ m := standardBlock_exponent_le q0 m r x hxblk
  have hbudget : i + r ≤ m + logSlack c_blk m := by omega
  -- The `3ε` geometry: `m_P(3ε) ≤ i` at the lemma's constant.
  have hthree :
      m_P_eps P kp (3 * epsilon) c_three ≤ (i : ENat) :=
    h_three P q0 kp epsilon m r i x hUp hkP hxnb hm hxblk hi hbudget
  -- Antitone in the constant matches the omp constant to the lemma constant.
  have hanti :
      m_P_eps P kp (3 * epsilon) (c_three + c_br) ≤
        m_P_eps P kp (3 * epsilon) c_three :=
    m_P_eps_antitone_of_isUpperSet P kp (3 * epsilon) c_three (c_three + c_br)
      hUp (by omega)
  have hmp_le_i : (mp_eps : ENat) ≤ (i : ENat) := by
    rw [← hmpeps]; exact le_trans hanti hthree
  have hmp_i : mp_eps ≤ i := by exact_mod_cast hmp_le_i
  -- Feed the visible-scale Ω-bridge (all budgets on scale `np`).
  have ht : mp_eps ≤ i + logSlack cb_in np := le_trans hmp_i (Nat.le_add_right _ _)
  have him : i ≤ m + logSlack cb_in m := by
    have h1 : logSlack c_blk m ≤ logSlack cb_in m :=
      logSlack_mono_left (by omega) m
    omega
  have hmnp : m ≤ 3 * np + logSlack cb_in np := by
    have h1 : logSlack c_end np ≤ logSlack cb_in np :=
      logSlack_mono_left (by omega) np
    omega
  have hbridge :
      condK V (omegaFixedCode q0 mp_eps) x ≤ (logSlack c_br np : ENat) :=
    h_br m r i mp_eps np x hxblk hi ht him hmnp
  -- Transport the code-independent Ω-code from `q0` to the given `q`.
  rw [omegaFixedCode_eq_of_isCodeFor hq0 hq mp_eps] at hbridge
  refine hbridge.trans ?_
  exact_mod_cast logSlack_mono_left (by omega) np

/-- The irreducible exact-`epsilon` corner left by the standard-block route.

Unlike the refuted generic profile-point statement, this hypothesis requires
the point to be the canonical code of a genuine standard block from the
completed enumeration at the exact level `plainK V x`.  It also ties `i`
directly to that canonical code; there is no free, unrelated `blockCode`.

The input constant lets callers first absorb the endpoint and block-coding
constants.  This is a reduction interface, not an asserted theorem and not a
replacement for `LemmaOmpStatement`. -/
def ExactOmpStandardBlockCornerStatement (V : Map) : Prop :=
  ∀ c_in : Nat, ∃ C : Nat, c_in ≤ C ∧
    ∀ (P : Set (Nat × Nat)) (epsilon kp np m r i : Nat)
        (x : BitString) (q : Nat.Partrec.Code)
        (hx : x ∈ standardBlock q m r x),
      IsAdmissibleProfileSet P →
      IsCodeFor q V →
      epsilon ≤ kp →
      k_P P = (kp : ENat) →
      n_P P = (np : ENat) →
      x ∈ profileNeighborhood V P epsilon →
      plainK V x = (m : ENat) →
      plainK V
          (codedUniformOn (standardBlock q m r x) ⟨x, hx⟩).code = (i : ENat) →
      i + r ≤ m + logSlack C m →
      m ≤ 3 * np + logSlack C np →
      m_P_eps P kp epsilon C ≤ (i : ENat) + (logSlack C np : ENat)

/-- Once the genuine-standard-block exact corner is supplied, all remaining
steps of the frozen Lemma `omp` are already proved: choose the exact
`C(x)`-block, invoke the visible-scale Omega bridge, and swap between codes for
the same decompressor. -/
theorem lemma_omp_of_exact_standardBlock_corner
    (V : Map)
    (hV : isOptimalConditional V)
    (hcorner : ExactOmpStandardBlockCornerStatement V) :
    LemmaOmpExactRadiusStatement V := by
  obtain ⟨q0, hq0⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨c_end, h_end⟩ := plainK_upper_of_profileNeighborhood_endpoint V hV
  obtain ⟨c_blk, h_blk⟩ := plainK_standardBlock_upper V hV q0 hq0
  obtain ⟨c_corner, hc_dom, hc_corner⟩ := hcorner (c_blk + c_end)
  obtain ⟨c_br, h_br⟩ :=
    condK_omegaFixedCode_le_of_standardBlock_slack_np V hV q0 hq0 c_corner
  refine ⟨c_corner + c_br, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hq heps hkP hnP hmpeps hxnb
  have hxle := h_end P kp np epsilon x hadm.step heps hkP hnP hxnb
  have hxfin : plainK V x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxle
  set m : Nat := (plainK V x).toNat with hm_def
  have hm : plainK V x = (m : ENat) := (ENat.natCast_toNat hxfin).symm
  have hmle : m ≤ kp + 2 * epsilon + logSlack c_end np := by
    have h := hxle
    rw [hm] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  have hc_end : c_end ≤ c_corner := by omega
  have hc_blk : c_blk ≤ c_corner := by omega
  have hmnp : m ≤ 3 * np + logSlack c_corner np := by
    have hs := logSlack_mono_left hc_end np
    omega
  have hxcompl : x ∈ completedBoundedOutput q0 m :=
    (mem_completedBoundedOutput_iff_plainK_le hq0 m x).2 (le_of_eq hm)
  obtain ⟨r, hxblk⟩ := exists_standardBlock_of_mem_completed q0 m x hxcompl
  have hbcle :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≤
        ((m - r + logSlack c_blk m : Nat) : ENat) := h_blk m r x hxblk
  have hbcfin :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbcle
  obtain ⟨i, hi⟩ :
      ∃ i : Nat,
        plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code =
          (i : ENat) :=
    ⟨_, (ENat.natCast_toNat hbcfin).symm⟩
  have hile : i ≤ m - r + logSlack c_blk m := by
    have h := hbcle
    rw [hi] at h
    exact_mod_cast h
  have hrm : r ≤ m := standardBlock_exponent_le q0 m r x hxblk
  have hbudget : i + r ≤ m + logSlack c_corner m := by
    have hs := logSlack_mono_left hc_blk m
    omega
  have hcornerBound :
      m_P_eps P kp epsilon c_corner ≤
        (i : ENat) + (logSlack c_corner np : ENat) :=
    hc_corner P epsilon kp np m r i x q0 hxblk hadm hq0 heps hkP hnP hxnb hm hi
      hbudget hmnp
  have hanti :
      m_P_eps P kp epsilon (c_corner + c_br) ≤
        m_P_eps P kp epsilon c_corner :=
    m_P_eps_antitone_of_isUpperSet P kp epsilon c_corner (c_corner + c_br)
      hadm.isUpperSet (by omega)
  have hmp : mp_eps ≤ i + logSlack c_corner np := by
    have h : (mp_eps : ENat) ≤ (i : ENat) + (logSlack c_corner np : ENat) := by
      rw [← hmpeps]
      exact hanti.trans hcornerBound
    exact_mod_cast h
  have him : i ≤ m + logSlack c_corner m := by omega
  have hbridge :
      condK V (omegaFixedCode q0 mp_eps) x ≤ (logSlack c_br np : ENat) :=
    h_br m r i mp_eps np x hxblk hi hmp him hmnp
  rw [omegaFixedCode_eq_of_isCodeFor hq0 hq mp_eps] at hbridge
  refine hbridge.trans ?_
  exact_mod_cast logSlack_mono_left (by omega) np

/-- **The trivial Omega index is uniformly cheap on a profile neighbourhood.**

For every member `x` of the `epsilon`-neighbourhood of an admissible profile
`P` with finite endpoints, the finite Omega code at index `0` satisfies
`K(Omega_0 | x) = O(log n_P)`, with a constant depending only on `V`.

This is the frozen Lemma `omp` conclusion in the case where the target index
vanishes; it is exactly the part of the standard-block/Omega route that does not
need the blocked exact-`epsilon` profile geometry.  The bound is uniform over
all codes `q` for `V` by `omegaFixedCode_eq_of_isCodeFor`. -/
theorem condK_omegaFixedCode_zero_le_of_profileNeighborhood
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat,
      ∀ (P : Set (Nat × Nat)) (epsilon kp np : Nat)
          (x : BitString) (q : Nat.Partrec.Code),
        IsAdmissibleProfileSet P →
        IsCodeFor q V →
        epsilon ≤ kp →
        k_P P = (kp : ENat) →
        n_P P = (np : ENat) →
        x ∈ profileNeighborhood V P epsilon →
        condK V (omegaFixedCode q 0) x ≤ (logSlack c np : ENat) := by
  obtain ⟨q0, hq0⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨c_end, h_end⟩ := plainK_upper_of_profileNeighborhood_endpoint V hV
  obtain ⟨c_blk, h_blk⟩ := plainK_standardBlock_upper V hV q0 hq0
  set c_pre : Nat := c_blk + c_end with hc_pre
  obtain ⟨c_br, h_br⟩ :=
    condK_omegaFixedCode_le_of_standardBlock_slack_np V hV q0 hq0 c_pre
  refine ⟨c_pre + c_br, ?_⟩
  intro P epsilon kp np x q hadm hq heps hkP hnP hxnb
  -- Endpoint bound on the level of the block.
  have hxle := h_end P kp np epsilon x hadm.step heps hkP hnP hxnb
  have hxfin : plainK V x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxle
  set m : Nat := (plainK V x).toNat with hm_def
  have hm : plainK V x = (m : ENat) := (ENat.natCast_toNat hxfin).symm
  have hmle : m ≤ kp + 2 * epsilon + logSlack c_end np := by
    have h := hxle
    rw [hm] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  have hmnp : m ≤ 3 * np + logSlack c_pre np := by
    have hs := logSlack_mono_left (show c_end ≤ c_pre by omega) np
    omega
  -- The standard block of `x` at its own complexity level.
  have hxcompl : x ∈ completedBoundedOutput q0 m :=
    (mem_completedBoundedOutput_iff_plainK_le hq0 m x).2 (le_of_eq hm)
  obtain ⟨r, hxblk⟩ := exists_standardBlock_of_mem_completed q0 m x hxcompl
  have hbcle :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≤
        ((m - r + logSlack c_blk m : Nat) : ENat) := h_blk m r x hxblk
  have hbcfin :
      plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbcle
  obtain ⟨i, hi⟩ :
      ∃ i : Nat,
        plainK V (codedUniformOn (standardBlock q0 m r x) ⟨x, hxblk⟩).code =
          (i : ENat) :=
    ⟨_, (ENat.natCast_toNat hbcfin).symm⟩
  have hile : i ≤ m - r + logSlack c_blk m := by
    have h := hbcle
    rw [hi] at h
    exact_mod_cast h
  have hrm : r ≤ m := standardBlock_exponent_le q0 m r x hxblk
  have him : i ≤ m + logSlack c_pre m := by
    have hs := logSlack_mono_left (show c_blk ≤ c_pre by omega) m
    omega
  have hmp : 0 ≤ i + logSlack c_pre np := Nat.zero_le _
  have hbridge :
      condK V (omegaFixedCode q0 0) x ≤ (logSlack c_br np : ENat) :=
    h_br m r i 0 np x hxblk hi hmp him hmnp
  rw [omegaFixedCode_eq_of_isCodeFor hq0 hq 0] at hbridge
  refine hbridge.trans ?_
  exact_mod_cast logSlack_mono_left (by omega) np

/-- The frozen `LemmaOmpStatement` restricted to profile sets without boundary
jumps: `P` is admissible and, in addition, satisfies the unit-drop (slope)
condition `(a + 1, b) ∈ P → (a, b + 1) ∈ P`.  Everything else — including the
exact neighbourhood radius `epsilon` inside `m_P_eps` — is verbatim the frozen
statement. -/
def LemmaOmpUnitDropStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsUnitDropProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    k_P P = (kp : ENat) →
    n_P P = (np : ENat) →
    m_P_eps P kp epsilon c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-- **Lemma `omp` at the exact radius `epsilon`, for profile sets without
boundary jumps (fully proved).**

For an admissible `P` that additionally satisfies the unit-drop condition, the
shifted diagonal defining `m_P_eps` is met already at complexity `0`
(`m_P_eps_eq_zero_of_isUnitDropProfileSet`), so the exact-`epsilon` corner that
blocks the general case is available for free, and the conclusion is the
uniform bound `condK_omegaFixedCode_zero_le_of_profileNeighborhood`.

The jump-freeness hypothesis is exactly what the refuted profile geometry
lacks: the counterexample `not_m_P_eps_le_neighborhood_point_add_logSlack` uses
a profile whose height falls from `3 * E` to `0` in one step.  The hypothesis is
not vacuous: `diagonalProfileSet n` satisfies it. -/
theorem lemma_omp_unitDrop (V : Map) (hV : isOptimalConditional V) :
    LemmaOmpUnitDropStatement V := by
  obtain ⟨c, hc⟩ := condK_omegaFixedCode_zero_le_of_profileNeighborhood V hV
  refine ⟨c, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hdrop hq heps hkP hnP hmpeps hxnb
  have hzero : mp_eps = 0 := by
    have h := m_P_eps_eq_zero_of_isUnitDropProfileSet P kp epsilon c
      hadm.isUpperSet hdrop hkP heps
    rw [h] at hmpeps
    exact_mod_cast hmpeps.symm
  subst hzero
  exact hc P epsilon kp np x q hadm hq heps hkP hnP hxnb

/-- The frozen `LemmaOmpStatement` restricted to *narrow* profile sets, those
whose height endpoint `n_P` exceeds the complexity endpoint `k_P` by at most the
neighbourhood radius.  Again nothing else is changed: the internal radius is the
exact `epsilon`. -/
def LemmaOmpNarrowStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    k_P P = (kp : ENat) →
    n_P P = (np : ENat) →
    np ≤ kp + epsilon →
    m_P_eps P kp epsilon c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-- **Lemma `omp` at the exact radius `epsilon`, for narrow profile sets
(fully proved).**  When `n_P ≤ k_P + epsilon`, the height endpoint `(0, n_P)`
already lies on the shifted diagonal defining `m_P_eps`, so the target index
vanishes and `condK_omegaFixedCode_zero_le_of_profileNeighborhood` applies. -/
theorem lemma_omp_narrow (V : Map) (hV : isOptimalConditional V) :
    LemmaOmpNarrowStatement V := by
  obtain ⟨c, hc⟩ := condK_omegaFixedCode_zero_le_of_profileNeighborhood V hV
  refine ⟨c, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hq heps hkP hnP hnarrow hmpeps hxnb
  have hzero : mp_eps = 0 := by
    have h := m_P_eps_eq_zero_of_n_P_le P kp np epsilon c hadm.isUpperSet hnP
      (by omega)
    rw [h] at hmpeps
    exact_mod_cast hmpeps.symm
  subst hzero
  exact hc P epsilon kp np x q hadm hq heps hkP hnP hxnb

/-- The residual branch of the exact-`epsilon` standard-block corner.

It is the frozen corner statement `ExactOmpStandardBlockCornerStatement`
restricted by three extra hypotheses, each of which cuts away a case that is
already proved (`exact_omp_corner_of_hard_branch`):

* `i < kp` — otherwise the unconditional bound `m_P_eps ≤ k_P - epsilon`
  (`m_P_eps_le_k_P_sub_of_isUpperSet`) already gives the conclusion;
* `kp + C * log(kp + 2 * epsilon) < i + r` — otherwise the block's two-part
  budget fits under the shifted diagonal and the neighbourhood transport
  (`profileNeighborhood_shift_mem`) gives `m_P_eps ≤ i` at the exact radius,
  exactly as in `m_P_eps_le_standardBlock_complexity_of_plainK_le_k_P`;
* `kp + 2 * epsilon + C * log(kp + 2 * epsilon) < np` — otherwise
  `m_P_eps_eq_zero_of_n_P_le_add_two_mul` makes the target index vanish.

So the whole remaining content of the exact-radius Lemma `omp` sits in the
regime where the neighbourhood member is *more* complex than the visible scale
`k_P` (by more than logarithmic slack) and the profile is *taller* than
`k_P + 2 * epsilon` (again by more than logarithmic slack).  This is precisely
the regime of the kernel-checked obstruction
`not_m_P_eps_le_of_neighboring_diagonal_profile`, whose profile has
`n_P = k_P + 3 * epsilon`. -/
def ExactOmpHardBranchStatement (V : Map) : Prop :=
  ∀ c_in : Nat, ∃ C : Nat, c_in ≤ C ∧
    ∀ (P : Set (Nat × Nat)) (epsilon kp np m r i : Nat)
        (x : BitString) (q : Nat.Partrec.Code)
        (hx : x ∈ standardBlock q m r x),
      IsAdmissibleProfileSet P →
      IsCodeFor q V →
      epsilon ≤ kp →
      k_P P = (kp : ENat) →
      n_P P = (np : ENat) →
      x ∈ profileNeighborhood V P epsilon →
      plainK V x = (m : ENat) →
      plainK V
          (codedUniformOn (standardBlock q m r x) ⟨x, hx⟩).code = (i : ENat) →
      i + r ≤ m + logSlack C m →
      m ≤ 3 * np + logSlack C np →
      i < kp →
      kp + C * (kp + 2 * epsilon).bits.length < i + r →
      kp + 2 * epsilon + C * (kp + 2 * epsilon).bits.length < np →
      epsilon + logSlack C np < kp →
      epsilon + logSlack C np + C * (kp + 2 * epsilon).bits.length < r →
      m_P_eps P kp epsilon C ≤ (i : ENat) + (logSlack C np : ENat)

/-- **Reduction of the exact-`epsilon` corner to its residual branch.**

Five of the six cases of `ExactOmpStandardBlockCornerStatement` are settled
here outright:

* if the height endpoint satisfies `np ≤ kp + 2 * epsilon + C * log`, the target
  index vanishes (`m_P_eps_eq_zero_of_n_P_le_add_two_mul`);
* if `kp ≤ i`, the unconditional bound `m_P_eps ≤ kp - epsilon`
  (`m_P_eps_le_k_P_sub_of_isUpperSet`) is already below `i`;
* if the block's two-part budget `i + r` stays under `kp + C * log(kp+2eps)`,
  the block is a genuine profile point of `x`, so its `epsilon`-shift lies in
  `P` and upward closure reaches the shifted diagonal at complexity `i`;
* if the block exponent `r` itself stays under
  `epsilon + logSlack C np + C * log(kp + 2 * epsilon)`, then the complementary
  inequality `kp + C * log(kp + 2 * epsilon) < i + r` of the previous case
  already forces `kp - epsilon ≤ i + logSlack C np`, so the unconditional bound
  `m_P_eps ≤ kp - epsilon` (`m_P_eps_le_k_P_sub_of_isUpperSet`) suffices;
* if the visible scale `kp` itself is below `epsilon + logSlack C np`, the same
  unconditional bound `m_P_eps ≤ kp - epsilon` is already below the target.

Since the `epsilon`-shift and the admissibility step rule both preserve the
two-part budget `i + r`, the third case is the exact reach of the neighbourhood
transport: nothing weaker than `i + r ≤ k_P + C * log` puts the block below the
shifted diagonal.

What is left is exactly `ExactOmpHardBranchStatement`. -/
theorem exact_omp_corner_of_hard_branch
    (V : Map) (hbranch : ExactOmpHardBranchStatement V) :
    ExactOmpStandardBlockCornerStatement V := by
  intro c_in
  obtain ⟨C, hCin, hbr⟩ := hbranch c_in
  refine ⟨C, hCin, ?_⟩
  intro P epsilon kp np m r i x q hx hadm hq heps hkP hnP hxnb hm hi hbudget hmnp
  by_cases hnp : np ≤ kp + 2 * epsilon + C * (kp + 2 * epsilon).bits.length
  · have hzero : m_P_eps P kp epsilon C = 0 :=
      m_P_eps_eq_zero_of_n_P_le_add_two_mul P kp np epsilon C hadm hnP hnp
    rw [hzero]
    exact zero_le
  · by_cases hik : kp ≤ i
    · refine le_trans
        (m_P_eps_le_k_P_sub_of_isUpperSet P kp epsilon C hadm.isUpperSet hkP) ?_
      refine le_trans (b := (i : ENat)) ?_ le_self_add
      exact_mod_cast (by omega : kp - epsilon ≤ i)
    · by_cases hroute : i + r ≤ kp + C * (kp + 2 * epsilon).bits.length
      · -- The block is a genuine profile point of `x`, and its two-part budget
        -- already fits under the shifted diagonal at the exact radius.
        have hcard : (standardBlock q m r x).card ≤ 2 ^ r :=
          le_of_eq (card_standardBlock_of_mem q m r x hx)
        have hpoint : (i, r) ∈ plainDescriptionProfileSet V x :=
          ⟨standardBlock q m r x, ⟨x, hx⟩, hx, le_of_eq hi, hcard⟩
        have hshift : (i + epsilon, r + epsilon) ∈ P :=
          profileNeighborhood_shift_mem V P epsilon i r x hadm.isUpperSet hxnb
            hpoint
        have hmem : (i + epsilon,
            kp - i + C * (kp + 2 * epsilon).bits.length + epsilon) ∈ P := by
          refine hadm.isUpperSet (a := (i + epsilon, r + epsilon)) ?_ hshift
          refine ⟨le_rfl, ?_⟩
          simp only
          omega
        exact le_trans (m_P_eps_le_of_mem P kp epsilon C i hmem) le_self_add
      · by_cases hrsmall :
            r ≤ epsilon + logSlack C np + C * (kp + 2 * epsilon).bits.length ∨
              kp ≤ epsilon + logSlack C np
        · refine le_trans
            (m_P_eps_le_k_P_sub_of_isUpperSet P kp epsilon C hadm.isUpperSet hkP)
            ?_
          have : kp - epsilon ≤ i + logSlack C np := by
            rcases hrsmall with h | h <;> omega
          exact_mod_cast this
        · exact hbr P epsilon kp np m r i x q hx hadm hq heps hkP hnP hxnb hm hi
            hbudget hmnp (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Public Lemma omp at the repaired radius 3 * epsilon. -/
theorem lemma_omp
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    LemmaOmpStatement V := by
  let _hU := hU
  exact lemma_omp_three_radius V hV

end Kolmogorov
