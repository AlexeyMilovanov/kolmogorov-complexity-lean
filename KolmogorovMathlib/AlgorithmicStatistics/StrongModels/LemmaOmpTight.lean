import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmp

/-!
# Lemma `omp` at the exact radius for tight-complexity neighbourhood members

The frozen `LemmaOmpStatement` is blocked at the exact radius `epsilon` only by
the possibility that a member `x` of the `epsilon`-neighbourhood of `P` has
complexity strictly above the endpoint `k_P`; the neighbourhood only forces
`C(x) ≤ k_P + 2 * epsilon`, and the missing `2 * epsilon` is not absorbable by
logarithmic slack (`ProfileOmpExactObstruction.lean`).

This module discharges the exact-radius statement for the complementary class:
neighbourhood members whose complexity does not exceed the endpoint,
`C(x) ≤ k_P`.  For those, the standard-block route of the source proof goes
through verbatim at the exact radius:

* `m_P_eps_le_standardBlock_complexity_of_plainK_le_k_P` — the exact-`epsilon`
  corner for a genuine standard block of such an `x`;
* `lemma_omp_tightComplexity` — the resulting exact-radius Lemma `omp`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **The exact-`epsilon` corner for a tight-complexity neighbourhood member.**

If `x` lies in the `epsilon`-neighbourhood of an admissible `P`, has complexity
`m ≤ k_P`, and `(i, r)` is the two-part budget of a genuine standard block of
`x` at level `m`, then the shifted diagonal defining `m_P_eps` at the *exact*
radius `epsilon` is met at complexity `i`. -/
theorem m_P_eps_le_standardBlock_complexity_of_plainK_le_k_P
    (V : Map) (P : Set (Nat × Nat)) (kp epsilon c c' i r m : Nat) (x : BitString)
    (hUp : IsUpperSet P)
    (hkP : k_P P = (kp : ENat))
    (hx : x ∈ profileNeighborhood V P epsilon)
    (hpoint : (i, r) ∈ plainDescriptionProfileSet V x)
    (hmkp : m ≤ kp)
    (hbudget : i + r ≤ m + logSlack c m)
    (hc : 2 * c ≤ c') :
    m_P_eps P kp epsilon c' ≤ (i : ENat) := by
  rcases Nat.lt_or_ge i kp with hik | hik
  · have hkpos : 1 ≤ kp := by omega
    have hshift : (i + epsilon, r + epsilon) ∈ P :=
      profileNeighborhood_shift_mem V P epsilon i r x hUp hx hpoint
    refine m_P_eps_le_of_mem P kp epsilon c' i ?_
    refine hUp (a := (i + epsilon, r + epsilon)) ?_ hshift
    refine ⟨le_rfl, ?_⟩
    simp only
    -- `r ≤ kp - i + c' * (bits (kp + 2 * epsilon)).length`
    have hLm : (Nat.bits m).length ≤ (Nat.bits (kp + 2 * epsilon)).length :=
      length_natBits_mono (by omega)
    have hLpos : 1 ≤ (Nat.bits (kp + 2 * epsilon)).length := by
      have := length_natBits_mono (show 1 ≤ kp + 2 * epsilon by omega)
      simpa using this
    have h1 : c * (Nat.bits m).length ≤
        c * (Nat.bits (kp + 2 * epsilon)).length :=
      Nat.mul_le_mul_left _ hLm
    have h2 : c ≤ c * (Nat.bits (kp + 2 * epsilon)).length := by
      calc c = c * 1 := (Nat.mul_one c).symm
        _ ≤ c * (Nat.bits (kp + 2 * epsilon)).length :=
            Nat.mul_le_mul_left _ hLpos
    have h3 : 2 * c * (Nat.bits (kp + 2 * epsilon)).length ≤
        c' * (Nat.bits (kp + 2 * epsilon)).length :=
      Nat.mul_le_mul_right _ hc
    have h4 : 2 * c * (Nat.bits (kp + 2 * epsilon)).length =
        c * (Nat.bits (kp + 2 * epsilon)).length +
          c * (Nat.bits (kp + 2 * epsilon)).length := by ring
    unfold logSlack at hbudget
    omega
  · exact (m_P_eps_le_k_P_of_eq P kp epsilon c' hUp hkP).trans (by exact_mod_cast hik)

/-- The frozen `LemmaOmpStatement` restricted to neighbourhood members whose
plain complexity does not exceed the complexity endpoint `k_P`.  Everything
else, including the exact neighbourhood radius `epsilon` inside `m_P_eps`, is
verbatim the frozen statement. -/
def LemmaOmpTightComplexityStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    k_P P = (kp : ENat) →
    n_P P = (np : ENat) →
    m_P_eps P kp epsilon c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    plainK V x ≤ (kp : ENat) →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-- **Lemma `omp` at the exact radius `epsilon`, for tight-complexity members
(fully proved).**

For `x` in the `epsilon`-neighbourhood of an admissible profile `P` with
`C(x) ≤ k_P`, the finite Ω-code `Ω_{m_P(epsilon)}` at the *exact* radius is
`O(log n_P)`-simple given `x`.

Proof: take the standard block of `x` at level `C(x)`; it is a genuine profile
point of `x` with two-part budget `C(x) + O(log)`, so
`m_P_eps_le_standardBlock_complexity_of_plainK_le_k_P` reads off
`m_P(epsilon) ≤ i`, and the visible-scale Ω-bridge transports `Ω_{m_P(epsilon)}`
back to `x`.  The bound is code-independent. -/
theorem lemma_omp_tightComplexity (V : Map) (hV : isOptimalConditional V) :
    LemmaOmpTightComplexityStatement V := by
  obtain ⟨q0, hq0⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨c_blk, h_blk⟩ := plainK_standardBlock_upper V hV q0 hq0
  set c_corner : Nat := 2 * c_blk with hc_corner
  obtain ⟨c_br, h_br⟩ :=
    condK_omegaFixedCode_le_of_standardBlock_slack_np V hV q0 hq0 c_corner
  refine ⟨c_corner + c_br, ?_⟩
  intro P epsilon kp np mp_eps x q hadm hq heps hkP hnP hmpeps hxnb hxK
  have hxfin : plainK V x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxK
  set m : Nat := (plainK V x).toNat with hm_def
  have hm : plainK V x = (m : ENat) := (ENat.natCast_toNat hxfin).symm
  have hmkp : m ≤ kp := by
    have h := hxK
    rw [hm] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  have hmnp : m ≤ 3 * np + logSlack c_corner np := by omega
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
  have hbudget : i + r ≤ m + logSlack c_blk m := by omega
  -- The block is a genuine profile point of `x`.
  have hcard : (standardBlock q0 m r x).card ≤ 2 ^ r :=
    le_of_eq (card_standardBlock_of_mem q0 m r x hxblk)
  have hpoint : (i, r) ∈ plainDescriptionProfileSet V x :=
    ⟨standardBlock q0 m r x, ⟨x, hxblk⟩, hxblk, le_of_eq hi, hcard⟩
  -- The exact-`epsilon` corner.
  have hcorner : m_P_eps P kp epsilon c_corner ≤ (i : ENat) :=
    m_P_eps_le_standardBlock_complexity_of_plainK_le_k_P V P kp epsilon c_blk
      c_corner i r m x hadm.isUpperSet hkP hxnb hpoint hmkp hbudget (by omega)
  have hanti :
      m_P_eps P kp epsilon (c_corner + c_br) ≤ m_P_eps P kp epsilon c_corner :=
    m_P_eps_antitone_of_isUpperSet P kp epsilon c_corner (c_corner + c_br)
      hadm.isUpperSet (by omega)
  have hmp : mp_eps ≤ i + logSlack c_corner np := by
    have h : (mp_eps : ENat) ≤ (i : ENat) := by
      rw [← hmpeps]
      exact hanti.trans hcorner
    have h' : mp_eps ≤ i := by exact_mod_cast h
    omega
  have him : i ≤ m + logSlack c_corner m := by
    have hs : logSlack c_blk m ≤ logSlack c_corner m :=
      logSlack_mono_left (by omega) m
    omega
  have hbridge :
      condK V (omegaFixedCode q0 mp_eps) x ≤ (logSlack c_br np : ENat) :=
    h_br m r i mp_eps np x hxblk hi hmp him hmnp
  rw [omegaFixedCode_eq_of_isCodeFor hq0 hq mp_eps] at hbridge
  refine hbridge.trans ?_
  exact_mod_cast logSlack_mono_left (by omega) np

end Kolmogorov
