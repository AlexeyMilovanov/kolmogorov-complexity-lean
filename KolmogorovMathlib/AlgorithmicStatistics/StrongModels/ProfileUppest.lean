import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmp
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileEndpointBound
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainSymmetry

/-!
# VS40 §7, Theorem `uppest` — the S9 upper bound on `#L(P, ε)`

Theorem `uppest` (source): `log #L(P, ε) ≤ k_P − m_P(ε) + 2ε + O(log n_P)`.

## Reduction to Lemma `omp`

The public endpoint `thm_uppest : ThmUppestStatement V` is here reduced, in a
single kernel-checked proof, to the frozen exact-`ε` `lemma_omp`
(`LemmaOmpStatement V`, still an open leaf — the only genuine obstruction on this
track; see `LemmaOmp.lean` for the exact-`ε` refutation of the profile-geometry
route and the fully-proved `3ε` companion `lemma_omp_three_radius`).

The subtlety solved here is the shared-constant design of both frozen
interfaces.  `LemmaOmpStatement` fixes *one* constant `c_omp` used both as the
`m_P_eps` index and as its own logarithmic slack, while the symmetry-of-
information reduction adds independent slacks (endpoint bound, Omega
lower/upper, SOI).  A naive intermediate `K(x | Ω_{m_P_eps ... c}) ≤ …` at the
caller's constant `c` would require an Omega-index bridge to reconcile the two
indices.  We avoid it entirely:

* count with **lemma_omp's own index** `m_omp = m_P_eps P k_P ε c_omp`
  (so `lemma_omp` applies verbatim: `K(Ω_{m_omp} | x) ≤ logSlack c_omp n_P`);
* `condK_reverse_of_plain_complexity_gap` (SOI) then bounds
  `K(x | Ω_{m_omp}) ≤ (k_P − m_omp) + 2ε + O(log n_P)`, using the endpoint bound
  `C(x) ≤ k_P + 2ε + O(log n_P)` and `C(Ω_{m_omp}) ≥ m_omp − O(1)`;
* `finiteSetLogCard_le_condK_budget` turns this into
  `log #S ≤ (k_P − m_omp) + 2ε + O(log n_P)`;
* finally `m_omp ≥ mp_eps` (antitonicity of `m_P_eps` in the constant, once the
  `uppest` constant is chosen `≥ c_omp`) gives `k_P − m_omp ≤ k_P − mp_eps`, so
  the bound is `≤ k_P − mp_eps + 2ε + logSlack c n_P` — exactly the frozen
  conclusion.  No Omega-index bridge is needed because the loss from `m_omp`
  versus `mp_eps` only *tightens* the upper bound.

The exact-`ε` neighbourhood radius inside `m_P_eps` is preserved throughout: the
frozen `ThmUppestStatement V` is proved unchanged, modulo the single frozen
`lemma_omp` dependency.
-/

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- **Theorem `uppest` (S9 upper bound).**  Reduced to the frozen exact-`ε`
`lemma_omp`; every other ingredient (endpoint bound, symmetry of information,
Omega complexity, counting) is proved.  See the module docstring for the
constant-reconciliation argument that removes the need for an Omega-index
bridge. -/
theorem thm_uppest
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ThmUppestStatement V := by
  -- A canonical code for `V`.
  obtain ⟨q0, hq0⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  -- The single genuine obstruction: exact-`ε` Lemma `omp`.
  obtain ⟨c_omp, h_omp⟩ := lemma_omp V U hV hU
  -- Plain-complexity endpoint bound on the neighbourhood.
  obtain ⟨c_end, h_end⟩ := plainK_upper_of_profileNeighborhood_endpoint V hV
  -- Complexity of the finite Omega code, both directions.
  obtain ⟨c_low, h_low⟩ := plainK_omegaFixedCode_lower V hV q0 hq0
  obtain ⟨c_up, h_up⟩ := plainK_omegaFixedCode_upper V hV q0
  -- Reverse symmetry of information for ordinary plain complexity.
  obtain ⟨c_soi, h_soi⟩ := condK_reverse_of_plain_complexity_gap V U hV hU
  -- Fold the SOI budget (linear in `n_P`) back onto a single `logSlack _ n_P`.
  obtain ⟨b_end, hb_end⟩ := logSlack_le_add_const c_end
  obtain ⟨b_omp, hb_omp⟩ := logSlack_le_add_const c_omp
  set B : Nat := b_end + c_up + b_omp with hB
  obtain ⟨C_fold, hC_fold⟩ := logSlack_linear_bound c_soi 6 B
  refine ⟨c_end + c_omp + C_fold + c_low + 1, ?_⟩
  intro P epsilon kp np mp_eps S hadm heps hkP hnP hmpeps hsubset
  -- lemma_omp's own index `m_omp = m_P_eps P kp ε c_omp`.
  obtain ⟨m_omp, hm_omp_eq⟩ :=
    exists_m_P_eps_eq_coe_of_k_P_eq P kp (3 * epsilon) c_omp hadm.isUpperSet hkP
  have hm_omp_le_kp : m_omp ≤ kp := by
    have h := m_P_eps_le_k_P_of_eq P kp (3 * epsilon) c_omp hadm.isUpperSet hkP
    rw [hm_omp_eq] at h; exact_mod_cast h
  -- The chosen `uppest` constant dominates `c_omp`, so `mp_eps ≤ m_omp`.
  have hmp_le : mp_eps ≤ m_omp := by
    have hanti := m_P_eps_antitone_of_isUpperSet P kp (3 * epsilon) c_omp
      (c_end + c_omp + C_fold + c_low + 1) hadm.isUpperSet (by omega)
    rw [hmpeps, hm_omp_eq] at hanti
    exact_mod_cast hanti
  -- Plain complexity of the counting condition `Ω_{m_omp}`, as a `Nat`.
  have hW_up := h_up m_omp
  have hW_fin : plainK V (omegaFixedCode q0 m_omp) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hW_up
  set kW : Nat := (plainK V (omegaFixedCode q0 m_omp)).toNat with hkW_def
  have hkW : plainK V (omegaFixedCode q0 m_omp) = (kW : ENat) := (ENat.natCast_toNat hW_fin).symm
  have hkW_up : kW ≤ m_omp + c_up := by rw [hkW] at hW_up; exact_mod_cast hW_up
  have hkW_low : m_omp ≤ kW + c_low := by
    have h := h_low m_omp; rw [hkW] at h; exact_mod_cast h
  -- The SOI budget scale `N` and its linear bound in `n_P`.
  set N : Nat :=
    (kp + 2 * epsilon + logSlack c_end np) + (m_omp + c_up) + logSlack c_omp np with hN_def
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm; rw [hkP, hnP] at h; exact_mod_cast h
  have hN_le : N ≤ 6 * np + B := by
    rw [hN_def, hB]
    have h1 := hb_end np
    have h2 := hb_omp np
    omega
  have hfold : logSlack c_soi N ≤ logSlack C_fold np :=
    (logSlack_mono_right c_soi hN_le).trans (hC_fold np)
  -- Counting: bound the log-cardinality by `K(x | Ω_{m_omp})` uniformly over `S`.
  have hcount : finiteSetLogCard S ≤
      (kp - m_omp + 2 * epsilon + logSlack c_end np + c_low + logSlack c_omp np
        + logSlack c_soi N) + 1 :=
    finiteSetLogCard_le_condK_budget V (omegaFixedCode q0 m_omp)
      (kp - m_omp + 2 * epsilon + logSlack c_end np + c_low + logSlack c_omp np
        + logSlack c_soi N) S (by
      intro x hx
      have hxnb : x ∈ profileNeighborhood V P epsilon := hsubset (Finset.mem_coe.mpr hx)
      -- Endpoint bound `C(x) ≤ kp + 2ε + logSlack c_end np`.
      have hxend : plainK V x ≤ ((kp + 2 * epsilon + logSlack c_end np : Nat) : ENat) :=
        h_end P kp np epsilon x hadm.step heps hkP hnP hxnb
      -- lemma_omp: `K(Ω_{m_omp} | x) ≤ logSlack c_omp np`.
      have hxomp : condK V (omegaFixedCode q0 m_omp) x ≤ (logSlack c_omp np : ENat) :=
        h_omp P epsilon kp np m_omp x q0 hadm hq0 heps hkP hnP hm_omp_eq hxnb
      -- Feed the SOI reverse.
      have hpx : plainK V x ≤ (N : ENat) := by
        refine hxend.trans ?_
        have hnat : kp + 2 * epsilon + logSlack c_end np ≤ N := by rw [hN_def]; omega
        exact_mod_cast hnat
      have hpy : plainK V (omegaFixedCode q0 m_omp) ≤ (N : ENat) := by
        rw [hkW]
        have hnat : kW ≤ N := by rw [hN_def]; omega
        exact_mod_cast hnat
      have hsN : logSlack c_omp np ≤ N := by rw [hN_def]; omega
      have hgap : plainK V x ≤ plainK V (omegaFixedCode q0 m_omp)
          + ((kp - m_omp + 2 * epsilon + logSlack c_end np + c_low : Nat) : ENat) := by
        rw [hkW]
        have hnat : kp + 2 * epsilon + logSlack c_end np
            ≤ kW + (kp - m_omp + 2 * epsilon + logSlack c_end np + c_low) := by omega
        calc plainK V x
            ≤ ((kp + 2 * epsilon + logSlack c_end np : Nat) : ENat) := hxend
          _ ≤ ((kW + (kp - m_omp + 2 * epsilon + logSlack c_end np + c_low) : Nat) : ENat) := by
              exact_mod_cast hnat
          _ = (kW : ENat)
                + ((kp - m_omp + 2 * epsilon + logSlack c_end np + c_low : Nat) : ENat) := by
              push_cast; ring
      have hsoi := h_soi x (omegaFixedCode q0 m_omp) N
        (kp - m_omp + 2 * epsilon + logSlack c_end np + c_low) (logSlack c_omp np)
        hpx hpy hxomp hsN hgap
      refine hsoi.trans (le_of_eq ?_)
      push_cast; ring)
  -- Fold the logarithmic terms into a single `logSlack` at the chosen constant.
  have hslackfinal :
      logSlack c_end np + c_low + logSlack c_omp np + logSlack C_fold np + 1
        ≤ logSlack (c_end + c_omp + C_fold + c_low + 1) np := by
    calc logSlack c_end np + c_low + logSlack c_omp np + logSlack C_fold np + 1
        = (logSlack c_end np + logSlack c_omp np + logSlack C_fold np) + c_low + 1 := by ring
      _ = logSlack (c_end + c_omp + C_fold) np + c_low + 1 := by
          rw [logSlack_add_const c_end c_omp np, logSlack_add_const (c_end + c_omp) C_fold np]
      _ ≤ logSlack (c_end + c_omp + C_fold + c_low) np + 1 := by
          have h := logSlack_add_nat_le (c_end + c_omp + C_fold) c_low np
          omega
      _ ≤ logSlack (c_end + c_omp + C_fold + c_low + 1) np :=
          logSlack_add_nat_le (c_end + c_omp + C_fold + c_low) 1 np
  -- Assemble the `Nat` conclusion and cast.
  have h_nat : finiteSetLogCard S ≤
      kp - mp_eps + 2 * epsilon + logSlack (c_end + c_omp + C_fold + c_low + 1) np := by
    omega
  exact_mod_cast h_nat

end Kolmogorov
