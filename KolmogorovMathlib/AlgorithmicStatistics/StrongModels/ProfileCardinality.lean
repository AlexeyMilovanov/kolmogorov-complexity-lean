import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Realization

/-!
# Profile Cardinality Bounds

This file contains the formalized interfaces for the cardinality bounds
of strings with a given profile, corresponding to Theorems `card`, `uppest`,
and Lemma `omp` from Section 7.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- A set of complexity/randomness-deficiency pairs is admissible when it is nonempty, upward
closed, and closed under moving budget from the second coordinate to the first. -/
def IsAdmissibleProfileSet (P : Set (Nat × Nat)) : Prop :=
  P.Nonempty ∧ IsUpperSet P ∧ ∀ a b c, (a, b + c) ∈ P → (a + b, c) ∈ P

/-- The staircase boundary of an admissible profile set: an antitone height function that vanishes
exactly from index `kP` on, starts at `nP`, drops strictly while positive, together with its
curve encoding `code` and the plain complexity `KP` of that encoding relative to `V`. -/
structure ProfileBoundary (V : Map) where
  height : Nat → Nat
  kP : Nat
  nP : Nat
  height_zero_of_ge : ∀ i, kP ≤ i → height i = 0
  height_pos_of_lt : ∀ i, i < kP → 0 < height i
  height_zero : height 0 = nP
  antitone : Antitone height
  slope : ∀ i, height i = 0 ∨ height (i + 1) < height i
  code : BitString
  h_code : code = curveEncode height kP
  KP : Nat
  h_KP : KP = (plainK V code).toNat

/-- The profile set cut out by a boundary: all pairs lying weakly above its height curve. -/
def profileSet (V : Map) (b : ProfileBoundary V) : Set (Nat × Nat) :=
  {q | b.height q.1 ≤ q.2}

/-- The vertical intercept of a profile set: the least `t` with `(0, t) ∈ P`. -/
noncomputable def nP (P : Set (Nat × Nat)) : ENat :=
  sInf {t : ENat | ∃ t_nat : Nat, t = (t_nat : ENat) ∧ (0, t_nat) ∈ P}

/-- The horizontal intercept of a profile set: the least `t` with `(t, 0) ∈ P`. -/
noncomputable def kP (P : Set (Nat × Nat)) : ENat :=
  sInf {t : ENat | ∃ t_nat : Nat, t = (t_nat : ENat) ∧ (t_nat, 0) ∈ P}

/-- The infimum of the `ENat` casts of the witnesses of a predicate on `Nat` is the least
witness. This is the shape shared by the profile endpoints `nP`, `kP` and `mP`, and it is the
general statement behind `nP_eq_of_mem_of_forall_le` and `kP_eq_of_mem_of_forall_le`. -/
theorem sInf_natCast_eq_of_least {p : Nat → Prop} {m : Nat} (hm : p m)
    (hle : ∀ t, p t → m ≤ t) :
    sInf {t : ENat | ∃ t_nat : Nat, t = (t_nat : ENat) ∧ p t_nat} = (m : ENat) := by
  refine le_antisymm (sInf_le ⟨m, rfl, hm⟩) (le_sInf ?_)
  rintro _ ⟨t, rfl, ht⟩
  exact_mod_cast hle t ht

/-- The vertical intercept is `m` as soon as `(0, m) ∈ P` and no point of `P` on the vertical
axis lies below height `m`. -/
theorem nP_eq_of_mem_of_forall_le {P : Set (Nat × Nat)} {m : Nat} (hm : (0, m) ∈ P)
    (hle : ∀ t, (0, t) ∈ P → m ≤ t) : nP P = (m : ENat) :=
  sInf_natCast_eq_of_least hm hle

/-- The horizontal intercept is `m` as soon as `(m, 0) ∈ P` and no point of `P` on the
horizontal axis lies left of `m`. -/
theorem kP_eq_of_mem_of_forall_le {P : Set (Nat × Nat)} {m : Nat} (hm : (m, 0) ∈ P)
    (hle : ∀ t, (t, 0) ∈ P → m ≤ t) : kP P = (m : ENat) :=
  sInf_natCast_eq_of_least hm hle

/-- The least first coordinate `t` at which the anti-diagonal of total budget `k` meets the profile
set, i.e. with `(t, k - t) ∈ P`. -/
noncomputable def mP (P : Set (Nat × Nat)) (k : Nat) : ENat :=
  sInf {t : ENat | ∃ t_nat : Nat, t = (t_nat : ENat) ∧ (t_nat, k - t_nat) ∈ P}

/-- The `epsilon`-slackened version of `mP`: the least `t` for which the point obtained from
`(t, k - t)` by adding the `epsilon` and logarithmic-overhead allowances lies in `P`. -/
noncomputable def mPEps (P : Set (Nat × Nat)) (k epsilon c : Nat) : ENat :=
  sInf {t : ENat | ∃ t_nat : Nat, t = (t_nat : ENat) ∧
    (t_nat + epsilon, k - t_nat + c * (k + 2 * epsilon).bits.length + epsilon) ∈ P}

/-- The neighborhood $L(P, \epsilon)$ of strings whose profile is $\epsilon$-close to $P$. -/
def profileNeighborhood (V : Map) (P : Set (Nat × Nat)) (epsilon : Nat) : Set BitString :=
  {x | ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x) P epsilon}

/-- Theorem `card` as a proposition about `V` and `T`: there is a constant `c` such that every
admissible profile set `P` cut out by a boundary `b`, with intercepts `kP P = kp`, `mP P kp = mp`
and `nP P = np`, admits (i) a nonempty finite set inside the
`(c * b.KP + logSlack c np)`-neighbourhood of `P` and (ii) a nonempty finite set of normal
strings whose profiles are `(c * b.KP + sqrtSlack c np)`-close to `P`, each of log-cardinality at
least `kp - mp - c`. -/
def ThmCardStatement (V T : Map) : Prop :=
  ∃ c : Nat, ∀ (P : Set (Nat × Nat)) (kp mp np : Nat) (b : ProfileBoundary V),
    IsAdmissibleProfileSet P →
    profileSet V b = P →
    kP P = (kp : ENat) →
    mP P kp = (mp : ENat) →
    nP P = (np : ENat) →
    (∃ S : Finset BitString,
      S.Nonempty ∧
      (S : Set BitString) ⊆ profileNeighborhood V P (c * b.KP + logSlack c np) ∧
      (kp - mp : ENat) ≤ (finiteSetLogCard S : ENat) + (c : ENat)) ∧
    (∃ S : Finset BitString,
      S.Nonempty ∧
      (S : Set BitString) ⊆ {x | IsNormalString V T x (logSlack c np) (sqrtSlack c np) ∧
        ProfileSetsWithinNeighborhood (plainDescriptionProfileSet V x) P
          (c * b.KP + sqrtSlack c np)} ∧
      (kp - mp : ENat) ≤ (finiteSetLogCard S : ENat) + (c : ENat))

/-- Theorem `uppest` as a proposition about `V`: there is a constant `c` such that for every
admissible profile set `P` with `epsilon ≤ kP P = kp`, `nP P = np` and
`mPEps P kp (3 * epsilon) c = mp_eps`, every finite set contained in the `epsilon`-neighbourhood
of `P` has log-cardinality at most `kp - mp_eps + 2 * epsilon + logSlack c np`. -/
def ThmUppestStatement (V : Map) : Prop :=
  ∃ c : Nat, ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat) (S : Finset BitString),
    IsAdmissibleProfileSet P →
    epsilon ≤ kp →
    kP P = (kp : ENat) →
    nP P = (np : ENat) →
    mPEps P kp (3 * epsilon) c = (mp_eps : ENat) →
    (S : Set BitString) ⊆ profileNeighborhood V P epsilon →
    (finiteSetLogCard S : ENat) ≤ (kp - mp_eps + 2 * epsilon + logSlack c np : ENat)

/-- Lemma `omp` at the exact radius `epsilon`, as a proposition about `V`: there is a constant
`c` such that for every admissible profile set `P` with `epsilon ≤ kP P = kp`, `nP P = np` and
`mPEps P kp epsilon c = mp_eps`, and every `x` in the `epsilon`-neighbourhood of `P`, the code
`omegaFixedCode q mp_eps` has conditional complexity at most `logSlack c np` given `x`. -/
def LemmaOmpExactRadiusStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    kP P = (kp : ENat) →
    nP P = (np : ENat) →
    mPEps P kp epsilon c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-- Lemma `omp` at the radius `3 * epsilon`, as a proposition about `V`: as
`LemmaOmpExactRadiusStatement`, but the Ω-index is `mPEps P kp (3 * epsilon) c` rather than
`mPEps P kp epsilon c`. -/
def LemmaOmpStatement (V : Map) : Prop :=
  ∃ c : Nat,
    ∀ (P : Set (Nat × Nat)) (epsilon kp np mp_eps : Nat)
        (x : BitString) (q : Nat.Partrec.Code),
    IsAdmissibleProfileSet P →
    IsCodeFor q V →
    epsilon ≤ kp →
    kP P = (kp : ENat) →
    nP P = (np : ENat) →
    mPEps P kp (3 * epsilon) c = (mp_eps : ENat) →
    x ∈ profileNeighborhood V P epsilon →
    condK V (omegaFixedCode q mp_eps) x ≤ (logSlack c np : ENat)

/-!
### Open Questions from Section 7

1. Is it true that for every minimal strong sufficient statistic A and for every
strong sufficient statistic B for x, we have KT(B | A) ≈ 0?
More specifically, is there a constant c such that: if A, B are epsilon-strong,
epsilon-sufficient statistics for x, and there is no (epsilon + c log n)-strong,
(epsilon + c log n)-sufficient statistic A' for x with K(A') <= K(A) - delta,
then KT(A | B) = O(epsilon + delta + log n)?

2. The same question, but assuming B also satisfies the minimality requirement.

3. (Merging strong sufficient statistics.) Is it true that if A, B are epsilon-strong,
epsilon-sufficient statistics for x, then there is a c*epsilon-strong, c*epsilon-sufficient
statistic D for x with log#D >= log#A + log#B - log#(A \cap B) - c(epsilon + log n)
and KT(D | A), KT(D | B) <= c(epsilon + log n)?
-/

/-- The defining diagonal for `mP` contains its endpoint candidate `k`. -/
theorem m_P_le_of_mem
    (P : Set (Nat × Nat)) (k : Nat)
    (hk : (k, 0) ∈ P) :
    mP P k ≤ (k : ENat) := by
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  use k
  exact ⟨rfl, by simpa using hk⟩

/-- The source profile-transfer property turns a height endpoint into a complexity endpoint. -/
theorem k_P_le_of_transfer
    (P : Set (Nat × Nat)) (n : Nat)
    (hn : (0, n) ∈ P)
    (hshift : ∀ a b c, (a, b + c) ∈ P → (a + b, c) ∈ P) :
    kP P ≤ (n : ENat) := by
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  use n
  refine ⟨rfl, ?_⟩
  have h := hshift 0 n 0 (by simpa using hn)
  simpa using h

/-- The source inequality `kP ≤ nP`, derived directly at the two infima.
No choice of a minimizing witness for `nP` is needed. -/
theorem k_P_le_n_P
    (P : Set (Nat × Nat))
    (hshift : ∀ a b c, (a, b + c) ∈ P → (a + b, c) ∈ P) :
    kP P ≤ nP P := by
  unfold kP nP
  apply sInf_le_sInf
  rintro _ ⟨n, rfl, hn⟩
  refine ⟨n, rfl, ?_⟩
  have h := hshift 0 n 0 (by simpa using hn)
  simpa using h

/-- A height endpoint of `P` is an upper bound for `nP`. -/
theorem n_P_le_of_mem
    (P : Set (Nat × Nat)) (n : Nat)
    (hn : (0, n) ∈ P) :
    nP P ≤ (n : ENat) := by
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  exact ⟨n, rfl, hn⟩

/-- An explicitly attained complexity endpoint witnesses `mP ≤ kP`. -/
theorem m_P_le_k_P_of_attained
    (P : Set (Nat × Nat)) (k : Nat)
    (hkP : kP P = (k : ENat))
    (hk : (k, 0) ∈ P) :
    mP P k ≤ kP P := by
  rw [hkP]
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  use k
  refine ⟨rfl, ?_⟩
  simpa using hk

/-- A point on the shifted diagonal is an upper bound for `mPEps`. -/
theorem m_P_eps_le_of_mem
    (P : Set (Nat × Nat)) (k epsilon c t : Nat)
    (h : (t + epsilon,
      k - t + c * (k + 2 * epsilon).bits.length + epsilon) ∈ P) :
    mPEps P k epsilon c ≤ (t : ENat) := by
  apply sInf_le
  simp only [Set.mem_ofPred_eq]
  exact ⟨t, rfl, h⟩

/-- An `ENat` infimum over coerced naturals is attained whenever its value is finite. -/
theorem enat_sInf_coe_mem_of_eq
    (Q : Nat → Prop) (k : Nat)
    (hInf : sInf {t : ENat | ∃ n : Nat, t = (n : ENat) ∧ Q n} = (k : ENat)) :
    Q k := by
  by_contra hk
  have hlower : ((k + 1 : Nat) : ENat) ≤
      sInf {t : ENat | ∃ n : Nat, t = (n : ENat) ∧ Q n} := by
    apply le_sInf
    rintro _ ⟨n, rfl, hn⟩
    have hkn : k ≤ n := by
      have h := sInf_le
        (show (n : ENat) ∈ {t : ENat | ∃ m : Nat, t = (m : ENat) ∧ Q m} from
          ⟨n, rfl, hn⟩)
      rw [hInf] at h
      exact_mod_cast h
    have hne : k ≠ n := by
      rintro rfl
      exact hk hn
    exact_mod_cast (show k + 1 ≤ n by omega)
  rw [hInf] at hlower
  have : k + 1 ≤ k := by exact_mod_cast hlower
  omega

/-- A finite value of `kP` is attained by an actual endpoint of `P`. -/
theorem k_P_mem_of_eq
    (P : Set (Nat × Nat)) (k : Nat)
    (hkP : kP P = (k : ENat)) :
    (k, 0) ∈ P := by
  unfold kP at hkP
  exact enat_sInf_coe_mem_of_eq (fun t => (t, 0) ∈ P) k hkP

/-- A finite value of `nP` is attained by an actual endpoint of `P`. -/
theorem n_P_mem_of_eq
    (P : Set (Nat × Nat)) (n : Nat)
    (hnP : nP P = (n : ENat)) :
    (0, n) ∈ P := by
  unfold nP at hnP
  exact enat_sInf_coe_mem_of_eq (fun t => (0, t) ∈ P) n hnP

/-- A finite value of `mP` is attained on its defining diagonal. -/
theorem m_P_mem_of_eq
    (P : Set (Nat × Nat)) (k m : Nat)
    (hmP : mP P k = (m : ENat)) :
    (m, k - m) ∈ P := by
  unfold mP at hmP
  exact enat_sInf_coe_mem_of_eq (fun t => (t, k - t) ∈ P) m hmP

/-- A finite value of `mPEps` is attained on its defining shifted diagonal. -/
theorem m_P_eps_mem_of_eq
    (P : Set (Nat × Nat)) (k epsilon c m : Nat)
    (hmP : mPEps P k epsilon c = (m : ENat)) :
    (m + epsilon,
      k - m + c * (k + 2 * epsilon).bits.length + epsilon) ∈ P := by
  unfold mPEps at hmP
  exact enat_sInf_coe_mem_of_eq
    (fun t => (t + epsilon,
      k - t + c * (k + 2 * epsilon).bits.length + epsilon) ∈ P) m hmP

/-- The source inequality `mP ≤ kP` when the finite value of `kP` is exposed. -/
theorem m_P_le_k_P_of_eq
    (P : Set (Nat × Nat)) (k : Nat)
    (hkP : kP P = (k : ENat)) :
    mP P k ≤ kP P :=
  m_P_le_k_P_of_attained P k hkP (k_P_mem_of_eq P k hkP)

/-- The complexity endpoint `kP` is always an admissible value for the shifted
diagonal defining `mPEps`, so `mPEps ≤ kP`. -/
theorem m_P_eps_le_k_P_of_eq
    (P : Set (Nat × Nat)) (kp epsilon c : Nat)
    (hUp : IsUpperSet P)
    (hkP : kP P = (kp : ENat)) :
    mPEps P kp epsilon c ≤ (kp : ENat) := by
  refine m_P_eps_le_of_mem P kp epsilon c kp ?_
  refine hUp (a := (kp, 0)) ?_ (k_P_mem_of_eq P kp hkP)
  exact Prod.mk_le_mk.mpr ⟨by omega, by omega⟩

/-- Enlarging the logarithmic coefficient can only lower `mPEps`, provided
the profile set is upper closed.  The upper-closure hypothesis is essential:
for an arbitrary set, raising the second coordinate can leave the set. -/
theorem m_P_eps_antitone_of_isUpperSet
    (P : Set (Nat × Nat)) (kp epsilon c₁ c₂ : Nat)
    (hUp : IsUpperSet P) (hc : c₁ ≤ c₂) :
    mPEps P kp epsilon c₂ ≤ mPEps P kp epsilon c₁ := by
  unfold mPEps
  apply sInf_le_sInf
  rintro _ ⟨t, rfl, ht⟩
  refine ⟨t, rfl, hUp ?_ ht⟩
  exact Prod.mk_le_mk.mpr ⟨le_rfl, by
    have hmul : c₁ * (kp + 2 * epsilon).bits.length ≤
        c₂ * (kp + 2 * epsilon).bits.length :=
      Nat.mul_le_mul_right _ hc
    omega⟩

/-- Once `kP` is finite, upper closure makes the shifted diagonal defining
`mPEps` nonempty, so its infimum is a coerced natural rather than `⊤`. -/
theorem exists_m_P_eps_eq_coe_of_k_P_eq
    (P : Set (Nat × Nat)) (kp epsilon c : Nat)
    (hUp : IsUpperSet P) (hkP : kP P = (kp : ENat)) :
    ∃ m : Nat, mPEps P kp epsilon c = (m : ENat) := by
  have hle : mPEps P kp epsilon c ≤ (kp : ENat) :=
    m_P_eps_le_k_P_of_eq P kp epsilon c hUp hkP
  have hne : mPEps P kp epsilon c ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top kp) hle
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨m, hm.symm⟩

/-! ### Admissibility corollaries

The three fields of `IsAdmissibleProfileSet` are exposed as named projections,
and the source endpoint inequalities `kP ≤ nP` and `mP ≤ kP ≤ nP` are
re-derived directly from admissibility (the step condition already fed to
`k_P_le_n_P`).  These let downstream proofs quote admissibility once and obtain
the ordering `mP ≤ kP ≤ nP` used throughout Section 7. -/

/-- An admissible profile set is nonempty. -/
theorem IsAdmissibleProfileSet.nonempty {P : Set (Nat × Nat)}
    (h : IsAdmissibleProfileSet P) : P.Nonempty := h.1

/-- An admissible profile set is upward closed. -/
theorem IsAdmissibleProfileSet.isUpperSet {P : Set (Nat × Nat)}
    (h : IsAdmissibleProfileSet P) : IsUpperSet P := h.2.1

/-- In an admissible profile set, budget may be shifted from the second coordinate to the first:
`(a, b + c) ∈ P` implies `(a + b, c) ∈ P`. -/
theorem IsAdmissibleProfileSet.step {P : Set (Nat × Nat)}
    (h : IsAdmissibleProfileSet P) :
    ∀ a b c, (a, b + c) ∈ P → (a + b, c) ∈ P := h.2.2

/-- The source inequality `kP ≤ nP`, extracted from admissibility. -/
theorem k_P_le_n_P_of_admissible {P : Set (Nat × Nat)}
    (h : IsAdmissibleProfileSet P) : kP P ≤ nP P :=
  k_P_le_n_P P h.step

/-- The full source ordering `mP ≤ kP ≤ nP` for an admissible `P` whose
complexity endpoint `kP` is finite. -/
theorem m_P_le_k_P_le_n_P_of_admissible {P : Set (Nat × Nat)} {k : Nat}
    (h : IsAdmissibleProfileSet P) (hkP : kP P = (k : ENat)) :
    mP P k ≤ kP P ∧ kP P ≤ nP P :=
  ⟨m_P_le_k_P_of_eq P k hkP, k_P_le_n_P_of_admissible h⟩

/-- The decoded profile set is exactly the epigraph of the boundary curve. -/
theorem mem_profileSet_iff (V : Map) (b : ProfileBoundary V) (q : Nat × Nat) :
    q ∈ profileSet V b ↔ b.height q.1 ≤ q.2 := Iff.rfl

/-- The height of a profile boundary vanishes at `i` exactly when `i` is at least its horizontal
intercept `kP`. -/
theorem ProfileBoundary.height_eq_zero_iff {V : Map} (b : ProfileBoundary V) (i : Nat) :
    b.height i = 0 ↔ b.kP ≤ i := by
  constructor
  · intro hzero
    by_contra hnot
    have hpos := b.height_pos_of_lt i (Nat.lt_of_not_ge hnot)
    omega
  · exact b.height_zero_of_ge i

/-- The canonical boundary code decodes to the represented height at every
coordinate, including the zero tail beyond `kP`. -/
theorem ProfileBoundary.decodeCurve_code {V : Map} (b : ProfileBoundary V) (i : Nat) :
    decodeCurve b.code i = b.height i := by
  rw [b.h_code]
  by_cases hi : i ≤ b.kP
  · exact decodeCurve_curveEncode b.height b.kP hi
  · have hlt : b.kP < i := Nat.lt_of_not_ge hi
    rw [decodeCurve_curveEncode_out_of_bounds b.height b.kP hlt,
      b.height_zero_of_ge i hlt.le]

/-- The stored left endpoint is exactly the height endpoint of the decoded
profile, rather than merely an upper bound. -/
theorem ProfileBoundary.n_P_profileSet {V : Map} (b : ProfileBoundary V) :
    Kolmogorov.nP (profileSet V b) = (b.nP : ENat) :=
  nP_eq_of_mem_of_forall_le (by change b.height 0 ≤ b.nP; rw [b.height_zero])
    (fun _ ht => by rw [← b.height_zero]; exact ht)

/-- The stored bottom endpoint is exactly the first zero of the decoded
profile boundary. -/
theorem ProfileBoundary.k_P_profileSet {V : Map} (b : ProfileBoundary V) :
    Kolmogorov.kP (profileSet V b) = (b.kP : ENat) :=
  kP_eq_of_mem_of_forall_le
    (by change b.height b.kP ≤ 0; rw [b.height_zero_of_ge b.kP le_rfl])
    (fun t ht => (b.height_eq_zero_iff t).mp (Nat.le_zero.mp ht))

/-! ### Representation of admissible profile sets by boundaries

The structure-function boundary `profileHeight P i = min {j | (i,j) ∈ P}` turns
any admissible `P` (nonempty, upward closed, step condition) with finite
endpoints `kP`, `nP` into a `ProfileBoundary` whose decoded epigraph is exactly
`P`.  This certifies that the `ProfileBoundary` hypothesis of `ThmCardStatement`
is non-vacuous: it is available for every admissible `P`.  The key point is that
the strict-slope field of `ProfileBoundary` follows from the step condition
`(a, b+c) ∈ P → (a+b, c) ∈ P`, applied with `b = 1`. -/

/-- The structure-function boundary of a profile set: the minimal log-size for
each complexity budget (with `sInf ∅ = 0` when the fibre is empty). -/
noncomputable def profileHeight (P : Set (Nat × Nat)) (i : Nat) : Nat :=
  sInf {j | (i, j) ∈ P}

/-- If the fibre of `P` over `i` is nonempty then the point at the fibre's height belongs to `P`. -/
theorem profileHeight_mem_of_fibre_nonempty {P : Set (Nat × Nat)} {i : Nat}
    (h : ∃ j, (i, j) ∈ P) : (i, profileHeight P i) ∈ P :=
  Nat.sInf_mem h

/-- The height of `P` over `i` is a lower bound for every `j` with `(i, j) ∈ P`. -/
theorem profileHeight_le {P : Set (Nat × Nat)} {i j : Nat}
    (h : (i, j) ∈ P) : profileHeight P i ≤ j :=
  Nat.sInf_le h

/-- Every complexity fibre of an admissible profile with finite endpoints is
nonempty: below `nP` the step condition slides the top point `(0, nP)` right,
and above `kP` upward closure supplies the bottom point `(·, 0)`. -/
theorem admissible_fibre_nonempty
    {P : Set (Nat × Nat)} {kp np : Nat}
    (h : IsAdmissibleProfileSet P)
    (hkP : kP P = (kp : ENat)) (hnP : nP P = (np : ENat)) :
    ∀ i, ∃ j, (i, j) ∈ P := by
  have hkp_mem : (kp, 0) ∈ P := k_P_mem_of_eq P kp hkP
  have hnp_mem : (0, np) ∈ P := n_P_mem_of_eq P np hnP
  have hkp_le_np : kp ≤ np := by
    have hle := k_P_le_n_P_of_admissible h
    rw [hkP, hnP] at hle
    exact_mod_cast hle
  intro i
  rcases Nat.lt_or_ge np i with hgt | hle
  · exact ⟨0, h.isUpperSet (Prod.mk_le_mk.mpr ⟨by omega, le_refl 0⟩) hkp_mem⟩
  · refine ⟨np - i, ?_⟩
    have h0 : (0, i + (np - i)) ∈ P := by
      rw [Nat.add_sub_cancel' hle]; exact hnp_mem
    simpa using h.step 0 i (np - i) h0

/-- **Representation lemma.** Every admissible profile set `P` with finite
endpoints `kP = kp`, `nP = np` is the decoded epigraph `profileSet V b` of a
`ProfileBoundary V` object `b` with `b.kP = kp` and `b.nP = np`.  Hence the
`ProfileBoundary` premise of `ThmCardStatement` can always be met. -/
theorem exists_profileBoundary_of_admissible
    (V : Map) (P : Set (Nat × Nat)) (kp np : Nat)
    (h : IsAdmissibleProfileSet P)
    (hkP : kP P = (kp : ENat)) (hnP : nP P = (np : ENat)) :
    ∃ b : ProfileBoundary V, b.kP = kp ∧ b.nP = np ∧ profileSet V b = P := by
  have hkp_mem : (kp, 0) ∈ P := k_P_mem_of_eq P kp hkP
  have hnp_mem : (0, np) ∈ P := n_P_mem_of_eq P np hnP
  have hupper := h.isUpperSet
  have hne : ∀ i, ∃ j, (i, j) ∈ P := admissible_fibre_nonempty h hkP hnP
  have h_attained : ∀ i, (i, profileHeight P i) ∈ P := fun i =>
    profileHeight_mem_of_fibre_nonempty (hne i)
  refine ⟨{
    height := profileHeight P
    kP := kp
    nP := np
    height_zero_of_ge := ?_
    height_pos_of_lt := ?_
    height_zero := ?_
    antitone := ?_
    slope := ?_
    code := curveEncode (profileHeight P) kp
    h_code := rfl
    KP := (plainK V (curveEncode (profileHeight P) kp)).toNat
    h_KP := rfl }, rfl, rfl, ?_⟩
  · -- height is 0 above the complexity endpoint
    intro i hi
    have hmem : (i, 0) ∈ P :=
      hupper (Prod.mk_le_mk.mpr ⟨hi, le_refl 0⟩) hkp_mem
    exact Nat.le_zero.mp (profileHeight_le hmem)
  · -- the complexity endpoint is the first zero of the boundary
    intro i hi
    by_contra hnot
    have hzero : profileHeight P i = 0 := Nat.eq_zero_of_not_pos hnot
    have hmem : (i, 0) ∈ P := by
      simpa [hzero] using h_attained i
    have hle : kP P ≤ (i : ENat) := by
      unfold kP
      apply sInf_le
      exact ⟨i, rfl, hmem⟩
    rw [hkP] at hle
    have : kp ≤ i := by exact_mod_cast hle
    omega
  · -- height at 0 is the length endpoint
    have h1 : profileHeight P 0 ≤ np := profileHeight_le hnp_mem
    have h2 : np ≤ profileHeight P 0 := by
      have hle := n_P_le_of_mem P (profileHeight P 0) (h_attained 0)
      rw [hnP] at hle
      exact_mod_cast hle
    omega
  · -- antitone
    intro i i' hii
    exact profileHeight_le
      (hupper (Prod.mk_le_mk.mpr ⟨hii, le_refl _⟩) (h_attained i))
  · -- strict slope from the step condition
    intro i
    rcases Nat.eq_zero_or_pos (profileHeight P i) with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr ?_
      have hmem : (i, 1 + (profileHeight P i - 1)) ∈ P := by
        have he : 1 + (profileHeight P i - 1) = profileHeight P i := by omega
        rw [he]; exact h_attained i
      have hnext := h.step i 1 (profileHeight P i - 1) hmem
      have hle := profileHeight_le hnext
      omega
  · -- decoded epigraph equals P
    ext ⟨a, s⟩
    constructor
    · intro hq
      exact hupper (Prod.mk_le_mk.mpr ⟨le_refl a, hq⟩) (h_attained a)
    · intro hq
      exact profileHeight_le hq

/-- If `P_x` is `epsilon`-close to `P`, the attained endpoint `(kP, 0)`
yields the enlarged profile point `(kP + epsilon, epsilon)` used in Lemma `omp`. -/
theorem plainProfile_endpoint_of_profileNeighborhood
    (V : Map) (P : Set (Nat × Nat)) (epsilon k : Nat)
    (x : BitString)
    (hkP : kP P = (k : ENat))
    (hx : x ∈ profileNeighborhood V P epsilon) :
    (k + epsilon, epsilon) ∈ plainDescriptionProfileSet V x := by
  have hnear : ProfileSetsWithinNeighborhood
      (plainDescriptionProfileSet V x) P epsilon := hx
  obtain ⟨q, hq, hdist⟩ := hnear.2 (k, 0) (k_P_mem_of_eq P k hkP)
  apply plainDescriptionProfileSet_isUpperSet V x
      (show q ≤ (k + epsilon, epsilon) from ?_) hq
  unfold natPairLInfDistance at hdist
  constructor
  · have hfirst := (Nat.le_max_left
      ((k - q.1) + (q.1 - k))
      ((0 - q.2) + (q.2 - 0))).trans hdist
    omega
  · have hsecond := (Nat.le_max_right
      ((k - q.1) + (q.1 - k))
      ((0 - q.2) + (q.2 - 0))).trans hdist
    omega

/-- Transfer of a two-part description of a neighborhood member into the shifted
diagonal defining `mPEps`: if `x` is `epsilon`-close to `P`, then every
`(i, j)`-description of `x` whose total budget `i + j` stays within the visible
scale `kP` plus logarithmic slack certifies `mPEps ≤ i`. -/
theorem m_P_eps_le_of_profileNeighborhood_point
    (V : Map) (P : Set (Nat × Nat)) (kp epsilon c i j : Nat) (x : BitString)
    (hUp : IsUpperSet P)
    (hkP : kP P = (kp : ENat))
    (hx : x ∈ profileNeighborhood V P epsilon)
    (hij : (i, j) ∈ plainDescriptionProfileSet V x)
    (hbudget : i + j ≤ kp + c * (kp + 2 * epsilon).bits.length) :
    mPEps P kp epsilon c ≤ (i : ENat) := by
  rcases Nat.lt_or_ge i kp with hik | hik
  · have hnear : ProfileSetsWithinNeighborhood
        (plainDescriptionProfileSet V x) P epsilon := hx
    obtain ⟨q, hq, hdist⟩ := hnear.1 (i, j) hij
    unfold natPairLInfDistance at hdist
    have h1 := (Nat.le_max_left ((i - q.1) + (q.1 - i))
      ((j - q.2) + (q.2 - j))).trans hdist
    have h2 := (Nat.le_max_right ((i - q.1) + (q.1 - i))
      ((j - q.2) + (q.2 - j))).trans hdist
    have hq' : (i + epsilon, j + epsilon) ∈ P :=
      hUp (show q ≤ (i + epsilon, j + epsilon) from ⟨by omega, by omega⟩) hq
    refine m_P_eps_le_of_mem P kp epsilon c i ?_
    refine hUp (a := (i + epsilon, j + epsilon)) ?_ hq'
    exact ⟨le_refl _, by simp only; omega⟩
  · exact (m_P_eps_le_k_P_of_eq P kp epsilon c hUp hkP).trans (by exact_mod_cast hik)

/-- Conditional descriptions of length at most `n` can produce at most as many
 distinct outputs as there are programs of length at most `n`. -/
theorem card_condK_le_boundedPrograms_length
    (V : Map) (y : BitString) (n : Nat) (S : Finset BitString)
    (h : ∀ x ∈ S, condK V x y ≤ (n : ENat)) :
    S.card ≤ (boundedPrograms n).length := by
  classical
  have h_exists : ∀ x ∈ S, ∃ p, p.length ≤ n ∧ produces V p y x := by
    intro x hx
    exact (condK_le_iff V x y n).mp (h x hx)
  let pOf : BitString → BitString := fun x ↦
    if hx : x ∈ S then Classical.choose (h_exists x hx) else []
  have hpOf_mem :
      Set.MapsTo pOf (S : Set BitString) ((boundedPrograms n).toFinset : Set BitString) := by
    intro x hx
    have hxf : x ∈ S := by simpa using hx
    have hspec := Classical.choose_spec (h_exists x hxf)
    change pOf x ∈ (boundedPrograms n).toFinset
    rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
    rw [List.mem_toFinset]
    exact (mem_boundedPrograms_iff (Classical.choose (h_exists x hxf)) n).mpr hspec.1
  have hpOf_inj : (S : Set BitString).InjOn pOf := by
    intro x hx z hz hxz
    have hxf : x ∈ S := by simpa using hx
    have hzf : z ∈ S := by simpa using hz
    have hxspec := Classical.choose_spec (h_exists x hxf)
    have hzspec := Classical.choose_spec (h_exists z hzf)
    have hxprod : produces V (pOf x) y x := by
      rw [show pOf x = Classical.choose (h_exists x hxf) by simp [pOf, hxf]]
      exact hxspec.2
    have hzprod : produces V (pOf x) y z := by
      rw [hxz]
      rw [show pOf z = Classical.choose (h_exists z hzf) by simp [pOf, hzf]]
      exact hzspec.2
    exact Part.mem_unique hxprod hzprod
  calc
    S.card ≤ ((boundedPrograms n).toFinset).card :=
      Finset.card_le_card_of_injOn pOf hpOf_mem hpOf_inj
    _ = (boundedPrograms n).length := by
      rw [List.toFinset_card_of_nodup (boundedPrograms_nodup n)]

/-- The logarithmic cardinality of a finite family with conditional complexity
 at most `n` is at most `n + 1`. -/
theorem finiteSetLogCard_le_condK_budget
    (V : Map) (y : BitString) (n : Nat) (S : Finset BitString)
    (h : ∀ x ∈ S, condK V x y ≤ (n : ENat)) :
    finiteSetLogCard S ≤ n + 1 := by
  rw [finiteSetLogCard_le_iff]
  exact (card_condK_le_boundedPrograms_length V y n S h).trans
    (Nat.le_of_lt (length_boundedPrograms_lt n))

end Kolmogorov
