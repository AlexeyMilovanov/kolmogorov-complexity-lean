import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PairStrongModels

/-!
# Normality of a pair with a conditionally random tail

If `z` is conditionally random given `y`, then the ordinary plain profile of
`pairCode y z` is the profile of `y` shifted by `|z|` in the second coordinate,
truncated by the sufficiency line of the pair (`rem:add-noise`).  This file
shows that the corresponding *strong* profile follows the same picture, so a
normal head produces a normal pair:

* below the base complexity the strong models of `y` are extended by the full
  noise cube (`strongProfile_pair_of_strongProfile_head`);
* along the sufficiency line the tail cubes of the pair supply the required
  strong models (`strongProfile_pair_tailCube`).
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- **Upper direction of the pair bound.**  Encoding the pair costs at most the
plain complexity of the first component, the length of the second component,
and a logarithmic overhead. -/
theorem plainK_pair_le_plainK_add_length
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ (x y : BitString) (kx : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) ≤
        ((kx + y.length + logSlack c (x.length + y.length) : Nat) : ENat) := by
  obtain ⟨cPair, hPair⟩ := plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨cB, hB⟩ := KP_le_condK_of_logSlack_budget V U hV hU
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cL, hL⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cB 2 (1 + cLen)
  refine ⟨cFold + (2 + cL + cPair), ?_⟩
  intro x y kx hkx
  set n := x.length + y.length with hn
  set N := 2 * n + (1 + cLen) with hN
  have hkxN : kx ≤ N := by
    have h : plainK V x ≤ ((x.length + cLen : Nat) : ENat) := by
      refine (hLen x).trans ?_
      push_cast
      exact le_rfl
    rw [hkx] at h
    have h' : kx ≤ x.length + cLen := by exact_mod_cast h
    simp only [hN, hn]
    omega
  have hKx : KPPlain U x ≤ ((kx + logSlack cB N : Nat) : ENat) :=
    hB x [] kx N hkx hkxN
  have hKy : KPPlain U y ≤
      ((y.length + 2 * (Nat.bits y.length).length + cL : Nat) : ENat) := by
    refine (hL y).trans ?_
    push_cast
    exact le_rfl
  have harith :
      kx + logSlack cB N + (y.length + 2 * (Nat.bits y.length).length + cL) + cPair
        ≤ kx + y.length + logSlack (cFold + (2 + cL + cPair)) n := by
    have h1 : logSlack cB N ≤ logSlack cFold n := hFold n
    have h2 : 2 * (Nat.bits y.length).length + cL + cPair
        ≤ logSlack (2 + cL + cPair) n := by
      have hylen : y.length ≤ n := by simp only [hn]; omega
      have hmono : (Nat.bits y.length).length ≤ (Nat.bits n).length :=
        length_natBits_mono hylen
      have hls : logSlack (2 + cL + cPair) n
          = (2 + cL + cPair) * (Nat.bits n).length + (2 + cL + cPair) := rfl
      nlinarith [hmono]
    have hsum : logSlack cFold n + logSlack (2 + cL + cPair) n
        = logSlack (cFold + (2 + cL + cPair)) n := logSlack_add_const _ _ _
    omega
  calc plainK V (pairCode x y) ≤ KPPlain U x + KPPlain U y + (cPair : ENat) :=
        hPair x y
    _ ≤ ((kx + logSlack cB N : Nat) : ENat)
          + ((y.length + 2 * (Nat.bits y.length).length + cL : Nat) : ENat)
          + (cPair : ENat) := by gcongr
    _ = ((kx + logSlack cB N + (y.length + 2 * (Nat.bits y.length).length + cL)
          + cPair : Nat) : ENat) := by push_cast; ring
    _ ≤ ((kx + y.length + logSlack (cFold + (2 + cL + cPair)) n : Nat) : ENat) := by
        exact_mod_cast harith

/-- **Two-sided pair estimate for a conditionally random tail.**  If `z` is
conditionally random given `y` up to loss `epsilon`, and `ky` is within `eta`
of a reference value `baseK`, then the plain complexity of the pair is within
`O(eta + epsilon) + O(log (|y| + d))` of `baseK + d`. -/
lemma pair_complexity_close_of_random_tail
    (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : Nat, ∀ (y z : BitString) (baseK d eta epsilon ky kyz : Nat),
      plainK V y = (ky : ENat) →
      plainK V (pairCode y z) = (kyz : ENat) →
      ky ≤ baseK + eta →
      baseK ≤ ky + eta →
      z.length = d →
      (d : ENat) ≤ condK V z y + (epsilon : ENat) →
      kyz ≤ baseK + d + (C * (eta + epsilon) + logSlack C (y.length + d)) ∧
        baseK + d ≤ kyz + (C * (eta + epsilon) + logSlack C (y.length + d)) := by
  obtain ⟨cUp, hUp⟩ := plainK_pair_le_plainK_add_length V U hV hU
  obtain ⟨cLow, hLow⟩ := plainK_pair_ge_plainK_add_length_of_random V U hV hU
  refine ⟨cUp + cLow + 1, ?_⟩
  intro y z baseK d eta epsilon ky kyz hky hkyz hkb hbk hz hrand
  subst hz
  have hupper : kyz ≤ ky + z.length + logSlack cUp (y.length + z.length) := by
    have h := hUp y z ky hky
    rw [hkyz] at h
    exact_mod_cast h
  have hlower : ky + z.length ≤ kyz + epsilon + logSlack cLow (y.length + z.length) :=
    hLow y z epsilon ky kyz hky hkyz hrand
  have hmono1 : logSlack cUp (y.length + z.length)
      ≤ logSlack (cUp + cLow + 1) (y.length + z.length) :=
    logSlack_mono_left (by omega) _
  have hmono2 : logSlack cLow (y.length + z.length)
      ≤ logSlack (cUp + cLow + 1) (y.length + z.length) :=
    logSlack_mono_left (by omega) _
  have hmul : eta + epsilon ≤ (cUp + cLow + 1) * (eta + epsilon) :=
    Nat.le_mul_of_pos_left _ (by omega)
  constructor <;> omega

/-! ### Strong profile points of the pair -/

/-- **Uniform-extension branch.**  A strong `(i,j)` model of the head yields a
strong `(i + O(log |z|), j + |z|)` model of the pair. -/
theorem strongProfile_pair_of_strongProfile_head
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (y z : BitString) (e i j : ℕ),
      InStrongDescriptionProfile V T y e i j →
      InStrongDescriptionProfile V T (pairCode y z) (e + c)
        (i + logSlack c z.length) (j + z.length) := by
  obtain ⟨cPlain, hPlain⟩ := finiteSetPairUniformExtension_plainSetComplexity_le V hV
  obtain ⟨cStrong, hStrong⟩ := finiteSetPairUniformExtension_isStrongSetModel T hT
  refine ⟨cPlain + cStrong, ?_⟩
  rintro y z e i j ⟨A, hA, ⟨⟨hmem, hcomp, hcard⟩, hstrong⟩⟩
  refine ⟨finiteSetPairUniformExtension A z.length,
    finiteSetPairUniformExtension_nonempty hA z.length, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · exact finiteSetPairUniformExtension_mem hmem rfl
  · calc plainSetComplexity V (finiteSetPairUniformExtension A z.length)
          (finiteSetPairUniformExtension_nonempty hA z.length)
        ≤ plainSetComplexity V A hA + (logSlack cPlain z.length : ENat) :=
          hPlain A hA z.length
      _ ≤ (i : ENat) + (logSlack (cPlain + cStrong) z.length : ENat) := by
          gcongr
          exact_mod_cast logSlack_mono_left (by omega) z.length
      _ = ((i + logSlack (cPlain + cStrong) z.length : ℕ) : ENat) := by push_cast; ring
  · rw [finiteSetPairUniformExtension_card, pow_add]
    exact Nat.mul_le_mul_right _ hcard
  · exact (hStrong A hA y z e hstrong).mono (by omega)

/-- **Sufficiency-line branch.**  Freezing all but the last `t` bits of the tail
gives a strong model of the pair of log-cardinality `t` and plain complexity
`C(y) + (|z| - t) + O(log (|y| + |z|))`. -/
theorem strongProfile_pair_tailCube
    (V U T : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (y z : BitString) (t ky : ℕ), t ≤ z.length →
      plainK V y = (ky : ENat) →
      InStrongDescriptionProfile V T (pairCode y z)
        (logSlack c (y.length + z.length))
        (ky + (z.length - t) + logSlack c (y.length + z.length)) t := by
  obtain ⟨cSet, hSet⟩ := pairTailCube_plainSetComplexity_le V hV
  obtain ⟨cStrong, hStrong⟩ := pairTailCube_isStrongSetModel T hT
  obtain ⟨cUp, hUp⟩ := plainK_pair_le_plainK_add_length V U hV hU
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cUp 3 1
  refine ⟨cUp + cFold + 1 + cSet + cStrong + 1, ?_⟩
  intro y z t ky ht hky
  have hwlen : (z.take (z.length - t)).length = z.length - t := by
    rw [List.length_take]
    omega
  have hdroplen : (z.drop (z.length - t)).length = t := by
    rw [List.length_drop]
    omega
  have hzsplit : z.take (z.length - t) ++ z.drop (z.length - t) = z :=
    List.take_append_drop _ _
  -- The numeric slack bookkeeping.
  have hB : (Nat.bits t).length ≤ (Nat.bits (y.length + z.length)).length :=
    length_natBits_mono (by omega)
  have hslackAll :
      logSlack cUp (y.length + z.length) + logSlack cFold (y.length + z.length)
          + (Nat.bits (y.length + z.length)).length + cSet + cStrong + 1
        ≤ logSlack (cUp + cFold + 1 + cSet + cStrong + 1)
            (y.length + z.length) := by
    have e1 : logSlack cUp (y.length + z.length)
        + logSlack cFold (y.length + z.length)
        = logSlack (cUp + cFold) (y.length + z.length) := logSlack_add_const _ _ _
    have e2 : (Nat.bits (y.length + z.length)).length + cSet + cStrong + 1
        ≤ logSlack (1 + cSet + cStrong + 1) (y.length + z.length) := by
      have hexp : logSlack (1 + cSet + cStrong + 1) (y.length + z.length)
          = (1 + cSet + cStrong + 1) * (Nat.bits (y.length + z.length)).length
            + (1 + cSet + cStrong + 1) := rfl
      have hmul : (1 + cSet + cStrong + 1) * (Nat.bits (y.length + z.length)).length
          = (Nat.bits (y.length + z.length)).length
            + (cSet + cStrong + 1) * (Nat.bits (y.length + z.length)).length := by
        ring
      omega
    have e3 : logSlack (cUp + cFold) (y.length + z.length)
        + logSlack (1 + cSet + cStrong + 1) (y.length + z.length)
        = logSlack (cUp + cFold + 1 + cSet + cStrong + 1) (y.length + z.length) := by
      rw [logSlack_add_const]
      congr 1
      omega
    omega
  refine ⟨pairTailCube y (z.take (z.length - t)) t,
    pairTailCube_nonempty _ _ _, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · have hmem := pairTailCube_mem (y := y) (w := z.take (z.length - t))
      (u := z.drop (z.length - t)) hdroplen
    rwa [hzsplit] at hmem
  · -- plain set complexity of the tail cube
    obtain ⟨k1, hk1⟩ : ∃ k : ℕ, plainK V (pairCode y (z.take (z.length - t))) = (k : ENat) :=
      ⟨(plainK V (pairCode y (z.take (z.length - t)))).toNat,
        (ENat.natCast_toNat (condK_ne_top_of_optimal V hV _ [])).symm⟩
    have hk1le : k1 ≤ ky + (z.length - t)
        + logSlack cUp (y.length + (z.length - t)) := by
      have h := hUp y (z.take (z.length - t)) ky hky
      rw [hk1, hwlen] at h
      exact_mod_cast h
    have hpair := hUp (pairCode y (z.take (z.length - t))) (Nat.bits t) k1 hk1
    have hMle : (pairCode y (z.take (z.length - t))).length + (Nat.bits t).length
        ≤ 3 * (y.length + z.length) + 1 := by
      rw [length_pairCode, hwlen]
      have := length_natBits_le_self t
      omega
    have hslackM : logSlack cUp ((pairCode y (z.take (z.length - t))).length
        + (Nat.bits t).length) ≤ logSlack cFold (y.length + z.length) :=
      le_trans (logSlack_mono_right cUp hMle) (hFold (y.length + z.length))
    have hslackLow : logSlack cUp (y.length + (z.length - t))
        ≤ logSlack cUp (y.length + z.length) :=
      logSlack_mono_right cUp (by omega)
    have hfinal :
        k1 + (Nat.bits t).length
            + logSlack cUp ((pairCode y (z.take (z.length - t))).length
              + (Nat.bits t).length) + cSet
          ≤ ky + (z.length - t)
            + logSlack (cUp + cFold + 1 + cSet + cStrong + 1)
              (y.length + z.length) := by
      omega
    calc plainSetComplexity V (pairTailCube y (z.take (z.length - t)) t)
          (pairTailCube_nonempty _ _ _)
        ≤ plainK V (pairCode (pairCode y (z.take (z.length - t))) (Nat.bits t))
            + (cSet : ENat) := hSet y (z.take (z.length - t)) t
      _ ≤ ((k1 + (Nat.bits t).length
            + logSlack cUp ((pairCode y (z.take (z.length - t))).length
              + (Nat.bits t).length) : ℕ) : ENat) + (cSet : ENat) := by
          gcongr
      _ = ((k1 + (Nat.bits t).length
            + logSlack cUp ((pairCode y (z.take (z.length - t))).length
              + (Nat.bits t).length) + cSet : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((ky + (z.length - t)
            + logSlack (cUp + cFold + 1 + cSet + cStrong + 1)
              (y.length + z.length) : ℕ) : ENat) := by exact_mod_cast hfinal
  · exact pairTailCube_card_le _ _ _
  · refine (hStrong y z t).mono ?_
    have hexp : logSlack (cUp + cFold + 1 + cSet + cStrong + 1)
        (y.length + z.length)
        = (cUp + cFold + 1 + cSet + cStrong + 1)
            * (Nat.bits (y.length + z.length)).length
          + (cUp + cFold + 1 + cSet + cStrong + 1) := rfl
    have hmul : (cUp + cFold + 1 + cSet + cStrong + 1)
          * (Nat.bits (y.length + z.length)).length
        = (Nat.bits (y.length + z.length)).length
          + (cUp + cFold + cSet + cStrong + 1)
            * (Nat.bits (y.length + z.length)).length := by ring
    omega

lemma normal_pair_of_conditionally_random_tail
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
  ∃ C : ℕ, ∀ (y z : BitString) (d strength delta epsilon : ℕ),
    IsNormalString V T y strength delta →
    z.length = d →
    (d : ENat) ≤ condK V z y + (epsilon : ENat) →
    IsNormalString V T (pairCode y z)
      (strength + logSlack C (y.length + d))
      (C * (delta + epsilon) + logSlack C (y.length + d)) := by
  obtain ⟨cTrans, hTrans⟩ := pairProfile_to_addNoiseProfileTransform V U hV hU
  obtain ⟨cExt, hExt⟩ := strongProfile_pair_of_strongProfile_head V T hV hT
  obtain ⟨cCube, hCube⟩ := strongProfile_pair_tailCube V U T hV hU hT
  obtain ⟨cSing, hSing⟩ := plainSetComplexity_singleton_le_plainK V hV
  obtain ⟨cPair, hPair⟩ := pair_complexity_close_of_random_tail V U hV hU
  refine ⟨cTrans + cExt + cCube + cPair + cSing + 1, ?_⟩
  intro y z d strength delta epsilon hnorm hzlen hrand
  subst hzlen
  -- elementary reformulation of the concrete distance
  have dist_le : ∀ (p q : ℕ × ℕ) (m : ℕ), p.1 ≤ q.1 + m → q.1 ≤ p.1 + m →
      p.2 ≤ q.2 + m → q.2 ≤ p.2 + m → natPairLInfDistance p q ≤ m := by
    intro p q m h1 h2 h3 h4
    unfold natPairLInfDistance
    apply max_le <;> omega
  have dist_ge : ∀ (p q : ℕ × ℕ) (m : ℕ), natPairLInfDistance p q ≤ m →
      p.1 ≤ q.1 + m ∧ q.1 ≤ p.1 + m ∧ p.2 ≤ q.2 + m ∧ q.2 ≤ p.2 + m := by
    intro p q m h
    unfold natPairLInfDistance at h
    have h1 := le_trans (le_max_left _ _) h
    have h2 := le_trans (le_max_right _ _) h
    omega
  set C := cTrans + cExt + cCube + cPair + cSing + 1 with hCdef
  obtain ⟨ky, hky⟩ : ∃ k : ℕ, plainK V y = (k : ENat) :=
    ⟨(plainK V y).toNat, (ENat.natCast_toNat (condK_ne_top_of_optimal V hV y [])).symm⟩
  obtain ⟨kyz, hkyz⟩ : ∃ k : ℕ, plainK V (pairCode y z) = (k : ENat) :=
    ⟨(plainK V (pairCode y z)).toNat,
      (ENat.natCast_toNat (condK_ne_top_of_optimal V hV (pairCode y z) [])).symm⟩
  obtain ⟨-, hlow⟩ := hPair y z ky z.length 0 epsilon ky kyz hky hkyz
    (by omega) (by omega) rfl hrand
  rw [Nat.zero_add] at hlow
  -- slack bookkeeping
  have hlsC : C ≤ logSlack C (y.length + z.length) := by
    unfold logSlack
    exact Nat.le_add_left _ _
  have hExtSlack : logSlack cExt z.length
      ≤ logSlack (cExt + cCube + cPair) (y.length + z.length) :=
    le_trans (logSlack_mono_right cExt (by omega))
      (logSlack_mono_left (by omega) _)
  have hCubeSlack : logSlack cCube (y.length + z.length)
      ≤ logSlack (cExt + cCube + cPair) (y.length + z.length) :=
    logSlack_mono_left (by omega) _
  have hPairSlack : logSlack cPair (y.length + z.length)
        + logSlack cCube (y.length + z.length)
      ≤ logSlack (cExt + cCube + cPair) (y.length + z.length) := by
    have h := logSlack_add_const cPair cCube (y.length + z.length)
    have h2 : logSlack (cPair + cCube) (y.length + z.length)
        ≤ logSlack (cExt + cCube + cPair) (y.length + z.length) :=
      logSlack_mono_left (by omega) _
    omega
  have hCubeC : logSlack cCube (y.length + z.length)
      ≤ logSlack C (y.length + z.length) :=
    logSlack_mono_left (by omega) _
  set M := delta + cSing + cPair * epsilon
    + logSlack (cExt + cCube + cPair) (y.length + z.length) with hMdef
  have hUpper := strongDescriptionProfileSet_isUpperSet V T (pairCode y z)
    (strength + logSlack C (y.length + z.length))
  -- every point of the add-noise transform is close to a strong profile point
  have key : ∀ a b : ℕ,
      (a, b) ∈ AddNoiseProfileTransform (plainDescriptionProfileSet V y) ky kyz
        z.length →
      ∃ q'' ∈ strongDescriptionProfileSet V T (pairCode y z)
          (strength + logSlack C (y.length + z.length)),
        natPairLInfDistance (a, b) q'' ≤ M := by
    rintro a b (⟨i, j, hi, hij, hq⟩ | ⟨hgt, hsum⟩)
    · have ha : a = i := congrArg Prod.fst hq
      have hb : b = j + z.length := congrArg Prod.snd hq
      obtain ⟨⟨i', j'⟩, hmem', hdist'⟩ := hnorm.1 (i, j) hij
      obtain ⟨d1, d2, d3, d4⟩ := dist_ge (i, j) (i', j') delta hdist'
      simp only at d1 d2 d3 d4
      have hstrong : InStrongDescriptionProfile V T (pairCode y z)
          (strength + cExt) (i' + logSlack cExt z.length) (j' + z.length) :=
        hExt y z strength i' j' hmem'
      refine ⟨(i' + logSlack cExt z.length, j' + z.length), ?_, ?_⟩
      · exact hstrong.mono_epsilon (by omega)
      · refine dist_le _ _ _ ?_ ?_ ?_ ?_ <;> simp only <;> omega
    · simp only at hgt hsum
      rcases Nat.lt_or_ge b z.length with hb | hb
      · -- sufficiency-line branch: freeze all but the last `b` bits of the tail
        have hcube : InStrongDescriptionProfile V T (pairCode y z)
            (logSlack cCube (y.length + z.length))
            (ky + (z.length - b) + logSlack cCube (y.length + z.length)) b :=
          hCube y z b ky (by omega) hky
        refine ⟨(max a (ky + (z.length - b)
          + logSlack cCube (y.length + z.length)), b), ?_, ?_⟩
        · refine hUpper (a := (ky + (z.length - b)
            + logSlack cCube (y.length + z.length), b)) ?_ ?_
          · exact Prod.mk_le_mk.mpr ⟨le_max_right _ _, le_rfl⟩
          · exact hcube.mono_epsilon (by omega)
        · refine dist_le _ _ _ ?_ ?_ ?_ ?_ <;> simp only <;> omega
      · -- above the noise level: extend a strong model of the head
        have hyplain : (a + cSing, 0) ∈ plainDescriptionProfileSet V y := by
          refine ⟨{y}, Finset.singleton_nonempty y,
            Finset.mem_singleton_self y, ?_, ?_⟩
          · calc plainSetComplexity V {y} (Finset.singleton_nonempty y)
                ≤ plainK V y + (cSing : ENat) := hSing y
              _ = ((ky + cSing : ℕ) : ENat) := by rw [hky]; push_cast; ring
              _ ≤ ((a + cSing : ℕ) : ENat) := by
                  exact_mod_cast (show ky + cSing ≤ a + cSing by omega)
          · simp
        obtain ⟨⟨i', j'⟩, hmem', hdist'⟩ := hnorm.1 (a + cSing, 0) hyplain
        obtain ⟨d1, d2, d3, d4⟩ := dist_ge (a + cSing, 0) (i', j') delta hdist'
        simp only at d1 d2 d3 d4
        have hstrong : InStrongDescriptionProfile V T (pairCode y z)
            (strength + cExt) (i' + logSlack cExt z.length) (j' + z.length) :=
          hExt y z strength i' j' hmem'
        refine ⟨(max a (i' + logSlack cExt z.length),
          max b (j' + z.length)), ?_, ?_⟩
        · refine hUpper (a := (i' + logSlack cExt z.length, j' + z.length)) ?_ ?_
          · exact Prod.mk_le_mk.mpr ⟨le_max_right _ _, le_max_right _ _⟩
          · exact hstrong.mono_epsilon (by omega)
        · refine dist_le _ _ _ ?_ ?_ ?_ ?_ <;> simp only <;> omega
  constructor
  · intro q hq
    obtain ⟨q', hq', hdist⟩ := hTrans y z epsilon ky kyz q hky hkyz hrand hq
    obtain ⟨q'', hq'', hdist''⟩ := key q'.1 q'.2 (by simpa using hq')
    refine ⟨q'', hq'', ?_⟩
    have htri := natPairLInfDistance_triangle q q' q''
    have hq'eq : (q'.1, q'.2) = q' := rfl
    rw [hq'eq] at hdist''
    have hfinal : cTrans * epsilon + logSlack cTrans (y.length + z.length) + M
        ≤ C * (delta + epsilon) + logSlack C (y.length + z.length) := by
      have hm1 : delta ≤ C * delta := Nat.le_mul_of_pos_left _ (by omega)
      have hm2 : (cTrans + cPair) * epsilon ≤ C * epsilon :=
        Nat.mul_le_mul_right _ (by omega)
      have hm3 : C * (delta + epsilon) = C * delta + C * epsilon := by ring
      have hm4 : (cTrans + cPair) * epsilon = cTrans * epsilon + cPair * epsilon := by
        ring
      have e1 : logSlack cTrans (y.length + z.length)
            + logSlack (cExt + cCube + cPair) (y.length + z.length)
          = logSlack (cTrans + (cExt + cCube + cPair)) (y.length + z.length) :=
        logSlack_add_const _ _ _
      have e2 : logSlack (cTrans + (cExt + cCube + cPair)) (y.length + z.length)
            + logSlack (cSing + 1) (y.length + z.length)
          = logSlack C (y.length + z.length) := by
        rw [logSlack_add_const]
        congr 1
        omega
      have e3 : cSing + 1 ≤ logSlack (cSing + 1) (y.length + z.length) := by
        unfold logSlack
        exact Nat.le_add_left _ _
      omega
    omega
  · intro q hq
    exact ⟨q, strongDescriptionProfileSet_subset_plain V T (pairCode y z) _ hq,
      by simp [natPairLInfDistance]⟩

end Kolmogorov
