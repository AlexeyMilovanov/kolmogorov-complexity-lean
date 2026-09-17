import KolmogorovMathlib.MonotoneComplexity.GacsDayGrayWitness
import KolmogorovMathlib.MonotoneComplexity.GacsDayAmplificationBarrier
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo
import KolmogorovMathlib.MonotoneComplexity.GacsDayHalfAmplification

/-!
# Forcing the server to reveal a witness

`FamilyWitnessForcing` names the property that carries the family game: against every legal
server play that serves all of the client's requests, the strategy eventually exhibits a witness
tree whose raised child has been served. `wins_of_familyWitnessForcing_positive` turns that
property into a win once the amplification is at least `3/4` and the root requests have the
prescribed dyadic size, and `grayFamilyGameSpec_of_witnessForcing` packages a legal
witness-forcing strategy as a solution of the family game specification. The two concrete
instances are `familyWitnessForcing_one` for the one-step half strategy and
`familyWitnessForcing_two` for the stage-two strategy, the latter resting on
`stageTwo_probeReady_eventually` and `stageTwo_raisedChild_served`. The mass contradiction is
`not_serves_all_of_witnessForcing_of_one_lt_target`: a witness-forcing strategy targeting total
mass above `1` cannot be served.
-/

namespace Kolmogorov

open scoped BigOperators

/-- The client family strategy `σ` forces witnesses: against every legal server play that serves
all positive requests, some stage produces a family of pairwise incomparable strings of depth
at most `deltaDepth`, each extending a cell allocated to its client and avoiding `A`, whose
mass per client is at least `kappa * dyadicScale alphaDepth`. -/
def FamilyWitnessForcing (kappa : ℚ) (h b alphaDepth deltaDepth n : ℕ) [NeZero n]
    (A : Allocation) (σ : ClientFamilyStrategy) : Prop :=
  ∀ sm, familyServerPlayLegal n b A sm →
    (∀ i, i < n → ∀ t₀, ∀ x : GacsDayNode, x.length ≤ h → (∀ dg,
      dg ∈ x → dg < b) → 0 < getReq (familyClientMoveAt (playClientFamily A n σ sm t₀) i) x →
      ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
        (getReq (familyClientMoveAt (playClientFamily A n σ sm t₀) i) x)) →
    ∃ (T m : ℕ) (c : Fin n × Fin m → BitString),
      (∀ p, (c p).length ≤ deltaDepth) ∧
      (∀ p, ∃ y ∈ getFamilyAlloc (sm T) p.1.val [], y <+: c p) ∧
      (∀ p q, p ≠ q → ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p))) ∧
      (∀ p, ∀ v ∈ A, ¬ ((c p) <+: v ∨ v <+: (c p))) ∧
      (∀ i : Fin n, kappa * dyadicScale alphaDepth
          ≤ ∑ j : Fin m, (1 / 2 : ℚ) ^ (c (i, j)).length) ∧
      ((3 / 4 : ℚ) * dyadicScale alphaDepth
          ≤ ∑ j : Fin m, (1 / 2 : ℚ) ^ (c (0, j)).length)

/-- A witness-forcing strategy with `3/4 ≤ kappa` and root requests of size `dyadicScale alphaDepth`
either leaves some positive request unserved or meets the gray family goal. -/
theorem wins_of_familyWitnessForcing_positive (kappa : ℚ) (h b alphaDepth deltaDepth n :
  ℕ) [NeZero n]
    (A : Allocation) (σ : ClientFamilyStrategy) :
    FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A σ →
    alphaDepth ≤ deltaDepth →
    (3 / 4 : ℚ) ≤ kappa →
    (∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
      getFamilyReq (playClientFamily A n σ sm t) i [] = dyadicScale alphaDepth) →
    ∀ sm, familyServerPlayLegal n b A sm →
      familyClientWinsUnservedPositive n h b (playClientFamily A n σ sm) sm ∨
      familyGrayGoal kappa ((3/4 : ℚ) * dyadicScale alphaDepth)
        alphaDepth deltaDepth n A (playClientFamily A n σ sm) sm := by
  intro hForcing h_scales h_kappa h_root sm hsm
  by_cases hwin : familyClientWinsUnservedPositive n h b (playClientFamily A n σ sm) sm
  · exact Or.inl hwin
  · refine Or.inr ?_
    have hserved : ∀ i < n, ∀ t₀ (x : GacsDayNode), x.length ≤ h → (∀ dg ∈ x, dg < b) →
      0 < getReq (familyClientMoveAt (playClientFamily A n σ sm t₀) i) x →
      ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
        (getReq (familyClientMoveAt (playClientFamily A n σ sm t₀) i) x) := by
      intro i hi t₀ x hlen hdig hpos
      by_contra hcon
      push Not at hcon
      exact hwin ⟨i, hi, t₀, x, hlen, hdig, hcon, hpos⟩
    obtain ⟨T, m, c, hc_len, hc_anc, hc_disj, hc_avoid, hmass_total, _hmass_root⟩ :=
      hForcing sm hsm hserved
    have hc_anc' : ∀ p, ∃ y ∈ familyAllocated n T sm, y <+: c p := by
      intro p
      obtain ⟨y, hy, hyp⟩ := hc_anc p
      exact ⟨y, Finset.mem_biUnion.mpr
        ⟨p.1, Finset.mem_univ _, List.mem_toFinset.mpr hy⟩, hyp⟩
    have hmass := familyGrayMass_ge_of_incomparable_witnesses
      (epsDepth := alphaDepth) (deltaDepth := deltaDepth) (n := n) (T := T)
      (A := A) (sm := sm) h_scales c hc_len hc_anc' hc_disj hc_avoid
    refine ⟨T, ?_, ?_, ?_⟩
    · have hsum : (n : ℚ) * (kappa * dyadicScale alphaDepth) ≤ ∑ p : Fin n × Fin m,
      (1 / 2 : ℚ) ^ (c p).length := by
        rw [Fintype.sum_prod_type]
        calc (n : ℚ) * (kappa * dyadicScale alphaDepth)
            = ∑ _i : Fin n, kappa * dyadicScale alphaDepth := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ∑ i : Fin n, ∑ k : Fin m, (1 / 2 : ℚ) ^ (c (i, k)).length :=
              Finset.sum_le_sum (fun i _ => hmass_total i)
      have : (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) ≤ (n : ℚ) * (kappa
        * dyadicScale alphaDepth) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right h_kappa
          simp only [dyadicScale]
          positivity
        · positivity
      exact le_trans this (le_trans hsum hmass)
    · have hroot_eq : totalRootRequest n (playClientFamily A n σ sm T) = (n : ℚ)
      * dyadicScale alphaDepth := by
        unfold totalRootRequest getFamilyReq
        have : ∀ i : Fin n, getReq (familyClientMoveAt
            (playClientFamily A n σ sm T) i.val) []
            = dyadicScale alphaDepth := by
          intro i
          exact h_root sm hsm T i.val i.isLt
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => this i)]
        simp
      rw [hroot_eq]
      have hsum : (n : ℚ) * (kappa * dyadicScale alphaDepth) ≤ ∑ p : Fin n × Fin m,
        (1 / 2 : ℚ) ^ (c p).length := by
        rw [Fintype.sum_prod_type]
        calc (n : ℚ) * (kappa * dyadicScale alphaDepth)
            = ∑ _i : Fin n, kappa * dyadicScale alphaDepth := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ∑ i : Fin n, ∑ k : Fin m, (1 / 2 : ℚ) ^ (c (i, k)).length :=
              Finset.sum_le_sum (fun i _ => hmass_total i)
      have : (n : ℚ) * (kappa * dyadicScale alphaDepth) = kappa * ((n : ℚ)
        * dyadicScale alphaDepth) := by ring
      rw [← this]
      exact le_trans hsum hmass
    · have hroot_eq : totalRootRequest n (playClientFamily A n σ sm T) =
          (n : ℚ) * dyadicScale alphaDepth := by
        unfold totalRootRequest getFamilyReq
        have : ∀ i : Fin n, getReq (familyClientMoveAt
            (playClientFamily A n σ sm T) i.val) [] = dyadicScale alphaDepth := by
          intro i
          exact h_root sm hsm T i.val i.isLt
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => this i)]
        simp
      rw [hroot_eq]
      calc
        (n : ℚ) * ((3 / 4 : ℚ) * dyadicScale alphaDepth) =
            (3 / 4 : ℚ) * ((n : ℚ) * dyadicScale alphaDepth) := by ring
        _ ≤ kappa * ((n : ℚ) * dyadicScale alphaDepth) :=
          mul_le_mul_of_nonneg_right h_kappa
            (mul_nonneg (by positivity)
              (by simp only [dyadicScale]; positivity))

/-- A witness-forcing strategy that is legal, avoids small requests, has the prescribed root
requests and is range- and tree-supported satisfies the full gray family game specification. -/
theorem grayFamilyGameSpec_of_witnessForcing (kappa : ℚ) (h b alphaDepth deltaDepth n :
  ℕ) [NeZero n]
    (A : Allocation) (σ : ClientFamilyStrategy)
    (h_forcing : FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A σ)
    (h_kappa : 1 ≤ kappa)
    (h_scales : alphaDepth ≤ deltaDepth)
    (h_legal : ∀ sm, familyServerPlayLegal n b A sm →
      familyClientPlayLegal n b (dyadicScale alphaDepth) (playClientFamily A n σ sm))
    (h_min : ∀ sm, familyServerPlayLegal n b A sm → ∀ t,
      familyRequestAvoidsSmall n ((1 / 2 : ℚ) ^ deltaDepth) (playClientFamily A n σ sm t))
    (h_root : ∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
      getFamilyReq (playClientFamily A n σ sm t) i [] = dyadicScale alphaDepth)
    (h_range : FamilyRangeSupported n b A σ)
    (h_tree : FamilyTreeSupported n h A σ) :
    GrayFamilyGameSpec kappa (dyadicScale alphaDepth) ((3 / 4 : ℚ) * dyadicScale alphaDepth)
      alphaDepth deltaDepth h b n A σ := by
  refine ⟨?_, h_kappa, ?_, ?_, h_scales, h_legal, h_min, ?_, ?_, h_range, h_tree⟩
  · exact NeZero.one_le
  · simp only [dyadicScale]; positivity
  · simp only [dyadicScale]; positivity
  · intro sm hsm
    have h_kappa_34 : (3 / 4 : ℚ) ≤ kappa := by linarith
    have hpos :=
      wins_of_familyWitnessForcing_positive kappa h b alphaDepth deltaDepth n A σ h_forcing h_scales
      h_kappa_34 h_root sm hsm
    rcases hpos with hwin | hgray
    · exact Or.inl (familyClientWinsUnserved_of_positive _ _ _ _ _ hwin)
    · exact Or.inr hgray
  · intro sm hsm
    have h_kappa_34 : (3 / 4 : ℚ) ≤ kappa := by linarith
    exact wins_of_familyWitnessForcing_positive kappa h b alphaDepth deltaDepth n A σ h_forcing
      h_scales h_kappa_34 h_root sm hsm

/-- The one-step half strategy is witness forcing at amplification `halfAmplification 1`, height
`2` and branching `2`. -/
theorem familyWitnessForcing_one (a e : ℕ) (hae : a ≤ e) (n : ℕ) [NeZero n]
    (A : Allocation) :
    FamilyWitnessForcing (halfAmplification 1) 2 2 a (e + 3) n A
      (halfStepFamilyStrategy a (e + 3)) := by
  classical
  intro sm hsm hserved
  set D := e + 3 with hD
  have halpha : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have htpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  have ht8 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ a / 8 := by
    have h1 : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℚ) ^ (a + 3) = (1 / 2 : ℚ) ^ a / 8 := by rw [pow_add]; ring
    linarith
  have hquart : (1 / 2 : ℚ) ^ (a + 2) = (1 / 2 : ℚ) ^ a / 4 := by rw [pow_add]; ring
  have hhalf : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
  -- every root child request of every tree is eventually served
  have hserve : ∀ p : Fin n × Fin 2, ∃ s : ℕ,
      Serves (getFamilyAlloc (sm s) p.1.val [p.2.val]) (getReq (halfStepMove a D) [p.2.val]) := by
    rintro ⟨i, j⟩
    have hpos : 0
      < getReq (familyClientMoveAt (playClientFamily A n (halfStepFamilyStrategy a D) sm 0)
      i.val) [j.val] := by
      rw [halfStep_getReq a D A n sm 0 i.isLt]
      fin_cases j
      · rw [getReq_halfStepMove_zero]; positivity
      · rw [getReq_halfStepMove_one]
        have hDstrict : a + 1 < D := by omega
        have hstrict : (1 / 2 : ℚ) ^ D < (1 / 2 : ℚ) ^ (a + 1) :=
          pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hDstrict
        linarith
    obtain ⟨t, ht⟩ := hserved i.val i.isLt 0 [j.val] (by simp)
      (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact j.isLt) hpos
    refine ⟨t, ?_⟩
    rwa [halfStep_getReq a D A n sm 0 i.isLt] at ht
  choose tt htt using hserve
  set T := Finset.univ.sup tt with hT
  have hservesT : ∀ p : Fin n × Fin 2,
      Serves (getFamilyAlloc (sm T) p.1.val [p.2.val])
        (getReq (halfStepMove a D) [p.2.val]) := fun p =>
    serves_mono_time (hsm.1 p.1.val p.1.isLt) (Finset.le_sup (Finset.mem_univ p)) (htt p)
  -- each of them forces a short cylinder
  have hcell : ∀ p : Fin n × Fin 2, ∃ c ∈ getFamilyAlloc (sm T) p.1.val [p.2.val],
      c.length ≤ a + p.2.val := by
    rintro ⟨i, j⟩
    have h := hservesT (i, j)
    match j with
    | ⟨0, _⟩ =>
      refine length_le_of_serves ?_ h
      simp only [getReq_halfStepMove_zero]
      linarith
    | ⟨1, _⟩ =>
      refine length_le_of_serves ?_ h
      simp only [getReq_halfStepMove_one]
      rw [show a + 1 + 1 = a + 2 from rfl, hquart]
      linarith
  choose c hc_mem hc_len using hcell
  have hroot_sub : ∀ (i : Fin n) (j : Fin 2), ∀ z ∈ getFamilyAlloc (sm T) i.val [j.val],
      ∃ y ∈ getFamilyAlloc (sm T) i.val [], y <+: z := by
    intro i j z hz
    have hco := (hsm.1 i.val i.isLt).1 T
    have := hco.1 [] j
    exact this z hz
  have hanc : ∀ p : Fin n × Fin 2,
      ∃ y ∈ getFamilyAlloc (sm T) p.1.val [], y <+: c p := by
    rintro ⟨i, j⟩
    exact hroot_sub i j (c (i, j)) (hc_mem (i, j))
  have hdisj : ∀ p q : Fin n × Fin 2, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := by
        intro h; exact hne (by simp [h])
      have hco := (hsm.1 i.val i.isLt).1 T
      have hd := hco.2 [] j j' hjj
      exact hd (c (i, j)) (hc_mem (i, j))
        (c (i, j')) (hc_mem (i, j'))
    · obtain ⟨y, hy, hyc⟩ := hroot_sub i j (c (i, j)) (hc_mem (i, j))
      obtain ⟨y', hy', hyc'⟩ := hroot_sub i' j' (c (i', j')) (hc_mem (i', j'))
      have hroot := hsm.2.1 T i.val i.isLt i'.val i'.isLt (fun h => hii (Fin.ext h))
      intro hcomp
      refine hroot y hy y' hy' ?_
      rcases hcomp with hcomp | hcomp
      · exact List.prefix_or_prefix_of_prefix (hyc.trans hcomp) hyc'
      · exact (List.prefix_or_prefix_of_prefix (hyc'.trans hcomp) hyc).symm
  have havoid : ∀ p : Fin n × Fin 2, ∀ u ∈ A, ¬ ((c p) <+: u ∨ u <+: (c p)) := by
    rintro ⟨i, j⟩ u hu
    exact hsm.2.2 T i.val i.isLt [j.val] (c (i, j)) (hc_mem (i, j)) u hu
  have hlenD : ∀ p : Fin n × Fin 2, (c p).length ≤ D := by
    rintro ⟨i, j⟩
    have := hc_len (i, j)
    have hj : j.val ≤ 1 := by omega
    omega
  have hinner : ∀ i : Fin n, halfAmplification 1 * dyadicScale a
      ≤ ∑ j : Fin 2, (1 / 2 : ℚ) ^ (c (i, j)).length := by
    intro i
    have e0 : (1 / 2 : ℚ) ^ a ≤ (1 / 2 : ℚ) ^ (c (i, 0)).length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simpa using hc_len (i, 0))
    have e1 : (1 / 2 : ℚ) ^ (a + 1) ≤ (1 / 2 : ℚ) ^ (c (i, 1)).length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simpa using hc_len (i, 1))
    rw [Fin.sum_univ_two]
    simp only [halfAmplification, dyadicScale]
    norm_num
    linarith
  refine ⟨T, 2, c, hlenD, hanc, hdisj, havoid, hinner, ?_⟩
  refine le_trans ?_ (hinner 0)
  have : (0 : ℚ) < dyadicScale a := by simp only [dyadicScale]; positivity
  simp only [halfAmplification]
  nlinarith

/-- In stage-two witness forcing, every client tree eventually reaches a state where `probeReady`
holds, provided all positive requests are served. -/
private lemma stageTwo_probeReady_eventually (a D : ℕ) (haD3 : a + 3 ≤ D) (n : ℕ) [NeZero n]
    (A : Allocation) (sm : ℕ → FamilyServerMove) (hsm : familyServerPlayLegal n 2 A sm)
    (hserved : ∀ i, i < n → ∀ t₀, ∀ x : GacsDayNode, x.length ≤ 4 → (∀ dg ∈ x, dg < 2) →
      0 < getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x →
      ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
        (getReq (familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x))
    (i : Fin n) : ∃ u : ℕ, probeReady a (familyServerMoveAt (sm u) i.val) = true := by
  have hmove : ∀ (t : ℕ),
      familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t) i.val
        = stageTwoMove a D (stageTwoChoice a (stageTwoHistory sm i.val t)) := fun t =>
    stageTwo_move_eq_choice a D A n sm t i.val i.isLt
  have hpos0 : 0 < getReq (familyClientMoveAt (playClientFamily A n
      (stageTwoFamilyStrategy a D) sm 0) i.val) [] := by
    rw [hmove 0, getReq_stageTwoMove_nil]; positivity
  obtain ⟨t0, ht0⟩ := hserved i.val i.isLt 0 [] (by simp) (by simp) hpos0
  have hpos1 : 0 < getReq (familyClientMoveAt (playClientFamily A n
      (stageTwoFamilyStrategy a D) sm 0) i.val) [0] := by
    rw [hmove 0, getReq_stageTwoMove_zero]
    exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 none 0)
  obtain ⟨t1, ht1⟩ := hserved i.val i.isLt 0 [0] (by simp)
    (by intro d hd; simp only [List.mem_singleton] at hd; omega) hpos1
  have hpos2 : 0 < getReq (familyClientMoveAt (playClientFamily A n
      (stageTwoFamilyStrategy a D) sm 0) i.val) [1] := by
    rw [hmove 0, getReq_stageTwoMove_one]
    exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 none 1)
  obtain ⟨t2, ht2⟩ := hserved i.val i.isLt 0 [1] (by simp)
    (by intro d hd; simp only [List.mem_singleton] at hd; omega) hpos2
  refine ⟨max t0 (max t1 t2), ?_⟩
  have hleg := hsm.1 i.val i.isLt
  have hs0 := serves_mono_time hleg (le_max_left t0 (max t1 t2)) ht0
  have hs1 := serves_mono_time hleg
    (le_trans (le_max_left t1 t2) (le_max_right t0 (max t1 t2))) ht1
  have hs2 := serves_mono_time hleg
    (le_trans (le_max_right t1 t2) (le_max_right t0 (max t1 t2))) ht2
  rw [hmove 0, getReq_stageTwoMove_nil] at hs0
  rw [hmove 0, getReq_stageTwoMove_zero] at hs1
  rw [hmove 0, getReq_stageTwoMove_one] at hs2
  unfold probeReady
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine shortCyl_isSome_of_serves ?_ hs0
    have h1 : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
    have h2 : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
    rw [h1]; linarith
  · exact shortCyl_isSome_of_serves (stageTwoReq_gt_quarter haD3 _ 0) hs1
  · exact shortCyl_isSome_of_serves (stageTwoReq_gt_quarter haD3 _ 1) hs2

/-- In stage-two witness forcing, every client tree eventually has its raised child request
served. -/
private lemma stageTwo_raisedChild_served (a D : ℕ) (haD3 : a + 3 ≤ D) (n : ℕ) [NeZero n]
    (A : Allocation) (sm : ℕ → FamilyServerMove)
    (hserved : StageTwoRequestsServed a D n A sm)
    (U : ℕ) (sIdx : Fin n → ℕ)
    (hschoice : ∀ i : Fin n, stageTwoChoice a (stageTwoHistory sm i.val (U + 1))
        = some (raisedChild a (familyServerMoveAt (sm (sIdx i)) i.val)))
    (i : Fin n) : ∃ t, Serves
      (getAlloc (familyServerMoveAt (sm t) i.val)
        [raisedChild a (familyServerMoveAt (sm (sIdx i)) i.val)])
      ((1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D) := by
  set j := raisedChild a (familyServerMoveAt (sm (sIdx i)) i.val) with hj
  have hj2 : j < 2 := raisedChild_lt_two _ _
  have hmove : familyClientMoveAt
      (playClientFamily A n (stageTwoFamilyStrategy a D) sm (U + 1)) i.val
      = stageTwoMove a D (stageTwoChoice a (stageTwoHistory sm i.val (U + 1))) :=
    stageTwo_move_eq_choice a D A n sm (U + 1) i.val i.isLt
  have hpos : 0 < getReq (familyClientMoveAt
      (playClientFamily A n (stageTwoFamilyStrategy a D) sm (U + 1)) i.val) [j] := by
    rw [hmove, hschoice i]
    interval_cases j
    · rw [getReq_stageTwoMove_zero]
      exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 _ 0)
    · rw [getReq_stageTwoMove_one]
      exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 _ 1)
  obtain ⟨t, ht⟩ := hserved i.val i.isLt (U + 1) [j] (by simp)
    (by intro d hd; simp only [List.mem_singleton] at hd; omega) hpos
  refine ⟨t, ?_⟩
  rw [hmove, hschoice i] at ht
  have hval : getReq (stageTwoMove a D (some j)) [j]
      = (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := by
    interval_cases j
    · rw [getReq_stageTwoMove_zero]; simp [stageTwoReq]
    · rw [getReq_stageTwoMove_one]; simp [stageTwoReq]
  rw [hval] at ht
  exact ht

/-- The stage-two family strategy is witness forcing at amplification `halfAmplification 2`,
height `4` and branching `2`. -/
theorem familyWitnessForcing_two (a e : ℕ) (hae : a ≤ e) (n : ℕ) [NeZero n]
    (A : Allocation) :
    FamilyWitnessForcing (halfAmplification 2) 4 2 a (e
      + 3) n A (stageTwoFamilyStrategy a (e + 3)) := by
  classical
  intro sm hsm hserved
  set D := e + 3 with hDdef
  have haD1 : a + 1 ≤ D := by omega
  have haD3 : a + 3 ≤ D := by omega
  have halpha : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have hprobeex := stageTwo_probeReady_eventually a D haD3 n A sm hsm hserved
  choose u hu using hprobeex
  set U := Finset.univ.sup u with hUdef
  have hUprobe : ∀ i : Fin n, probeReady a (familyServerMoveAt (sm U) i.val) = true := fun i =>
    probeReady_mono (hsm.1 i.val i.isLt) (Finset.le_sup (Finset.mem_univ i)) (hu i)
  have hchoice : ∀ i : Fin n, ∃ s : ℕ, s ≤ U ∧
      probeReady a (familyServerMoveAt (sm s) i.val) = true ∧
      stageTwoChoice a (stageTwoHistory sm i.val (U + 1))
        = some (raisedChild a (familyServerMoveAt (sm s) i.val)) := by
    intro i
    have hmem : familyServerMoveAt (sm U) i.val ∈ stageTwoHistory sm i.val (U + 1) :=
      stageTwoHistory_mem_of_lt (by omega)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (firstProbe_isSome_of_mem hmem (hUprobe i))
    obtain ⟨hvp, hvmem⟩ := firstProbe_spec hv
    obtain ⟨s, hs, rfl⟩ := mem_stageTwoHistory hvmem
    exact ⟨s, by omega, hvp, by simp [stageTwoChoice, hv]⟩
  choose sIdx hsU hsprobe hschoice using hchoice
  have hraise := stageTwo_raisedChild_served a D haD3 n A sm hserved U sIdx hschoice
  choose tt htt using hraise
  set T := max (U + 1) (Finset.univ.sup tt) with hTdef
  have hwex : ∀ i : Fin n, ∃ w : Fin 3 → BitString,
      StageTwoWitnesses a A (getAlloc (familyServerMoveAt (sm T) i.val) []) w := by
    intro i
    refine stageTwo_tree_witnesses (D := D) (hsm.1 i.val i.isLt)
      (fun t x => hsm.2.2 t i.val i.isLt x) (s := sIdx i) (T := T)
      (by rw [hTdef]; exact le_trans (hsU i) (le_trans (Nat.le_succ U) (le_max_left _ _)))
      (hsprobe i) ?_
    exact serves_mono_time (hsm.1 i.val i.isLt)
      (le_max_of_le_right (Finset.le_sup (Finset.mem_univ i))) (htt i)
  choose w hw using hwex
  set c : Fin n × Fin 3 → BitString := fun p => w p.1 p.2 with hcdef
  have hrootanc : ∀ (i : Fin n) (k : Fin 3),
      ∃ y ∈ getFamilyAlloc (sm T) i.val [], y <+: c (i, k) := fun i k => (hw i).2.2.1 k
  have hlenbound : ∀ p : Fin n × Fin 3, (c p).length ≤ a + 1 := by
    rintro ⟨i, k⟩
    obtain ⟨⟨h0, h1, h2⟩, -⟩ := hw i
    fin_cases k
    · exact le_trans h0 (by omega)
    · exact h1
    · exact h2
  have hlenD : ∀ p : Fin n × Fin 3, (c p).length ≤ D := fun p =>
    le_trans (hlenbound p) (by omega)
  have hanc : ∀ p : Fin n × Fin 3,
      ∃ y ∈ getFamilyAlloc (sm T) p.1.val [], y <+: c p := by
    rintro ⟨i, k⟩
    exact hrootanc i k
  have hdisj : ∀ p q : Fin n × Fin 3, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)) := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hkk : k ≠ k' := by
        intro h; exact hne (by simp [h])
      exact (hw i).2.1 k k' hkk
    · obtain ⟨y, hy, hyc⟩ := hrootanc i k
      obtain ⟨y', hy', hyc'⟩ := hrootanc i' k'
      have hroot := hsm.2.1 T i.val i.isLt i'.val i'.isLt (fun h => hii (Fin.ext h))
      intro hcomp
      refine hroot y hy y' hy' ?_
      rcases hcomp with hcomp | hcomp
      · exact List.prefix_or_prefix_of_prefix (hyc.trans hcomp) hyc'
      · exact (List.prefix_or_prefix_of_prefix (hyc'.trans hcomp) hyc).symm
  have havoidc : ∀ p : Fin n × Fin 3, ∀ v ∈ A, ¬ ((c p) <+: v ∨ v <+: (c p)) := by
    rintro ⟨i, k⟩
    exact (hw i).2.2.2 k
  have hinner : ∀ i : Fin n, halfAmplification 2 * dyadicScale a
      ≤ ∑ k : Fin 3, (1 / 2 : ℚ) ^ (c (i, k)).length := by
    intro i
    obtain ⟨⟨h0, h1, h2⟩, -⟩ := hw i
    rw [Fin.sum_univ_three]
    have e0 : (1 / 2 : ℚ) ^ a ≤ (1 / 2 : ℚ) ^ (c (i, 0)).length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h0
    have e1 : (1 / 2 : ℚ) ^ (a + 1) ≤ (1 / 2 : ℚ) ^ (c (i, 1)).length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
    have e2 : (1 / 2 : ℚ) ^ (a + 1) ≤ (1 / 2 : ℚ) ^ (c (i, 2)).length :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
    have hhalf : (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a := by
      rw [pow_add]; ring
    simp only [halfAmplification, dyadicScale]
    norm_num
    linarith
  refine ⟨T, 3, c, hlenD, hanc, hdisj, havoidc, hinner, ?_⟩
  refine le_trans ?_ (hinner 0)
  have : (0 : ℚ) < dyadicScale a := by simp only [dyadicScale]; positivity
  simp only [halfAmplification]
  nlinarith

/-- If a witness-forcing strategy targets total mass above `1`, no legal server play can serve all
of its requests. -/
theorem not_serves_all_of_witnessForcing_of_one_lt_target (kappa : ℚ) (h b alphaDepth deltaDepth n :
  ℕ) [NeZero n]
    (A : Allocation) (σ : ClientFamilyStrategy)
    (h_forcing : FamilyWitnessForcing kappa h b alphaDepth deltaDepth n A σ)
    (h_scales : alphaDepth ≤ deltaDepth)
    (h_gt : 1 < kappa * n * dyadicScale alphaDepth) :
    ¬ ∃ sm, familyServerPlayLegal n b A sm ∧
      (∀ i, i < n → ∀ t₀, ∀ x : GacsDayNode, x.length ≤ h → (∀ dg, dg ∈ x → dg < b) →
        ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
          (getReq (familyClientMoveAt (playClientFamily A n σ sm t₀) i) x)) := by
  rintro ⟨sm, hsm, hserves⟩
  obtain ⟨T, m, c, hc_len, hc_anc, hc_disj, hc_avoid, hmass_total, _hmass_root⟩ :=
    h_forcing sm hsm (fun i hi t0 x hlen hdig hpos => hserves i hi t0 x hlen hdig)
  -- Summing the per-tree witness mass over the `n` trees gives at least
  -- `n * kappa * alpha`, but the pairwise-incomparable cells are capped at `1`
  -- by the Kraft bound `familyGrayMass_le_one`.
  have hsum : (n : ℚ) * (kappa * dyadicScale alphaDepth)
      ≤ ∑ p : Fin n × Fin m, (1 / 2 : ℚ) ^ (c p).length := by
    rw [Fintype.sum_prod_type]
    calc (n : ℚ) * (kappa * dyadicScale alphaDepth)
        = ∑ _i : Fin n, kappa * dyadicScale alphaDepth := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin n, ∑ k : Fin m, (1 / 2 : ℚ) ^ (c (i, k)).length :=
          Finset.sum_le_sum (fun i _ => hmass_total i)
  have hc_anc' : ∀ p, ∃ y ∈ familyAllocated n T sm, y <+: c p := by
    intro p
    obtain ⟨y, hy, hyp⟩ := hc_anc p
    exact ⟨y, Finset.mem_biUnion.mpr
      ⟨p.1, Finset.mem_univ _, List.mem_toFinset.mpr hy⟩, hyp⟩
  have hmass := familyGrayMass_ge_of_incomparable_witnesses
    (epsDepth := alphaDepth) (deltaDepth := deltaDepth) (n := n) (T := T)
    (A := A) (sm := sm) h_scales c hc_len hc_anc' hc_disj hc_avoid
  have hle1 := familyGrayMass_le_one alphaDepth deltaDepth n T A sm
  have hfinal : (n : ℚ) * (kappa * dyadicScale alphaDepth) ≤ 1 :=
    le_trans hsum (le_trans hmass hle1)
  have hcomm : kappa * (n : ℚ) * dyadicScale alphaDepth
      = (n : ℚ) * (kappa * dyadicScale alphaDepth) := by ring
  rw [hcomm] at h_gt
  linarith
end Kolmogorov
