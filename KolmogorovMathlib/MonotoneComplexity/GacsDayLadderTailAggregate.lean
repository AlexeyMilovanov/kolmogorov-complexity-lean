import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailMass

/-!
# Aggregate terminal mass for the gray-ladder tail

At a terminal state at most one quarter of the source sons are still active.
Every other source son has a (possibly son-dependent) reserve time.  The
temporal reserve lemma therefore turns the resolved three quarters into the
aggregate gray mass needed by Day's half-step.
-/

namespace Kolmogorov

private abbrev GrayTailSourceSon (n a e : Nat) :=
  Fin n × Fin (2 ^ (e - a))

private def grayTailSourceEmbedding (q L a e : Nat) :
    Fin (2 ^ (e - a)) → Fin (grayTailBranch q L a e) :=
  fun c => ⟨c.val, lt_of_lt_of_le c.isLt
    (two_pow_sub_le_ladderBranching (grayTailBaseBranch q L) a e)⟩

private def GrayTailSourceActive {n q L a e : Nat}
    (st : GrayTailState n (grayTailBranch q L a e))
    (p : GrayTailSourceSon n a e) : Prop :=
  GrayTailHasSon st.slots p.1 (grayTailSourceEmbedding q L a e p.2)

private noncomputable def grayTailSourceActiveFinset
    {n q L a e : Nat}
    (st : GrayTailState n (grayTailBranch q L a e)) :
    Finset (GrayTailSourceSon n a e) := by
  classical
  exact Finset.univ.filter (GrayTailSourceActive st)

private lemma grayTail_sourceActive_card_le_slots_length
    {n q L a e : Nat}
    (st : GrayTailState n (grayTailBranch q L a e)) :
    (grayTailSourceActiveFinset st).card ≤ st.slots.length := by
  classical
  let pick : {p : GrayTailSourceSon n a e // GrayTailSourceActive st p} →
      {s : GrayTailSlot n (grayTailBranch q L a e) // s ∈ st.slots} :=
    fun p => ⟨Classical.choose p.property,
      (Classical.choose_spec p.property).1⟩
  have hpick : Function.Injective pick := by
    intro p r hpr
    have hpRoot : (pick p).1.1 = p.1.1 := by
      dsimp [pick]
      exact (Classical.choose_spec p.property).2.1
    have hrRoot : (pick r).1.1 = r.1.1 := by
      dsimp [pick]
      exact (Classical.choose_spec r.property).2.1
    have hpSon : (pick p).1.2.1 =
        grayTailSourceEmbedding q L a e p.1.2 := by
      dsimp [pick]
      exact (Classical.choose_spec p.property).2.2
    have hrSon : (pick r).1.2.1 =
        grayTailSourceEmbedding q L a e r.1.2 := by
      dsimp [pick]
      exact (Classical.choose_spec r.property).2.2
    apply Subtype.ext
    apply Prod.ext
    · exact hpRoot.symm.trans
        ((congrArg (fun s => s.1.1) hpr).trans hrRoot)
    · apply Fin.ext
      have hEmb := hpSon.symm.trans
        ((congrArg (fun s => s.1.2.1) hpr).trans hrSon)
      simpa [grayTailSourceEmbedding] using congrArg Fin.val hEmb
  have hsub : Fintype.card {p : GrayTailSourceSon n a e //
        GrayTailSourceActive st p} ≤
      Fintype.card {s : GrayTailSlot n (grayTailBranch q L a e) //
        s ∈ st.slots} := Fintype.card_le_of_injective pick hpick
  calc
    (grayTailSourceActiveFinset st).card =
        Fintype.card {p : GrayTailSourceSon n a e //
          GrayTailSourceActive st p} := by
      simpa [grayTailSourceActiveFinset] using
        (Fintype.card_subtype (GrayTailSourceActive st)).symm
    _ ≤ Fintype.card {s : GrayTailSlot n (grayTailBranch q L a e) //
          s ∈ st.slots} := hsub
    _ = st.slots.toFinset.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext s
      simp
    _ ≤ st.slots.length := List.toFinset_card_le st.slots

/-- If the tail controller is terminal and no positive request remains
unserved, then the resolved source sons already contribute three quarters of
the source mass at every finer depth. -/
theorem grayTail_terminal_target_mass
    {n q L a e t deltaDepth : Nat} {sigma : FamilyStrategyScheme}
    {A : Allocation} {sm : Nat → FamilyServerMove}
    (ha : 1 ≤ a) (hae : a ≤ e) (hed : e ≤ deltaDepth)
    (hsm : familyServerPlayLegal n (grayTailBranch q L a e) A sm)
    (hterminal : ((grayTailStateAt
      (n := n) (b := grayTailBranch q L a e)
      q L a e sigma A sm t).done ||
        (grayTailStateAt
          (n := n) (b := grayTailBranch q L a e)
          q L a e sigma A sm t).slots.isEmpty) = true)
    (hnotwin : ¬ familyClientWinsUnservedPositive n (2 * (q + 1))
      (grayTailBranch q L a e)
      (playClientFamily A n (grayTailStrategy q L a e sigma) sm) sm) :
    ∃ T, (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) ≤
      familyGrayMass e deltaDepth n T A sm := by
  classical
  let st := grayTailStateAt
    (n := n) (b := grayTailBranch q L a e)
    q L a e sigma A sm t
  let active : GrayTailSourceSon n a e → Prop :=
    GrayTailSourceActive st
  let Inactive := {p : GrayTailSourceSon n a e // ¬ active p}
  have hexists : ∀ j : Inactive, ∃ T R,
      IsTailFamilyReserve e (grayTailBranch q L a e) A n j.1.1.val
        (sm T) [(grayTailSourceEmbedding q L a e j.1.2).val] R := by
    intro j
    have hflow := (grayTail_terminal_resolution
      (sigma := sigma) hterminal).2 j.1.1
        (grayTailSourceEmbedding q L a e j.1.2) j.1.2.isLt
    rcases hflow with hactive | hresolved
    · exact (j.property hactive).elim
    · exact grayTail_terminal_resolved_son_has_reserve ha hae hsm hterminal
        hnotwin j.1.1 (grayTailSourceEmbedding q L a e j.1.2) hresolved
  let reserveTime : Inactive → Nat := fun j => Classical.choose (hexists j)
  let reserveCell : Inactive → BitString := fun j =>
    Classical.choose (Classical.choose_spec (hexists j))
  have hreserve : ∀ j : Inactive,
      IsTailFamilyReserve e (grayTailBranch q L a e) A n j.1.1.val
        (sm (reserveTime j))
        [(grayTailSourceEmbedding q L a e j.1.2).val]
        (reserveCell j) := by
    intro j
    exact Classical.choose_spec (Classical.choose_spec (hexists j))
  let T := Finset.univ.sup reserveTime
  have htime : ∀ j : Inactive, reserveTime j ≤ T := by
    intro j
    exact Finset.le_sup (Finset.mem_univ j)
  have hdistinct : ∀ j l : Inactive, j ≠ l →
      j.1.1.val ≠ l.1.1.val ∨
        ¬ ([(grayTailSourceEmbedding q L a e j.1.2).val] <+:
              [(grayTailSourceEmbedding q L a e l.1.2).val] ∨
            [(grayTailSourceEmbedding q L a e l.1.2).val] <+:
              [(grayTailSourceEmbedding q L a e j.1.2).val]) := by
    intro j l hjl
    by_cases hroot : j.1.1.val = l.1.1.val
    · right
      intro hprefix
      apply hjl
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext hroot
      · apply Fin.ext
        rcases hprefix with hprefix | hprefix
        · simpa [grayTailSourceEmbedding] using hprefix
        · symm
          simpa [grayTailSourceEmbedding] using hprefix
    · exact Or.inl hroot
  have hmass : (Fintype.card Inactive : Rat) * dyadicScale e ≤
      familyGrayMass e deltaDepth n T A sm := by
    simpa [dyadicScale] using
      (familyGrayMass_ge_of_tailFamilyReserves_at_times
        (epsDepth := e) (deltaDepth := deltaDepth) (n := n) (T := T)
        (b := grayTailBranch q L a e) hed hsm reserveTime
        (fun j => j.1.1.val)
        (fun j => [(grayTailSourceEmbedding q L a e j.1.2).val])
        reserveCell htime
        (fun j => j.1.1.isLt)
        (by
          intro j d hd
          simp only [List.mem_singleton] at hd
          subst d
          exact (grayTailSourceEmbedding q L a e j.1.2).isLt)
        hdistinct hreserve)
  have hactiveCard : Fintype.card {p : GrayTailSourceSon n a e // active p} ≤
      st.slots.length := by
    calc
      Fintype.card {p : GrayTailSourceSon n a e // active p} =
          (grayTailSourceActiveFinset st).card := by
        simpa [active, grayTailSourceActiveFinset] using
          Fintype.card_subtype active
      _ ≤ st.slots.length :=
        grayTail_sourceActive_card_le_slots_length st
  have hwidth : 4 * st.slots.length ≤ n * 2 ^ (e - a) := by
    simpa [st] using (grayTail_terminal_resolution
      (sigma := sigma) hterminal).1
  have hcompl : Fintype.card Inactive =
      n * 2 ^ (e - a) -
        Fintype.card {p : GrayTailSourceSon n a e // active p} := by
    rw [show Fintype.card Inactive =
        Fintype.card (GrayTailSourceSon n a e) -
          Fintype.card {p : GrayTailSourceSon n a e // active p} by
      simp [Inactive]]
    simp [GrayTailSourceSon]
  have hcardNat : 3 * (n * 2 ^ (e - a)) ≤ 4 * Fintype.card Inactive := by
    omega
  have hcardRat : (3 / 4 : Rat) * ((n * 2 ^ (e - a) : Nat) : Rat) ≤
      (Fintype.card Inactive : Rat) := by
    have hcast : (3 : Rat) * ((n * 2 ^ (e - a) : Nat) : Rat) ≤
        (4 : Rat) * (Fintype.card Inactive : Rat) := by
      exact_mod_cast hcardNat
    nlinarith
  refine ⟨T, ?_⟩
  calc
    (n : Rat) * ((3 / 4 : Rat) * dyadicScale a) =
        (3 / 4 : Rat) * ((n * 2 ^ (e - a) : Nat) : Rat) *
          dyadicScale e := by
      rw [← two_pow_sub_mul_dyadicScale hae]
      push_cast
      ring
    _ ≤ (Fintype.card Inactive : Rat) * dyadicScale e :=
      mul_le_mul_of_nonneg_right hcardRat (dyadicScale_pos e).le
    _ ≤ familyGrayMass e deltaDepth n T A sm := hmass

end Kolmogorov
