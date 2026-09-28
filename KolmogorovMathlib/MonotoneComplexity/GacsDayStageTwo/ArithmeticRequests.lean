import KolmogorovMathlib.MonotoneComplexity.GacsDayHalfAmplification
import KolmogorovMathlib.MonotoneComplexity.GacsDayStageTwo.ServerProbes

/-!
# The arithmetic of the stage-two requests

The request assignment of the second amplification stage and the estimates the family game needs
from it: the move is superadditive over children (`sum_getReq_stageTwoMove_children`), every
request is `0` or at least `2 ^ (-D)` (`getReq_stageTwoMove_min`), fixing the choice can only
raise requests (`getReq_stageTwoMove_mono`), and along a play the choice is made once and then
kept (`stageTwoChoice_step`). `StageTwoRequestsServed` and `StageTwoServedPlay` package a legal
server play that serves every positive stage-two request, the situation from which the
contradiction is drawn. The results are `grayFamilyGameSpec_stageTwo`, solving the family game
specification at every dyadic request scale, and `grayFamilyStageSpec_two`, the stage-`2`
invariant of the family induction with its depth loss and branching.
-/

namespace Kolmogorov

/-- The stage-two move is superadditive: the two children never exceed their parent. -/
lemma sum_getReq_stageTwoMove_children {a D : ℕ} (h : a + 1 ≤ D) (j : Option ℕ)
    (x : GacsDayNode) :
    ∑ c : Fin 2, getReq (stageTwoMove a D j) (x ++ [c.val])
      ≤ getReq (stageTwoMove a D j) x := by
  rw [Fin.sum_univ_two]
  by_cases h0 : x = []
  · subst h0
    have hz : getReq (stageTwoMove a D j) ([] ++ [((0 : Fin 2) : ℕ)]) = stageTwoReq a D j 0 := by
      simp
    have ho : getReq (stageTwoMove a D j) ([] ++ [((1 : Fin 2) : ℕ)]) = stageTwoReq a D j 1 := by
      simp
    rw [hz, ho, getReq_stageTwoMove_nil]
    exact stageTwoReq_sum_le j
  · have hxlen : 1 ≤ x.length := List.length_pos_iff.mpr h0
    have hz : ∀ c : Fin 2, getReq (stageTwoMove a D j) (x ++ [(c : ℕ)]) = 0 := by
      intro c
      refine getReq_stageTwoMove_of_two_le_length ?_
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hz 0, hz 1, add_zero]
    exact getReq_stageTwoMove_nonneg h j x

/-- Every request of the stage-two move is either `0` or at least `2 ^ (-D)`. -/
lemma getReq_stageTwoMove_min {a D : ℕ} (h : a + 2 ≤ D) (j : Option ℕ) (x : GacsDayNode) :
    getReq (stageTwoMove a D j) x = 0 ∨ (1 / 2 : ℚ) ^ D ≤ getReq (stageTwoMove a D j) x := by
  by_cases h0 : x = []
  · refine Or.inr ?_
    rw [h0, getReq_stageTwoMove_nil]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  by_cases h1 : x = [0]
  · exact Or.inr (by rw [h1, getReq_stageTwoMove_zero]; exact stageTwoReq_ge_delta h j 0)
  by_cases h2 : x = [1]
  · exact Or.inr (by rw [h2, getReq_stageTwoMove_one]; exact stageTwoReq_ge_delta h j 1)
  · exact Or.inl (getReq_stageTwoMove_eq_zero h0 h1 h2)

/-- Fixing the choice can only raise the stage-two requests. -/
lemma getReq_stageTwoMove_mono {a D : ℕ} {j j' : Option ℕ} (h : j = none ∨ j = j')
    (x : GacsDayNode) :
    getReq (stageTwoMove a D j) x ≤ getReq (stageTwoMove a D j') x := by
  by_cases h0 : x = []
  · rw [h0, getReq_stageTwoMove_nil, getReq_stageTwoMove_nil]
  by_cases h1 : x = [0]
  · rw [h1, getReq_stageTwoMove_zero, getReq_stageTwoMove_zero]
    exact stageTwoReq_le_of_choice_mono 0 h
  by_cases h2 : x = [1]
  · rw [h2, getReq_stageTwoMove_one, getReq_stageTwoMove_one]
    exact stageTwoReq_le_of_choice_mono 1 h
  · rw [getReq_stageTwoMove_eq_zero h0 h1 h2, getReq_stageTwoMove_eq_zero h0 h1 h2]

/-- Along a play the stage-two choice is made once and then kept. -/
lemma stageTwoChoice_step (a : ℕ) (sm : ℕ → FamilyServerMove) (i t : ℕ) :
    stageTwoChoice a (stageTwoHistory sm i t) = none ∨
      stageTwoChoice a (stageTwoHistory sm i t)
        = stageTwoChoice a (stageTwoHistory sm i (t + 1)) := by
  rcases hf : firstProbe a (stageTwoHistory sm i t) with _ | v
  · exact Or.inl (by simp [stageTwoChoice, hf])
  · refine Or.inr ?_
    rw [stageTwoHistory_succ]
    simp [stageTwoChoice, hf, firstProbe_append_of_some hf]

/-! ### Helper lemmas for stage-two family game winning -/

/-- Every positive request that the stage-two family play makes at a binary node of depth at
most `4` is served by the server at some time.  This is the hypothesis under which the stage-two
branch is analysed once the alternative — an unserved request, which the client wins outright —
has been ruled out. -/
def StageTwoRequestsServed (a D n : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove) : Prop :=
  ∀ (i : ℕ), i < n → ∀ (t₀ : ℕ) (x : GacsDayNode), x.length ≤ 4 →
    (∀ d ∈ x, d < 2) → 0 < getReq (familyClientMoveAt
      (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x →
    ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
      (getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x)

/-- A *served stage-two play*: the server play `sm` is legal for the allocation `A` on the
binary branch, each of the `n` clients displays the stage-two move dictated by its own probe
history, and every positive request it makes at depth at most `4` is served at some later
server time.  These three facts are what the analysis of the stage-two branch always has in
hand, and each of them is used by every lemma that takes this bundle. -/
structure StageTwoServedPlay (a D n : ℕ) (A : Allocation) (sm : ℕ → FamilyServerMove) : Prop where
  /-- The server play is legal on the binary branch. -/
  server_legal : familyServerPlayLegal n 2 A sm
  /-- Every client displays the stage-two move of its own history. -/
  move_eq : ∀ (t i : ℕ), i < n →
    familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t) i
      = stageTwoMove a D (stageTwoChoice a (stageTwoHistory sm i t))
  /-- Every positive request at depth at most `4` is eventually served. -/
  served : StageTwoRequestsServed a D n A sm

/-- If every positive request of the stage-two strategy is eventually served, there is a single
server time `U` at which every client tree is probe-ready. -/
private lemma stageTwo_probe_ready_eventually {a D n : ℕ} (haD3 : a + 3 ≤ D)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (hplay : StageTwoServedPlay a D n A sm) :
    ∃ U : ℕ, ∀ i : Fin n, probeReady a (familyServerMoveAt (sm U) i.val) = true := by
  obtain ⟨hsm, hmove, hserved⟩ := hplay
  have hprobeex : ∀ i : Fin n, ∃ u : ℕ,
      probeReady a (familyServerMoveAt (sm u) i.val) = true := by
    intro i
    have hpos0 : 0 < getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm 0) i.val) [] := by
      rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_nil]; positivity
    obtain ⟨t0, ht0⟩ := hserved i.val i.isLt 0 [] (by simp) (by simp) hpos0
    have hpos1 : 0 < getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm 0) i.val) [0] := by
      rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_zero]
      exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 none 0)
    obtain ⟨t1, ht1⟩ := hserved i.val i.isLt 0 [0] (by simp)
      (by intro d hd; simp only [List.mem_singleton] at hd; omega) hpos1
    have hpos2 : 0 < getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm 0) i.val) [1] := by
      rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_one]
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
    rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_nil] at hs0
    rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_zero] at hs1
    rw [hmove 0 i.val i.isLt, getReq_stageTwoMove_one] at hs2
    unfold probeReady
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine shortCyl_isSome_of_serves ?_ hs0
      have : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
      rw [this]
      have : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
      linarith
    · exact shortCyl_isSome_of_serves (stageTwoReq_gt_quarter haD3 _ 0) hs1
    · exact shortCyl_isSome_of_serves (stageTwoReq_gt_quarter haD3 _ 1) hs2
  choose u hu using hprobeex
  refine ⟨Finset.univ.sup u, ?_⟩
  intro i
  exact probeReady_mono (hsm.1 i.val i.isLt) (Finset.le_sup (Finset.mem_univ i)) (hu i)

/-- Deriving stage-two choice from probe answers. -/
private lemma stageTwo_choice_of_probe {a n : ℕ} (sm : ℕ → FamilyServerMove)
    (U : ℕ) (hUprobe : ∀ i : Fin n, probeReady a (familyServerMoveAt (sm U) i.val) = true)
    (i : Fin n) :
    ∃ s : ℕ, s ≤ U ∧ probeReady a (familyServerMoveAt (sm s) i.val) = true ∧
      stageTwoChoice a (stageTwoHistory sm i.val (U + 1))
        = some (raisedChild a (familyServerMoveAt (sm s) i.val)) := by
  have hmem : familyServerMoveAt (sm U) i.val ∈ stageTwoHistory sm i.val (U + 1) :=
    stageTwoHistory_mem_of_lt (by omega)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (firstProbe_isSome_of_mem hmem (hUprobe i))
  obtain ⟨hvp, hvmem⟩ := firstProbe_spec hv
  obtain ⟨s, hs, rfl⟩ := mem_stageTwoHistory hvmem
  exact ⟨s, by omega, hvp, by simp [stageTwoChoice, hv]⟩

/-- If every positive request of the stage-two strategy is eventually served, the stage-two
strategy meets the family gray-mass goal at amplification `halfAmplification 2`. -/
private lemma stageTwo_win_branch {a e D n : ℕ} (haD1 : a + 1 ≤ D) (heD : e ≤ D) (haD3 : a + 3 ≤ D)
    (A : Allocation) (sm : ℕ → FamilyServerMove) (hplay : StageTwoServedPlay a D n A sm) :
    familyGrayGoal (halfAmplification 2) ((3 / 4 : ℚ) * dyadicScale a) e D n A
      (playClientFamily A n (stageTwoFamilyStrategy a D) sm) sm := by
  obtain ⟨hsm, hmove, hserved⟩ := hplay
  obtain ⟨U, hUprobe⟩ := stageTwo_probe_ready_eventually haD3 A sm ⟨hsm, hmove, hserved⟩
  have hchoice := fun i => stageTwo_choice_of_probe sm U hUprobe i
  choose sIdx hsU hsprobe hschoice using hchoice
  have hraise : ∀ i : Fin n, ∃ t, Serves
      (getAlloc (familyServerMoveAt (sm t) i.val)
        [raisedChild a (familyServerMoveAt (sm (sIdx i)) i.val)])
      ((1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D) := by
    intro i
    set j := raisedChild a (familyServerMoveAt (sm (sIdx i)) i.val) with hj
    have hj2 : j < 2 := raisedChild_lt_two _ _
    have hjpos : 0 < getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm (U + 1)) i.val) [j] := by
      have hmove_step := hmove (U + 1) i.val i.isLt
      rw [hmove_step, hschoice i]
      interval_cases j
      · rw [getReq_stageTwoMove_zero]
        exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 _ 0)
      · rw [getReq_stageTwoMove_one]
        exact lt_trans (by positivity) (stageTwoReq_gt_quarter haD3 _ 1)
    obtain ⟨t, ht⟩ := hserved i.val i.isLt (U + 1) [j] (by simp)
      (by intro d hd; simp only [List.mem_singleton] at hd; omega) hjpos
    refine ⟨t, ?_⟩
    have hmove_step := hmove (U + 1) i.val i.isLt
    rw [hmove_step, hschoice i] at ht
    have hval : getReq (stageTwoMove a D (some j)) [j]
        = (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := by
      interval_cases j
      · rw [getReq_stageTwoMove_zero]; simp [stageTwoReq]
      · rw [getReq_stageTwoMove_one]; simp [stageTwoReq]
    rw [hval] at ht
    exact ht
  choose htt htt_serves using hraise
  set T := max (U + 1) (Finset.univ.sup htt) with hTdef
  have hwex : ∀ i : Fin n, ∃ w : Fin 3 → BitString,
      StageTwoWitnesses a A (getAlloc (familyServerMoveAt (sm T) i.val) []) w := by
    intro i
    have hsT : sIdx i ≤ T := by
      rw [hTdef]
      exact le_trans (hsU i) (le_trans (Nat.le_succ U) (le_max_left (U + 1) (Finset.univ.sup htt)))
    refine stageTwo_tree_witnesses (D := D) (hsm.1 i.val i.isLt)
      (fun t x => hsm.2.2 t i.val i.isLt x) (s := sIdx i) (T := T)
      hsT (hsprobe i) ?_
    exact serves_mono_time (hsm.1 i.val i.isLt)
      (le_max_of_le_right (Finset.le_sup (Finset.mem_univ i))) (htt_serves i)
  choose w hw using hwex
  set c : Fin n × Fin 3 → BitString := fun p => w p.1 p.2 with hcdef
  have hrootanc : ∀ (i : Fin n) (k : Fin 3),
      ∃ y ∈ getFamilyAlloc (sm T) i.val [], y <+: c (i, k) := by
    intro i k
    exact (hw i).2.2.1 k
  have hlenbound : ∀ p : Fin n × Fin 3, (c p).length ≤ a + 1 := by
    rintro ⟨i, k⟩
    obtain ⟨⟨h0, h1, h2⟩, -⟩ := hw i
    fin_cases k
    · exact le_trans h0 (by omega)
    · exact h1
    · exact h2
  have hlenD : ∀ p : Fin n × Fin 3, (c p).length ≤ D := fun p =>
    le_trans (hlenbound p) haD1
  have hanc : ∀ p : Fin n × Fin 3, ∃ y ∈ familyAllocated n T sm, y <+: c p := by
    rintro ⟨i, k⟩
    obtain ⟨y, hy, hyc⟩ := hrootanc i k
    exact ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr hy⟩, hyc⟩
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
  have hmass := familyGrayMass_ge_of_incomparable_witnesses (epsDepth := e) (deltaDepth := D)
    (n := n) (T := T) (A := A) (sm := sm) heD c hlenD hanc hdisj havoidc
  have hinner : ∀ i : Fin n,
      (2 : ℚ) * (1 / 2 : ℚ) ^ a ≤ ∑ k : Fin 3, (1 / 2 : ℚ) ^ (c (i, k)).length := by
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
    linarith
  have hsum : (2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
      ≤ ∑ p : Fin n × Fin 3, (1 / 2 : ℚ) ^ (c p).length := by
    rw [Fintype.sum_prod_type]
    calc (2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
        = ∑ _i : Fin n, (2 : ℚ) * (1 / 2 : ℚ) ^ a := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ∑ i : Fin n, ∑ k : Fin 3, (1 / 2 : ℚ) ^ (c (i, k)).length :=
          Finset.sum_le_sum (fun i _ => hinner i)
  have hgray : (2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
      ≤ familyGrayMass e D n T A sm := le_trans hsum hmass
  have hroot : totalRootRequest n
      (playClientFamily A n (stageTwoFamilyStrategy a D) sm T) = (n : ℚ) * (1 / 2 : ℚ) ^ a := by
    unfold totalRootRequest getFamilyReq
    have : ∀ i : Fin n, getReq (familyClientMoveAt
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm T) i.val) []
        = (1 / 2 : ℚ) ^ a := by
      intro i
      rw [hmove T i.val i.isLt, getReq_stageTwoMove_nil]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => this i)]
    simp
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := by positivity
  have hpa : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ a := by positivity
  refine ⟨T, ?_, ?_, ?_⟩
  · simp only [dyadicScale]
    have h1 : (n : ℚ) * ((3 / 4 : ℚ) * (1 / 2 : ℚ) ^ a)
        = (3 / 4 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a) := by ring
    have h2 : (3 / 4 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a)
        ≤ (2 : ℚ) * ((n : ℚ) * (1 / 2 : ℚ) ^ a) := by nlinarith
    linarith [h1, h2, hgray]
  · rw [hroot]
    simp only [halfAmplification]
    norm_num
    linarith [hgray]
  · rw [hroot]
    simp only [halfAmplification, dyadicScale]
    norm_num
    nlinarith

/-! ### The stage-two family game -/

/-- **Second amplification stage.** For every dyadic request scale `2 ^ (-a)`,
every coarse scale `e ≥ a`, every nonempty family and every unavailable set, the
reactive probe-and-raise strategy wins the family game with amplification `2`,
at height `4`, branching `2` and fine scale `e + 3`. -/
theorem grayFamilyGameSpec_stageTwo (a e : ℕ) (hae : a ≤ e) (n : ℕ) (hn : 1 ≤ n)
    (A : Allocation) :
    GrayFamilyGameSpec (halfAmplification 2) (dyadicScale a) ((3 / 4 : ℚ) * dyadicScale a)
      e (e + 3) 4 2 n A (stageTwoFamilyStrategy a (e + 3)) := by
  classical
  set D := e + 3 with hDdef
  have haD1 : a + 1 ≤ D := by omega
  have haD2 : a + 2 ≤ D := by omega
  have haD3 : a + 3 ≤ D := by omega
  have heD : e ≤ D := by omega
  have halpha : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have hmove : ∀ (sm : ℕ → FamilyServerMove) (t i : ℕ), i < n →
      familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t) i
        = stageTwoMove a D (stageTwoChoice a (stageTwoHistory sm i t)) :=
    fun sm t i hi => stageTwo_move_eq_choice a D A n sm t i hi
  refine ⟨hn, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [halfAmplification]
  · simpa only [dyadicScale] using halpha
  · have : (0 : ℚ) ≤ dyadicScale a := by simp only [dyadicScale]; positivity
    linarith
  · -- legal
    intro sm _hsm
    constructor
    · intro t i hi
      refine ⟨?_, ?_, ?_⟩
      · intro x
        rw [hmove sm t i hi]
        exact getReq_stageTwoMove_nonneg haD1 _ x
      · rw [hmove sm t i hi, getReq_stageTwoMove_nil]
        simp [dyadicScale]
      · intro x
        rw [hmove sm t i hi]
        exact sum_getReq_stageTwoMove_children haD1 _ x
    · intro t i hi x
      simp only [getFamilyReq]
      rw [hmove sm t i hi, hmove sm (t + 1) i hi]
      exact getReq_stageTwoMove_mono (stageTwoChoice_step a sm i t) x
  · -- minimum_request
    intro sm _hsm t i hi x
    rw [hmove sm t i hi]
    exact getReq_stageTwoMove_min haD2 _ x
  · -- wins
    intro sm hsm
    by_cases hwin : familyClientWinsUnserved n 4 2
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm) sm
    · exact Or.inl hwin
    right
    have hserved : ∀ (i : ℕ), i < n → ∀ (t₀ : ℕ) (x : GacsDayNode), x.length ≤ 4 →
        (∀ d ∈ x, d < 2) → 0 < getReq (familyClientMoveAt
          (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x →
        ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
          (getReq (familyClientMoveAt
            (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x) := by
      intro i hi t₀ x hlen hdig _
      by_contra hcon
      push_neg at hcon
      exact hwin ⟨i, hi, t₀, x, hlen, hdig, hcon⟩
    exact stageTwo_win_branch haD1 heD haD3 A sm ⟨hsm, hmove sm, hserved⟩
  · -- wins_positively
    intro sm hsm
    by_cases hwin : familyClientWinsUnservedPositive n 4 2
        (playClientFamily A n (stageTwoFamilyStrategy a D) sm) sm
    · exact Or.inl hwin
    right
    have hserved_pos : ∀ (i : ℕ), i < n → ∀ (t₀ : ℕ) (x : GacsDayNode), x.length ≤ 4 →
        (∀ d ∈ x, d < 2) → 0 < getReq (familyClientMoveAt
            (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x → ∃ t,
              Serves (getAlloc (familyServerMoveAt (sm t) i) x)
          (getReq (familyClientMoveAt
            (playClientFamily A n (stageTwoFamilyStrategy a D) sm t₀) i) x) := by
      intro i hi t₀ x hlen hdig hpos
      by_contra hcon
      push_neg at hcon
      exact hwin ⟨i, hi, t₀, x, hlen, hdig, hcon, hpos⟩
    exact stageTwo_win_branch haD1 heD haD3 A sm ⟨hsm, hmove sm, hserved_pos⟩
  · -- range_supported
    intro hist x i hi j hj
    unfold stageTwoFamilyStrategy
    rw [familyClientMoveAt_ofFn _ hj]
    unfold stageTwoTreeMove
    by_cases hx : x = []
    · subst hx
      refine getReq_stageTwoMove_eq_zero (by simp) ?_ ?_
      · intro h
        simp only [List.nil_append, List.cons.injEq] at h
        omega
      · intro h
        simp only [List.nil_append, List.cons.injEq] at h
        omega
    · refine getReq_stageTwoMove_of_two_le_length ?_
      have hxlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · -- tree_supported
    intro hist x hx j hj
    unfold stageTwoFamilyStrategy
    rw [familyClientMoveAt_ofFn _ hj]
    unfold stageTwoTreeMove
    exact getReq_stageTwoMove_of_two_le_length (by omega)

/-- The stage-`2` invariant of the family induction, proved outright: depth loss
`e + 3`, branching `2`, and the reactive probe-and-raise client as the strategy.
This is the `kappa = 2` rung of the ladder, one step past
`grayFamilyStageSpec_one`. -/
theorem grayFamilyStageSpec_two :
    GrayFamilyStageSpec 2 (fun _a e => e + 3) (fun _a _e => 2)
      (fun a e => stageTwoFamilyStrategy a (e + 3)) := by
  intro alphaDepth epsDepth _ha hae
  refine ⟨by dsimp only; omega, fun n A hn => ?_⟩
  simpa using grayFamilyGameSpec_stageTwo alphaDepth epsDepth hae n hn A

end Kolmogorov
