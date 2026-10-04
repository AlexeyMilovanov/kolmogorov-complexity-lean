import KolmogorovMathlib.MonotoneComplexity.GacsDayHalfAmplification

/-!
# Gacs-Day stage two: server probes

Prefix helpers and probe lemmas for the stage-two server of the Gacs-Day construction.
-/

namespace Kolmogorov

/-! ### Prefix helpers -/

/-- Incompatibility is inherited by extensions on the right. -/
lemma not_prefixComparable_append {x y z : BitString}
    (h : ¬ (x <+: y ∨ y <+: x)) : ¬ (x <+: y ++ z ∨ y ++ z <+: x) := by
  rintro (h1 | h1)
  · exact h (List.prefix_or_prefix_of_prefix h1 (List.prefix_append y z))
  · exact h (Or.inr ((List.prefix_append y z).trans h1))

/-- Two different one-bit extensions of a cell are incompatible. -/
lemma not_prefixComparable_extend (c : BitString) :
    ¬ ((c ++ [false]) <+: (c ++ [true]) ∨ (c ++ [true]) <+: (c ++ [false])) := by
  rw [List.prefix_append_right_inj, List.prefix_append_right_inj]
  decide

/-- Avoiding the unavailable set is inherited by extensions. -/
lemma avoidsUnavailable_append {c z : BitString} {A : Allocation}
    (h : ∀ u ∈ A, ¬ (c <+: u ∨ u <+: c)) :
    ∀ u ∈ A, ¬ ((c ++ z) <+: u ∨ u <+: (c ++ z)) := by
  intro u hu hcmp
  refine h u hu ?_
  rcases hcmp with h1 | h1
  · exact Or.inl ((List.prefix_append c z).trans h1)
  · exact (List.prefix_or_prefix_of_prefix h1 (List.prefix_append c z)).symm

/-- Allocations only grow with time. -/
lemma allocationSubset_mono_time {b : ℕ} {sm : ℕ → ServerMove}
    (hleg : serverPlayLegal b sm) {t T : ℕ} (hle : t ≤ T) (x : GacsDayNode) :
    allocationSubset (getAlloc (sm t) x) (getAlloc (sm T) x) := by
  induction hle with
  | refl => exact allocationSubset_refl _
  | step h ih => exact allocationSubset_trans ih (hleg.2 _ x)

/-! ### Reading the server's probe answer -/

/-- The first allocated cylinder of length at most `m`, if any. -/
def shortCyl (m : ℕ) (alloc : Allocation) : Option BitString :=
  alloc.find? (fun c => decide (c.length ≤ m))

/-- The short cylinder returned by the search belongs to the allocation and has length at most
`m`. -/
lemma shortCyl_spec {m : ℕ} {alloc : Allocation} {c : BitString}
    (h : shortCyl m alloc = some c) : c ∈ alloc ∧ c.length ≤ m := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

/-- An allocation serving more than `2 ^ (-(m+1))` contains a cylinder of length at most `m`. -/
lemma shortCyl_isSome_of_serves {m : ℕ} {alloc : Allocation} {q : ℚ}
    (hq : (1 / 2 : ℚ) ^ (m + 1) < q) (h : Serves alloc q) :
    (shortCyl m alloc).isSome := by
  obtain ⟨c, hc, hlen⟩ := length_le_of_serves hq h
  rcases hs : shortCyl m alloc with _ | v
  · exfalso
    have := List.find?_eq_none.mp hs c hc
    simp [hlen] at this
  · simp

/-- The root cylinder the server used to answer the probe. -/
def probeRoot (a : ℕ) (sm : ServerMove) : Option BitString := shortCyl a (getAlloc sm [])

/-- The cylinder the server used to answer the probe at root child `i`. -/
def probeChild (a : ℕ) (sm : ServerMove) (i : ℕ) : Option BitString :=
  shortCyl (a + 1) (getAlloc sm [i])

/-- The server has answered the whole probe. -/
def probeReady (a : ℕ) (sm : ServerMove) : Bool :=
  (probeRoot a sm).isSome && (probeChild a sm 0).isSome && (probeChild a sm 1).isSome

/-- Which root child the client raises: the one whose *sibling* cylinder is
comparable with the root cylinder, so that the sibling blocks it. -/
def raisedChild (a : ℕ) (sm : ServerMove) : ℕ :=
  match probeRoot a sm, probeChild a sm 1 with
  | some R, some c1 => if R.isPrefixOf c1 || c1.isPrefixOf R then 0 else 1
  | _, _ => 0

/-- The raised child of a server move is `0` or `1`. -/
lemma raisedChild_lt_two (a : ℕ) (sm : ServerMove) : raisedChild a sm < 2 := by
  unfold raisedChild
  rcases probeRoot a sm with _ | R
  · simp
  rcases probeChild a sm 1 with _ | c1
  · simp
  · simp only []
    split <;> omega

/-- The first server move of a history that answers the probe. -/
def firstProbe (a : ℕ) : List ServerMove → Option ServerMove
  | [] => none
  | m :: ms => if probeReady a m then some m else firstProbe a ms

/-- The first probe found in a history is probe-ready and occurs in the history. -/
lemma firstProbe_spec {a : ℕ} {l : List ServerMove} {v : ServerMove}
    (h : firstProbe a l = some v) : probeReady a v = true ∧ v ∈ l := by
  induction l with
  | nil => simp [firstProbe] at h
  | cons m ms ih =>
    by_cases hm : probeReady a m
    · rw [firstProbe, ite_eq_left hm] at h
      cases h
      exact ⟨hm, by simp⟩
    · rw [firstProbe, ite_eq_right hm] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨h1, by simp [h2]⟩

/-- Extending the history does not change the first probe once one has been found. -/
lemma firstProbe_append_of_some {a : ℕ} {l l' : List ServerMove} {v : ServerMove}
    (h : firstProbe a l = some v) : firstProbe a (l ++ l') = some v := by
  induction l with
  | nil => simp [firstProbe] at h
  | cons m ms ih =>
    by_cases hm : probeReady a m
    · rw [firstProbe, ite_eq_left hm] at h
      cases h
      simp [firstProbe, hm]
    · rw [firstProbe, ite_eq_right hm] at h
      simp [firstProbe, hm, ih h]

/-- A probe-ready move in the history guarantees that a first probe is found. -/
lemma firstProbe_isSome_of_mem {a : ℕ} {l : List ServerMove} {m : ServerMove}
    (hm : m ∈ l) (hp : probeReady a m = true) : (firstProbe a l).isSome := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases hx : probeReady a x
    · simp [firstProbe, hx]
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hp hx
      · simpa [firstProbe, hx] using ih hm'

/-! ### The stage-two client -/

/-- The request at root child `i`: half the root request, corrected by
`± 2 ^ (-D)` according to whether `i` is the raised child. -/
def stageTwoReq (a D : ℕ) (j : Option ℕ) (i : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ (a + 1) + (if j = some i then (1 / 2 : ℚ) ^ D else -(1 / 2 : ℚ) ^ D)

/-- The client move: `2 ^ (-a)` at the root, and the two corrected halves at the
root children. `j = none` is the probe phase. -/
def stageTwoMove (a D : ℕ) (j : Option ℕ) : ClientMove :=
  [(([] : GacsDayNode), (1 / 2 : ℚ) ^ a),
   (([0] : GacsDayNode), stageTwoReq a D j 0),
   (([1] : GacsDayNode), stageTwoReq a D j 1)]

/-- The raised child determined by a history of server moves in one tree. -/
def stageTwoChoice (a : ℕ) (l : List ServerMove) : Option ℕ :=
  (firstProbe a l).map (raisedChild a)

/-- The move the stage-two strategy plays against a recorded history of server moves. -/
def stageTwoTreeMove (a D : ℕ) (l : List ServerMove) : ClientMove :=
  stageTwoMove a D (stageTwoChoice a l)

/-- The stage-two family strategy: every tree of the family plays the reactive
two-phase strategy, driven by that tree's own history. -/
def stageTwoFamilyStrategy (a D : ℕ) : ClientFamilyStrategy :=
  fun _A n hist =>
    List.ofFn (fun i : Fin n =>
      stageTwoTreeMove a D (hist.2.map (fun m => familyServerMoveAt m i.val)))

/-- The server moves seen by tree `i` before time `t`. -/
def stageTwoHistory (sm : ℕ → FamilyServerMove) (i t : ℕ) : List ServerMove :=
  List.ofFn (fun k : Fin t => familyServerMoveAt (sm k.val) i)

/-- The history of client `i` grows by that client's row of the current server move. -/
lemma stageTwoHistory_succ (sm : ℕ → FamilyServerMove) (i t : ℕ) :
    stageTwoHistory sm i (t + 1)
      = stageTwoHistory sm i t ++ [familyServerMoveAt (sm t) i] := by
  unfold stageTwoHistory
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- Every entry of the history is a row of a server move played before the current time. -/
lemma mem_stageTwoHistory {sm : ℕ → FamilyServerMove} {i t : ℕ} {v : ServerMove}
    (h : v ∈ stageTwoHistory sm i t) : ∃ s < t, v = familyServerMoveAt (sm s) i := by
  rw [stageTwoHistory, List.mem_ofFn] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k.val, k.isLt, hk.symm⟩

/-- Every earlier server move of a client occurs in its history. -/
lemma stageTwoHistory_mem_of_lt {sm : ℕ → FamilyServerMove} {i s t : ℕ} (hst : s < t) :
    familyServerMoveAt (sm s) i ∈ stageTwoHistory sm i t := by
  rw [stageTwoHistory, List.mem_ofFn]
  exact ⟨⟨s, hst⟩, rfl⟩

/-! ### Elementary request computations -/

/-- The stage-two move requests `2 ^ (-a)` at the root. -/
@[simp] lemma getReq_stageTwoMove_nil (a D : ℕ) (j : Option ℕ) :
    getReq (stageTwoMove a D j) [] = (1 / 2 : ℚ) ^ a := rfl

/-- The stage-two move requests `stageTwoReq a D j 0` at the child `0`. -/
@[simp] lemma getReq_stageTwoMove_zero (a D : ℕ) (j : Option ℕ) :
    getReq (stageTwoMove a D j) [0] = stageTwoReq a D j 0 := rfl

/-- The stage-two move requests `stageTwoReq a D j 1` at the child `1`. -/
@[simp] lemma getReq_stageTwoMove_one (a D : ℕ) (j : Option ℕ) :
    getReq (stageTwoMove a D j) [1] = stageTwoReq a D j 1 := rfl

/-- Away from the root and its two children the stage-two move requests nothing. -/
lemma getReq_stageTwoMove_eq_zero {a D : ℕ} {j : Option ℕ} {x : GacsDayNode}
    (h0 : x ≠ []) (h1 : x ≠ [0]) (h2 : x ≠ [1]) :
    getReq (stageTwoMove a D j) x = 0 := by
  have e0 : (x == ([] : GacsDayNode)) = false := by simpa using h0
  have e1 : (x == ([0] : GacsDayNode)) = false := by simpa using h1
  have e2 : (x == ([1] : GacsDayNode)) = false := by simpa using h2
  simp [getReq, stageTwoMove, List.lookup, e0, e1, e2]

/-- Below depth `2` the stage-two move requests nothing. -/
lemma getReq_stageTwoMove_of_two_le_length {a D : ℕ} {j : Option ℕ} {x : GacsDayNode}
    (hx : 2 ≤ x.length) : getReq (stageTwoMove a D j) x = 0 := by
  refine getReq_stageTwoMove_eq_zero ?_ ?_ ?_ <;>
    · intro h; rw [h] at hx; simp at hx

/-- Fixing the choice can only raise the stage-two son requests. -/
lemma stageTwoReq_le_of_choice_mono {a D : ℕ} {j j' : Option ℕ} (i : ℕ)
    (h : j = none ∨ j = j') : stageTwoReq a D j i ≤ stageTwoReq a D j' i := by
  have hp : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  rcases h with rfl | rfl
  · unfold stageTwoReq
    rw [ite_eq_right (by simp)]
    split <;> linarith
  · exact le_rfl

/-! ### The play of the stage-two strategy -/

/-- Client `i` of a family move given by `List.ofFn f` plays `f i`. -/
lemma familyClientMoveAt_ofFn {n : ℕ} (f : Fin n → ClientMove) {i : ℕ} (hi : i < n) :
    familyClientMoveAt (List.ofFn f) i = f ⟨i, hi⟩ := by
  unfold familyClientMoveAt
  rw [List.getD_eq_getElem?_getD]
  simp [hi]

/-- Each client of the stage-two family strategy plays the stage-two move of its own history. -/
lemma stageTwo_move_eq (a D : ℕ) (A : Allocation) (n : ℕ) (sm : ℕ → FamilyServerMove)
    (t : ℕ) {i : ℕ} (hi : i < n) :
    familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t) i
      = stageTwoTreeMove a D (stageTwoHistory sm i t) := by
  cases t with
  | zero =>
    rw [playClientFamily]
    unfold stageTwoFamilyStrategy
    rw [familyClientMoveAt_ofFn _ hi]
    simp [stageTwoHistory]
  | succ t =>
    rw [playClientFamily]
    unfold stageTwoFamilyStrategy
    rw [familyClientMoveAt_ofFn _ hi]
    simp [stageTwoHistory, List.map_ofFn, Function.comp_def]

/-- Each client of the stage-two family strategy plays the stage-two move determined by the
probe choice read off its own history. -/
lemma stageTwo_move_eq_choice (a D : ℕ) (A : Allocation) (n : ℕ)
    (sm : ℕ → FamilyServerMove) (t i : ℕ) (hi : i < n) :
    familyClientMoveAt (playClientFamily A n (stageTwoFamilyStrategy a D) sm t) i
      = stageTwoMove a D (stageTwoChoice a (stageTwoHistory sm i t)) := by
  rw [stageTwo_move_eq a D A n sm t hi]
  rfl

/-! ### The blocking lemma

The heart of the stage: if the sibling of the raised child is prefix-comparable
with the root cylinder `R`, then the cylinder that serves the raised request
cannot be comparable with `R`, because the sibling's cylinder persists inside
the sibling's allocation and is incompatible with it. -/

/-- A reserve of length `a` comparable with a cylinder above `y` stays incomparable with any
short string that avoids `y`. -/
lemma blocking_incomparable {a : ℕ} {R c y Dj : BitString}
    (hR : R.length = a) (hDj : Dj.length ≤ a)
    (hcmp : R <+: c ∨ c <+: R) (hy : y <+: c)
    (hdisj : ¬ (Dj <+: y ∨ y <+: Dj)) :
    ¬ (R <+: Dj ∨ Dj <+: R) := by
  rintro (h | h)
  · have hlen : R.length = Dj.length := le_antisymm h.length_le (by omega)
    have hRD : R = Dj := h.eq_of_length hlen
    subst hRD
    refine hdisj ?_
    rcases hcmp with hc | hc
    · exact List.prefix_or_prefix_of_prefix hc hy
    · exact Or.inr (hy.trans hc)
  · refine hdisj ?_
    rcases hcmp with hc | hc
    · exact List.prefix_or_prefix_of_prefix (h.trans hc) hy
    · exact (List.prefix_or_prefix_of_prefix (hy.trans hc) h).symm

/-- Three pairwise incompatible cells of lengths `a`, `a+1`, `a+1` that sit below
the root allocation and avoid the unavailable set. This is the shape in which
every case of the stage-two argument delivers its gray witnesses. -/
def StageTwoWitnesses (a : ℕ) (A rootAlloc : Allocation) (w : Fin 3 → BitString) : Prop :=
  ((w 0).length ≤ a ∧ (w 1).length ≤ a + 1 ∧ (w 2).length ≤ a + 1) ∧
    (∀ k l, k ≠ l → ¬ (w k <+: w l ∨ w l <+: w k)) ∧
    (∀ k, ∃ v ∈ rootAlloc, v <+: w k) ∧
    (∀ k, ∀ u ∈ A, ¬ (w k <+: u ∨ u <+: w k))

/-- Three pairwise incomparable short strings, each anchored in the root allocation and avoiding
the unavailable set, form a stage-two witness triple. -/
lemma stageTwo_witness_pack {a : ℕ} {A rootAlloc : Allocation} {x y z : BitString}
    (hx : x.length ≤ a) (hy : y.length ≤ a + 1) (hz : z.length ≤ a + 1)
    (hxy : ¬ (x <+: y ∨ y <+: x)) (hxz : ¬ (x <+: z ∨ z <+: x))
    (hyz : ¬ (y <+: z ∨ z <+: y))
    (hax : ∃ v ∈ rootAlloc, v <+: x) (hay : ∃ v ∈ rootAlloc, v <+: y)
    (haz : ∃ v ∈ rootAlloc, v <+: z)
    (hux : ∀ u ∈ A, ¬ (x <+: u ∨ u <+: x)) (huy : ∀ u ∈ A, ¬ (y <+: u ∨ u <+: y))
    (huz : ∀ u ∈ A, ¬ (z <+: u ∨ u <+: z)) :
    ∃ w : Fin 3 → BitString, StageTwoWitnesses a A rootAlloc w := by
  refine ⟨![x, y, z], ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · simpa using hz
  · intro k l hkl
    fin_cases k <;> fin_cases l <;>
      first
        | exact absurd rfl hkl
        | exact hxy | exact hxz | exact hyz
        | exact fun h => hxy h.symm | exact fun h => hxz h.symm | exact fun h => hyz h.symm
  · intro k
    fin_cases k
    · simpa using hax
    · simpa using hay
    · simpa using haz
  · intro k
    fin_cases k
    · simpa using hux
    · simpa using huy
    · simpa using huz

/-! ### The forced gray witnesses of one tree -/

/-- A child allocation sits below the root allocation. -/
lemma child_alloc_anc {sm : ℕ → ServerMove} (hleg : serverPlayLegal 2 sm) (t : ℕ)
    (i : Fin 2) {c : BitString} (hc : c ∈ getAlloc (sm t) [i.val]) :
    ∃ v ∈ getAlloc (sm t) [], v <+: c := by
  have h := (hleg.1 t).1 [] i
  simpa using h c (by simpa using hc)

/-- Allocations of two different root children are incompatible. -/
lemma sibling_incomparable {sm : ℕ → ServerMove} (hleg : serverPlayLegal 2 sm) (t : ℕ)
    {i i' : Fin 2} (hii : i ≠ i') {c c' : BitString}
    (hc : c ∈ getAlloc (sm t) [i.val]) (hc' : c' ∈ getAlloc (sm t) [i'.val]) :
    ¬ (c <+: c' ∨ c' <+: c) := by
  have h := (hleg.1 t).2 [] i i' hii
  simpa using h c (by simpa using hc) c' (by simpa using hc')

/-- **The stage-two forcing.** Against a legal server that has answered the
probe at time `s` and has served the raised request at time `T ≥ s`, the client
holds three pairwise incompatible cells of lengths `a`, `a+1`, `a+1` below the
root allocation: gray mass `2 * 2 ^ (-a)`. -/
lemma stageTwo_tree_witnesses {a D : ℕ} {A : Allocation} {sm : ℕ → ServerMove}
    (hleg : serverPlayLegal 2 sm)
    (havoid : ∀ t x, allocationAvoidsUnavailable A (getAlloc (sm t) x))
    {s T : ℕ} (hsT : s ≤ T)
    (hprobe : probeReady a (sm s) = true)
    (hserve : Serves (getAlloc (sm T) [raisedChild a (sm s)])
      ((1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D)) :
    ∃ w : Fin 3 → BitString, StageTwoWitnesses a A (getAlloc (sm T) []) w := by
  classical
  -- the three probe answers
  have hready : (probeRoot a (sm s)).isSome ∧ (probeChild a (sm s) 0).isSome ∧
      (probeChild a (sm s) 1).isSome := by
    unfold probeReady at hprobe
    simp only [Bool.and_eq_true] at hprobe
    exact ⟨hprobe.1.1, hprobe.1.2, hprobe.2⟩
  obtain ⟨R, hRopt⟩ := Option.isSome_iff_exists.mp hready.1
  obtain ⟨c0, hc0opt⟩ := Option.isSome_iff_exists.mp hready.2.1
  obtain ⟨c1, hc1opt⟩ := Option.isSome_iff_exists.mp hready.2.2
  obtain ⟨hRmem, hRlen⟩ := shortCyl_spec (by simpa [probeRoot] using hRopt)
  obtain ⟨hc0mem, hc0len⟩ := shortCyl_spec (by simpa [probeChild] using hc0opt)
  obtain ⟨hc1mem, hc1len⟩ := shortCyl_spec (by simpa [probeChild] using hc1opt)
  -- the cylinder that serves the raised request
  have hbig : (1 / 2 : ℚ) ^ (a + 1) < (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := by
    have : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
    linarith
  obtain ⟨Dj, hDjmem, hDjlen⟩ := length_le_of_serves hbig hserve
  -- persistence and ancestors
  have hancR : ∀ z : BitString, ∃ v ∈ getAlloc (sm T) [], v <+: R ++ z := by
    intro z
    obtain ⟨v, hv, hvR⟩ := allocationSubset_mono_time hleg hsT [] R hRmem
    exact ⟨v, hv, hvR.trans (List.prefix_append R z)⟩
  have hancChild : ∀ (i : Fin 2) {c : BitString}, c ∈ getAlloc (sm s) [i.val] →
      ∀ z : BitString, ∃ v ∈ getAlloc (sm T) [], v <+: c ++ z := by
    intro i c hc z
    obtain ⟨y, hy, hyc⟩ := allocationSubset_mono_time hleg hsT [i.val] c hc
    obtain ⟨v, hv, hvy⟩ := child_alloc_anc hleg T i hy
    exact ⟨v, hv, (hvy.trans hyc).trans (List.prefix_append c z)⟩
  have hancDj : ∀ z : BitString, ∃ v ∈ getAlloc (sm T) [], v <+: Dj ++ z := by
    intro z
    obtain ⟨v, hv, hvD⟩ :=
      child_alloc_anc hleg T ⟨raisedChild a (sm s), raisedChild_lt_two a (sm s)⟩ hDjmem
    exact ⟨v, hv, hvD.trans (List.prefix_append Dj z)⟩
  -- avoidance of the unavailable set
  have havR : ∀ u ∈ A, ¬ (R <+: u ∨ u <+: R) := havoid s [] R hRmem
  have havc0 : ∀ u ∈ A, ¬ (c0 <+: u ∨ u <+: c0) := havoid s [0] c0 hc0mem
  have havc1 : ∀ u ∈ A, ¬ (c1 <+: u ∨ u <+: c1) := havoid s [1] c1 hc1mem
  have havDj : ∀ u ∈ A, ¬ (Dj <+: u ∨ u <+: Dj) :=
    havoid T [raisedChild a (sm s)] Dj hDjmem
  -- the decision rule
  have hjdef : raisedChild a (sm s) = if R.isPrefixOf c1 || c1.isPrefixOf R then 0 else 1 := by
    simp only [raisedChild, hRopt, hc1opt]
  -- the case where the root cylinder alone carries twice the root request
  by_cases hRshort : R.length < a
  · refine stageTwo_witness_pack (a := a) (A := A) (x := R ++ [true])
      (y := R ++ [false, false]) (z := R ++ [false, true]) ?_ ?_ ?_ ?_ ?_ ?_
      (hancR _) (hancR _) (hancR _)
      (avoidsUnavailable_append havR) (avoidsUnavailable_append havR)
      (avoidsUnavailable_append havR)
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · rw [List.prefix_append_right_inj, List.prefix_append_right_inj]; decide
    · rw [List.prefix_append_right_inj, List.prefix_append_right_inj]; decide
    · rw [List.prefix_append_right_inj, List.prefix_append_right_inj]; decide
  have hRa : R.length = a := le_antisymm hRlen (by omega)
  -- otherwise the raised child is blocked, or the three probe cells already work
  by_cases hcmp1 : R <+: c1 ∨ c1 <+: R
  · -- the sibling is child `1`, and it is comparable with `R`
    have hj0 : raisedChild a (sm s) = 0 := by
      rw [hjdef]
      have hb : (R.isPrefixOf c1 || c1.isPrefixOf R) = true := by
        rcases hcmp1 with h | h
        · simp [List.isPrefixOf_iff_prefix.mpr h]
        · simp [List.isPrefixOf_iff_prefix.mpr h]
      simp [hb]
    obtain ⟨y1, hy1mem, hy1⟩ := allocationSubset_mono_time hleg hsT [1] c1 hc1mem
    have hdisj : ¬ (Dj <+: y1 ∨ y1 <+: Dj) := by
      refine sibling_incomparable hleg T (i := 0) (i' := 1) (by decide) ?_ ?_
      · simpa [hj0] using hDjmem
      · simpa using hy1mem
    have hinc : ¬ (R <+: Dj ∨ Dj <+: R) :=
      blocking_incomparable hRa hDjlen hcmp1 hy1 hdisj
    refine stageTwo_witness_pack (a := a) (A := A) (x := R)
      (y := Dj ++ [false]) (z := Dj ++ [true]) (by omega) ?_ ?_
      (not_prefixComparable_append hinc) (not_prefixComparable_append hinc)
      (not_prefixComparable_extend Dj)
      (by simpa using hancR []) (hancDj _) (hancDj _)
      havR (avoidsUnavailable_append havDj) (avoidsUnavailable_append havDj)
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · have hj1 : raisedChild a (sm s) = 1 := by
      rw [hjdef]
      have hb : (R.isPrefixOf c1 || c1.isPrefixOf R) = false := by
        rcases hb0 : R.isPrefixOf c1 with _ | _
        · rcases hb1 : c1.isPrefixOf R with _ | _
          · simp
          · exact absurd (Or.inr (List.isPrefixOf_iff_prefix.mp hb1)) hcmp1
        · exact absurd (Or.inl (List.isPrefixOf_iff_prefix.mp hb0)) hcmp1
      simp [hb]
    by_cases hcmp0 : R <+: c0 ∨ c0 <+: R
    · -- the sibling is child `0`, and it is comparable with `R`
      obtain ⟨y0, hy0mem, hy0⟩ := allocationSubset_mono_time hleg hsT [0] c0 hc0mem
      have hdisj : ¬ (Dj <+: y0 ∨ y0 <+: Dj) := by
        refine sibling_incomparable hleg T (i := 1) (i' := 0) (by decide) ?_ ?_
        · simpa [hj1] using hDjmem
        · simpa using hy0mem
      have hinc : ¬ (R <+: Dj ∨ Dj <+: R) :=
        blocking_incomparable hRa hDjlen hcmp0 hy0 hdisj
      refine stageTwo_witness_pack (a := a) (A := A) (x := R)
        (y := Dj ++ [false]) (z := Dj ++ [true]) (by omega) ?_ ?_
        (not_prefixComparable_append hinc) (not_prefixComparable_append hinc)
        (not_prefixComparable_extend Dj)
        (by simpa using hancR []) (hancDj _) (hancDj _)
        havR (avoidsUnavailable_append havDj) (avoidsUnavailable_append havDj)
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · -- neither probe cell is comparable with the root cylinder
      have hc01 : ¬ (c0 <+: c1 ∨ c1 <+: c0) :=
        sibling_incomparable hleg s (i := 0) (i' := 1) (by decide)
          (by simpa using hc0mem) (by simpa using hc1mem)
      exact stageTwo_witness_pack (a := a) (A := A) (x := R) (y := c0) (z := c1)
        (by omega) hc0len hc1len hcmp0 hcmp1 hc01
        (by simpa using hancR []) (by simpa using hancChild 0 hc0mem [])
        (by simpa using hancChild 1 hc1mem [])
        havR havc0 havc1

/-! ### Monotonicity of the probe answer -/

/-- A short cylinder found in an allocation is still found in any larger allocation. -/
lemma shortCyl_isSome_mono {m : ℕ} {a1 a2 : Allocation} (h : allocationSubset a1 a2)
    (hs : (shortCyl m a1).isSome) : (shortCyl m a2).isSome := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨hcmem, hclen⟩ := shortCyl_spec hc
  obtain ⟨v, hv, hvc⟩ := h c hcmem
  rcases hs2 : shortCyl m a2 with _ | v2
  · exfalso
    have := List.find?_eq_none.mp hs2 v hv
    have hvlen : v.length ≤ m := le_trans hvc.length_le hclen
    simp [hvlen] at this
  · simp

/-- Along a legal play, once a move is probe-ready every later move is. -/
lemma probeReady_mono {a : ℕ} {sm : ℕ → ServerMove} (hleg : serverPlayLegal 2 sm) {t T : ℕ}
    (htT : t ≤ T) (hp : probeReady a (sm t) = true) : probeReady a (sm T) = true := by
  unfold probeReady at hp ⊢
  simp only [Bool.and_eq_true] at hp ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact shortCyl_isSome_mono (allocationSubset_mono_time hleg htT []) hp.1.1
  · exact shortCyl_isSome_mono (allocationSubset_mono_time hleg htT [0]) hp.1.2
  · exact shortCyl_isSome_mono (allocationSubset_mono_time hleg htT [1]) hp.2

/-! ### Arithmetic of the stage-two requests -/

/-- The stage-two son requests are nonnegative. -/
lemma stageTwoReq_nonneg {a D : ℕ} (h : a + 1 ≤ D) (j : Option ℕ) (i : ℕ) :
    0 ≤ stageTwoReq a D j i := by
  have hle : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  unfold stageTwoReq
  split <;> linarith

/-- The stage-two son requests are at least the fine scale `2 ^ (-D)`. -/
lemma stageTwoReq_ge_delta {a D : ℕ} (h : a + 2 ≤ D) (j : Option ℕ) (i : ℕ) :
    (1 / 2 : ℚ) ^ D ≤ stageTwoReq a D j i := by
  have hle : (1 / 2 : ℚ) ^ (a + 2) ≤ (1 / 2 : ℚ) ^ (a + 1) / 2 := by
    rw [pow_succ]; ring_nf; norm_num
  have hD : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ (a + 1) := by positivity
  unfold stageTwoReq
  split <;> linarith

/-- The stage-two son requests stay below `2 ^ (-(a+1)) + 2 ^ (-D)`. -/
lemma stageTwoReq_le_top {a D : ℕ} (j : Option ℕ) (i : ℕ) :
    stageTwoReq a D j i ≤ (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ D := by
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  unfold stageTwoReq
  split <;> linarith

/-- The stage-two son requests exceed `2 ^ (-(a+2))`. -/
lemma stageTwoReq_gt_quarter {a D : ℕ} (h : a + 3 ≤ D) (j : Option ℕ) (i : ℕ) :
    (1 / 2 : ℚ) ^ (a + 2) < stageTwoReq a D j i := by
  have hD : (1 / 2 : ℚ) ^ D ≤ (1 / 2 : ℚ) ^ (a + 3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have h1 : (1 / 2 : ℚ) ^ (a + 2) = (1 / 2 : ℚ) ^ a / 4 := by rw [pow_add]; ring
  have h2 : (1 / 2 : ℚ) ^ (a + 3) = (1 / 2 : ℚ) ^ a / 8 := by rw [pow_add]; ring
  have h3 : (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a / 2 := by rw [pow_add]; ring
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ a := by positivity
  have hDpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  unfold stageTwoReq
  rw [h1, h3]
  split <;> linarith

/-- The two stage-two son requests together stay within the root request `2 ^ (-a)`. -/
lemma stageTwoReq_sum_le {a D : ℕ} (j : Option ℕ) :
    stageTwoReq a D j 0 + stageTwoReq a D j 1 ≤ (1 / 2 : ℚ) ^ a := by
  have hpos : (0 : ℚ) < (1 / 2 : ℚ) ^ D := by positivity
  have hhalf : (1 / 2 : ℚ) ^ (a + 1) + (1 / 2 : ℚ) ^ (a + 1) = (1 / 2 : ℚ) ^ a := by
    rw [pow_add]; ring
  unfold stageTwoReq
  split_ifs with h0 h1 h1
  · exact absurd (h0.symm.trans h1) (by simp)
  · linarith
  · linarith
  · linarith

/-- The stage-two move is nonnegative at every node. -/
lemma getReq_stageTwoMove_nonneg {a D : ℕ} (h : a + 1 ≤ D) (j : Option ℕ) (x : GacsDayNode) :
    0 ≤ getReq (stageTwoMove a D j) x := by
  by_cases h0 : x = []
  · rw [h0, getReq_stageTwoMove_nil]; positivity
  by_cases h1 : x = [0]
  · rw [h1, getReq_stageTwoMove_zero]; exact stageTwoReq_nonneg h j 0
  by_cases h2 : x = [1]
  · rw [h2, getReq_stageTwoMove_one]; exact stageTwoReq_nonneg h j 1
  · rw [getReq_stageTwoMove_eq_zero h0 h1 h2]

end Kolmogorov
