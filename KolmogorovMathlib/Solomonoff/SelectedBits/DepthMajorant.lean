import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation
import KolmogorovMathlib.Solomonoff.SelectedBits.Basic
import KolmogorovMathlib.Solomonoff.SelectedBits.Packing

/-!
# The finite-depth majorant and the antichain budget of the demands

Fix a prefix-closed set `T` of words, a gain family `G` and rational stages `Ms s x` that are
nonnegative, coherent over children and nondecreasing in `s` (`IsCoherentStages`).  At a node
`z` with next bit `b`, the stage ratio of the sibling `z (!b)` is `childRatio Ms s z b`; the
node contributes the factor `nodeFactor`, which is the gain at that ratio when the sibling
leaves `T` (a forced node) and `1` otherwise.  The *stage demand* of a word `x ∈ T` is

  `stageDemand G T Ms s x = Ms s x * ∏_{i < |x|} nodeFactor G T Ms s (x.take i) x[i]`,

and `0` outside `T`.  Stage demands need not increase with `s`.  The main result of this module
is the antichain budget `sum_iSup_stageDemand_le`: on every finite prefix-free set, the
suprema over the stages of the demands sum to at most `1` when every root stage is at most `1`.

The proof uses the *depth process* `depthProcess G T Ms d u`, built by recursion on the depth
budget `d` (blueprint node B30): the root coordinate is `Ms s u`; below two valid children it
places their processes; below a single valid child `v` with forbidden sibling `w` it places the
envelope process of the child's process with `a s = Ms s v`, `b s = Ms s w`.  Each
`depthProcess G T Ms d u s` is a raw flow from `u` (`isRawFlowFrom_depthProcess`) with root
exactly `Ms s u` (`depthProcess_root`), nondecreasing in `s` (`depthProcess_le_succ`), and it
dominates the products of the node factors between `u` and every word of `T` of length at most
`|u| + d` (`le_depthProcess`).  The finite-stage bound with witness times is
`sum_stageDemand_le_of_witness`.

The stages of the universal semimeasure are `qStage q s x = q s x / 2 ^ s` for a simple tree
approximation `q` (`isCoherentStages_qStage`, `qStage_root`).
-/

namespace Kolmogorov.SelectedBits

open scoped ENNReal

/-! ### Coherent rational stages -/

/-- Rational stages of a tree semimeasure: nonnegative, coherent over the two children, and
nondecreasing in the stage. -/
structure IsCoherentStages (Ms : ℕ → BitString → ℚ) : Prop where
  /-- Stage masses are nonnegative. -/
  nonneg : ∀ s x, 0 ≤ Ms s x
  /-- The two children together carry at most the stage mass of the parent. -/
  coherent : ∀ s x, Ms s (x ++ [false]) + Ms s (x ++ [true]) ≤ Ms s x
  /-- Stage masses do not decrease from one stage to the next. -/
  mono : ∀ s x, Ms s x ≤ Ms (s + 1) x

/-- Coherent stages are monotone in the stage. -/
theorem IsCoherentStages.monotone {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms)
    (x : BitString) : Monotone (fun s => Ms s x) :=
  monotone_nat_of_le_succ fun s => hMs.mono s x

/-! ### Stage ratios, node factors and stage demands -/

/-- The stage ratio of the sibling `z ++ [!b]` of the child `z ++ [b]`:
`Ms s (z (!b)) / (Ms s (z b) + Ms s (z (!b)))`, and `0` when both stage masses vanish. -/
def childRatio (Ms : ℕ → BitString → ℚ) (s : ℕ) (z : BitString) (b : Bool) : ℚ :=
  Ms s (z ++ [!b]) / (Ms s (z ++ [b]) + Ms s (z ++ [!b]))

/-- The real cast of the stage ratio is the sibling ratio of the real stage masses. -/
theorem cast_childRatio (Ms : ℕ → BitString → ℚ) (s : ℕ) (z : BitString) (b : Bool) :
    ((childRatio Ms s z b : ℚ) : ℝ) =
      ratioOf (Ms s (z ++ [b]) : ℝ) (Ms s (z ++ [!b]) : ℝ) := by
  simp [childRatio, ratioOf]

open Classical in
/-- The factor contributed by the node `z` on the way to the child `z ++ [b]`: the gain at the
stage ratio `childRatio Ms s z b` when the sibling `z ++ [!b]` is not in `T`, and `1`
otherwise. -/
noncomputable def nodeFactor (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ)
    (s : ℕ) (z : BitString) (b : Bool) : ℚ :=
  if z ++ [!b] ∈ T then 1 else G.gain s (childRatio Ms s z b)

/-- Every node factor is at least `1`. -/
theorem one_le_nodeFactor (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ)
    (s : ℕ) (z : BitString) (b : Bool) : 1 ≤ nodeFactor G T Ms s z b := by
  unfold nodeFactor
  split_ifs
  · exact le_rfl
  · exact G.one_le _ _

/-- The product of the node factors along `x` from the length of `u` on: the factors of the
prefixes `x.take i`, `u.length ≤ i < x.length`, each on the way to the next bit of `x`. -/
noncomputable def forcedGainProd (G : GainFamily) (T : Set BitString)
    (Ms : ℕ → BitString → ℚ) (s : ℕ) (u x : BitString) : ℚ :=
  ∏ i ∈ Finset.Ico u.length x.length, nodeFactor G T Ms s (x.take i) (x.getD i false)

/-- Every product of node factors is at least `1`. -/
theorem one_le_forcedGainProd (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ)
    (s : ℕ) (u x : BitString) : 1 ≤ forcedGainProd G T Ms s u x :=
  Finset.prod_induction _ (fun c => 1 ≤ c) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun _ _ => one_le_nodeFactor G T Ms s _ _

open Classical in
/-- The **stage demand** of a word: on `T`, its stage mass times the product of the node
factors of all its strict prefixes; `0` outside `T`. -/
noncomputable def stageDemand (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ)
    (s : ℕ) (x : BitString) : ℚ :=
  if x ∈ T then Ms s x * forcedGainProd G T Ms s [] x else 0

/-- Stage demands of nonnegative stages are nonnegative. -/
theorem stageDemand_nonneg (G : GainFamily) (T : Set BitString) {Ms : ℕ → BitString → ℚ}
    (hMs : ∀ s x, 0 ≤ Ms s x) (s : ℕ) (x : BitString) : 0 ≤ stageDemand G T Ms s x := by
  unfold stageDemand
  split_ifs
  · exact mul_nonneg (hMs s x) (zero_le_one.trans (one_le_forcedGainProd G T Ms s [] x))
  · exact le_rfl

/-! ### The depth process -/

open Classical in
/-- The **depth process** below the node `u` with depth budget `d`, at stage `s`.  Its root
coordinate is `Ms s u`.  With budget `0`, or when no child of `u` is in `T`, nothing else is
placed.  When both children are in `T`, their depth processes of budget `d` are placed below
them.  When exactly one child `v = u ++ [b]` is in `T`, the envelope process of the depth
process of `v` is placed below `v`, with the stage ratio `childRatio Ms t u b` and the absolute
length bound `u.length + (d + 1)`. -/
noncomputable def depthProcess (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ) :
    ℕ → BitString → ℕ → BitString → ℝ
  | 0, u => fun s y => if y = u then (Ms s u : ℝ) else 0
  | d + 1, u => fun s y =>
      if y = u then (Ms s u : ℝ)
      else if u ++ [false] ∈ T then
        if u ++ [true] ∈ T then
          (if u ++ [false] <+: y then depthProcess G T Ms d (u ++ [false]) s y
            else if u ++ [true] <+: y then depthProcess G T Ms d (u ++ [true]) s y else 0)
        else envelopeProcess G (depthProcess G T Ms d (u ++ [false]))
          (fun t => childRatio Ms t u false) (u ++ [false]) (u.length + (d + 1)) s y
      else if u ++ [true] ∈ T then
        envelopeProcess G (depthProcess G T Ms d (u ++ [true]))
          (fun t => childRatio Ms t u true) (u ++ [true]) (u.length + (d + 1)) s y
      else 0

/-- The root coordinate of the depth process is exactly the stage mass of the root. -/
theorem depthProcess_root (G : GainFamily) (T : Set BitString) (Ms : ℕ → BitString → ℚ)
    (d : ℕ) (u : BitString) (s : ℕ) : depthProcess G T Ms d u s u = Ms s u := by
  cases d <;> simp [depthProcess]

/-- The depth process of nonnegative stages is nonnegative. -/
theorem depthProcess_nonneg (G : GainFamily) (T : Set BitString) {Ms : ℕ → BitString → ℚ}
    (hMs : ∀ s x, 0 ≤ Ms s x) (d : ℕ) (u : BitString) (s : ℕ) (y : BitString) :
    0 ≤ depthProcess G T Ms d u s y := by
  induction d generalizing u s y with
  | zero =>
    simp only [depthProcess]
    split_ifs
    · exact_mod_cast hMs s u
    · exact le_rfl
  | succ d ih =>
    simp only [depthProcess]
    split_ifs
    all_goals first
      | exact_mod_cast hMs s u
      | exact ih _ _ _
      | exact truncatedEnvelope_nonneg
          (fun x => packedDemand_nonneg G (fun t z => ih _ t z) _ s x) _ _ y
      | exact le_rfl

/-- The depth process does not decrease from one stage to the next: the root uses
`IsCoherentStages.mono`, the one-child case `envelopeProcess_le_succ`. -/
theorem depthProcess_le_succ (G : GainFamily) (T : Set BitString) {Ms : ℕ → BitString → ℚ}
    (hMs : IsCoherentStages Ms) (d : ℕ) (u : BitString) (s : ℕ) (y : BitString) :
    depthProcess G T Ms d u s y ≤ depthProcess G T Ms d u (s + 1) y := by
  induction d generalizing u y with
  | zero =>
    simp only [depthProcess]
    split_ifs
    · exact_mod_cast hMs.mono s u
    · exact le_rfl
  | succ d ih =>
    simp only [depthProcess]
    split_ifs
    all_goals first
      | exact_mod_cast hMs.mono s u
      | exact ih _ _
      | exact envelopeProcess_le_succ _ _ _ _ _ _ _
      | exact le_rfl

/-- The depth process is monotone in the stage. -/
theorem depthProcess_mono (G : GainFamily) (T : Set BitString) {Ms : ℕ → BitString → ℚ}
    (hMs : IsCoherentStages Ms) (d : ℕ) (u : BitString) {s s' : ℕ} (hss : s ≤ s')
    (y : BitString) : depthProcess G T Ms d u s y ≤ depthProcess G T Ms d u s' y :=
  monotone_nat_of_le_succ (fun t => depthProcess_le_succ G T hMs d u t y) hss

/-! ### The depth process is a raw flow -/

/-- The envelope process below a child of `u` vanishes at the other child. -/
theorem envelopeProcess_sibling_eq_zero (G : GainFamily) (A : ℕ → BitString → ℝ) (r : ℕ → ℚ)
    (u : BitString) {b c : Bool} (hbc : b ≠ c) (D s : ℕ) :
    envelopeProcess G A r (u ++ [b]) D s (u ++ [c]) = 0 :=
  truncatedEnvelope_of_not fun h => hbc (eq_of_append_singleton_prefix h.1 List.prefix_rfl)

/-- The envelope process of nonnegative masses is coherent at every word `x` at least as long
as its root `v`: at the extensions of `v` it is a raw flow, and the children of the other such
words lie outside its domain. -/
theorem envelopeProcess_children_le (G : GainFamily) {A : ℕ → BitString → ℝ}
    (hA : ∀ t y, 0 ≤ A t y) (r : ℕ → ℚ) {v x : BitString} (D s : ℕ)
    (hvx : v.length ≤ x.length) :
    envelopeProcess G A r v D s (x ++ [false]) + envelopeProcess G A r v D s (x ++ [true]) ≤
      envelopeProcess G A r v D s x := by
  by_cases h : v <+: x
  · exact (isRawFlowFrom_envelopeProcess G hA r v D s).coherent x h
  · have hb : ∀ b : Bool, envelopeProcess G A r v D s (x ++ [b]) = 0 := fun b =>
      truncatedEnvelope_of_not fun h' =>
        h (List.prefix_of_prefix_length_le h'.1 (List.prefix_append x [b]) hvx)
    rw [hb false, hb true, add_zero]
    exact (isRawFlowFrom_envelopeProcess G hA r v D s).nonneg x

/-- The root bound of the envelope process placed below a single valid child `u ++ [b]`: it is
at most the stage masses of the two children (`envelopeProcess_root_le` for the child process,
with the stage masses of the sibling as forbidden masses). -/
theorem envelopeProcess_depthProcess_root_le (G : GainFamily) (T : Set BitString)
    {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms) (d : ℕ) (u : BitString) (b : Bool)
    (hflow : ∀ t, IsRawFlowFrom (u ++ [b]) (depthProcess G T Ms d (u ++ [b]) t)) (D s : ℕ) :
    envelopeProcess G (depthProcess G T Ms d (u ++ [b])) (fun t => childRatio Ms t u b)
        (u ++ [b]) D s (u ++ [b]) ≤ (Ms s (u ++ [b]) : ℝ) + (Ms s (u ++ [!b]) : ℝ) := by
  have h := envelopeProcess_root_le G (A := depthProcess G T Ms d (u ++ [b]))
    (b := fun t => (Ms t (u ++ [!b]) : ℝ)) (r := fun t => childRatio Ms t u b) hflow
    (depthProcess_le_succ G T hMs d (u ++ [b]))
    (fun t t' htt => Rat.cast_le.mpr (hMs.monotone _ htt))
    (fun t => Rat.cast_nonneg.mpr (hMs.nonneg t _))
    (fun t => by rw [cast_childRatio, depthProcess_root]) D s
  rwa [depthProcess_root] at h

/-- Coherence of the depth process of budget `d + 1` at its root `u`: the two children carry at
most `Ms s u`, given that the depth processes of budget `d` are raw flows. -/
theorem depthProcess_succ_children_le_root (G : GainFamily) (T : Set BitString)
    {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms) (d : ℕ) (u : BitString) (s : ℕ)
    (ih : ∀ v t, IsRawFlowFrom v (depthProcess G T Ms d v t)) :
    depthProcess G T Ms (d + 1) u s (u ++ [false]) +
        depthProcess G T Ms (d + 1) u s (u ++ [true]) ≤ depthProcess G T Ms (d + 1) u s u := by
  have hne : ∀ b : Bool, u ++ [b] ≠ u := fun b h => by simpa using congrArg List.length h
  have hcoh : (Ms s (u ++ [false]) : ℝ) + (Ms s (u ++ [true]) : ℝ) ≤ (Ms s u : ℝ) := by
    exact_mod_cast hMs.coherent s u
  have hnp : ¬ u ++ [false] <+: u ++ [true] := fun h =>
    Bool.false_ne_true (eq_of_append_singleton_prefix h List.prefix_rfl)
  rw [depthProcess_root]
  by_cases h0 : u ++ [false] ∈ T <;> by_cases h1 : u ++ [true] ∈ T
  · simp only [depthProcess, hne, h0, h1, hnp, List.prefix_refl, ↓reduceIte, depthProcess_root]
    exact hcoh
  · simp only [depthProcess, hne, h0, h1, ↓reduceIte]
    rw [envelopeProcess_sibling_eq_zero G _ _ u Bool.false_ne_true, add_zero]
    exact (envelopeProcess_depthProcess_root_le G T hMs d u false (ih _) _ s).trans hcoh
  · simp only [depthProcess, hne, h0, h1, ↓reduceIte]
    rw [envelopeProcess_sibling_eq_zero G _ _ u (by decide : true ≠ false), zero_add]
    exact (envelopeProcess_depthProcess_root_le G T hMs d u true (ih _) _ s).trans
      (by rw [add_comm]; exact hcoh)
  · simp only [depthProcess, hne, h0, h1, ↓reduceIte, add_zero]
    exact Rat.cast_nonneg.mpr (hMs.nonneg s u)

/-- Coherence of the depth process of budget `d + 1` at a strict extension `x` of its root: the
values come from the process of a valid child, from the envelope process below the single valid
child, or vanish. -/
theorem depthProcess_succ_children_le_of_ne (G : GainFamily) (T : Set BitString)
    {Ms : ℕ → BitString → ℚ} (d : ℕ) (u : BitString) (s : ℕ)
    (ih : ∀ v t, IsRawFlowFrom v (depthProcess G T Ms d v t)) {x : BitString}
    (hux : u <+: x) (hxu : x ≠ u) :
    depthProcess G T Ms (d + 1) u s (x ++ [false]) +
        depthProcess G T Ms (d + 1) u s (x ++ [true]) ≤ depthProcess G T Ms (d + 1) u s x := by
  obtain ⟨c, hc⟩ := exists_child_prefix_of_prefix_of_ne hux (Ne.symm hxu)
  have hlen : u.length + 1 ≤ x.length := by simpa using hc.length_le
  have hne : ∀ b : Bool, x ++ [b] ≠ u := fun b h => by
    have := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at this
    omega
  have hcb : ∀ b : Bool, u ++ [c] <+: x ++ [b] := fun b => hc.trans (List.prefix_append x [b])
  have hA : ∀ v t y, 0 ≤ depthProcess G T Ms d v t y := fun v t y => (ih v t).nonneg y
  by_cases h0 : u ++ [false] ∈ T <;> by_cases h1 : u ++ [true] ∈ T
  · simp only [depthProcess, hne, hxu, h0, h1, ↓reduceIte]
    cases c
    · simp only [hc, hcb, ↓reduceIte]
      exact (ih _ s).coherent x hc
    · have hn : ∀ y, u ++ [true] <+: y → ¬ u ++ [false] <+: y := fun y h h' =>
        Bool.false_ne_true (eq_of_append_singleton_prefix h' h)
      simp only [hc, hcb, hn x hc, hn _ (hcb false), hn _ (hcb true), ↓reduceIte]
      exact (ih _ s).coherent x hc
  · simp only [depthProcess, hne, hxu, h0, h1, ↓reduceIte]
    exact envelopeProcess_children_le G (hA _) _ _ _ (by simpa using hlen)
  · simp only [depthProcess, hne, hxu, h0, h1, ↓reduceIte]
    exact envelopeProcess_children_le G (hA _) _ _ _ (by simpa using hlen)
  · simp only [depthProcess, hne, hxu, h0, h1, ↓reduceIte, add_zero, le_refl]

/-- **The depth process is a raw flow from its root.**  By induction on `d`: at the root `u`
the children carry at most `Ms s u` (`depthProcess_succ_children_le_root`: coherence of the
stages, and `envelopeProcess_root_le` below a single valid child); at a strict extension of `u`
the values come from the process of a valid child, from the envelope process
(`isRawFlowFrom_envelopeProcess`) or vanish (`depthProcess_succ_children_le_of_ne`). -/
theorem isRawFlowFrom_depthProcess (G : GainFamily) (T : Set BitString)
    {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms) (d : ℕ) (u : BitString) (s : ℕ) :
    IsRawFlowFrom u (depthProcess G T Ms d u s) := by
  induction d generalizing u s with
  | zero =>
    refine ⟨depthProcess_nonneg G T hMs.nonneg 0 u s, fun x hux => ?_⟩
    have hb : ∀ b : Bool, depthProcess G T Ms 0 u s (x ++ [b]) = 0 := fun b => by
      have hne : x ++ [b] ≠ u := fun h => by
        have := congrArg List.length h
        have := hux.length_le
        simp only [List.length_append, List.length_singleton] at *
        omega
      simp [depthProcess, hne]
    rw [hb false, hb true, add_zero]
    exact depthProcess_nonneg G T hMs.nonneg 0 u s x
  | succ d ih =>
    refine ⟨depthProcess_nonneg G T hMs.nonneg (d + 1) u s, fun x hux => ?_⟩
    rcases eq_or_ne x u with rfl | hxu
    · exact depthProcess_succ_children_le_root G T hMs d _ s ih
    · exact depthProcess_succ_children_le_of_ne G T d u s ih hux hxu

/-! ### Domination of the forced products -/

/-- Splitting off the first node factor: if the child `u ++ [b]` is a prefix of `x`, the product
of the node factors along `x` from `u` is the factor of `u` towards `b` times the product from
`u ++ [b]`. -/
theorem forcedGainProd_eq_nodeFactor_mul (G : GainFamily) (T : Set BitString)
    (Ms : ℕ → BitString → ℚ) (s : ℕ) {u x : BitString} {b : Bool} (hc : u ++ [b] <+: x) :
    forcedGainProd G T Ms s u x =
      nodeFactor G T Ms s u b * forcedGainProd G T Ms s (u ++ [b]) x := by
  have hlen : u.length < x.length := by
    have := hc.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  have htake : x.take u.length = u :=
    (List.prefix_iff_eq_take.mp ((List.prefix_append u [b]).trans hc)).symm
  have hget : x.getD u.length false = b := by
    obtain ⟨t, rfl⟩ := hc
    simp
  unfold forcedGainProd
  rw [Finset.prod_eq_prod_Ico_succ_bot hlen, htake, hget, List.length_append,
    List.length_singleton]

/-- One step of the domination: if the child `u ++ [b]` of `u ≠ x` is a prefix of `x ∈ T`, a
lower bound `Ms s x * P` for the depth process of budget `d` of the child at `x` gives the lower
bound `Ms s x * (nodeFactor G T Ms s u b * P)` for the depth process of budget `d + 1` of `u`.
With two valid children the factor is `1` and the child process is placed below the child;
with a single valid child the factor is the gain at `childRatio Ms s u b`, and
`gain_mul_le_envelopeProcess` applies. -/
theorem nodeFactor_mul_le_depthProcess_succ (G : GainFamily) {T : Set BitString}
    (hT : PrefixClosed T) (Ms : ℕ → BitString → ℚ) (d : ℕ) (u : BitString) (s : ℕ)
    {x : BitString} (hx : x ∈ T) {b : Bool} (hc : u ++ [b] <+: x) (hxu : x ≠ u)
    (hlen : x.length ≤ u.length + (d + 1)) (P : ℚ)
    (hP : ((Ms s x * P : ℚ) : ℝ) ≤ depthProcess G T Ms d (u ++ [b]) s x) :
    ((Ms s x * (nodeFactor G T Ms s u b * P) : ℚ) : ℝ) ≤ depthProcess G T Ms (d + 1) u s x := by
  have hcT : u ++ [b] ∈ T := hT hc hx
  have hgain : ∀ c : Bool, (G.gain s (childRatio Ms s u c) : ℝ) * ((Ms s x * P : ℚ) : ℝ) ≤
      (G.gain s (childRatio Ms s u c) : ℝ) * depthProcess G T Ms d (u ++ [b]) s x :=
    fun c => mul_le_mul_of_nonneg_left hP (G.gain_cast_pos _ _).le
  have hcast : ∀ g : ℚ, ((Ms s x * (g * P) : ℚ) : ℝ) = (g : ℝ) * ((Ms s x * P : ℚ) : ℝ) :=
    fun g => by push_cast; ring
  cases b with
  | false =>
    by_cases h1 : u ++ [true] ∈ T
    · have hnf : nodeFactor G T Ms s u false = 1 := by simp [nodeFactor, h1]
      simp only [depthProcess, hxu, hcT, h1, hc, ↓reduceIte, hnf, one_mul]
      exact hP
    · have hnf : nodeFactor G T Ms s u false = G.gain s (childRatio Ms s u false) := by
        simp [nodeFactor, h1]
      simp only [depthProcess, hxu, hcT, h1, ↓reduceIte, hnf]
      rw [hcast]
      exact (hgain false).trans (gain_mul_le_envelopeProcess G
        (depthProcess G T Ms d (u ++ [false])) (fun t => childRatio Ms t u false) s hc hlen)
  | true =>
    by_cases h0 : u ++ [false] ∈ T
    · have hnf : nodeFactor G T Ms s u true = 1 := by simp [nodeFactor, h0]
      have hn0 : ¬ u ++ [false] <+: x := fun h =>
        Bool.false_ne_true (eq_of_append_singleton_prefix h hc)
      simp only [depthProcess, hxu, hcT, h0, hn0, hc, ↓reduceIte, hnf, one_mul]
      exact hP
    · have hnf : nodeFactor G T Ms s u true = G.gain s (childRatio Ms s u true) := by
        simp [nodeFactor, h0]
      simp only [depthProcess, hxu, hcT, h0, ↓reduceIte, hnf]
      rw [hcast]
      exact (hgain true).trans (gain_mul_le_envelopeProcess G
        (depthProcess G T Ms d (u ++ [true])) (fun t => childRatio Ms t u true) s hc hlen)

/-- **Domination of the forced products.**  For a prefix-closed `T`, every word `x ∈ T`
extending `u` with `x.length ≤ u.length + d` satisfies
`Ms s x * forcedGainProd G T Ms s u x ≤ depthProcess G T Ms d u s x`.  By induction on `d`:
for `x = u` the product is empty; otherwise the child `u ++ [b]` on the way to `x` is a prefix
of `x`, the first node factor splits off (`forcedGainProd_eq_nodeFactor_mul`) and
`nodeFactor_mul_le_depthProcess_succ` applies to the induction hypothesis at the child. -/
theorem le_depthProcess (G : GainFamily) {T : Set BitString} (hT : PrefixClosed T)
    (Ms : ℕ → BitString → ℚ) (d : ℕ) (u : BitString) (s : ℕ) {x : BitString} (hx : x ∈ T)
    (hux : u <+: x) (hlen : x.length ≤ u.length + d) :
    ((Ms s x * forcedGainProd G T Ms s u x : ℚ) : ℝ) ≤ depthProcess G T Ms d u s x := by
  induction d generalizing u with
  | zero =>
    obtain rfl : u = x := hux.eq_of_length (by have := hux.length_le; omega)
    simp [forcedGainProd, depthProcess_root]
  | succ d ih =>
    rcases eq_or_ne x u with rfl | hxu
    · simp [forcedGainProd, depthProcess_root]
    · obtain ⟨b, hc⟩ := exists_child_prefix_of_prefix_of_ne hux (Ne.symm hxu)
      have hlen' : x.length ≤ (u ++ [b]).length + d := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [forcedGainProd_eq_nodeFactor_mul G T Ms s hc]
      exact nodeFactor_mul_le_depthProcess_succ G hT Ms d u s hx hc hxu hlen _
        (ih (u ++ [b]) hc hlen')

/-! ### The antichain budget of the stage demands -/

/-- **The finite-stage antichain budget with witness times.**  For a prefix-closed `T`,
coherent stages, a finite prefix-free set `S` and witness times `τ x ≤ s`, the stage demands
`stageDemand G T Ms (τ x) x` sum to at most `Ms s []`: with `D` the largest length in `S`,
each demand is at most `depthProcess G T Ms D [] s x`, and the antichain bound of this raw flow
concludes. -/
theorem sum_stageDemand_le_of_witness (G : GainFamily) {T : Set BitString}
    (hT : PrefixClosed T) {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms) (s : ℕ)
    (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) (τ : BitString → ℕ)
    (hτ : ∀ x ∈ S, τ x ≤ s) :
    ∑ x ∈ S, (stageDemand G T Ms (τ x) x : ℝ) ≤ Ms s [] := by
  have hflow := isRawFlowFrom_depthProcess G T hMs (S.sup List.length) [] s
  have hlen : ∀ x ∈ S, x.length ≤ ([] : BitString).length + S.sup List.length := fun x hx => by
    simpa using Finset.le_sup (f := List.length) hx
  calc ∑ x ∈ S, (stageDemand G T Ms (τ x) x : ℝ)
      ≤ ∑ x ∈ S, depthProcess G T Ms (S.sup List.length) [] s x := by
        refine Finset.sum_le_sum fun x hx => ?_
        unfold stageDemand
        split_ifs with hxT
        · exact (le_depthProcess G hT Ms _ [] (τ x) hxT List.nil_prefix (hlen x hx)).trans
            (depthProcess_mono G T hMs _ [] (hτ x hx) x)
        · simpa using hflow.nonneg x
    _ ≤ depthProcess G T Ms (S.sup List.length) [] s [] :=
        hflow.sum_antichain_le S (fun x _ => List.nil_prefix) hS
    _ = Ms s [] := depthProcess_root G T Ms _ [] s

/-- **The antichain budget of the demands.**  For a prefix-closed `T` and coherent stages with
root stages at most `1`, the suprema over the stages of the stage demands sum to at most `1`
over every finite prefix-free set: the running maxima of the demands have the same suprema and
are monotone, so the finite sum and the supremum commute, and at each stage the maximizing
times are witness times for `sum_stageDemand_le_of_witness`. -/
theorem sum_iSup_stageDemand_le (G : GainFamily) {T : Set BitString} (hT : PrefixClosed T)
    {Ms : ℕ → BitString → ℚ} (hMs : IsCoherentStages Ms) (hroot : ∀ s, Ms s [] ≤ 1)
    (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ x ∈ S, ⨆ s, ENNReal.ofReal (stageDemand G T Ms s x : ℝ) ≤ 1 := by
  let g : BitString → ℕ → ℝ≥0∞ := fun x s =>
    (Finset.range (s + 1)).sup fun t => ENNReal.ofReal (stageDemand G T Ms t x : ℝ)
  have hg_mono : ∀ x, Monotone (g x) := fun x s s' hss =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hsup : ∀ x, ⨆ s, ENNReal.ofReal (stageDemand G T Ms s x : ℝ) = ⨆ s, g x s := by
    intro x
    apply le_antisymm
    · exact iSup_mono fun s => Finset.le_sup (f := fun t => ENNReal.ofReal
        (stageDemand G T Ms t x : ℝ)) (Finset.self_mem_range_succ s)
    · exact iSup_le fun s => Finset.sup_le fun t _ =>
        le_iSup (fun s => ENNReal.ofReal (stageDemand G T Ms s x : ℝ)) t
  simp_rw [hsup]
  rw [ENNReal.finsetSum_iSup_of_monotone hg_mono]
  refine iSup_le fun s => ?_
  have hex : ∀ x, ∃ t ≤ s, g x s = ENNReal.ofReal (stageDemand G T Ms t x : ℝ) := by
    intro x
    obtain ⟨t, ht, h⟩ := Finset.exists_mem_eq_sup (Finset.range (s + 1))
      Finset.nonempty_range_add_one fun t => ENNReal.ofReal (stageDemand G T Ms t x : ℝ)
    exact ⟨t, Nat.lt_succ_iff.mp (Finset.mem_range.mp ht), h⟩
  choose τ hτs hτ using hex
  calc ∑ x ∈ S, g x s = ∑ x ∈ S, ENNReal.ofReal (stageDemand G T Ms (τ x) x : ℝ) :=
        Finset.sum_congr rfl fun x _ => hτ x
    _ = ENNReal.ofReal (∑ x ∈ S, (stageDemand G T Ms (τ x) x : ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg fun x _ => by
          exact_mod_cast stageDemand_nonneg G T hMs.nonneg _ x).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal
        ((sum_stageDemand_le_of_witness G hT hMs s S hS τ fun x _ => hτs x).trans
          (by exact_mod_cast hroot s))
    _ = 1 := ENNReal.ofReal_one

/-! ### The stages of a simple tree approximation -/

/-- The rational stage `q s x / 2 ^ s` of a numerator approximation `q`. -/
def qStage (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : ℚ := (q s x : ℚ) / 2 ^ s

/-- The real cast of a rational stage is the real value of its dyadic value. -/
theorem cast_qStage (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) :
    ((qStage q s x : ℚ) : ℝ) = (dyadicValue (q s x) s).toReal := by
  simp [qStage, dyadicValue, ENNReal.toReal_div]

/-- Rational stages are nonnegative. -/
theorem qStage_nonneg (q : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : 0 ≤ qStage q s x := by
  unfold qStage
  positivity

/-- The root stage of a simple tree approximation is `1`. -/
theorem qStage_root {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) (s : ℕ) : qStage q s [] = 1 := by
  rw [qStage, hq.1 s]
  push_cast
  exact div_self (pow_ne_zero _ two_ne_zero)

/-- The rational stages of a simple tree approximation are coherent. -/
theorem isCoherentStages_qStage {a : BitString → ℝ≥0∞} {q : ℕ → BitString → ℕ}
    (hq : IsSimpleTreeApproximation a q) : IsCoherentStages (qStage q) := by
  refine ⟨qStage_nonneg q, fun s x => ?_, fun s x => ?_⟩
  · unfold qStage
    rw [← add_div]
    gcongr
    exact_mod_cast hq.2.1 s x
  · have h1 : ((qStage q s x : ℚ) : ℝ) ≤ ((qStage q (s + 1) x : ℚ) : ℝ) := by
      rw [cast_qStage, cast_qStage]
      exact ENNReal.toReal_mono (dyadicValue_lt_top _ _).ne (hq.2.2.2.1 s x)
    exact_mod_cast h1

end Kolmogorov.SelectedBits
