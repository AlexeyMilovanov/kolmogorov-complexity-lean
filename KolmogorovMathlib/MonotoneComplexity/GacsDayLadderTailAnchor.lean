import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction

/-!
# Anchored tail reserves

`IsTailReserve` only records that the reserve `R` is *comparable* with some
cylinder allocated at its owner `x`.  The construction
`exists_tailReserve_of_serves` actually produces the strictly stronger
witness

```text
∃ v ∈ getAlloc m x, v <+: R
```

-- the reserve sits *inside* an already allocated cylinder -- and then throws
it away.  That witness is exactly what makes a reserve usable at a **later**
server time: allocations only grow along a legal play, so an allocated
ancestor of `R` at time `t` still has an allocated ancestor at every later
time `T`, and coherence at `T` then separates `R` from everything allocated at
an incomparable vertex or in another tree.  Without the anchor one only knows
that `R` meets *something* allocated at `x`, which gives no later-time
information at all.

This module adds the anchored predicate and the strengthened construction.
Nothing existing is weakened: `IsAnchoredTailReserve` projects onto
`IsTailReserve`, so every previously proved consumer still applies.
-/

namespace Kolmogorov

/-! ### Anchored reserves in a single tree -/

/-- A tail reserve together with the allocated cylinder it was carved out of.
`v <+: R` says the reserve is contained in space already allocated to `x`. -/
def IsAnchoredTailReserve (e b : ℕ) (A : Allocation) (m : ServerMove)
    (x : GacsDayNode) (R : BitString) : Prop :=
  IsTailReserve e b A m x R ∧ ∃ v ∈ getAlloc m x, v <+: R

/-- An anchored reserve is in particular a reserve. -/
theorem IsAnchoredTailReserve.toIsTailReserve {e b : ℕ} {A : Allocation}
    {m : ServerMove} {x : GacsDayNode} {R : BitString}
    (h : IsAnchoredTailReserve e b A m x R) : IsTailReserve e b A m x R := h.1

/-- An anchored reserve extends a string the server has allocated at the node. -/
theorem IsAnchoredTailReserve.anchor {e b : ℕ} {A : Allocation}
    {m : ServerMove} {x : GacsDayNode} {R : BitString}
    (h : IsAnchoredTailReserve e b A m x R) :
    ∃ v ∈ getAlloc m x, v <+: R := h.2

/-- **The anchored form of `exists_tailReserve_of_serves`.**  Serving a request
of size `2 ^ (-e)` produces an *anchored* epsilon-reserve. -/
theorem exists_anchoredTailReserve_of_serves
    {e b : ℕ} {A : Allocation} {m : ServerMove} {x : GacsDayNode}
    (hcoh : serverMoveCoherent b m)
    (hx : ∀ d ∈ x, d < b)
    (havoid : allocationAvoidsUnavailable A (getAlloc m x))
    (hserve : Serves (getAlloc m x) (dyadicScale e)) :
    ∃ R, IsAnchoredTailReserve e b A m x R := by
  obtain ⟨R, hR, v, hv, hvR⟩ :=
    exists_tailReserve_of_serves hcoh hx havoid hserve
  exact ⟨R, hR, v, hv, hvR⟩

/-- **Later-time spatial exclusion.**  An anchored reserve acquired at time `t`
is incomparable with every cylinder allocated at any later time `T` at a vertex
incomparable with its owner.

This is the fact `IsTailReserve` cannot supply: it needs the allocated ancestor
of `R`, which persists in time, rather than a merely comparable cell. -/
theorem IsAnchoredTailReserve.excludes_incomparable_later
    {e b t T : ℕ} {A : Allocation} {sm : ℕ → ServerMove}
    (hsm : serverPlayLegal b sm) (htT : t ≤ T)
    {x : GacsDayNode} (hx : ∀ d ∈ x, d < b)
    {R : BitString} (hR : IsAnchoredTailReserve e b A (sm t) x R)
    {y : GacsDayNode} (hy : ∀ d ∈ y, d < b)
    (hxy : ¬ (x <+: y ∨ y <+: x)) {c : BitString}
    (hc : c ∈ getAlloc (sm T) y) :
    ¬ (R <+: c ∨ c <+: R) := by
  intro hRc
  obtain ⟨v, hv, hvR⟩ := hR.2
  obtain ⟨w, hw, hwv⟩ := allocationSubset_mono_time hsm htT x v hv
  have hwR : w <+: R := hwv.trans hvR
  have hdisj := disjointAllocations_of_incomparable (hsm.1 T)
    (not_or.mp hxy).1 (not_or.mp hxy).2 hx hy
  exact hdisj w hw c hc
    (prefixComparable_of_prefix_of_prefixComparable hwR hRc)

/-! ### Anchored reserves in a family -/

/-- A family reserve together with its allocated anchor. -/
def IsAnchoredTailFamilyReserve (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) : Prop :=
  IsTailFamilyReserve e b A n i sm x R ∧
    ∃ v ∈ getFamilyAlloc sm i x, v <+: R

/-- An anchored family reserve is in particular a family reserve. -/
theorem IsAnchoredTailFamilyReserve.toIsTailFamilyReserve
    {e b n i : ℕ} {A : Allocation} {sm : FamilyServerMove}
    {x : GacsDayNode} {R : BitString}
    (h : IsAnchoredTailFamilyReserve e b A n i sm x R) :
    IsTailFamilyReserve e b A n i sm x R := h.1

/-- An anchored family reserve extends a string the server has allocated to that client at the
node. -/
theorem IsAnchoredTailFamilyReserve.anchor
    {e b n i : ℕ} {A : Allocation} {sm : FamilyServerMove}
    {x : GacsDayNode} {R : BitString}
    (h : IsAnchoredTailFamilyReserve e b A n i sm x R) :
    ∃ v ∈ getFamilyAlloc sm i x, v <+: R := h.2
/-! ### Executable anchored reserve search -/

/-- Decide whether some cylinder of `S` is an allocated ancestor of `R`. -/
def anchorsB (S : List BitString) (R : BitString) : Bool :=
  S.any fun v => v.isPrefixOf R

/-- The anchoring test holds exactly when some string of `S` is a prefix of `R`. -/
lemma anchorsB_eq_true_iff (S : List BitString) (R : BitString) :
    anchorsB S R = true ↔ ∃ v ∈ S, v <+: R := by
  simp [anchorsB, isPrefixOf_eq_decide]

/-- The Boolean test for an anchored family reserve. -/
def anchoredTailFamilyReserveAtB (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) : Bool :=
  tailFamilyReserveAtB e b A n i sm x R && anchorsB (getFamilyAlloc sm i x) R

/-- The decidable test for an anchored family reserve agrees with the predicate. -/
lemma anchoredTailFamilyReserveAtB_eq_true_iff
    (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) (R : BitString) :
    anchoredTailFamilyReserveAtB e b A n i sm x R = true ↔
      IsAnchoredTailFamilyReserve e b A n i sm x R := by
  rw [anchoredTailFamilyReserveAtB, Bool.and_eq_true,
    tailFamilyReserveAtB_eq_true_iff, anchorsB_eq_true_iff]
  rfl

/-- Search all length-`e` cylinders for an anchored family reserve. -/
def getAnchoredTailFamilyReserve (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) : Option BitString :=
  (allStrings e).find? (anchoredTailFamilyReserveAtB e b A n i sm x)

/-- The search returns an anchored family reserve exactly when one exists. -/
lemma getAnchoredTailFamilyReserve_isSome_iff
    (e b : ℕ) (A : Allocation) (n i : ℕ)
    (sm : FamilyServerMove) (x : GacsDayNode) :
    (getAnchoredTailFamilyReserve e b A n i sm x).isSome ↔
      ∃ R, IsAnchoredTailFamilyReserve e b A n i sm x R := by
  constructor
  · intro hs
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨R, (anchoredTailFamilyReserveAtB_eq_true_iff e b A n i sm x R).mp
      (List.find?_some hR)⟩
  · rintro ⟨R, hR⟩
    have hmem : R ∈ allStrings e := (mem_allStrings e R).mpr hR.1.1.1
    rcases hf : (allStrings e).find?
        (anchoredTailFamilyReserveAtB e b A n i sm x) with _ | S
    · have hfalse := List.find?_eq_none.mp hf R hmem
      rw [(anchoredTailFamilyReserveAtB_eq_true_iff
        e b A n i sm x R).mpr hR] at hfalse
      exact absurd rfl hfalse
    · simp [getAnchoredTailFamilyReserve, hf]

/-- Where an anchored family reserve is found, a plain family reserve is found too. -/
theorem getTailFamilyReserve_isSome_of_anchored
    {e b : ℕ} {A : Allocation} {n i : ℕ}
    {sm : FamilyServerMove} {x : GacsDayNode}
    (h : (getAnchoredTailFamilyReserve e b A n i sm x).isSome) :
    (getTailFamilyReserve e b A n i sm x).isSome := by
  obtain ⟨R, hR⟩ := (getAnchoredTailFamilyReserve_isSome_iff e b A n i sm x).mp h
  exact (getTailFamilyReserve_isSome_iff e b A n i sm x).mpr
    ⟨R, hR.toIsTailFamilyReserve⟩

/-- **The anchored form of `exists_tailFamilyReserve_of_serves`.** -/
theorem exists_anchoredTailFamilyReserve_of_serves
    {e b n i T : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    {x : GacsDayNode}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n)
    (hx : ∀ d ∈ x, d < b)
    (hserve : Serves (getFamilyAlloc (sm T) i x) (dyadicScale e)) :
    ∃ R, IsAnchoredTailFamilyReserve e b A n i (sm T) x R := by
  have hcoh := (hsm.1 i hi).1 T
  have havoid := hsm.2.2 T i hi x
  obtain ⟨R, hR, v, hv, hvR⟩ :=
    exists_tailReserve_of_serves hcoh hx havoid hserve
  refine ⟨R, ⟨hR, ?_⟩, v, hv, hvR⟩
  intro j hj hji c hc hcomp
  obtain ⟨u, hu, huv⟩ :=
    allocationSubset_getAlloc_root hcoh x hx v hv
  have hroot := hsm.2.1 T i hi j hj (Ne.symm hji)
  exact hroot u hu c hc
    (prefixComparable_of_prefix_of_prefixComparable (huv.trans hvR) hcomp)

/-- Later-time exclusion inside the owner's own tree. -/
theorem IsAnchoredTailFamilyReserve.excludes_incomparable_later
    {e b n i t T : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n) (htT : t ≤ T)
    {x : GacsDayNode} (hx : ∀ d ∈ x, d < b)
    {R : BitString}
    (hR : IsAnchoredTailFamilyReserve e b A n i (sm t) x R)
    {y : GacsDayNode} (hy : ∀ d ∈ y, d < b)
    (hxy : ¬ (x <+: y ∨ y <+: x)) {c : BitString}
    (hc : c ∈ getFamilyAlloc (sm T) i y) :
    ¬ (R <+: c ∨ c <+: R) :=
  IsAnchoredTailReserve.excludes_incomparable_later
    (sm := fun s => familyServerMoveAt (sm s) i) (hsm.1 i hi) htT hx
    ⟨hR.1.1, hR.2⟩ hy hxy hc

/-- Later-time exclusion against every *other* tree of the family. -/
theorem IsAnchoredTailFamilyReserve.excludes_other_tree_later
    {e b n i j t T : ℕ} {A : Allocation} {sm : ℕ → FamilyServerMove}
    (hsm : familyServerPlayLegal n b A sm) (hi : i < n) (hj : j < n)
    (hij : j ≠ i) (htT : t ≤ T)
    {x : GacsDayNode} (hx : ∀ d ∈ x, d < b)
    {R : BitString}
    (hR : IsAnchoredTailFamilyReserve e b A n i (sm t) x R)
    {c : BitString} (hc : c ∈ getFamilyAlloc (sm T) j []) :
    ¬ (R <+: c ∨ c <+: R) := by
  intro hRc
  obtain ⟨v, hv, hvR⟩ := hR.2
  obtain ⟨w, hw, hwv⟩ :=
    allocationSubset_mono_time (hsm.1 i hi) htT x v hv
  obtain ⟨u, hu, huw⟩ :=
    allocationSubset_getAlloc_root ((hsm.1 i hi).1 T) x hx w hw
  have huR : u <+: R := huw.trans (hwv.trans hvR)
  exact hsm.2.1 T i hi j hj (Ne.symm hij) u hu c hc
    (prefixComparable_of_prefix_of_prefixComparable huR hRc)

end Kolmogorov
