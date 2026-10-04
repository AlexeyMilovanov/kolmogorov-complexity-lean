import KolmogorovMathlib.MonotoneComplexity.APrioriSublevelMaxNodes
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.NestedAllocation
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Greedy address state

The state of the greedy address assignment for a priori sublevel sets: a finite list of
`(address, node)` pairs together with its basic accessors.
-/

namespace Kolmogorov

/-! ## The state of the construction -/

/-- The state of the greedy address assignment: a finite list of `(address, node)` pairs. -/
abbrev AddrList := List (BitString × BitString)

/-- The nodes recorded in a state. -/
def addrNodes (R : AddrList) : List BitString := R.map Prod.snd

/-- The addresses in use in a state. -/
def addrUsed (R : AddrList) : List BitString := R.map Prod.fst

/-- The addresses assigned to the node `y`. -/
def addrsAt (R : AddrList) (y : BitString) : List BitString :=
  (R.filter (fun q => decide (q.2 = y))).map Prod.fst

/-- The set of nodes of a state, together with the root. -/
def addrNodesFinset (R : AddrList) : Finset BitString :=
  insert [] (addrNodes R).toFinset

/-- Boolean prefix test. -/
def isPrefixB (y z : BitString) : Bool := z.take y.length == y

/-- `y` is currently a leaf: no recorded node strictly extends it. -/
def isLeafIn (R : AddrList) (y : BitString) : Bool :=
  !(addrNodes R).any (fun z => isPrefixB y z && !(z == y))

/-- The first address of length `k` that is not yet in use. -/
def freshAddr (k : ℕ) (R : AddrList) : BitString :=
  ((exactLengthPrograms k).filter (fun p => decide (p ∉ addrUsed R))).headD
    (List.replicate k false)

/-- The nonempty prefixes of `x`, shortest first. -/
def branchPrefixes (x : BitString) : List BitString :=
  (List.range x.length).map (fun i => x.take (i + 1))

/-- One step of the greedy construction: record the node `x`. -/
def insertNode (k : ℕ) (R : AddrList) (x : BitString) : AddrList :=
  bif (decide (x = []) || decide (x ∈ addrNodes R)) then R
  else bif (!decide (x.dropLast = []) && isLeafIn R x.dropLast) then
    ((addrsAt R x.dropLast).headD (freshAddr k R), x) :: R
  else (branchPrefixes x).map (fun z => (freshAddr k R, z)) ++ R

/-- Record the whole branch ending at `x`, shortest prefix first. -/
def insertBranch (k : ℕ) (R : AddrList) (x : BitString) : AddrList :=
  (branchPrefixes x).foldl (insertNode k) R

/-- The invariant maintained by the greedy construction. -/
structure GreedyInv (k : ℕ) (R : AddrList) : Prop where
  /-- Every address has length `k`. -/
  len : ∀ p x, (p, x) ∈ R → p.length = k
  /-- The root is never assigned an address. -/
  ne_nil : ∀ p x, (p, x) ∈ R → x ≠ []
  /-- All recorded nodes lie in the sublevel tree. -/
  mem_sub : ∀ p x, (p, x) ∈ R → x ∈ kaSublevel k
  /-- Addresses propagate to nonempty prefixes. -/
  lower : ∀ p x z, (p, x) ∈ R → z <+: x → z ≠ [] → (p, z) ∈ R
  /-- The nodes with a given address form a chain. -/
  chain : ∀ p x y, (p, x) ∈ R → (p, y) ∈ R → x <+: y ∨ y <+: x
  /-- At most one address per current leaf is in use. -/
  bound : (addrUsed R).toFinset.card ≤ (maxNodes (addrNodesFinset R)).card

/-! ## Basic facts about the state -/

/-- A node is recorded exactly when some address is assigned to it. -/
theorem mem_addrNodes {R : AddrList} {x : BitString} :
    x ∈ addrNodes R ↔ ∃ p, (p, x) ∈ R := by
  simp only [addrNodes, List.mem_map, Prod.exists]
  exact ⟨fun ⟨p, y, hmem, hy⟩ => ⟨p, hy ▸ hmem⟩, fun ⟨p, hmem⟩ => ⟨p, x, hmem, rfl⟩⟩

/-- An address is in use exactly when it is assigned to some node. -/
theorem mem_addrUsed {R : AddrList} {p : BitString} :
    p ∈ addrUsed R ↔ ∃ x, (p, x) ∈ R := by
  simp only [addrUsed, List.mem_map, Prod.exists]
  exact ⟨fun ⟨a, b, hmem, ha⟩ => ⟨b, ha ▸ hmem⟩, fun ⟨x, hmem⟩ => ⟨p, x, hmem, rfl⟩⟩

/-- The addresses listed at a node are exactly the addresses assigned to it. -/
theorem mem_addrsAt {R : AddrList} {y p : BitString} :
    p ∈ addrsAt R y ↔ (p, y) ∈ R := by
  simp only [addrsAt, List.mem_map, List.mem_filter, Prod.exists, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, ⟨hmem, rfl⟩, rfl⟩; exact hmem
  · intro hmem; exact ⟨p, y, ⟨hmem, rfl⟩, rfl⟩

/-- The node set of a state consists of the root and the recorded nodes. -/
theorem mem_addrNodesFinset {R : AddrList} {z : BitString} :
    z ∈ addrNodesFinset R ↔ z = [] ∨ ∃ p, (p, z) ∈ R := by
  simp only [addrNodesFinset, Finset.mem_insert, List.mem_toFinset, mem_addrNodes]

/-- Recording one more pair inserts its node into the node set. -/
theorem addrNodesFinset_cons (q x : BitString) (R : AddrList) :
    addrNodesFinset ((q, x) :: R) = insert x (addrNodesFinset R) := by
  classical
  ext z
  simp only [mem_addrNodesFinset, Finset.mem_insert, List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro (rfl | ⟨p, hp | hp⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hp.2
    · exact Or.inr (Or.inr ⟨p, hp⟩)
  · rintro (rfl | rfl | ⟨p, hp⟩)
    · exact Or.inr ⟨q, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨p, Or.inr hp⟩

/-- The maximal nodes of a set are its elements with no proper extension in the set. -/
theorem maxNodes_mem_iff {S : Finset BitString} {y : BitString} :
    y ∈ maxNodes S ↔ y ∈ S ∧ ∀ z ∈ S, y <+: z → y = z := by
  classical
  simp [maxNodes, Finset.mem_filter]

/-- The boolean prefix test decides the prefix relation. -/
theorem isPrefixB_iff {y z : BitString} : isPrefixB y z = true ↔ y <+: z := by
  simp only [isPrefixB, beq_iff_eq]
  exact ⟨fun h => List.prefix_iff_eq_take.mpr h.symm, fun h => (List.prefix_iff_eq_take.mp h).symm⟩

/-- The leaf test fires exactly when no recorded node properly extends the given one. -/
theorem isLeafIn_iff {R : AddrList} {y : BitString} :
    isLeafIn R y = true ↔ ∀ z ∈ addrNodes R, y <+: z → z = y := by
  unfold isLeafIn
  rw [Bool.not_eq_true', List.any_eq_false]
  constructor
  · intro h z hz hyz
    by_contra hne
    exact h z hz (by simp [isPrefixB_iff.mpr hyz, hne])
  · intro h z hz hcon
    rw [Bool.and_eq_true] at hcon
    have h1 := isPrefixB_iff.mp hcon.1
    have h2 : z ≠ y := by simpa using hcon.2
    exact h2 (h z hz h1)

/-- The branch of `x` consists of its nonempty prefixes. -/
theorem mem_branchPrefixes {x z : BitString} :
    z ∈ branchPrefixes x ↔ z <+: x ∧ z ≠ [] := by
  simp only [branchPrefixes, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨List.take_prefix _ _, ?_⟩
    intro hnil
    have hlen : (x.take (i + 1)).length = 0 := by rw [hnil]; rfl
    rw [List.length_take] at hlen
    omega
  · rintro ⟨hz, hne⟩
    refine ⟨z.length - 1, ?_, ?_⟩
    · have h1 : z.length ≤ x.length := hz.length_le
      have h2 : 0 < z.length := List.length_pos_iff.mpr hne
      omega
    · have h2 : 0 < z.length := List.length_pos_iff.mpr hne
      have h3 : z.length - 1 + 1 = z.length := by omega
      rw [h3]
      exact (List.prefix_iff_eq_take.mp hz).symm

/-- A fresh address has the prescribed length. -/
theorem freshAddr_length (k : ℕ) (R : AddrList) : (freshAddr k R).length = k := by
  unfold freshAddr
  cases h : ((exactLengthPrograms k).filter (fun p => decide (p ∉ addrUsed R))) with
  | nil => simp
  | cons a t =>
    have ha : a ∈ (exactLengthPrograms k).filter (fun p => decide (p ∉ addrUsed R)) := by
      rw [h]; exact List.mem_cons_self ..
    simpa using exactLengthPrograms_length_eq k a (List.mem_of_mem_filter ha)

/-- As long as fewer than `2 ^ k` addresses are in use, the fresh address is genuinely unused. -/
theorem freshAddr_not_mem {k : ℕ} {R : AddrList}
    (hcard : (addrUsed R).toFinset.card < 2 ^ k) : freshAddr k R ∉ addrUsed R := by
  classical
  unfold freshAddr
  cases h : ((exactLengthPrograms k).filter (fun p => decide (p ∉ addrUsed R))) with
  | nil =>
    exfalso
    have hsub : (exactLengthPrograms k).toFinset ⊆ (addrUsed R).toFinset := by
      intro p hp
      rw [List.mem_toFinset] at hp ⊢
      by_contra hpu
      have hmem : p ∈ (exactLengthPrograms k).filter (fun q => decide (q ∉ addrUsed R)) :=
        List.mem_filter.mpr ⟨hp, by simpa using hpu⟩
      rw [h] at hmem
      exact absurd hmem List.not_mem_nil
    have h1 : (exactLengthPrograms k).toFinset.card = 2 ^ k := by
      rw [List.toFinset_card_of_nodup (exactLengthPrograms_nodup k), length_exactLengthPrograms]
    have h2 := Finset.card_le_card hsub
    omega
  | cons a t =>
    have ha : a ∈ (exactLengthPrograms k).filter (fun p => decide (p ∉ addrUsed R)) := by
      rw [h]; exact List.mem_cons_self ..
    simpa using List.of_mem_filter ha

/-- A proper prefix of `x` is a prefix of `x` without its last bit. -/
theorem dropLast_prefix_of_prefix_ne {z x : BitString} (hz : z <+: x) (hne : z ≠ x) :
    z <+: x.dropLast := by
  have hlt : z.length < x.length :=
    lt_of_le_of_ne hz.length_le (fun hh => hne (hz.eq_of_length hh))
  refine prefix_of_prefix_of_length_le hz (List.dropLast_prefix x) ?_
  rw [List.length_dropLast]
  omega

/-- Under the greedy invariant, the node set is prefix-closed. -/
theorem addrNodesFinset_prefixClosed {k : ℕ} {R : AddrList} (h : GreedyInv k R) :
    ∀ a b, a <+: b → b ∈ addrNodesFinset R → a ∈ addrNodesFinset R := by
  intro a b hab hb
  rcases mem_addrNodesFinset.mp hb with rfl | ⟨p, hp⟩
  · rw [List.prefix_nil.mp hab]
    exact mem_addrNodesFinset.mpr (Or.inl rfl)
  · by_cases hnil : a = []
    · exact mem_addrNodesFinset.mpr (Or.inl hnil)
    · exact mem_addrNodesFinset.mpr (Or.inr ⟨p, h.lower _ _ _ hp hab hnil⟩)

/-- Under the greedy invariant, every node lies in the sublevel tree. -/
theorem addrNodesFinset_subset_kaSublevel {k : ℕ} {R : AddrList} (h : GreedyInv k R)
    (hnil : [] ∈ kaSublevel k) : ∀ z ∈ addrNodesFinset R, z ∈ kaSublevel k := by
  intro z hz
  rcases mem_addrNodesFinset.mp hz with rfl | ⟨p, hp⟩
  · exact hnil
  · exact h.mem_sub _ _ hp

/-! ## Preservation of the invariant: reusing the address of a leaf -/

/-- Recording a new node `x` whose immediate predecessor is currently a leaf, by reusing one of
the predecessor's addresses, preserves the invariant. -/
theorem greedyInv_cons_reuse {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x p : BitString}
    (hxne : x ≠ []) (hxnot : x ∉ addrNodes R) (hx : x ∈ kaSublevel k)
    (hy : (p, x.dropLast) ∈ R) (hleaf : isLeafIn R x.dropLast = true) :
    GreedyInv k ((p, x) :: R) := by
  classical
  set S := addrNodesFinset R with hS
  set y := x.dropLast with hydef
  have hypre : y <+: x := List.dropLast_prefix x
  have hylen : y.length + 1 = x.length := by
    rw [hydef, List.length_dropLast]
    have hpos : 0 < x.length := List.length_pos_iff.mpr hxne
    omega
  have hyS : y ∈ S := mem_addrNodesFinset.mpr (Or.inr ⟨p, hy⟩)
  have hymax : y ∈ maxNodes S := by
    refine maxNodes_mem_iff.mpr ⟨hyS, fun z hz hyz => ?_⟩
    rcases mem_addrNodesFinset.mp hz with rfl | ⟨q, hq⟩
    · exact List.prefix_nil.mp hyz
    · exact (isLeafIn_iff.mp hleaf z (mem_addrNodes.mpr ⟨q, hq⟩) hyz).symm
  have hxS : x ∉ S := by
    intro hmem
    rcases mem_addrNodesFinset.mp hmem with rfl | ⟨q, hq⟩
    · exact hxne rfl
    · exact hxnot (mem_addrNodes.mpr ⟨q, hq⟩)
  have hxpre : ∀ z, z <+: x → z ≠ x → z ∈ S := by
    intro z hz hne
    by_cases hnil : z = []
    · exact mem_addrNodesFinset.mpr (Or.inl hnil)
    · exact mem_addrNodesFinset.mpr
        (Or.inr ⟨p, h.lower _ _ _ hy (dropLast_prefix_of_prefix_ne hz hne) hnil⟩)
  have key : ∀ b, (p, b) ∈ R → b <+: x := by
    intro b hb
    rcases h.chain _ _ _ hb hy with hbb | hbb
    · exact hbb.trans hypre
    · rw [isLeafIn_iff.mp hleaf b (mem_addrNodes.mpr ⟨p, hb⟩) hbb]
      exact hypre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q z hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · rw [(Prod.mk.injEq .. ▸ heq : q = p ∧ z = x).1]; exact h.len _ _ hy
    · exact h.len _ _ hmem'
  · intro q z hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · rw [(Prod.mk.injEq .. ▸ heq : q = p ∧ z = x).2]; exact hxne
    · exact h.ne_nil _ _ hmem'
  · intro q z hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · rw [(Prod.mk.injEq .. ▸ heq : q = p ∧ z = x).2]; exact hx
    · exact h.mem_sub _ _ hmem'
  · intro q a z hmem hza hzne
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ : q = p ∧ a = x := Prod.mk.injEq .. ▸ heq
      by_cases hzx : z = a
      · exact List.mem_cons.mpr (Or.inl (by rw [hzx]))
      · exact List.mem_cons.mpr (Or.inr
          (h.lower _ _ _ hy (dropLast_prefix_of_prefix_ne hza hzx) hzne))
    · exact List.mem_cons.mpr (Or.inr (h.lower _ _ _ hmem' hza hzne))
  · intro q a b hma hmb
    rcases List.mem_cons.mp hma with ha | ha <;> rcases List.mem_cons.mp hmb with hb | hb
    · have h1 : q = p ∧ a = x := Prod.mk.injEq .. ▸ ha
      have h2 : q = p ∧ b = x := Prod.mk.injEq .. ▸ hb
      rw [h1.2, h2.2]
      exact Or.inl (List.prefix_refl _)
    · have h1 : q = p ∧ a = x := Prod.mk.injEq .. ▸ ha
      rw [h1.2]
      exact Or.inr (key b (h1.1 ▸ hb))
    · have h2 : q = p ∧ b = x := Prod.mk.injEq .. ▸ hb
      rw [h2.2]
      exact Or.inl (key a (h2.1 ▸ ha))
    · exact h.chain _ _ _ ha hb
  · have hused : (addrUsed ((p, x) :: R)).toFinset = (addrUsed R).toFinset := by
      have hp : p ∈ addrUsed R := mem_addrUsed.mpr ⟨_, hy⟩
      simp only [addrUsed, List.map_cons, List.toFinset_cons]
      exact Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hp)
    rw [hused, addrNodesFinset_cons p x R,
      maxNodes_insert_of_maximal hxS (addrNodesFinset_prefixClosed h) hxpre y
        ⟨hypre, hylen⟩ hymax]
    exact h.bound

/-! ## Preservation of the invariant: allocating a fresh address -/

/-- Membership in a state extended by a whole fresh branch. -/
theorem mem_freshList {q x : BitString} {R : AddrList} {a z : BitString} :
    (a, z) ∈ (branchPrefixes x).map (fun w => (q, w)) ++ R ↔
      (a = q ∧ z <+: x ∧ z ≠ []) ∨ (a, z) ∈ R := by
  simp only [List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨w, hw, rfl, rfl⟩ | hR)
    · exact Or.inl ⟨rfl, mem_branchPrefixes.mp hw⟩
    · exact Or.inr hR
  · rintro (⟨rfl, hz⟩ | hR)
    · exact Or.inl ⟨z, mem_branchPrefixes.mpr hz, rfl, rfl⟩
    · exact Or.inr hR

/-- A maximal node of the node set passes the leaf test. -/
theorem maxNodes_isLeafIn {R : AddrList} {y : BitString}
    (hy : y ∈ maxNodes (addrNodesFinset R)) : isLeafIn R y = true := by
  refine isLeafIn_iff.mpr (fun z hz hyz => ?_)
  obtain ⟨p, hp⟩ := mem_addrNodes.mp hz
  exact ((maxNodes_mem_iff.mp hy).2 z (mem_addrNodesFinset.mpr (Or.inr ⟨p, hp⟩)) hyz).symm

/-- Under the greedy invariant, the root is maximal only in the empty state. -/
theorem eq_nil_of_nil_maxNodes {k : ℕ} {R : AddrList} (h : GreedyInv k R)
    (hnil : [] ∈ maxNodes (addrNodesFinset R)) : R = [] := by
  rcases R with _ | ⟨⟨p, x⟩, t⟩
  · rfl
  · exfalso
    have hx : x ∈ addrNodesFinset ((p, x) :: t) :=
      mem_addrNodesFinset.mpr (Or.inr ⟨p, List.mem_cons_self ..⟩)
    have hxx := (maxNodes_mem_iff.mp hnil).2 x hx List.nil_prefix
    exact h.ne_nil p x (List.mem_cons_self ..) hxx.symm

/-- Recording a fresh branch puts exactly one new address into use. -/
theorem addrUsed_freshList {q x : BitString} {R : AddrList} (hxne : x ≠ []) :
    (addrUsed ((branchPrefixes x).map (fun w => (q, w)) ++ R)).toFinset
      = insert q (addrUsed R).toFinset := by
  classical
  ext a
  simp only [List.mem_toFinset, mem_addrUsed, Finset.mem_insert, mem_freshList]
  constructor
  · rintro ⟨z, ⟨rfl, -⟩ | hR⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, hR⟩
  · rintro (rfl | ⟨z, hz⟩)
    · exact ⟨x, Or.inl ⟨rfl, List.prefix_refl _, hxne⟩⟩
    · exact ⟨z, Or.inr hz⟩

/-- Recording a fresh branch whose proper prefixes are known adds exactly the node `x`. -/
theorem addrNodesFinset_freshList {q x : BitString} {R : AddrList} (hxne : x ≠ [])
    (hpre : ∀ z, z <+: x → z ≠ x → z ∈ addrNodesFinset R) :
    addrNodesFinset ((branchPrefixes x).map (fun w => (q, w)) ++ R)
      = insert x (addrNodesFinset R) := by
  classical
  ext z
  simp only [mem_addrNodesFinset, Finset.mem_insert, mem_freshList]
  constructor
  · rintro (rfl | ⟨p, ⟨rfl, hzx, hzne⟩ | hR⟩)
    · exact Or.inr (Or.inl rfl)
    · by_cases hzx' : z = x
      · exact Or.inl hzx'
      · exact Or.inr (mem_addrNodesFinset.mp (hpre z hzx hzx'))
    · exact Or.inr (Or.inr ⟨p, hR⟩)
  · rintro (rfl | rfl | ⟨p, hp⟩)
    · exact Or.inr ⟨q, Or.inl ⟨rfl, List.prefix_refl _, hxne⟩⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨p, Or.inr hp⟩

/-- Recording a new node `x` whose immediate predecessor is either the root or is no longer a
leaf, by allocating a completely fresh address to the whole branch ending at `x`, preserves the
invariant. -/
theorem greedyInv_freshStep {k : ℕ} {R : AddrList} (h : GreedyInv k R) {x : BitString}
    (hxne : x ≠ []) (hxnot : x ∉ addrNodes R) (hx : x ∈ kaSublevel k)
    (hpre : ∀ z, z <+: x → z ≠ x → z ∈ addrNodesFinset R)
    (hcase : x.dropLast = [] ∨ isLeafIn R x.dropLast = false) :
    GreedyInv k ((branchPrefixes x).map (fun w => (freshAddr k R, w)) ++ R) := by
  classical
  set S := addrNodesFinset R with hS
  set y := x.dropLast with hydef
  set q := freshAddr k R with hqdef
  have hnilmem : [] ∈ kaSublevel k := kaSublevel_prefixClosed List.nil_prefix hx
  have hypre : y <+: x := List.dropLast_prefix x
  have hylen : y.length + 1 = x.length := by
    rw [hydef, List.length_dropLast]
    have hpos : 0 < x.length := List.length_pos_iff.mpr hxne
    omega
  have hxS : x ∉ S := by
    intro hmem
    rcases mem_addrNodesFinset.mp hmem with rfl | ⟨p, hp⟩
    · exact hxne rfl
    · exact hxnot (mem_addrNodes.mpr ⟨p, hp⟩)
  have hSsub : ∀ z ∈ insert x S, z ∈ kaSublevel k := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hx
    · exact addrNodesFinset_subset_kaSublevel h hnilmem z hz'
  have hle2k : (maxNodes (insert x S)).card ≤ 2 ^ k :=
    maxNodes_card_le_of_subset_kaSublevel hSsub
  have hkey : (addrUsed R).toFinset.card < 2 ^ k ∧
      (addrUsed R).toFinset.card + 1 ≤ (maxNodes (insert x S)).card := by
    by_cases hymax : y ∈ maxNodes S
    · have hyn : y = [] := by
        rcases hcase with hnil | hfalse
        · exact hnil
        · rw [maxNodes_isLeafIn hymax] at hfalse; exact absurd hfalse (by simp)
      have hRnil : R = [] := eq_nil_of_nil_maxNodes h (hyn ▸ hymax)
      have hcard0 : (addrUsed R).toFinset.card = 0 := by simp [hRnil, addrUsed]
      have h1 : 1 ≤ (maxNodes S).card := Finset.card_pos.mpr ⟨y, hymax⟩
      have heq := maxNodes_insert_of_maximal hxS (addrNodesFinset_prefixClosed h) hpre y
        ⟨hypre, hylen⟩ hymax
      refine ⟨?_, ?_⟩
      · rw [hcard0]; exact Nat.two_pow_pos k
      · rw [hcard0, heq]; exact h1
    · have heq := maxNodes_insert_of_not_maximal hxS (addrNodesFinset_prefixClosed h) hpre y
        ⟨hypre, hylen⟩ hymax
      have hb := h.bound
      rw [← hS] at hb
      omega
  have hfresh : q ∉ addrUsed R := freshAddr_not_mem hkey.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a z hmem
    rcases mem_freshList.mp hmem with ⟨rfl, -⟩ | hR
    · exact freshAddr_length k R
    · exact h.len _ _ hR
  · intro a z hmem
    rcases mem_freshList.mp hmem with ⟨-, -, hzne⟩ | hR
    · exact hzne
    · exact h.ne_nil _ _ hR
  · intro a z hmem
    rcases mem_freshList.mp hmem with ⟨-, hzx, -⟩ | hR
    · exact kaSublevel_prefixClosed hzx hx
    · exact h.mem_sub _ _ hR
  · intro a z w hmem hwz hwne
    rcases mem_freshList.mp hmem with ⟨rfl, hzx, -⟩ | hR
    · exact mem_freshList.mpr (Or.inl ⟨rfl, hwz.trans hzx, hwne⟩)
    · exact mem_freshList.mpr (Or.inr (h.lower _ _ _ hR hwz hwne))
  · intro a z w hz hw
    rcases mem_freshList.mp hz with ⟨rfl, hzx, -⟩ | hzR
    · rcases mem_freshList.mp hw with ⟨-, hwx, -⟩ | hwR
      · rcases le_total z.length w.length with hle | hle
        · exact Or.inl (prefix_of_prefix_of_length_le hzx hwx hle)
        · exact Or.inr (prefix_of_prefix_of_length_le hwx hzx hle)
      · exact absurd (mem_addrUsed.mpr ⟨w, hwR⟩) hfresh
    · rcases mem_freshList.mp hw with ⟨rfl, -, -⟩ | hwR
      · exact absurd (mem_addrUsed.mpr ⟨z, hzR⟩) hfresh
      · exact h.chain _ _ _ hzR hwR
  · rw [addrUsed_freshList hxne, addrNodesFinset_freshList hxne hpre,
      Finset.card_insert_of_notMem (by simpa using hfresh)]
    exact hkey.2

/-! ## Preservation of the invariant: a single step and a whole branch -/

/-- Recording a node keeps every earlier pair. -/
theorem insertNode_subset (k : ℕ) (R : AddrList) (x : BitString) {q : BitString × BitString}
    (hq : q ∈ R) : q ∈ insertNode k R x := by
  unfold insertNode
  cases h1 : (decide (x = []) || decide (x ∈ addrNodes R)) with
  | true => simpa using hq
  | false =>
    cases h2 : (!decide (x.dropLast = []) && isLeafIn R x.dropLast) with
    | true => simp only [Bool.cond_false, Bool.cond_true, List.mem_cons]; exact Or.inr hq
    | false => simp only [Bool.cond_false, List.mem_append]; exact Or.inr hq

/-- Recording a list of nodes keeps every earlier pair. -/
theorem foldl_insertNode_subset (k : ℕ) (xs : List BitString) (R : AddrList)
    {q : BitString × BitString} (hq : q ∈ R) : q ∈ xs.foldl (insertNode k) R := by
  induction xs generalizing R with
  | nil => exact hq
  | cons a t ih => exact ih _ (insertNode_subset k R a hq)

/-- Recording a branch keeps every earlier pair. -/
theorem insertBranch_subset (k : ℕ) (R : AddrList) (x : BitString)
    {q : BitString × BitString} (hq : q ∈ R) : q ∈ insertBranch k R x :=
  foldl_insertNode_subset k _ _ hq

/-- Recording a list of branches keeps every earlier pair. -/
theorem foldl_insertBranch_subset (k : ℕ) (xs : List BitString) (R : AddrList)
    {q : BitString × BitString} (hq : q ∈ R) : q ∈ xs.foldl (insertBranch k) R := by
  induction xs generalizing R with
  | nil => exact hq
  | cons a t ih => exact ih _ (insertBranch_subset k R a hq)

/-- The first address listed at a node is indeed assigned to it. -/
theorem headD_addrsAt_mem {R : AddrList} {y d : BitString} (h : ∃ p, (p, y) ∈ R) :
    ((addrsAt R y).headD d, y) ∈ R := by
  obtain ⟨p, hp⟩ := h
  have hmem : p ∈ addrsAt R y := mem_addrsAt.mpr hp
  cases hl : addrsAt R y with
  | nil => rw [hl] at hmem; exact absurd hmem List.not_mem_nil
  | cons a t =>
    have ha : a ∈ addrsAt R y := by rw [hl]; exact List.mem_cons_self ..
    simp only [List.headD_cons]
    exact mem_addrsAt.mp ha

/-- Recording a nonempty node makes it a node of the state. -/
theorem mem_addrNodes_insertNode (k : ℕ) (R : AddrList) {x : BitString} (hxne : x ≠ []) :
    x ∈ addrNodes (insertNode k R x) := by
  unfold insertNode
  cases h1 : (decide (x = []) || decide (x ∈ addrNodes R)) with
  | true =>
    simp only [Bool.cond_true]
    rcases Bool.or_eq_true .. |>.mp h1 with h | h
    · exact absurd (of_decide_eq_true h) hxne
    · exact of_decide_eq_true h
  | false =>
    cases h2 : (!decide (x.dropLast = []) && isLeafIn R x.dropLast) with
    | true =>
      simp only [Bool.cond_false, Bool.cond_true]
      exact mem_addrNodes.mpr ⟨_, List.mem_cons_self ..⟩
    | false =>
      simp only [Bool.cond_false]
      exact mem_addrNodes.mpr
        ⟨freshAddr k R, mem_freshList.mpr (Or.inl ⟨rfl, List.prefix_refl _, hxne⟩)⟩

end Kolmogorov
