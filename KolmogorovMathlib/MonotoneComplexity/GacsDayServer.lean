import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.MonotoneOptimality
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools

/-!
# The server play induced by a monotone decompressor

The adversary the client is played against: given a monotone decompressor, the stage-`t` server
grants at each node the strings it has so far been seen to produce above that node.
`gacsDayServerStage` is that move and `gacsDayServerStageAlloc` its allocation at a node.

### Outline

* the dictionary between nodes of the binary game tree and bit strings
  (`gacsDayNodeToBitString`, `gacsDayNodeOfBitString`, with the round-trip lemmas), and the
  enumerations `gacsDayBitStringsUpTo`, `allGacsDayNodesUpTo` of the finitely many short ones;
* the stage allocations, their explicit membership test
  (`mem_getAlloc_gacsDayServerStage_iff`) and computability
  (`computable_gacsDayServerStage`);
* legality: the stage allocations grow (`getAlloc_gacsDayServerStage_mono`), each stage is
  coherent, so `serverPlayLegal_gacsDayServerStage`;
* `monotoneProduces_eventually_mem_gacsDayServerStage`, which says nothing the decompressor
  produces escapes the server play, so a client win really is a defect of the decompressor.
-/

namespace Kolmogorov
open ENNReal MeasureTheory

/-- The bit string of a node of the binary game tree, reading the child `1` as `true`. -/
def gacsDayNodeToBitString : GacsDayNode → BitString
  | [] => []
  | (n :: ns) => (n = 1) :: gacsDayNodeToBitString ns

/-- The node of the binary game tree named by a bit string. -/
def gacsDayNodeOfBitString : BitString → GacsDayNode
  | [] => []
  | (b :: bs) => (if b then 1 else 0) :: gacsDayNodeOfBitString bs

/-- All bit strings of length `n`. -/
def gacsDayBitStringsOfLength (n : ℕ) : List BitString :=
  allStrings n

/-- All bit strings of length at most `t`. -/
def gacsDayBitStringsUpTo (t : ℕ) : List BitString :=
  List.flatten (List.map gacsDayBitStringsOfLength (List.range (t + 1)))

/-- All nodes of the binary game tree at depth `n`. -/
def gacsDayNodeOfLength (n : ℕ) : List GacsDayNode :=
  List.map gacsDayNodeOfBitString (allStrings n)

/-- All nodes of the binary game tree of depth at most `t`. -/
def allGacsDayNodesUpTo (t : ℕ) : List GacsDayNode :=
  List.flatten (List.map gacsDayNodeOfLength (List.range (t + 1)))

/-- Reading a bit string as a node and back recovers the string. -/
@[simp] lemma gacsDayNodeToBitString_nodeOfBitString (x : BitString) :
    gacsDayNodeToBitString (gacsDayNodeOfBitString x) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      cases b <;>
        simp [gacsDayNodeOfBitString, gacsDayNodeToBitString, ih]

/-- Reading a binary node as a string and back recovers the node. -/
lemma gacsDayNodeOfBitString_nodeToBitString {x : GacsDayNode}
    (hx : ∀ a ∈ x, a < 2) :
    gacsDayNodeOfBitString (gacsDayNodeToBitString x) = x := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      have ha := hx a (by simp)
      have htail : ∀ b ∈ x, b < 2 := by
        intro b hb
        exact hx b (by simp [hb])
      interval_cases a <;>
        simp [gacsDayNodeOfBitString, gacsDayNodeToBitString, ih htail]

/-- Reading a node as a bit string preserves its length. -/
@[simp] lemma gacsDayNodeToBitString_length (x : GacsDayNode) :
    (gacsDayNodeToBitString x).length = x.length := by
  induction x <;> simp [gacsDayNodeToBitString, *]

/-- A string of length at most `t` is enumerated by `gacsDayBitStringsUpTo t`. -/
lemma mem_gacsDayBitStringsUpTo_of_length_le {t : ℕ} {x : BitString}
    (hx : x.length ≤ t) :
    x ∈ gacsDayBitStringsUpTo t := by
  simp only [gacsDayBitStringsUpTo, List.mem_flatten, List.mem_map]
  refine ⟨gacsDayBitStringsOfLength x.length, ?_, ?_⟩
  · exact ⟨x.length, by simp [hx], rfl⟩
  · exact (mem_allStrings x.length x).mpr rfl

/-- A binary node of depth at most `t` is enumerated by `allGacsDayNodesUpTo t`. -/
lemma mem_allGacsDayNodesUpTo_of_binary {t : ℕ} {x : GacsDayNode}
    (hlen : x.length ≤ t) (hx : ∀ a ∈ x, a < 2) :
    x ∈ allGacsDayNodesUpTo t := by
  simp only [allGacsDayNodesUpTo, List.mem_flatten, List.mem_map]
  refine ⟨gacsDayNodeOfLength x.length, ?_, ?_⟩
  · exact ⟨x.length, by simp [hlen], rfl⟩
  · simp only [gacsDayNodeOfLength, List.mem_map]
    exact ⟨gacsDayNodeToBitString x,
      (mem_allStrings x.length _).mpr (gacsDayNodeToBitString_length x),
      gacsDayNodeOfBitString_nodeToBitString hx⟩

/-- The strings the stage-`t` server allocates at a node: those it has already been seen to
produce, by time `t`, on some extension of that node. -/
def gacsDayServerStageAlloc (chk : (BitString × BitString) → ℕ
                              → Bool) (t : ℕ) (x : GacsDayNode) : Allocation :=
  let all_p := gacsDayBitStringsUpTo t
  let all_y := gacsDayBitStringsUpTo t
  List.filter (fun p =>
    List.any all_y (fun y =>
      (gacsDayNodeToBitString x <+: y) && chk (p, y) t
    )
  ) all_p

/-- The server move at stage `t`: every node of depth at most `t` with its stage allocation. -/
def gacsDayServerStage (chk : (BitString × BitString) → ℕ → Bool) (t : ℕ) : ServerMove :=
  List.map (fun x => (x, gacsDayServerStageAlloc chk t x)) (allGacsDayNodesUpTo t)

/-- At a node the stage server enumerates, its allocation is the stage allocation. -/
lemma getAlloc_gacsDayServerStage_of_mem
    (chk : (BitString × BitString) → ℕ → Bool) (t : ℕ) (x : GacsDayNode)
    (hx : x ∈ allGacsDayNodesUpTo t) :
    getAlloc (gacsDayServerStage chk t) x = gacsDayServerStageAlloc chk t x := by
  simp only [getAlloc, gacsDayServerStage]
  have hlookup : ∀ l : List GacsDayNode, x ∈ l →
      List.lookup x (List.map (fun y => (y, gacsDayServerStageAlloc chk t y)) l) =
        some (gacsDayServerStageAlloc chk t x) := by
    intro l hl
    induction l with
    | nil => exact (List.not_mem_nil hl).elim
    | cons a l ih =>
        rcases List.mem_cons.mp hl with rfl | hl
        · simp
        · simp only [List.map_cons, List.lookup_cons]
          by_cases hax : x = a
          · subst a
            simp
          · have hbeq : (x == a) = false := beq_eq_false_iff_ne.mpr hax
            rw [hbeq]
            exact ih hl
  rw [hlookup _ hx]

/-- The staged server play is computable when its approximation test is. -/
lemma computable_gacsDayServerStage (chk : (BitString × BitString) → ℕ
                                      → Bool) (hcomp : Computable₂ chk) :
    Computable (fun t => gacsDayServerStage chk t) := by
  have hallPrim : Primrec allStrings := by
    convert Primrec.nat_rec' _ _ _ using 1
    rotate_left
    · exact fun n => n
    · exact fun _ => [[]]
    · exact fun _ p => p.2.map (List.cons false) ++ p.2.map (List.cons true)
    · exact Primrec.id
    · exact Primrec.const [[]]
    · apply Primrec₂.comp
      · exact Primrec.list_append
      · apply Primrec.list_map
        · exact Primrec.snd.comp Primrec.snd
        · exact Primrec₂.comp Primrec.list_cons (Primrec.const false) Primrec.snd
      · apply Primrec.list_map
        · exact Primrec.snd.comp Primrec.snd
        · exact Primrec.list_cons.comp (Primrec.const true) Primrec.snd
    · funext n
      induction n <;> simp [*, allStrings]
  have hnodePrim : Primrec gacsDayNodeOfBitString := by
    have hbody : Primrec₂
        (fun (_ : BitString) (b : Bool) => bif b then 1 else 0) := by
      exact (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)).to₂
    refine (Primrec.list_map Primrec.id hbody).of_eq ?_
    intro x
    induction x with
    | nil => rfl
    | cons b x ih =>
        simp only [id_eq, Bool.cond_eq_ite] at ih
        cases b <;> simp [gacsDayNodeOfBitString, ih]
  have hbitsUpPrim : Primrec gacsDayBitStringsUpTo := by
    have h := Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
      ((hallPrim.comp Primrec.snd).to₂)
    exact h.of_eq (fun t => by
      simp only [gacsDayBitStringsUpTo]
      rfl)
  have hnodeLevelPrim : Primrec gacsDayNodeOfLength := by
    exact (Primrec.list_map hallPrim ((hnodePrim.comp Primrec.snd).to₂)).of_eq
      (fun _ => rfl)
  have hnodesUpPrim : Primrec allGacsDayNodesUpTo := by
    have h := Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
      ((hnodeLevelPrim.comp Primrec.snd).to₂)
    exact h.of_eq (fun _ => rfl)
  have hprefPrim : Primrec₂ (fun x y : BitString => decide (x <+: y)) := by
    have h : Primrec (fun p : BitString × BitString =>
        decide (p.1 = p.2.take p.1.length)) :=
      (primrec_decideEq (β := BitString)).comp Primrec.fst
        (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
    exact h.to₂.of_eq (fun a b =>
      (decide_eq_decide.mpr
        (List.prefix_iff_eq_take (l₁ := a) (l₂ := b))).symm)
  have hany : Computable (fun r : (ℕ × GacsDayNode) × BitString =>
      (gacsDayBitStringsUpTo r.1.1).any (fun y =>
        (gacsDayNodeToBitString r.1.2 <+: y) && chk (r.2, y) r.1.1)) := by
    have hlist : Computable (fun r : (ℕ × GacsDayNode) × BitString =>
        gacsDayBitStringsUpTo r.1.1) :=
      hbitsUpPrim.to_comp.comp (Computable.fst.comp Computable.fst)
    have hpred : Computable₂
        (fun (r : (ℕ × GacsDayNode) × BitString) y =>
          (gacsDayNodeToBitString r.1.2 <+: y) && chk (r.2, y) r.1.1) := by
      have hnode : Computable
          (fun q : ((ℕ × GacsDayNode) × BitString) × BitString =>
            gacsDayNodeToBitString q.1.1.2) := by
        have hb : Computable gacsDayNodeToBitString := by
          have hbody : Computable₂
              (fun (_ : GacsDayNode) n => decide (n = 1)) := by
            have heq : Primrec₂ (fun n m : ℕ => decide (n = m)) :=
              primrec_decideEq
            exact (heq.to_comp.comp Computable.snd (Computable.const 1)).to₂.of_eq
              (fun _ => rfl)
          exact (Computable.list_map Computable.id hbody).of_eq (fun x => by
            induction x with
            | nil => rfl
            | cons n x ih =>
                simp only [id_eq] at ih
                simp [gacsDayNodeToBitString, ih])
        exact hb.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      have hy : Computable
          (fun q : ((ℕ × GacsDayNode) × BitString) × BitString => q.2) :=
        Computable.snd
      have hpref := hprefPrim.to_comp.comp hnode hy
      have harg : Computable
          (fun q : ((ℕ × GacsDayNode) × BitString) × BitString =>
            (q.1.2, q.2)) :=
        (Computable.snd.comp Computable.fst).pair Computable.snd
      have hstage : Computable
          (fun q : ((ℕ × GacsDayNode) × BitString) × BitString => q.1.1.1) :=
        Computable.fst.comp (Computable.fst.comp Computable.fst)
      have hchk := hcomp.comp harg hstage
      exact (Primrec.and.to_comp.comp hpref hchk).to₂
    exact computable_list_any hlist hpred
  have halloc : Computable (fun q : ℕ × GacsDayNode =>
      gacsDayServerStageAlloc chk q.1 q.2) := by
    have hlist : Computable
        (fun q : ℕ × GacsDayNode => gacsDayBitStringsUpTo q.1) :=
      hbitsUpPrim.to_comp.comp Computable.fst
    exact (computable_list_filter hlist hany.to₂).of_eq (fun _ => rfl)
  have hmap : Computable₂ (fun t (x : GacsDayNode) =>
      (x, gacsDayServerStageAlloc chk t x)) :=
    (Computable.pair Computable.snd halloc).to₂
  exact (Computable.list_map hnodesUpPrim.to_comp hmap).of_eq (fun _ => rfl)


/-- Appending a child to a node appends the corresponding bit to its string. -/
lemma gacsDayNodeToBitString_append_singleton (x : GacsDayNode) (c : ℕ) :
    gacsDayNodeToBitString (x ++ [c]) = gacsDayNodeToBitString x ++ [decide (c = 1)] := by
  induction x with | nil => rfl | cons a x ih => simp [gacsDayNodeToBitString, ih]

/-- An enumerated string has length at most `t`. -/
lemma length_le_of_mem_gacsDayBitStringsUpTo {t : ℕ} {x : BitString}
    (hx : x ∈ gacsDayBitStringsUpTo t) : x.length ≤ t := by
  simp only [gacsDayBitStringsUpTo, List.mem_flatten, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨l, ⟨n, hn1, hn2⟩, hx⟩
  subst hn2
  simp only [gacsDayBitStringsOfLength, mem_allStrings] at hx
  omega

/-- The node of a bit string has the length of that string. -/
lemma gacsDayNodeOfBitString_length (bs : BitString) :
    (gacsDayNodeOfBitString bs).length = bs.length := by
  induction bs with | nil => rfl | cons b bs ih => simp [gacsDayNodeOfBitString, ih]

/-- An enumerated node has depth at most `t`. -/
lemma length_le_of_mem_allGacsDayNodesUpTo {t : ℕ} {x : GacsDayNode}
    (hx : x ∈ allGacsDayNodesUpTo t) : x.length ≤ t := by
  simp only [allGacsDayNodesUpTo, List.mem_flatten, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨l, ⟨n, hn1, hn2⟩, hx⟩
  subst hn2
  simp only [gacsDayNodeOfLength, List.mem_map] at hx
  rcases hx with ⟨bs, hbs1, hbs2⟩
  subst hbs2
  simp only [mem_allStrings] at hbs1
  rw [gacsDayNodeOfBitString_length]
  omega

/-- The node of a bit string only uses the children `0` and `1`. -/
lemma binary_gacsDayNodeOfBitString (bs : BitString) (a : ℕ) (ha : a
                                                               ∈ gacsDayNodeOfBitString bs) : a
  < 2 := by
  induction bs with
  | nil => contradiction
  | cons b bs ih =>
      simp only [gacsDayNodeOfBitString, List.mem_cons] at ha
      rcases ha with rfl | ha
      · cases b <;> simp
      · exact ih ha

/-- An enumerated node only uses the children `0` and `1`. -/
lemma binary_of_mem_allGacsDayNodesUpTo {t : ℕ} {x : GacsDayNode}
    (hx : x ∈ allGacsDayNodesUpTo t) (a : ℕ) (ha : a ∈ x) : a < 2 := by
  simp only [allGacsDayNodesUpTo, List.mem_flatten, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨l, ⟨n, hn1, hn2⟩, hx⟩
  subst hn2
  simp only [gacsDayNodeOfLength, List.mem_map] at hx
  rcases hx with ⟨bs, hbs1, hbs2⟩
  subst hbs2
  exact binary_gacsDayNodeOfBitString bs a ha

/-- At a node the stage server does not enumerate, it allocates nothing. -/
lemma getAlloc_gacsDayServerStage_eq_nil_of_not_mem
    (chk : (BitString × BitString) → ℕ → Bool) (t : ℕ) (x : GacsDayNode)
    (hx : x ∉ allGacsDayNodesUpTo t) :
    getAlloc (gacsDayServerStage chk t) x = [] := by
  simp only [getAlloc, gacsDayServerStage]
  have hlookup : ∀ l : List GacsDayNode, x ∉ l →
      List.lookup x (List.map (fun y => (y, gacsDayServerStageAlloc chk t y)) l) = none := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
        rw [List.mem_cons, not_or] at hl
        have hbeq : (x == a) = false := beq_eq_false_iff_ne.mpr hl.1
        simp only [List.map_cons, List.lookup_cons, hbeq]
        exact ih hl.2
  rw [hlookup _ hx]

/-- Membership in a stage allocation spelled out: both strings are short enough, the node is
binary, and the test fires on an extension of the node. -/
lemma mem_getAlloc_gacsDayServerStage_iff
    (chk : (BitString × BitString) → ℕ → Bool) (t : ℕ) (x : GacsDayNode) (p : BitString) :
    p ∈ getAlloc (gacsDayServerStage chk t) x ↔
      p.length ≤ t ∧ x.length ≤ t ∧ (∀ a ∈ x, a < 2) ∧
      ∃ y, y.length ≤ t ∧ gacsDayNodeToBitString x <+: y ∧ chk (p, y) t = true := by
  by_cases hx : x ∈ allGacsDayNodesUpTo t
  · rw [getAlloc_gacsDayServerStage_of_mem _ _ _ hx]
    simp only [gacsDayServerStageAlloc, List.mem_filter, List.any_eq_true, Bool.and_eq_true,
                decide_eq_true_eq]
    have hx_len : x.length ≤ t := length_le_of_mem_allGacsDayNodesUpTo hx
    have hx_bin : ∀ a ∈ x, a < 2 := binary_of_mem_allGacsDayNodesUpTo hx
    constructor
    · rintro ⟨hp_mem, ⟨y, hy_mem, hy_pref, hy_chk⟩⟩
      refine ⟨length_le_of_mem_gacsDayBitStringsUpTo hp_mem, hx_len, hx_bin, y,
               length_le_of_mem_gacsDayBitStringsUpTo hy_mem, hy_pref, hy_chk⟩
    · rintro ⟨hp_len, _, _, ⟨y, hy_len, hy_pref, hy_chk⟩⟩
      refine ⟨mem_gacsDayBitStringsUpTo_of_length_le hp_len, y,
               mem_gacsDayBitStringsUpTo_of_length_le hy_len, hy_pref, hy_chk⟩
  · rw [getAlloc_gacsDayServerStage_eq_nil_of_not_mem _ _ _ hx]
    simp only [List.not_mem_nil, false_iff]
    intro h
    rcases h with ⟨-, hx_len, hx_bin, -⟩
    exact hx (mem_allGacsDayNodesUpTo_of_binary hx_len hx_bin)

/-- Two prefixes of one list of the same length are equal. -/
lemma isPrefix_eq_of_length_eq {α} {a b c : List α} (ha : a <+: c) (hb : b <+: c) (h : a.length
                                                                                    = b.length) : a
  = b := by
  have ha2 := List.prefix_iff_eq_take.mp ha
  have hb2 := List.prefix_iff_eq_take.mp hb
  rw [ha2, hb2, h]

/-- Two comparable strings extending `x` by one bit each extend it by the same bit. -/
lemma bitStream_prefix_comparable_of_common_upper {y₁ y₂ : BitString} {b₁ b₂ : Bool} {x : BitString}
    (h₁ : x ++ [b₁] <+: y₁) (h₂ : x ++ [b₂] <+: y₂) (hy : y₁ <+: y₂ ∨ y₂ <+: y₁) :
    b₁ = b₂ := by
  have h_eq : x ++ [b₁] = x ++ [b₂] := by
    rcases hy with hy | hy
    · exact isPrefix_eq_of_length_eq (List.IsPrefix.trans h₁ hy) h₂ (by simp)
    · exact isPrefix_eq_of_length_eq h₁ (List.IsPrefix.trans h₂ hy) (by simp)
  simpa using h_eq

/-- The stage allocation of a child is contained in that of its parent. -/
lemma gacsDayServerStageAlloc_child_subset
    (chk : (BitString × BitString) → ℕ → Bool) (t : ℕ) (x : GacsDayNode) (c : ℕ) :
    getAlloc (gacsDayServerStage chk t) (x ++ [c]) ⊆ getAlloc (gacsDayServerStage chk t) x := by
  intro p hp
  rw [mem_getAlloc_gacsDayServerStage_iff] at hp
  rcases hp with ⟨hp_len, hxc_len, hxc_bin, y, hy_len, hy_pref, hy_chk⟩
  rw [mem_getAlloc_gacsDayServerStage_iff]
  refine ⟨hp_len, ?_, ?_, y, hy_len, ?_, hy_chk⟩
  · simp only [List.length_append, List.length_singleton] at hxc_len
    omega
  · intro a ha
    exact hxc_bin a (List.mem_append.mpr (Or.inl ha))
  · rw [gacsDayNodeToBitString_append_singleton] at hy_pref
    exact List.IsPrefix.trans (List.prefix_append _ _) hy_pref

/-- Distinct children of a node get disjoint stage allocations. -/
lemma gacsDayServerStageAlloc_siblings_disjoint
    {D : BitStream → BitStream}
    (chk : (BitString × BitString) → ℕ → Bool)
    (hD : IsContinuousStreamMap D)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (t : ℕ) (x : GacsDayNode) (c₁ c₂ : ℕ) (hc : c₁ ≠ c₂) (hc₁ : c₁ < 2) (hc₂ : c₂ < 2) :
    disjointAllocations (getAlloc (gacsDayServerStage chk t) (x ++ [c₁]))
                        (getAlloc (gacsDayServerStage chk t) (x ++ [c₂])) := by
  intro p hp q hq hpq
  rw [mem_getAlloc_gacsDayServerStage_iff] at hp hq
  rcases hp with ⟨_, _, _, y₁, _, hy₁_pref, hy₁_chk⟩
  rcases hq with ⟨_, _, _, y₂, _, hy₂_pref, hy₂_chk⟩
  have hy₁_graph : streamLowerGraph D p y₁ :=
    (h_approx (p, y₁)).mp ⟨t, hy₁_chk⟩
  have hy₂_graph : streamLowerGraph D q y₂ :=
    (h_approx (q, y₂)).mp ⟨t, hy₂_chk⟩
  have hy_comp : y₁ <+: y₂ ∨ y₂ <+: y₁ :=
    IsStreamLowerGraph.output_compatible_of_input_compatible
      (continuousStreamMap_lowerGraph_isStreamLowerGraph hD.1)
      hpq hy₁_graph hy₂_graph
  rw [gacsDayNodeToBitString_append_singleton] at hy₁_pref hy₂_pref
  have hb : decide (c₁ = 1) = decide (c₂ = 1) :=
    bitStream_prefix_comparable_of_common_upper hy₁_pref hy₂_pref hy_comp
  have hc1_cases : c₁ = 0 ∨ c₁ = 1 := by omega
  have hc2_cases : c₂ = 0 ∨ c₂ = 1 := by omega
  rcases hc1_cases with rfl | rfl <;> rcases hc2_cases with rfl | rfl <;> revert hb hc <;> simp

/-- The stage allocations grow with the stage. -/
lemma getAlloc_gacsDayServerStage_mono
    (chk : (BitString × BitString) → ℕ → Bool)
    (hchk : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (t : ℕ) (x : GacsDayNode) :
    getAlloc (gacsDayServerStage chk t) x ⊆ getAlloc (gacsDayServerStage chk (t + 1)) x := by
  intro p hp
  rw [mem_getAlloc_gacsDayServerStage_iff] at hp
  rcases hp with ⟨hp_len, hx_len, hx_bin, y, hy_len, hy_pref, hy_chk⟩
  rw [mem_getAlloc_gacsDayServerStage_iff]
  refine ⟨by omega, by omega, hx_bin, y, by omega, hy_pref, hchk (p, y) t (t + 1) (by omega) hy_chk⟩



/-- Each stage of the server play is a coherent binary server move. -/
lemma serverMoveCoherent_gacsDayServerStage {D : BitStream → BitStream}
    (chk : (BitString × BitString) → ℕ → Bool)
    (hD : IsContinuousStreamMap D)
    (_hchk : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (t : ℕ) :
    serverMoveCoherent 2 (gacsDayServerStage chk t) := by
  refine ⟨?_, ?_⟩
  · intro x c p hp
    exact ⟨p, gacsDayServerStageAlloc_child_subset chk t x c hp, List.prefix_refl _⟩
  · intro x c1 c2 hc
    have hc1 : (c1 : ℕ) < 2 := c1.isLt
    have hc2 : (c2 : ℕ) < 2 := c2.isLt
    exact gacsDayServerStageAlloc_siblings_disjoint chk hD h_approx t x c1 c2
      (by exact fun h => hc (Fin.ext h)) hc1 hc2

/-- The staged server play is a legal binary server play. -/
lemma serverPlayLegal_gacsDayServerStage {D : BitStream → BitStream}
    (chk : (BitString × BitString) → ℕ → Bool)
    (hD : IsContinuousStreamMap D)
    (hchk : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2) :
    serverPlayLegal 2 (gacsDayServerStage chk) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact serverMoveCoherent_gacsDayServerStage chk hD hchk h_approx t
  · intro t x p hp
    exact ⟨p, getAlloc_gacsDayServerStage_mono chk hchk t x hp, List.prefix_refl _⟩

/-- A string the decompressor produces above a node is eventually allocated at that node by the
staged server. -/
lemma monotoneProduces_eventually_mem_gacsDayServerStage {D : BitStream → BitStream}
    (chk : (BitString × BitString) → ℕ → Bool)
    (hchk : ∀ a s t, s ≤ t → chk a s = true → chk a t = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (x : GacsDayNode) (hx : ∀ a ∈ x, a < 2) (p : BitString)
    (hp : monotoneProduces D p (gacsDayNodeToBitString x)) :
    ∃ t, p ∈ getAlloc (gacsDayServerStage chk t) x := by
  have hpGraph : streamLowerGraph D p (gacsDayNodeToBitString x) := hp
  obtain ⟨s, hs⟩ :=
    (h_approx (p, gacsDayNodeToBitString x)).mpr hpGraph
  let t := max s (max p.length x.length)
  have hst : s ≤ t := le_trans (le_max_left _ _) (le_refl _)
  have hpt : p.length ≤ t :=
    le_trans (le_max_left _ _) (le_max_right s _)
  have hxt : x.length ≤ t :=
    le_trans (le_max_right _ _) (le_max_right s _)
  have hcheck : chk (p, gacsDayNodeToBitString x) t = true :=
    hchk _ s t hst hs
  refine ⟨t, ?_⟩
  rw [getAlloc_gacsDayServerStage_of_mem chk t x
    (mem_allGacsDayNodesUpTo_of_binary hxt hx)]
  rw [gacsDayServerStageAlloc, List.mem_filter]
  refine ⟨mem_gacsDayBitStringsUpTo_of_length_le hpt, ?_⟩
  simp only [List.any_eq_true, Bool.and_eq_true]
  exact ⟨gacsDayNodeToBitString x,
    mem_gacsDayBitStringsUpTo_of_length_le (by simpa using hxt),
    ⟨by simp, hcheck⟩⟩

end Kolmogorov
