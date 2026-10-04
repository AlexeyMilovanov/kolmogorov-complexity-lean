import KolmogorovMathlib.AlgorithmicRandomness.Multiplicity

/-!
# Disjointification of an effectively open set

An effectively open set is given as a computable union of cylinders
`U = ⋃ j, Ω_{h j}`; the intervals `Ω_{h j}` may overlap, so `∑ j, μ (Ω_{h j})`
can be much larger than `μ U`. Here we refine such a union into a computable
family of *pairwise disjoint* cylinders with the same union, so that the sum of
the masses of the new intervals is exactly `μ U` (SUV Problems 68-69).

The construction is the usual one: the `k`-th interval is replaced by
`Ω_{h k} \ ⋃_{j < k} Ω_{h j}`, which is cut into cylinders `Ω_u` where `u`
ranges over the strings of length `maxLen h (k+1)` extending `h k` and extending
no `h j` with `j < k`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ### Maximal length of the first intervals -/

/-- `natMaxBelow len k` is the maximum of `len j` for `j < k`. -/
def natMaxBelow (len : ℕ → ℕ) : ℕ → ℕ :=
  fun k => Nat.rec 0 (fun y IH => max IH (len y)) k

/-- The running maximum of `len` over indices below `k` dominates each of those values. -/
lemma le_natMaxBelow (len : ℕ → ℕ) {j k : ℕ} (h : j < k) : len j ≤ natMaxBelow len k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hstep : natMaxBelow len (k + 1) = max (natMaxBelow len k) (len k) := rfl
    rw [hstep]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact le_trans (ih hlt) (le_max_left _ _)
    · subst heq; exact le_max_right _ _

/-- The running maximum of a computable family is computable. -/
lemma computable_natMaxBelow {α : Type*} [Primcodable α] {L : α → ℕ → ℕ}
    (hL : Computable (fun q : α × ℕ => L q.1 q.2)) :
    Computable (fun q : α × ℕ => natMaxBelow (L q.1) q.2) := by
  have hstep : Computable₂ (fun (q : α × ℕ) (p : ℕ × ℕ) => max p.2 (L q.1 p.1)) := by
    have hl : Computable (fun r : (α × ℕ) × (ℕ × ℕ) => L r.1.1 r.2.1) :=
      hL.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
    exact Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd) hl
  exact Computable.nat_rec Computable.snd (Computable.const 0) hstep

/-- The length of the `j`-th interval (zero if it is empty). -/
def lenOf (h : ℕ → Option BitString) (j : ℕ) : ℕ := ((h j).map List.length).getD 0

/-- The length of the string emitted at a given index is computable. -/
lemma computable_lenOf {α : Type*} [Primcodable α] {F : α → ℕ → Option BitString}
    (hF : Computable (fun q : α × ℕ => F q.1 q.2)) :
    Computable (fun q : α × ℕ => lenOf (F q.1) q.2) := by
  have hmap : Computable (fun q : α × ℕ => (F q.1 q.2).map List.length) :=
    Computable.option_map hF (Primrec.list_length.to_comp.comp Computable.snd)
  exact Computable.option_getD hmap (Computable.const 0)

/-- The maximal length of the intervals `h j` for `j < k`. -/
def maxLen (h : ℕ → Option BitString) (k : ℕ) : ℕ := natMaxBelow (lenOf h) k

/-- The length emitted at index `j` is at most the running maximum over indices below `k`
whenever `j < k`. -/
lemma lenOf_le_maxLen (h : ℕ → Option BitString) {j k : ℕ} (hjk : j < k) :
    lenOf h j ≤ maxLen h k := le_natMaxBelow _ hjk

/-- The running maximum of the emitted lengths is computable. -/
lemma computable_maxLen {α : Type*} [Primcodable α] {F : α → ℕ → Option BitString}
    (hF : Computable (fun q : α × ℕ => F q.1 q.2)) :
    Computable (fun q : α × ℕ => maxLen (F q.1) q.2) :=
  computable_natMaxBelow (L := fun a j => lenOf (F a) j) (computable_lenOf hF)

/-! ### The disjointified enumeration -/

/-- The test deciding whether the cylinder `Ω_u` is one of the pieces into which
the `k`-th interval of `h` is cut. -/
def disjBit (h : ℕ → Option BitString) (u : BitString) (k : ℕ) : Bool :=
  (u.length == maxLen h (k + 1)) && coverBit h u k && (coverCount h u k == 0)

/-- Enumerate the cylinders `Ω_u` selected by a decidable test `P u k`, where the
index `i` codes the pair `(k, u)`. -/
def selEnum (P : BitString → ℕ → Bool) (i : ℕ) : Option BitString :=
  (Encodable.decode₂ BitString (Nat.unpair i).2).bind fun u =>
    bif P u (Nat.unpair i).1 then some u else none

/-- The disjointified enumeration of the intervals of `h`. -/
def disjEnum (h : ℕ → Option BitString) : ℕ → Option BitString :=
  selEnum (disjBit h)

/-- A string accepted at stage `k` by the disjointification test has the stage's uniform length,
is covered at that stage, and is covered by no earlier index. -/
lemma disjBit_spec {h : ℕ → Option BitString} {u : BitString} {k : ℕ}
    (hb : disjBit h u k = true) :
    u.length = maxLen h (k + 1) ∧ coverBit h u k = true ∧ coverCount h u k = 0 := by
  unfold disjBit at hb
  rw [Bool.and_eq_true, Bool.and_eq_true] at hb
  exact ⟨by simpa using hb.1.1, hb.1.2, by simpa using hb.2⟩

/-- A value emitted by the disjointified enumeration at index `i` is the string coded by the
second component of `i`, accepted at the stage given by the first component. -/
lemma disjEnum_eq_some {h : ℕ → Option BitString} {i : ℕ} {u : BitString}
    (hu : disjEnum h i = some u) :
    Encodable.encode u = (Nat.unpair i).2 ∧ disjBit h u (Nat.unpair i).1 = true := by
  unfold disjEnum selEnum at hu
  cases hd : Encodable.decode₂ BitString (Nat.unpair i).2 with
  | none => rw [hd] at hu; simp at hu
  | some v =>
    rw [hd] at hu
    simp only [Option.bind_some] at hu
    cases hbit : disjBit h v (Nat.unpair i).1 with
    | false => rw [hbit] at hu; simp at hu
    | true =>
      rw [hbit] at hu
      simp only [Bool.cond_true, Option.some.injEq] at hu
      subst hu
      exact ⟨Encodable.decode₂_eq_some.mp hd, hbit⟩

/-- Every string accepted at stage `k` is emitted by the disjointified enumeration, at the index
pairing `k` with its code. -/
lemma disjEnum_of_disjBit {h : ℕ → Option BitString} {u : BitString} {k : ℕ}
    (hb : disjBit h u k = true) :
    disjEnum h (Nat.pair k (Encodable.encode u)) = some u := by
  unfold disjEnum selEnum
  rw [Nat.unpair_pair, Encodable.encodek₂]
  simp only [Option.bind_some]
  rw [hb]
  rfl

/-- Selecting the strings passing a computable test yields a computable enumeration. -/
lemma computable_selEnum {P : ℕ → BitString → ℕ → Bool}
    (hP : Computable (fun r : (ℕ × ℕ) × BitString => P r.1.1 r.2 (Nat.unpair r.1.2).1)) :
    Computable₂ (fun m i => selEnum (P m) i) := by
  have hdec : Computable (fun q : ℕ × ℕ => Encodable.decode₂ BitString (Nat.unpair q.2).2) :=
    (Primrec.decode₂.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  refine Computable.option_bind hdec ?_
  exact Computable.cond hP (Computable.option_some.comp Computable.snd)
    (Computable.const none)

/-- The disjointification test is computable in the enumeration, the string and the stage. -/
lemma computable_disjBit {β : Type*} [Primcodable β] {F : β → ℕ → Option BitString}
    {S : β → BitString} {K : β → ℕ} (hF : Computable (fun p : β × ℕ => F p.1 p.2))
    (hS : Computable S) (hK : Computable K) :
    Computable (fun b : β => disjBit (F b) (S b) (K b)) := by
  unfold disjBit
  have hpair : Computable (fun b : β => (b, K b)) := Computable.pair Computable.id hK
  have hcb : Computable (fun b : β => coverBit (F b) (S b) (K b)) :=
    (computable_coverBit_param hF hS).comp hpair
  have hcnt : Computable (fun b : β => coverCount (F b) (S b) (K b)) :=
    (computable_coverCount_param hF hS).comp hpair
  have hmx : Computable (fun b : β => maxLen (F b) (K b + 1)) :=
    (computable_maxLen hF).comp (Computable.pair Computable.id (Primrec.succ.to_comp.comp hK))
  have hlen : Computable (fun b : β => (S b).length) :=
    Primrec.list_length.to_comp.comp hS
  have hb1 : Computable (fun b : β => (S b).length == maxLen (F b) (K b + 1)) :=
    (Primrec₂.to_comp Primrec.beq).comp hlen hmx
  have hb3 : Computable (fun b : β => coverCount (F b) (S b) (K b) == 0) :=
    (Primrec₂.to_comp Primrec.beq).comp hcnt (Computable.const 0)
  have hand1 : Computable (fun b : β =>
      ((S b).length == maxLen (F b) (K b + 1)) && coverBit (F b) (S b) (K b)) :=
    (Primrec₂.to_comp Primrec.and).comp hb1 hcb
  exact (Primrec₂.to_comp Primrec.and).comp hand1 hb3

/-- Disjointification takes a computable family of enumerations to a computable family. -/
lemma computable_disjEnum {F : ℕ → ℕ → Option BitString} (hF : Computable₂ F) :
    Computable₂ (fun m i => disjEnum (F m) i) := by
  refine computable_selEnum (P := fun a u k => disjBit (F a) u k) ?_
  have hFr : Computable (fun p : ((ℕ × ℕ) × BitString) × ℕ => F p.1.1.1 p.2) :=
    hF.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hSr : Computable (fun r : (ℕ × ℕ) × BitString => r.2) := Computable.snd
  have hKr : Computable (fun r : (ℕ × ℕ) × BitString => (Nat.unpair r.1.2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp
  exact computable_disjBit hFr hSr hKr

/-! ### Geometry of the disjointified family -/

/-- A prefix of an initial segment of a sequence is itself an initial segment of it. -/
lemma isCantorPrefix_of_prefix {t u : BitString} {x : CantorSeq} (htu : t <+: u)
    (hu : IsCantorPrefix u x) : IsCantorPrefix t x :=
  cantorCylinder_subset_of_prefix htu hu

/-- Two initial segments of the same sequence are comparable: the shorter is a prefix of the
longer. -/
lemma prefix_of_isCantorPrefix {t u : BitString} {x : CantorSeq} (ht : IsCantorPrefix t x)
    (hu : IsCantorPrefix u x) (hlen : t.length ≤ u.length) : t <+: u := by
  have h1 : cantorPrefix x t.length = t := (isCantorPrefix_iff_cantorPrefix_eq t x).1 ht
  have h2 : cantorPrefix x u.length = u := (isCantorPrefix_iff_cantorPrefix_eq u x).1 hu
  rw [← h1, ← h2]
  exact cantorPrefix_mono x hlen

/-- Each set of the disjointified enumeration is contained in the union of the original one. -/
lemma coverSet_disjEnum_subset (h : ℕ → Option BitString) (i : ℕ) :
    coverSet (disjEnum h) i ⊆ ⋃ j, coverSet h j := by
  intro x hx
  cases hu : disjEnum h i with
  | none => rw [coverSet, hu] at hx; simp at hx
  | some u =>
    have hxu : x ∈ cantorCylinder u := by rw [coverSet, hu] at hx; simpa using hx
    obtain ⟨-, hbit⟩ := disjEnum_eq_some hu
    obtain ⟨-, hcb, -⟩ := disjBit_spec hbit
    obtain ⟨t, hht, htu⟩ := (coverBit_eq_true_iff h u (Nat.unpair i).1).mp hcb
    refine Set.mem_iUnion.2 ⟨(Nat.unpair i).1, ?_⟩
    rw [coverSet, hht]
    exact cantorCylinder_subset_of_prefix htu hxu

/-- Disjointification does not change the open set covered by an enumeration. -/
lemma coverSet_disjEnum_iUnion (h : ℕ → Option BitString) :
    (⋃ i, coverSet (disjEnum h) i) = ⋃ j, coverSet h j := by
  classical
  refine Set.Subset.antisymm (Set.iUnion_subset (coverSet_disjEnum_subset h)) ?_
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have hP : ∃ k, ∃ t, h k = some t ∧ IsCantorPrefix t x := by
    cases hhj : h j with
    | none => rw [coverSet, hhj] at hj; simp at hj
    | some t =>
      refine ⟨j, t, hhj, ?_⟩
      rw [coverSet, hhj] at hj
      simpa [cantorCylinder] using hj
  set k := Nat.find hP with hk
  obtain ⟨t, hht, htx⟩ := Nat.find_spec hP
  rw [← hk] at hht
  set L := maxLen h (k + 1) with hL
  set u := cantorPrefix x L with hu
  have hxu : x ∈ cantorCylinder u := mem_cantorCylinder_cantorPrefix x L
  have hux : IsCantorPrefix u x := hxu
  have hlen0 : lenOf h k = t.length := by simp [lenOf, hht]
  have htlen : t.length ≤ L := by
    rw [← hlen0]
    exact lenOf_le_maxLen h (Nat.lt_succ_self k)
  have htu : t <+: u := by
    rw [hu]
    have h1 : cantorPrefix x t.length = t := (isCantorPrefix_iff_cantorPrefix_eq t x).1 htx
    rw [← h1]
    exact cantorPrefix_mono x htlen
  have hcb : coverBit h u k = true := (coverBit_eq_true_iff h u k).2 ⟨t, hht, htu⟩
  have hcnt : coverCount h u k = 0 := by
    rw [coverCount_eq_zero_iff]
    intro m hm
    by_contra hcon
    have hcbm : coverBit h u m = true := by simpa using hcon
    obtain ⟨tm, hhm, htmu⟩ := (coverBit_eq_true_iff h u m).mp hcbm
    exact Nat.find_min hP hm ⟨tm, hhm, isCantorPrefix_of_prefix htmu hux⟩
  have hbit : disjBit h u k = true := by
    unfold disjBit
    have hlen : (u.length == maxLen h (k + 1)) = true := by
      simp [hu, hL]
    rw [hlen, hcb, hcnt]
    rfl
  refine Set.mem_iUnion.2 ⟨Nat.pair k (Encodable.encode u), ?_⟩
  rw [coverSet, disjEnum_of_disjBit hbit]
  simpa using hxu

/-- Sets of the disjointified enumeration coming from different stages are disjoint. -/
lemma coverSet_disjEnum_disjoint_of_lt {h : ℕ → Option BitString} {i i' : ℕ}
    (hlt : (Nat.unpair i).1 < (Nat.unpair i').1) :
    Disjoint (coverSet (disjEnum h) i) (coverSet (disjEnum h) i') := by
  cases hu : disjEnum h i with
  | none => simp [coverSet, hu]
  | some u =>
    cases hu' : disjEnum h i' with
    | none => simp [coverSet, hu']
    | some u' =>
      obtain ⟨-, hbit⟩ := disjEnum_eq_some hu
      obtain ⟨-, hbit'⟩ := disjEnum_eq_some hu'
      obtain ⟨-, hcb, -⟩ := disjBit_spec hbit
      obtain ⟨hlen', -, hcnt'⟩ := disjBit_spec hbit'
      obtain ⟨t, hht, htu⟩ := (coverBit_eq_true_iff h u (Nat.unpair i).1).mp hcb
      rw [coverSet, coverSet, hu, hu']
      simp only [Option.elim_some]
      rw [Set.disjoint_left]
      intro x hx hx'
      have hux : IsCantorPrefix u x := hx
      have hu'x : IsCantorPrefix u' x := hx'
      have htx : IsCantorPrefix t x := isCantorPrefix_of_prefix htu hux
      have hlen0 : lenOf h (Nat.unpair i).1 = t.length := by simp [lenOf, hht]
      have htlen : t.length ≤ u'.length := by
        rw [hlen', ← hlen0]
        exact lenOf_le_maxLen h (by omega)
      have htu' : t <+: u' := prefix_of_isCantorPrefix htx hu'x htlen
      have hcb' : coverBit h u' (Nat.unpair i).1 = true :=
        (coverBit_eq_true_iff h u' (Nat.unpair i).1).2 ⟨t, hht, htu'⟩
      have := (coverCount_eq_zero_iff h u' (Nat.unpair i').1).mp hcnt' _ hlt
      rw [hcb'] at this
      exact Bool.noConfusion this

/-- The sets of a disjointified enumeration are pairwise disjoint. -/
lemma coverSet_disjEnum_pairwise (h : ℕ → Option BitString) :
    Pairwise (Function.onFun Disjoint (coverSet (disjEnum h))) := by
  intro i i' hne
  rcases lt_trichotomy (Nat.unpair i).1 (Nat.unpair i').1 with hlt | heq | hgt
  · exact coverSet_disjEnum_disjoint_of_lt hlt
  · -- same level: the two strings have the same length and are distinct
    cases hu : disjEnum h i with
    | none => simp [Function.onFun, coverSet, hu]
    | some u =>
      cases hu' : disjEnum h i' with
      | none => simp [Function.onFun, coverSet, hu']
      | some u' =>
        obtain ⟨hcode, hbit⟩ := disjEnum_eq_some hu
        obtain ⟨hcode', hbit'⟩ := disjEnum_eq_some hu'
        obtain ⟨hlen, -, -⟩ := disjBit_spec hbit
        obtain ⟨hlen', -, -⟩ := disjBit_spec hbit'
        have hne' : u ≠ u' := by
          intro hcon
          apply hne
          have h2 : (Nat.unpair i).2 = (Nat.unpair i').2 := by
            rw [← hcode, ← hcode', hcon]
          have := Nat.pair_unpair i
          rw [← Nat.pair_unpair i, ← Nat.pair_unpair i', heq, h2]
        have hlenu : u.length = u'.length := by rw [hlen, hlen', heq]
        have hnp1 : ¬ u <+: u' := by
          intro hpre
          exact hne' (List.IsPrefix.eq_of_length hpre hlenu)
        have hnp2 : ¬ u' <+: u := by
          intro hpre
          exact hne' (List.IsPrefix.eq_of_length hpre hlenu.symm).symm
        change Disjoint (coverSet (disjEnum h) i) (coverSet (disjEnum h) i')
        rw [coverSet, coverSet, hu, hu']
        simpa using cantorCylinder_disjoint_of_incompatible hnp1 hnp2
  · exact (coverSet_disjEnum_disjoint_of_lt hgt).symm

/-- The masses of the disjointified intervals sum to the measure of the union. -/
theorem tsum_measure_disjEnum (μ : Measure CantorSeq) (h : ℕ → Option BitString) :
    (∑' i, (disjEnum h i).elim 0 (cantorMass μ)) = μ (⋃ j, coverSet h j) := by
  have h1 : (∑' i, μ (coverSet (disjEnum h) i)) = μ (⋃ i, coverSet (disjEnum h) i) :=
    (measure_iUnion (coverSet_disjEnum_pairwise h)
      (measurableSet_coverSet (disjEnum h))).symm
  rw [← coverSet_disjEnum_iUnion h, ← h1]
  exact tsum_congr fun i => (measure_coverSet μ (disjEnum h) i).symm

end Kolmogorov
