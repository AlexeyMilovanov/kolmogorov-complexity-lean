import KolmogorovMathlib.StrongMerging.Lower.Reservoir.Stream

/-!
# The moving-sphere reservoir game: counting, choice and transitions

Counting consequences of `ValidHistory`, the availability of the reservoir choice
(blueprint node L16, `chooseReservoir_spec`) and the transition rules (node L17,
`reservoirTransition_spec`) of the generic game.

Part of `KolmogorovMathlib.StrongMerging.Lower.Reservoir`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Counting consequences of `ValidHistory` -/

/-- **Set mass bound.**  The total mass of the set events of a valid history is at most
`(K+τ+1) 2^(K+τ)`.
Proof: every set event `(Q, i)` has `i ≤ K + τ` and `|Q| ≤ 2^(K+τ-i)`; grouping by `i`,
`setMass ≤ ∑_{i ≤ K+τ} costCount i · 2^(K+τ-i) ≤ ∑_{i ≤ K+τ} 2^i 2^(K+τ-i) = (K+τ+1) 2^(K+τ)`.
Reference: paper, proof of Lemma `lem:ham-reservoir` (marked union bound); L16, L19. -/
theorem setMass_le {G : ResGame α} {K τ S : ℕ} {evs : List (ResEvent α)}
    (hv : ValidHistory G K τ S evs) : setMass evs ≤ (K + τ + 1) * 2 ^ (K + τ) := by
  have hw : ∀ e ∈ evs, ResEvent.setCard e ≤
      ∑ i ∈ Finset.range (K + τ + 1), if ResEvent.hasCost i e then 2 ^ (K + τ - i) else 0 := by
    intro e he
    cases e with
    | point u => simp [ResEvent.setCard]
    | table P => simp [ResEvent.setCard]
    | set Q j =>
      obtain ⟨hj, -, hQ⟩ := hv.set_elig Q j he
      have hsum : (∑ i ∈ Finset.range (K + τ + 1),
          if ResEvent.hasCost i (ResEvent.set Q j) then 2 ^ (K + τ - i) else 0) =
          2 ^ (K + τ - j) := by
        rw [Finset.sum_eq_single j]
        · simp [ResEvent.hasCost]
        · intro b _ hb
          simp [ResEvent.hasCost, Ne.symm hb]
        · intro hj'
          exact absurd (Finset.mem_range.mpr (by omega)) hj'
      rw [hsum]
      have h2 : 2 ^ (K + τ) = 2 ^ (K + τ - j) * 2 ^ j := by
        rw [← pow_add]
        congr 1
        omega
      rw [h2] at hQ
      exact Nat.le_of_mul_le_mul_right hQ (by positivity)
  have hstep : ∀ l : List (ResEvent α), (∀ e ∈ l, ResEvent.setCard e ≤
      ∑ i ∈ Finset.range (K + τ + 1), if ResEvent.hasCost i e then 2 ^ (K + τ - i) else 0) →
      setMass l ≤ ∑ i ∈ Finset.range (K + τ + 1), costCount l i * 2 ^ (K + τ - i) := by
    intro l
    induction l with
    | nil => intro _; simp [setMass]
    | cons e l ih =>
      intro hl
      have h1 := hl e (by simp)
      have h2 := ih (fun x hx => hl x (by simp [hx]))
      have hm : setMass (e :: l) = ResEvent.setCard e + setMass l := by simp [setMass]
      have hc : ∀ i, costCount (e :: l) i * 2 ^ (K + τ - i) =
          (if ResEvent.hasCost i e then 2 ^ (K + τ - i) else 0) +
            costCount l i * 2 ^ (K + τ - i) := by
        intro i
        simp only [costCount, List.countP_cons]
        split_ifs <;> ring
      rw [hm, Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib]
      exact Nat.add_le_add h1 h2
  calc setMass evs ≤ ∑ i ∈ Finset.range (K + τ + 1), costCount evs i * 2 ^ (K + τ - i) :=
        hstep evs hw
    _ ≤ ∑ _i ∈ Finset.range (K + τ + 1), 2 ^ (K + τ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ K + τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc costCount evs i * 2 ^ (K + τ - i) ≤ 2 ^ i * 2 ^ (K + τ - i) :=
              Nat.mul_le_mul_right _ (hv.cost_count i)
          _ = 2 ^ (K + τ) := by
              rw [← pow_add]
              congr 1
              omega
    _ = (K + τ + 1) * 2 ^ (K + τ) := by simp

/-- **Length bound.**  A valid history has at most `2^K + 2^(K+τ+1) + 2^(S+1)` events.
Proof: each event is a point, set or table event; the set events have cost `≤ K + τ`, so their
number is `∑_{i ≤ K+τ} costCount i ≤ ∑_{i ≤ K+τ} 2^i < 2^(K+τ+1)`.
Reference: L21 ("the event family is finite"). -/
theorem length_le_of_validHistory {G : ResGame α} {K τ S : ℕ} {evs : List (ResEvent α)}
    (hv : ValidHistory G K τ S evs) : evs.length ≤ 2 ^ K + 2 ^ (K + τ + 1) + 2 ^ (S + 1) := by
  have key : ∀ l : List (ResEvent α), (∀ Q i, ResEvent.set Q i ∈ l → i ≤ K + τ) →
      l.length = pointCount l + (∑ i ∈ Finset.range (K + τ + 1), costCount l i) +
        tableCount l := by
    intro l
    induction l with
    | nil => intro _; simp [pointCount, costCount, tableCount]
    | cons e l ih =>
      intro hl
      have ih' := ih (fun Q i h => hl Q i (List.mem_cons_of_mem _ h))
      cases e with
      | point u =>
        have e1 : pointCount (ResEvent.point u :: l) = pointCount l + 1 := by
          simp [pointCount, List.countP_cons, ResEvent.isPoint]
        have e2 : ∀ i, costCount (ResEvent.point u :: l) i = costCount l i := by
          intro i
          simp [costCount, ResEvent.hasCost]
        have e3 : tableCount (ResEvent.point u :: l) = tableCount l := by
          simp [tableCount, ResEvent.isTable]
        have hs : ∑ i ∈ Finset.range (K + τ + 1), costCount (ResEvent.point u :: l) i =
            ∑ i ∈ Finset.range (K + τ + 1), costCount l i := Finset.sum_congr rfl fun i _ => e2 i
        rw [e1, e3, hs, List.length_cons]
        omega
      | set Q j =>
        have hj : j ≤ K + τ := hl Q j (by simp)
        have e1 : pointCount (ResEvent.set Q j :: l) = pointCount l := by
          simp [pointCount, ResEvent.isPoint]
        have e2 : ∀ i, costCount (ResEvent.set Q j :: l) i =
            costCount l i + if j = i then 1 else 0 := by
          intro i
          simp [costCount, List.countP_cons, ResEvent.hasCost]
        have e3 : tableCount (ResEvent.set Q j :: l) = tableCount l := by
          simp [tableCount, ResEvent.isTable]
        have hjr : j ∈ Finset.range (K + τ + 1) := Finset.mem_range.mpr (by omega)
        have hs : ∑ i ∈ Finset.range (K + τ + 1), costCount (ResEvent.set Q j :: l) i =
            ∑ i ∈ Finset.range (K + τ + 1), costCount l i + 1 := by
          rw [Finset.sum_congr rfl fun i _ => e2 i, Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp only [hjr, ↓reduceIte]
        rw [e1, e3, hs, List.length_cons]
        omega
      | table P =>
        have e1 : pointCount (ResEvent.table P :: l) = pointCount l := by
          simp [pointCount, ResEvent.isPoint]
        have e2 : ∀ i, costCount (ResEvent.table P :: l) i = costCount l i := by
          intro i
          simp [costCount, ResEvent.hasCost]
        have e3 : tableCount (ResEvent.table P :: l) = tableCount l + 1 := by
          simp [tableCount, List.countP_cons, ResEvent.isTable]
        have hs : ∑ i ∈ Finset.range (K + τ + 1), costCount (ResEvent.table P :: l) i =
            ∑ i ∈ Finset.range (K + τ + 1), costCount l i := Finset.sum_congr rfl fun i _ => e2 i
        rw [e1, e3, hs, List.length_cons]
        omega
  have hgeom : ∀ n, ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  have hlen := key evs fun Q i h => (hv.set_elig Q i h).1
  have hcost : ∑ i ∈ Finset.range (K + τ + 1), costCount evs i ≤
      ∑ i ∈ Finset.range (K + τ + 1), 2 ^ i :=
    Finset.sum_le_sum fun i _ => hv.cost_count i
  have h1 := hgeom (K + τ + 1)
  have h2 := hv.point_count
  have h3 := hv.table_count
  omega

/-! ### L16: availability of the reservoir choice -/

/-- **Union bound for the bad sets.**  Summed over all centers, the bad sets have total size at
most `N |marks|` plus the sum over the known tables of their heavy-point counts.
Proof: `badSet ⊆ (S_z ∩ marks) ∪ ⋃_{P ∈ tables} tableHeavyPoints P z`; `card_union_le` and a
list union bound give the pointwise inequality; then swap sums (`Finset.sum_comm`) and use
`∑_{z ∈ cube} |S_z ∩ marks| = ∑_{u ∈ marks} #{z ∈ cube : u ∈ S_z} ≤ N |marks|` (double counting,
`Finset.sum_card_inter`-style, with `hinc` and `List.toFinset_card_of_nodup`).
Reference: paper, proof of Lemma `lem:ham-reservoir` ("A uniform sphere contains on average...");
L16. -/
theorem sum_card_badSet_le (G : ResGame α) (marks : Finset α) (tables : List (List (Finset α)))
    (hnodup : G.centers.Nodup)
    (hinc : ∀ u, (G.centers.filter fun z => decide (u ∈ G.sphere z)).length ≤ G.N) :
    ((∑ z ∈ G.cube, (badSet G marks tables z).card : ℕ) : ℝ) ≤
      (G.N : ℝ) * marks.card +
        (tables.map fun P => ((∑ z ∈ G.cube, (tableHeavyPoints G P z).card : ℕ) : ℝ)).sum := by
  classical
  have hU : ∀ l : List (Finset α), (listUnion l).card ≤ (l.map Finset.card).sum := by
    intro l
    induction l with
    | nil => simp [listUnion]
    | cons Q l ih =>
      change (Q ∪ listUnion l).card ≤ _
      rw [List.map_cons, List.sum_cons]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)
  have hpt : ∀ z, (badSet G marks tables z).card ≤ (marks.filter (· ∈ G.sphere z)).card +
      (tables.map fun P => (tableHeavyPoints G P z).card).sum := by
    intro z
    have hsub : badSet G marks tables z ⊆ (marks.filter (· ∈ G.sphere z)) ∪
        listUnion (tables.map fun P => tableHeavyPoints G P z) := by
      intro u hu
      rw [badSet, Finset.mem_filter] at hu
      rcases hu.2 with hm | ⟨P, hP, Q, hQ, huQ, hh⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hu.1⟩)
      · refine Finset.mem_union_right _ (mem_listUnion.mpr
          ⟨tableHeavyPoints G P z, List.mem_map.mpr ⟨P, hP, rfl⟩, ?_⟩)
        exact Finset.mem_filter.mpr ⟨hu.1, Q, hQ, huQ, hh⟩
    have h2 := hU (tables.map fun P => tableHeavyPoints G P z)
    rw [List.map_map] at h2
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left h2 _))
  have hinc' : ∀ u, (G.cube.filter fun z => u ∈ G.sphere z).card ≤ G.N := by
    intro u
    have heq : (G.cube.filter fun z => u ∈ G.sphere z) =
        (G.centers.filter fun z => decide (u ∈ G.sphere z)).toFinset := by
      ext z
      simp [ResGame.cube]
    rw [heq, List.toFinset_card_of_nodup (hnodup.filter _)]
    exact hinc u
  have hmarks : ∑ z ∈ G.cube, (marks.filter (· ∈ G.sphere z)).card ≤ G.N * marks.card := by
    calc ∑ z ∈ G.cube, (marks.filter (· ∈ G.sphere z)).card
        = ∑ z ∈ G.cube, ∑ u ∈ marks, if u ∈ G.sphere z then 1 else 0 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.card_filter]
      _ = ∑ u ∈ marks, ∑ z ∈ G.cube, if u ∈ G.sphere z then 1 else 0 := Finset.sum_comm
      _ = ∑ u ∈ marks, (G.cube.filter fun z => u ∈ G.sphere z).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.card_filter]
      _ ≤ ∑ _u ∈ marks, G.N := Finset.sum_le_sum fun u _ => hinc' u
      _ = G.N * marks.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hswap : ∀ l : List (List (Finset α)),
      ∑ z ∈ G.cube, (l.map fun P => (tableHeavyPoints G P z).card).sum =
        (l.map fun P => ∑ z ∈ G.cube, (tableHeavyPoints G P z).card).sum := by
    intro l
    induction l with
    | nil => simp
    | cons P l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  have htot : ∑ z ∈ G.cube, (badSet G marks tables z).card ≤ G.N * marks.card +
      (tables.map fun P => ∑ z ∈ G.cube, (tableHeavyPoints G P z).card).sum := by
    calc ∑ z ∈ G.cube, (badSet G marks tables z).card
        ≤ ∑ z ∈ G.cube, ((marks.filter (· ∈ G.sphere z)).card +
            (tables.map fun P => (tableHeavyPoints G P z).card).sum) :=
          Finset.sum_le_sum fun z _ => hpt z
      _ = _ := by rw [Finset.sum_add_distrib, hswap]
      _ ≤ _ := Nat.add_le_add_right hmarks _
  have hcast : ((tables.map fun P => ∑ z ∈ G.cube, (tableHeavyPoints G P z).card).sum : ℝ) =
      (tables.map fun P => ((∑ z ∈ G.cube, (tableHeavyPoints G P z).card : ℕ) : ℝ)).sum := by
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  calc ((∑ z ∈ G.cube, (badSet G marks tables z).card : ℕ) : ℝ)
      ≤ ((G.N * marks.card +
          (tables.map fun P => ∑ z ∈ G.cube, (tableHeavyPoints G P z).card).sum : ℕ) : ℝ) := by
        exact_mod_cast htot
    _ = _ := by rw [Nat.cast_add, Nat.cast_mul, hcast]

/-- **Union bound over the tables.**  If each of the known tables contributes at most `b`, the
list sum is at most `#tables · b`.
Proof: `List.sum_le_card_nsmul` on the mapped list, `List.length_map`, `nsmul_eq_mul`. -/
theorem sum_map_le_length_mul {β : Type*} (l : List β) (f : β → ℝ) (b : ℝ)
    (h : ∀ x ∈ l, f x ≤ b) : (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [add_mul, one_mul]
    linarith

/-- **Finite averaging.**  If `∑_{z ∈ s} f z ≤ |s| b` over a nonempty finite set, some `z ∈ s`
has `f z ≤ b`.
Proof: otherwise `∑ f > ∑ b = |s| b` (`Finset.sum_lt_sum_of_nonempty`).
Reference: L16 ("Prove explicitly that a finite average bound supplies a passing center"). -/
theorem exists_le_of_sum_le {β : Type*} (s : Finset β) (hs : s.Nonempty) (f : β → ℕ) (b : ℝ)
    (h : ((∑ z ∈ s, f z : ℕ) : ℝ) ≤ s.card * b) : ∃ z ∈ s, (f z : ℝ) ≤ b := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hlt : ∑ _z ∈ s, b < ∑ z ∈ s, ((f z : ℕ) : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hs fun z hz => hcon z hz
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  push_cast at h
  linarith

/-- **The first passing center.**  If some center passes the choice test, `chooseCenter` returns
a center of the list that passes it.
Proof: `List.find?_isSome` gives `some z`; `List.find?_some` gives the test,
`List.mem_of_find?_eq_some` the membership. -/
theorem chooseCenter_spec (G : ResGame α) (marks : Finset α) (tables : List (List (Finset α)))
    (h : ∃ z ∈ G.centers, 32 * (badSet G marks tables z).card ≤ G.N) :
    ∃ z, chooseCenter G marks tables = some z ∧ z ∈ G.centers ∧
      32 * (badSet G marks tables z).card ≤ G.N := by
  obtain ⟨z, hz, hp⟩ := h
  have hsome : (G.centers.find? fun z =>
      decide (32 * (badSet G marks tables z).card ≤ G.N)).isSome := by
    rw [List.find?_isSome]
    exact ⟨z, hz, by simpa using hp⟩
  obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨z', hz', List.mem_of_find?_eq_some hz', ?_⟩
  simpa using List.find?_some hz'

/-- **A center passing the choice test exists** (the averaging step of node L16).  If the marked
set has `256 |marks| ≤ |cube|`, and there are at most `2^(S+1)` known tables, all exact
partitions, then some center has `32 |B_z| ≤ N`: the expected marked fraction and the expected
heavy fraction of a sphere are each at most `1/256`. -/
theorem exists_good_center {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (marks : Finset α) (tables : List (List (Finset α)))
    (hmarks : 256 * marks.card ≤ G.centers.length) (htab : tables.length ≤ 2 ^ (S + 1))
    (hvalid : ∀ P ∈ tables, IsCellPartition G.cube P) :
    ∃ z ∈ G.centers, 32 * (badSet G marks tables z).card ≤ G.N := by
  have hcube : G.cube.card = G.centers.length := List.toFinset_card_of_nodup hG.centers_nodup
  have hne : G.cube.Nonempty := by
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hG.centers_ne_nil
    exact ⟨z, List.mem_toFinset.mpr hz⟩
  set c : ℝ := (G.cube.card : ℝ)
  set n : ℝ := (G.N : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hθ := hG.theta_nonneg
  have h1 := sum_card_badSet_le G marks tables hG.centers_nodup hG.incidence
  have h2 := sum_map_le_length_mul tables
    (fun P => ((∑ z ∈ G.cube, (tableHeavyPoints G P z).card : ℕ) : ℝ)) (c * n * θ)
    (fun P hP => hG.heavy_bound P (hvalid P hP))
  have hL : (tables.length : ℝ) ≤ (2 : ℝ) ^ (S + 1) := by exact_mod_cast htab
  have hA : (tables.length : ℝ) * (c * n * θ) ≤ c * n / 256 := by
    have hcn : 0 ≤ c * n := mul_nonneg hc hn
    calc (tables.length : ℝ) * (c * n * θ) = (tables.length * θ) * (c * n) := by ring
      _ ≤ ((2 : ℝ) ^ (S + 1) * θ) * (c * n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hθ) hcn
      _ ≤ (1 / 256) * (c * n) := mul_le_mul_of_nonneg_right hG.heavy hcn
      _ = c * n / 256 := by ring
  have hB : n * (marks.card : ℝ) ≤ c * n / 256 := by
    have : (256 * marks.card : ℝ) ≤ c := by
      rw [show c = (G.cube.card : ℝ) from rfl, hcube]; exact_mod_cast hmarks
    nlinarith
  have hsum : ((∑ z ∈ G.cube, (badSet G marks tables z).card : ℕ) : ℝ) ≤ c * (n / 128) := by
    linarith
  obtain ⟨z, hz, hle⟩ := exists_le_of_sum_le G.cube hne _ (n / 128) hsum
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have : ((32 * (badSet G marks tables z).card : ℕ) : ℝ) ≤ G.N := by
    push_cast; linarith
  exact_mod_cast this

/-- The reservoir lies in the sphere of the chosen center.
Proof: unfold `chooseReservoir`; in the `some` case `S_z \ B_z ⊆ S_z`, in the fallback case the
reservoir is empty. -/
theorem chooseReservoir_subset_sphere (G : ResGame α) (marks : Finset α)
    (tables : List (List (Finset α))) :
    (chooseReservoir G marks tables).2 ⊆ G.sphere (chooseReservoir G marks tables).1 := by
  unfold chooseReservoir
  split
  · exact Finset.sdiff_subset
  · exact Finset.empty_subset _

/-- The reservoir avoids the marked points.
Proof: marked points of `S_z` lie in `B_z`, which is removed; the fallback is empty. -/
theorem chooseReservoir_disjoint_marks (G : ResGame α) (marks : Finset α)
    (tables : List (List (Finset α))) : Disjoint (chooseReservoir G marks tables).2 marks := by
  unfold chooseReservoir
  split
  · rw [Finset.disjoint_left]
    intro u hu hm
    rw [Finset.mem_sdiff] at hu
    exact hu.2 (Finset.mem_filter.mpr ⟨hu.1, Or.inl hm⟩)
  · exact Finset.disjoint_empty_left _

/-- **Light cells after a choice.**  For every cell `Q` of a known table with `2^ℓ ≤ |Q|`, the
new reservoir satisfies `2^δ |Q ∩ W| ≤ |Q|`.
Proof: if `Q` is heavy for the chosen `z`, every point of `Q ∩ S_z` is in `B_z`, so
`Q ∩ W = ∅`; otherwise `2^δ |Q ∩ S_z| ≤ |Q|` and `Q ∩ W ⊆ Q ∩ S_z`.  The fallback reservoir is
empty.  Reference: paper ("If the cell was heavy then all its sphere points were deleted at that
choice"); L16, L19. -/
theorem chooseReservoir_light (G : ResGame α) (marks : Finset α)
    (tables : List (List (Finset α))) :
    ∀ P ∈ tables, ∀ Q ∈ P, 2 ^ G.ell ≤ Q.card →
      2 ^ G.delta * (Q ∩ (chooseReservoir G marks tables).2).card ≤ Q.card := by
  intro P hP Q hQ hℓ
  unfold chooseReservoir
  split
  · rename_i z _
    by_cases hh : IsHeavyCell G z Q
    · have hempty : Q ∩ (G.sphere z \ badSet G marks tables z) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        rw [Finset.mem_inter, Finset.mem_sdiff] at hu
        exact hu.2.2 (Finset.mem_filter.mpr ⟨hu.2.1, Or.inr ⟨P, hP, Q, hQ, hu.1, hh⟩⟩)
      change 2 ^ G.delta * (Q ∩ (G.sphere z \ badSet G marks tables z)).card ≤ Q.card
      rw [hempty, Finset.card_empty, Nat.mul_zero]
      exact Nat.zero_le _
    · have h1 : ¬ Q.card < 2 ^ G.delta * (Q ∩ G.sphere z).card := fun h => hh ⟨hℓ, h⟩
      have h2 : (Q ∩ (G.sphere z \ badSet G marks tables z)).card ≤ (Q ∩ G.sphere z).card :=
        Finset.card_le_card (Finset.inter_subset_inter (subset_refl _) Finset.sdiff_subset)
      change 2 ^ G.delta * (Q ∩ (G.sphere z \ badSet G marks tables z)).card ≤ Q.card
      exact (Nat.mul_le_mul_left _ h2).trans (not_lt.mp h1)
  · change 2 ^ G.delta * (Q ∩ ∅).card ≤ Q.card
    rw [Finset.inter_empty, Finset.card_empty, Nat.mul_zero]
    exact Nat.zero_le _

/-- **Size of a passing choice.**  If the first passing center is `z`, the reservoir is
`S_z \ B_z` and `32 |S_z \ B_z| ≥ 31 N`.
Proof: unfold `chooseReservoir` at `some z`; `B_z ⊆ S_z` (`filter_subset`),
`card_sdiff_add_card_eq_card`, `|S_z| = N`, and `32 |B_z| ≤ N`. -/
theorem chooseReservoir_of_chooseCenter (G : ResGame α) (marks : Finset α)
    (tables : List (List (Finset α))) {z : α} (hz : chooseCenter G marks tables = some z)
    (hcard : (G.sphere z).card = G.N) (hbad : 32 * (badSet G marks tables z).card ≤ G.N) :
    chooseReservoir G marks tables = (z, G.sphere z \ badSet G marks tables z) ∧
      31 * G.N ≤ 32 * (G.sphere z \ badSet G marks tables z).card := by
  have heq : chooseReservoir G marks tables = (z, G.sphere z \ badSet G marks tables z) := by
    unfold chooseReservoir
    rw [hz]
  refine ⟨heq, ?_⟩
  have hsub : badSet G marks tables z ⊆ G.sphere z := Finset.filter_subset _ _
  have := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- **Choose reservoir** (blueprint node L16).  Under the game hypotheses, for marked points with
`256 |marks| ≤ |cube|` (supplied by the density inequality and the L14 counts) and at most
`2^(S+1)` known tables, all exact partitions, the canonical search finds a center `z` of the cube
with `32 |B_z| ≤ N`; the reservoir is `S_z \ B_z`, of size at least `31 N / 32`, disjoint from
all marked points, and every large cell of a known table meets it lightly. -/
theorem chooseReservoir_spec {G : ResGame α} {K τ S : ℕ} {θ : ℝ} (hG : GameHyp G K τ S θ)
    (marks : Finset α) (tables : List (List (Finset α)))
    (hmarks : 256 * marks.card ≤ G.centers.length) (htab : tables.length ≤ 2 ^ (S + 1))
    (hvalid : ∀ P ∈ tables, IsCellPartition G.cube P) :
    (chooseReservoir G marks tables).1 ∈ G.centers ∧
      32 * (badSet G marks tables (chooseReservoir G marks tables).1).card ≤ G.N ∧
      (chooseReservoir G marks tables).2 =
        G.sphere (chooseReservoir G marks tables).1 \
          badSet G marks tables (chooseReservoir G marks tables).1 ∧
      31 * G.N ≤ 32 * (chooseReservoir G marks tables).2.card ∧
      (chooseReservoir G marks tables).2 ⊆ G.sphere (chooseReservoir G marks tables).1 ∧
      Disjoint (chooseReservoir G marks tables).2 marks ∧
      (∀ P ∈ tables, ∀ Q ∈ P, 2 ^ G.ell ≤ Q.card →
        2 ^ G.delta * (Q ∩ (chooseReservoir G marks tables).2).card ≤ Q.card) := by
  obtain ⟨z, hz, hzc, hbad⟩ :=
    chooseCenter_spec G marks tables (exists_good_center hG marks tables hmarks htab hvalid)
  obtain ⟨heq, hbig⟩ :=
    chooseReservoir_of_chooseCenter G marks tables hz (hG.sphere_card z hzc) hbad
  refine ⟨?_, ?_, ?_, ?_, chooseReservoir_subset_sphere G marks tables,
    chooseReservoir_disjoint_marks G marks tables, chooseReservoir_light G marks tables⟩ <;>
    rw [heq] <;> assumption

/-! ### L17: the transition rules -/

/-- **Each transition emits at most one center**, and when it emits one it is the new center.
Proof: unfold `reservoirTransition`, `pointStep`, `setStep`, `tableStep`, `ordinaryCheck`,
`reselect`; split on the `if`s; every branch either keeps `emitted` or conses the new center. -/
theorem reservoirTransition_emitted (G : ResGame α) (st : ReservoirState α) (e : ResEvent α) :
    (reservoirTransition G st e).emitted = st.emitted ∨
      (reservoirTransition G st e).emitted = (reservoirTransition G st e).center :: st.emitted := by
  have key : ∀ st' : ReservoirState α, (st'.ordinaryCheck G).emitted = st'.emitted ∨
      (st'.ordinaryCheck G).emitted = (st'.ordinaryCheck G).center :: st'.emitted := by
    intro st'
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  cases e with
  | point u =>
    exact key
      { st with
        marks := insert u st.marks
        live := st.live.erase u
        pointCharge := st.pointCharge + if u ∈ st.live then 1 else 0 }
  | set Q i =>
    simp only [reservoirTransition, ReservoirState.setStep]
    split_ifs
    · exact key _
    · exact key _
  | table P => exact Or.inr rfl

/-- **Ordinary reset rule.**  The reset test performs an ordinary reset (and increments the reset
counter) exactly when `8 |W| < 7 N`; point and set events apply it after their deletions.
Proof: unfold `ordinaryCheck`; `split_ifs`; `omega`. -/
theorem ordinaryCheck_reset_iff (G : ResGame α) (st : ReservoirState α) :
    (st.ordinaryCheck G).ordinaryResets = st.ordinaryResets + 1 ↔
      8 * st.live.card < 7 * G.N := by
  unfold ReservoirState.ordinaryCheck
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **Monotonicity of the board.**  A transition never removes a known table, a marked vertex or
a marked cell (permanent marks).
Proof: unfold the three steps; `ordinaryCheck` and `reselect` do not touch these fields, and the
steps only add to them (`subset_insert`, `subset_union_left`, `List.mem_cons_of_mem`,
`List.mem_append_right`).  Reference: L18 ("Known tables and permanent marks are monotone"). -/
theorem reservoirTransition_mono (G : ResGame α) (st : ReservoirState α) (e : ResEvent α) :
    (∀ P ∈ st.tables, P ∈ (reservoirTransition G st e).tables) ∧
      st.marks ⊆ (reservoirTransition G st e).marks ∧
      ∀ Q ∈ st.markedCells, Q ∈ (reservoirTransition G st e).markedCells := by
  have hoc : ∀ st' : ReservoirState α, (st'.ordinaryCheck G).tables = st'.tables ∧
      (st'.ordinaryCheck G).marks = st'.marks ∧
      (st'.ordinaryCheck G).markedCells = st'.markedCells := by
    intro st'
    unfold ReservoirState.ordinaryCheck
    split_ifs
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  cases e with
  | point u =>
    set st' : ReservoirState α :=
      { st with
        marks := insert u st.marks
        live := st.live.erase u
        pointCharge := st.pointCharge + if u ∈ st.live then 1 else 0 } with hst'
    obtain ⟨h1, h2, h3⟩ := hoc st'
    refine ⟨fun P hP => ?_, ?_, fun Q hQ => ?_⟩
    · change P ∈ (st'.ordinaryCheck G).tables
      rw [h1]
      exact hP
    · change st.marks ⊆ (st'.ordinaryCheck G).marks
      rw [h2]
      exact Finset.subset_insert u st.marks
    · change Q ∈ (st'.ordinaryCheck G).markedCells
      rw [h3]
      exact hQ
  | set Q i =>
    change (∀ P ∈ st.tables, P ∈ (st.setStep G Q i).tables) ∧
      st.marks ⊆ (st.setStep G Q i).marks ∧
      ∀ Q' ∈ st.markedCells, Q' ∈ (st.setStep G Q i).markedCells
    unfold ReservoirState.setStep
    split_ifs
    · refine ⟨fun P hP => ?_, ?_, fun Q' hQ' => ?_⟩
      · rw [(hoc _).1]
        exact hP
      · rw [(hoc _).2.1]
        exact Finset.subset_union_left
      · rw [(hoc _).2.2]
        exact List.mem_cons_of_mem _ hQ'
    · refine ⟨fun P hP => ?_, ?_, fun Q' hQ' => ?_⟩
      · rw [(hoc _).1]
        exact hP
      · rw [(hoc _).2.1]
      · rw [(hoc _).2.2]
        exact hQ'
  | table P =>
    refine ⟨fun P' hP' => ?_, ?_, fun Q hQ => ?_⟩
    · exact List.mem_cons_of_mem _ hP'
    · exact Finset.subset_union_left
    · exact List.mem_append_right _ hQ

/-- **Ordinary reset rule for point events.**  A point event performs an ordinary reset exactly
when `8 |W \ {u}| < 7 N`.
Proof: unfold `pointStep`, `ordinaryCheck`; `split_ifs`; the counter is incremented exactly in
the reset branch. -/
theorem pointStep_reset_iff (G : ResGame α) (st : ReservoirState α) (u : α) :
    (st.pointStep G u).ordinaryResets = st.ordinaryResets + 1 ↔
      8 * (st.live.erase u).card < 7 * G.N := by
  exact ordinaryCheck_reset_iff G
    { st with
      marks := insert u st.marks
      live := st.live.erase u
      pointCharge := st.pointCharge + if u ∈ st.live then 1 else 0 }

/-- **Reservoir transition** (blueprint node L17).  The deterministic transition
`reservoirTransition` emits at most one center per event, the new center; a table event (atomic:
add the table, activate the stored cells, then the forced choice) emits exactly one center; a
point event performs an ordinary reset iff `8 |W| < 7 N` after the deletion. -/
theorem reservoirTransition_spec (G : ResGame α) (st : ReservoirState α) :
    (∀ e, (reservoirTransition G st e).emitted = st.emitted ∨
      (reservoirTransition G st e).emitted = (reservoirTransition G st e).center :: st.emitted) ∧
    (∀ P, (reservoirTransition G st (.table P)).emitted =
      (reservoirTransition G st (.table P)).center :: st.emitted) ∧
    (∀ u, (reservoirTransition G st (.point u)).ordinaryResets = st.ordinaryResets + 1 ↔
      8 * (st.live.erase u).card < 7 * G.N) :=
  ⟨reservoirTransition_emitted G st, fun _ => rfl, pointStep_reset_iff G st⟩

/-- **Emitted centers grow by appending** along a growing history (used by the occurrence code,
node L22).
Proof: induction on the appended suffix with `run_append_singleton` and
`reservoirTransition_emitted`: `emitted` is unchanged or gains one element at its head, so its
reverse gains one element at its end. -/
theorem emittedCenters_prefix (G : ResGame α) {l₁ l₂ : List (ResEvent α)} (h : l₁ <+: l₂) :
    emittedCenters G l₁ <+: emittedCenters G l₂ := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton t e ih =>
    refine ih.trans ?_
    rw [← List.append_assoc]
    unfold emittedCenters
    rw [run_append_singleton]
    rcases reservoirTransition_emitted G (run G (l₁ ++ t)) e with h | h
    · rw [h]
    · rw [h, List.reverse_cons]
      exact List.prefix_append _ _

end Kolmogorov.StrongMerging.Lower
