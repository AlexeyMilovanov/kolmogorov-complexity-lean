import KolmogorovMathlib.Complexity.GeneralScheme.Frequencies.MaximalFrequency

/-!
# Partial Sequences

Frequencies of partial computable sequences. For a partial computable `f : ℕ →. ℕ`, the lower
frequency `lowerFreqPart f k` counts the `i < N` at which `f` is defined with value `k`, divided
by `N`.

The main declaration is `exists_computable_lowerFreqPart_le` (SUV Problem 213, Section 6.4.3):
there is a total computable sequence `g` whose lower frequencies are at least those of `f`.
The proof bounds the `liminf` of the (lower semicomputable) frequency semimeasures by a
`0'`-lower-semicomputable semimeasure, built by a run that performs raising requests one at a
time as long as every row stays a semimeasure, and then applies Theorem 136.
-/

namespace Kolmogorov
namespace GeneralScheme

/-- Row-safety of a finite list of raising requests `(N, k, ε)` (used in the proof of
`exists_computable_lowerFreqPart_le_liminf_bound`): for every row `n` there is a
semimeasure `ρ` (all finite partial sums `≤ 1`) that dominates `m (·, n)` and, for every request
`(N, k, ε)` of the list with `N ≤ n`, also `ε` at the place `k`. Equivalently, after raising
`m (k, n)` to at least `ε` for all `n ≥ N` and every request, all rows are still semimeasures. -/
private def exists_computable_lowerFreqPart_le_liminf_bound_safe
    (m : ℕ × ℕ → ℝ) (L : List (ℕ × ℕ × ℚ)) : Prop :=
  ∀ n : ℕ, ∃ ρ : ℕ → ℝ, (∀ k, m (k, n) ≤ ρ k) ∧
    (∀ t ∈ L, t.1 ≤ n → (t.2.2 : ℝ) ≤ ρ t.2.1) ∧ ∀ N, ∑ k ∈ Finset.range N, ρ k ≤ 1

open Classical in
/-- The run of the construction in the proof of
`exists_computable_lowerFreqPart_le_liminf_bound`: the list of the requests performed among
the first `j` triples `(N, k, ε)` (in the order of `Denumerable.ofNat (ℕ × ℕ × ℚ)`). The `j`-th
triple is performed iff the rows stay semimeasures after adding it. -/
private noncomputable def exists_computable_lowerFreqPart_le_liminf_bound_stage
    (m : ℕ × ℕ → ℝ) : ℕ → List (ℕ × ℕ × ℚ)
  | 0 => []
  | j + 1 =>
    if exists_computable_lowerFreqPart_le_liminf_bound_safe m
        (Denumerable.ofNat (ℕ × ℕ × ℚ) j ::
          exists_computable_lowerFreqPart_le_liminf_bound_stage m j)
    then Denumerable.ofNat (ℕ × ℕ × ℚ) j ::
      exists_computable_lowerFreqPart_le_liminf_bound_stage m j
    else exists_computable_lowerFreqPart_le_liminf_bound_stage m j

/-- The value `q k`: the supremum of the `ε` of the performed requests `(N, k, ε)`. -/
private noncomputable def exists_computable_lowerFreqPart_le_liminf_bound_q
    (m : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ (j N : ℕ) (ε : ℚ),
    (N, k, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j ∧ x = ε}

/-- A list of requests `(N, k, ε)` raises the value at `k` of row `n` above `r`. -/
private def exists_computable_lowerFreqPart_le_unsafe_re_raised
    (L : List (ℕ × ℕ × ℚ)) (n i : ℕ) (r : ℚ) : Bool :=
  L.any (fun t => decide (t.1 ≤ n) && decide (t.2.1 = i) && decide (r < t.2.2))

private theorem exists_computable_lowerFreqPart_le_unsafe_re_raised_iff
    (L : List (ℕ × ℕ × ℚ)) (n i : ℕ) (r : ℚ) :
    exists_computable_lowerFreqPart_le_unsafe_re_raised L n i r = true ↔
      ∃ t ∈ L, t.1 ≤ n ∧ t.2.1 = i ∧ r < t.2.2 := by
  simp [exists_computable_lowerFreqPart_le_unsafe_re_raised,
    List.any_eq_true, and_assoc]

private theorem exists_computable_lowerFreqPart_le_unsafe_re_computable_raised :
    Computable (fun x : List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ =>
      exists_computable_lowerFreqPart_le_unsafe_re_raised
        x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold exists_computable_lowerFreqPart_le_unsafe_re_raised
  refine computable_list_any (f := fun x : List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ => x.1)
    (p := fun x t => decide (t.1 ≤ x.2.1) && decide (t.2.1 = x.2.2.1) && decide (x.2.2.2 < t.2.2))
    Computable.fst ?_
  have ht1 : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.2.1) :=
    Computable.fst.comp Computable.snd
  have ht2 : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have ht3 : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hn : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hi : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hr : Computable (fun y : (List (ℕ × ℕ × ℚ) × ℕ × ℕ × ℚ) × (ℕ × ℕ × ℚ) => y.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have h1 := (PrimrecRel.decide Primrec.nat_le).to_comp.comp ht1 hn
  have h2 := (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp ht2 hi
  have h3 := computable₂_ratLt.comp hr ht3
  exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp h1 h2) h3).to₂

/-- Bounded conjunction of enumerable predicates is enumerable. -/
private theorem exists_computable_lowerFreqPart_le_unsafe_re_bforall
    {α : Type*} [Primcodable α] (A : Set ℕ) (F : α × ℕ → Prop)
    (hF : PointToSet.IsREIn A F) (n : α → ℕ) (hn : ComputableIn {charOracle A} n) :
    PointToSet.IsREIn A (fun a => ∀ i < n a, F (a, i)) := by
  obtain ⟨f, hf, hdom⟩ := hF
  have hh : PartrecIn₂ {charOracle A} (fun (a : α) (p : ℕ × ℕ) => f (a, p.1)) :=
    hf.comp (ComputableIn.pair ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd))
  have hg : PartrecIn {charOracle A} (fun _ : α => (Part.some (0 : ℕ))) :=
    (ComputableIn.const (0 : ℕ)).partrecIn
  have := PointToSet.relative_closure_nat_rec A n (fun _ => Part.some 0)
    (fun a p => f (a, p.1)) hn hg hh
  refine ⟨_, this, fun a => ?_⟩
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => Part ℕ) (Part.some (0:ℕ))
        (fun i ih => ih.bind fun b => f (a, (i, b).1)) m).Dom
      ↔ ∀ i < m, F (a, i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Part.bind_dom]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h1 i h
        · subst h; exact (hdom _).mpr h2
      · intro h
        exact ⟨fun i hi => h i (by omega), (hdom _).mp (h m (by omega))⟩
  exact (key (n a)).symm

/-- A decidable computable disjunct can be added to an enumerable predicate. -/
private theorem exists_computable_lowerFreqPart_le_unsafe_re_or_decide
    {α : Type*} [Primcodable α] {A : Set ℕ} {F : α → Prop} (hF : PointToSet.IsREIn A F)
    (b : α → Bool) (hb : Computable b) :
    PointToSet.IsREIn A (fun a => b a = true ∨ F a) := by
  obtain ⟨f, hf, hdom⟩ := hF
  refine ⟨fun a => cond (b a) (Part.some 0) (f a),
    PartrecIn.cond hb.computableIn (ComputableIn.const 0).partrecIn hf, fun a => ?_⟩
  cases hba : b a <;> simp [hdom, hba]

/-- Rational lower approximations of a finite sum exceeding `1`. -/
private theorem exists_computable_lowerFreqPart_le_unsafe_re_rs_of_sum
    (c : ℕ → ℝ) (N : ℕ) (h : 1 < ∑ i ∈ Finset.range N, c i) :
    ∃ rs : List ℚ, rs.length = N ∧ (∀ i < rs.length, ((rs.getD i 0 : ℚ) : ℝ) < c i) ∧
      1 < ∑ i ∈ Finset.range rs.length, ((rs.getD i 0 : ℚ) : ℝ) := by
  set δ := ∑ i ∈ Finset.range N, c i - 1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ε : ℝ := δ / (N + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hex : ∀ i, ∃ r : ℚ, c i - ε < r ∧ (r : ℝ) < c i := fun i =>
    exists_rat_btwn (by linarith)
  choose r hr1 hr2 using hex
  refine ⟨(List.range N).map r, by simp, ?_, ?_⟩
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    simpa [List.getD_eq_getElem?_getD, hi] using hr2 i
  · simp only [List.length_map, List.length_range]
    have hg : ∀ i ∈ Finset.range N, ((((List.range N).map r).getD i 0 : ℚ) : ℝ) = r i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp [List.getD_eq_getElem?_getD, hi']
    rw [Finset.sum_congr rfl (fun i hi => by rw [hg i hi])]
    have hle : ∑ i ∈ Finset.range N, (c i - r i) ≤ N * ε := by
      calc ∑ i ∈ Finset.range N, (c i - r i) ≤ ∑ i ∈ Finset.range N, ε :=
            Finset.sum_le_sum (fun i _ => by linarith [hr1 i])
        _ = N * ε := by simp
    have hNε : (N : ℝ) * ε < δ := by
      rw [hε, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have : ∑ i ∈ Finset.range N, (c i - r i)
        = ∑ i ∈ Finset.range N, c i - ∑ i ∈ Finset.range N, (r i : ℝ) := by
      rw [Finset.sum_sub_distrib]
    linarith

/-- Step 1a of the proof of
`exists_computable_lowerFreqPart_le_unsafe_re`: a list is unsafe iff for
some row `n` there are rationals `rᵢ` (`i < |rs|`), each below `m (i, n)` or below a raise at `i`,
with `∑ rᵢ > 1`. -/
private theorem exists_computable_lowerFreqPart_le_unsafe_re_iff
    (m : ℕ × ℕ → ℝ) (L : List (ℕ × ℕ × ℚ)) :
    ¬ exists_computable_lowerFreqPart_le_liminf_bound_safe m L ↔
      ∃ (n : ℕ) (rs : List ℚ), (∀ i < rs.length,
        exists_computable_lowerFreqPart_le_unsafe_re_raised
          L n i (rs.getD i 0) = true ∨ ((rs.getD i 0 : ℚ) : ℝ) < m (i, n)) ∧
        1 < ∑ i ∈ Finset.range rs.length, ((rs.getD i 0 : ℚ) : ℝ) := by
  classical
  constructor
  · intro hns
    by_contra hno
    apply hns
    intro n
    let S : ℕ → Finset ℝ := fun k => insert (m (k, n))
      ((L.toFinset.filter (fun t => t.1 ≤ n ∧ t.2.1 = k)).image (fun t => (t.2.2 : ℝ)))
    have hne : ∀ k, (S k).Nonempty := fun k => ⟨_, Finset.mem_insert_self _ _⟩
    let ρ : ℕ → ℝ := fun k => (S k).max' (hne k)
    have hρ1 : ∀ k, m (k, n) ≤ ρ k := fun k =>
      Finset.le_max' _ _ (Finset.mem_insert_self _ _)
    have hρ2 : ∀ t ∈ L, t.1 ≤ n → (t.2.2 : ℝ) ≤ ρ t.2.1 := by
      intro t ht htn
      have hmem : (t.2.2 : ℝ) ∈ S t.2.1 :=
        Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨t, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ht, htn, rfl⟩, rfl⟩)
      exact Finset.le_max' _ _ hmem
    have hρ3 : ∀ (r : ℚ) (k : ℕ), (r : ℝ) < ρ k →
        exists_computable_lowerFreqPart_le_unsafe_re_raised L n k r = true
          ∨ (r : ℝ) < m (k, n) := by
      intro r k hr
      have hmem : ρ k ∈ S k := Finset.max'_mem _ _
      rcases Finset.mem_insert.mp hmem with h | h
      · right; rwa [h] at hr
      · left
        obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp h
        obtain ⟨htL, htn, htk⟩ := Finset.mem_filter.mp ht
        rw [exists_computable_lowerFreqPart_le_unsafe_re_raised_iff]
        refine ⟨t, List.mem_toFinset.mp htL, htn, htk, ?_⟩
        have : (r : ℝ) < t.2.2 := by rw [hteq]; exact hr
        exact_mod_cast this
    refine ⟨ρ, hρ1, hρ2, fun N => ?_⟩
    by_contra hN
    push Not at hN
    obtain ⟨rs, hlen, hlt, hsum⟩ :=
      exists_computable_lowerFreqPart_le_unsafe_re_rs_of_sum ρ N hN
    exact hno ⟨n, rs, fun i hi => hρ3 _ i (hlt i hi), hsum⟩
  · rintro ⟨n, rs, h1, h2⟩ hsafe
    obtain ⟨ρ, hρm, hρL, hρs⟩ := hsafe n
    have hlt : ∀ i < rs.length, ((rs.getD i 0 : ℚ) : ℝ) < ρ i := by
      intro i hi
      rcases h1 i hi with h | h
      · obtain ⟨t, htL, htn, hti, hrt⟩ :=
          (exists_computable_lowerFreqPart_le_unsafe_re_raised_iff
            _ _ _ _).mp h
        have : ((rs.getD i 0 : ℚ) : ℝ) < t.2.2 := by exact_mod_cast hrt
        have := hρL t htL htn
        rw [hti] at this
        linarith
      · exact lt_of_lt_of_le h (hρm i)
    have : ∑ i ∈ Finset.range rs.length, ((rs.getD i 0 : ℚ) : ℝ) ≤
        ∑ i ∈ Finset.range rs.length, ρ i :=
      Finset.sum_le_sum (fun i hi => (hlt i (Finset.mem_range.mp hi)).le)
    linarith [hρs rs.length]

/-- Step 1 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`:
the negation of the row-safety test is enumerable. If `m` is lower semicomputable without oracle
then the set of lists `L` of requests that are NOT row-safe is enumerable (without oracle): `L`
is unsafe iff for some `n` and `N` the sum `∑_{k<N} max (m (k, n)) (raises of L at k for n)`
exceeds `1` (when all those sums are `≤ 1`, the maxima themselves form the semimeasure `ρ`); each
summand is a maximum of the lower semicomputable `m (k, n)` and finitely many rationals, hence
lower semicomputable uniformly in `(L, n, k)`, and `> 1` is witnessed by rational lower bounds. -/
private theorem exists_computable_lowerFreqPart_le_unsafe_re
    {m : ℕ × ℕ → ℝ} (hm : PointToSet.IsLowerSemicomputableIn (∅ : Set ℕ) m) :
    PointToSet.IsREIn (∅ : Set ℕ)
      (fun L : List (ℕ × ℕ × ℚ) =>
        ¬ exists_computable_lowerFreqPart_le_liminf_bound_safe m L) := by
  classical
  have hcut : PointToSet.IsREIn (∅ : Set ℕ)
      (fun w : (ℕ × ℕ) × ℚ => (w.2 : ℝ) < m w.1) := hm
  have hgetD : Computable₂ (fun (l : List ℚ) (i : ℕ) => l.getD i 0) :=
    (Primrec.list_getD (0 : ℚ)).to_comp
  have hget : Computable (fun x : (List (ℕ × ℕ × ℚ) × ℕ × List ℚ) × ℕ =>
      x.1.2.2.getD x.2 0) :=
    hgetD.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd
  have hR1 : PointToSet.IsREIn (∅ : Set ℕ)
      (fun x : (List (ℕ × ℕ × ℚ) × ℕ × List ℚ) × ℕ =>
        exists_computable_lowerFreqPart_le_unsafe_re_raised
            x.1.1 x.1.2.1 x.2 (x.1.2.2.getD x.2 0) = true ∨
          ((x.1.2.2.getD x.2 0 : ℚ) : ℝ) < m (x.2, x.1.2.1)) := by
    refine exists_computable_lowerFreqPart_le_unsafe_re_or_decide
      (F := fun x : (List (ℕ × ℕ × ℚ) × ℕ × List ℚ) × ℕ =>
        ((x.1.2.2.getD x.2 0 : ℚ) : ℝ) < m (x.2, x.1.2.1)) ?_ _ ?_
    · exact hcut.comp (f := fun x : (List (ℕ × ℕ × ℚ) × ℕ × List ℚ) × ℕ =>
        ((x.2, x.1.2.1), x.1.2.2.getD x.2 0)) (Computable.computableIn
          (Computable.pair (Computable.pair Computable.snd
            (Computable.fst.comp (Computable.snd.comp Computable.fst))) hget))
    · exact exists_computable_lowerFreqPart_le_unsafe_re_computable_raised.comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
            (Computable.pair Computable.snd hget)))
  have hR2 := exists_computable_lowerFreqPart_le_unsafe_re_bforall
    (∅ : Set ℕ) _ hR1 (fun a : List (ℕ × ℕ × ℚ) × ℕ × List ℚ => a.2.2.length)
    (Computable.computableIn (Computable.list_length.comp (Computable.snd.comp Computable.snd)))
  have hR3 : PointToSet.IsREIn (∅ : Set ℕ)
      (fun a : List (ℕ × ℕ × ℚ) × ℕ × List ℚ =>
        1 < ratRangeSumP (fun (l : List ℚ) (i : ℕ) => l.getD i 0) a.2.2 a.2.2.length) := by
    refine PointToSet.isREIn_of_computable_decide ?_
    have hsum : Computable (fun q : List ℚ × ℕ =>
        ratRangeSumP (fun (l : List ℚ) (i : ℕ) => l.getD i 0) q.1 q.2) :=
      computable_ratRangeSumP hgetD
    have hpr : Computable (fun a : List (ℕ × ℕ × ℚ) × ℕ × List ℚ => (a.2.2, a.2.2.length)) :=
      Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.list_length.comp (Computable.snd.comp Computable.snd))
    have hs : Computable (fun a : List (ℕ × ℕ × ℚ) × ℕ × List ℚ =>
        (fun q : List ℚ × ℕ =>
          ratRangeSumP (fun (l : List ℚ) (i : ℕ) => l.getD i 0) q.1 q.2) (a.2.2, a.2.2.length)) :=
      Computable.comp hsum hpr
    exact computable₂_ratLt.comp (Computable.const (1 : ℚ)) hs
  have hR := (hR2.and hR3).exists (β := ℕ × List ℚ)
  obtain ⟨f, hf, hd⟩ := hR
  refine ⟨f, hf, fun L => ?_⟩
  refine Iff.trans
    (exists_computable_lowerFreqPart_le_unsafe_re_iff m L) ?_
  refine Iff.trans ?_ (hd L)
  have hcast : ∀ rs : List ℚ,
      ((ratRangeSumP (fun (l : List ℚ) (i : ℕ) => l.getD i 0) rs rs.length : ℚ) : ℝ) =
        ∑ i ∈ Finset.range rs.length, ((rs.getD i 0 : ℚ) : ℝ) := by
    intro rs
    rw [ratRangeSumP_eq]; push_cast; rfl
  constructor
  · rintro ⟨n, rs, h1, h2⟩
    refine ⟨(n, rs), h1, ?_⟩
    have : (1 : ℝ) < ((ratRangeSumP (fun (l : List ℚ) (i : ℕ) => l.getD i 0) rs rs.length : ℚ) : ℝ)
        := by
      rw [hcast]; exact h2
    exact_mod_cast this
  · rintro ⟨⟨n, rs⟩, h1, h2⟩
    refine ⟨n, rs, h1, ?_⟩
    rw [← hcast]
    exact_mod_cast h2

/-- Auxiliary: an enumerable (without oracle) predicate is the projection of a computable
Boolean test `g a k`. -/
private theorem exists_computable_lowerFreqPart_le_stage_re_aux_semidecide
    {α : Type*} [Primcodable α] {P : α → Prop} (hP : PointToSet.IsREIn (∅ : Set ℕ) P) :
    ∃ g : α → ℕ → Bool, Computable₂ g ∧ ∀ a, P a ↔ ∃ k, g a k = true := by
  obtain ⟨f, hf, hdom⟩ := hP
  have hO : ∀ o ∈ ({charOracle (∅ : Set ℕ)} : Set (ℕ →. ℕ)), Partrec o := by
    intro o ho
    rw [Set.mem_singleton_iff.mp ho]
    exact (Computable.const 0).partrec.of_eq fun n => by simp [charOracle]
  have hfp : Partrec f := RecursiveIn.partrec_of_oracle hO hf
  have hf' : Partrec (fun a => (f a).map fun _ => ()) :=
    Partrec.map hfp (Computable.const ()).to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf'
  refine ⟨fun a k => (Nat.Partrec.Code.evaln k c (Encodable.encode a)).isSome,
    ((Primrec.option_isSome.to_comp).comp ((evalnCoreComputable c).comp
      (Computable.pair Computable.snd (Computable.encode.comp Computable.fst)))).to₂, fun a => ?_⟩
  rw [hdom a]
  have := partrecCodeDom (fun a => (f a).map fun _ => ()) c hc a
  simpa using this

/-- Auxiliary: membership of a triple in a list is a computable Boolean test. -/
private theorem stage_re_mem_computable :
    Computable (fun p : (ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℚ) => decide (p.1 ∈ p.2)) := by
  have h1 : Primrec (fun p : (ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℚ) => p.2.idxOf p.1) :=
    Primrec.list_idxOf.comp Primrec.fst Primrec.snd
  have h2 : Primrec (fun p : (ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℚ) => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  refine (PrimrecPred.decide (Primrec.nat_lt.comp h1 h2)).to_comp.of_eq fun p => ?_
  simp [List.idxOf_lt_length_iff]

/-- Auxiliary: the run `stage m` is computable in `0'`, given a computable semidecision `g` of
the unsafe lists. -/
private theorem stage_re_rec {m : ℕ × ℕ → ℝ} {g : List (ℕ × ℕ × ℚ) → ℕ → Bool}
    (hg : Computable₂ g)
    (hgspec : ∀ a, ¬ exists_computable_lowerFreqPart_le_liminf_bound_safe m a ↔
      ∃ k, g a k = true) :
    ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun j : ℕ => exists_computable_lowerFreqPart_le_liminf_bound_stage m j) := by
  obtain ⟨h, hh, hspec⟩ := Kolmogorov.exists_computableInJump_semidecide hg
  have hhalt : haltingChi = charOracle jumpSet := by
    funext n
    simp only [haltingChi, charOracle, jumpSet, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) h := by
    simpa [ComputableInJump, hhalt] using hh
  -- one step of the run
  let F : Bool × (ℕ × List (ℕ × ℕ × ℚ)) → List (ℕ × ℕ × ℚ) := fun p =>
    cond p.1 p.2.2 (Denumerable.ofNat (ℕ × ℕ × ℚ) p.2.1 :: p.2.2)
  have hF : Computable F :=
    Computable.cond Computable.fst (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp
        ((Computable.ofNat (ℕ × ℕ × ℚ)).comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))
  have hcons : Computable (fun p : ℕ × List (ℕ × ℕ × ℚ) =>
      Denumerable.ofNat (ℕ × ℕ × ℚ) p.1 :: p.2) :=
    Computable.list_cons.comp ((Computable.ofNat (ℕ × ℕ × ℚ)).comp Computable.fst)
      Computable.snd
  have hstep : ComputableIn₂ ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun (_ : ℕ) (p : ℕ × List (ℕ × ℕ × ℚ)) =>
        F (h (Denumerable.ofNat (ℕ × ℕ × ℚ) p.1 :: p.2), p)) := by
    refine ComputableIn₂.mk ?_
    refine hF.computableIn.comp (ComputableIn.pair ?_ ComputableIn.snd)
    exact hh'.comp (hcons.computableIn.comp ComputableIn.snd)
  have hrec : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun j : ℕ => exists_computable_lowerFreqPart_le_liminf_bound_stage m j) := by
    refine (ComputableIn.nat_rec (f := fun j : ℕ => j)
      (g := fun _ : ℕ => ([] : List (ℕ × ℕ × ℚ))) ComputableIn.id
      (ComputableIn.const []) hstep).of_eq fun j => ?_
    change Nat.rec (motive := fun _ => List (ℕ × ℕ × ℚ)) []
      (fun y ih => F (h (Denumerable.ofNat (ℕ × ℕ × ℚ) y :: ih), (y, ih))) j = _
    induction j with
    | zero => rfl
    | succ j ih =>
      refine Eq.trans (congrArg (fun L => F (h (Denumerable.ofNat (ℕ × ℕ × ℚ) j :: L), (j, L)))
        ih) ?_
      simp only [exists_computable_lowerFreqPart_le_liminf_bound_stage, F]
      by_cases hs : exists_computable_lowerFreqPart_le_liminf_bound_safe m
          (Denumerable.ofNat (ℕ × ℕ × ℚ) j ::
            exists_computable_lowerFreqPart_le_liminf_bound_stage m j)
      · have hf : h (Denumerable.ofNat (ℕ × ℕ × ℚ) j ::
            exists_computable_lowerFreqPart_le_liminf_bound_stage m j) = false := by
          by_contra hne
          exact ((hgspec _).2 ((hspec _).1 (by simpa using hne))) hs
        rw [ite_eq_left hs]; simp only [hf, Bool.cond_false]
      · have ht : h (Denumerable.ofNat (ℕ × ℕ × ℚ) j ::
            exists_computable_lowerFreqPart_le_liminf_bound_stage m j) = true :=
          (hspec _).2 ((hgspec _).1 hs)
        rw [ite_eq_right hs]; simp only [ht, Bool.cond_true]
  exact hrec

/-- Auxiliary: if `S` is `0'`-computable, so is the test `w.2 ∈ S w.1`. -/
private theorem stage_re_key (S : ℕ → List (ℕ × ℕ × ℚ))
    (hS : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) S) :
    ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun w : ℕ × (ℕ × ℕ × ℚ) => decide (w.2 ∈ S w.1)) := by
  have hmem : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun p : (ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℚ) => decide (p.1 ∈ p.2)) :=
    stage_re_mem_computable.computableIn
  have hS1 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun w : ℕ × (ℕ × ℕ × ℚ) => S w.1) :=
    hS.comp ComputableIn.fst
  have hw2 : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun w : ℕ × (ℕ × ℕ × ℚ) => w.2) :=
    ComputableIn.snd
  have hp : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ))
      (fun w : ℕ × (ℕ × ℕ × ℚ) => (w.2, S w.1)) :=
    ComputableIn.pair hw2 hS1
  exact (ComputableIn.comp hmem hp).of_eq fun w => rfl

/-- Step 2 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`:
the run is `0'`-enumerable. If the unsafe lists are enumerable (Step 1), then the relation
"the triple `t` is in the list performed among the first `j` triples" is enumerable relative to
`0'` (`jumpSet`): by recursion on `j`, the list `stage m j` is computable from the `0'`-decision of
the enumerable predicate "`L` is unsafe" (`Kolmogorov.exists_computableInJump_semidecide`), and
membership of a triple in a list is decidable. -/
private theorem exists_computable_lowerFreqPart_le_stage_re
    {m : ℕ × ℕ → ℝ}
    (hU : PointToSet.IsREIn (∅ : Set ℕ)
      (fun L : List (ℕ × ℕ × ℚ) =>
        ¬ exists_computable_lowerFreqPart_le_liminf_bound_safe m L)) :
    PointToSet.IsREIn jumpSet
      (fun w : ℕ × (ℕ × ℕ × ℚ) =>
        w.2 ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m w.1) := by
  obtain ⟨g, hg, hgspec⟩ :=
    exists_computable_lowerFreqPart_le_stage_re_aux_semidecide hU
  have hrec := stage_re_rec hg hgspec
  exact PointToSet.isREIn_of_computableIn_decide jumpSet
    (fun w : ℕ × (ℕ × ℕ × ℚ) =>
      w.2 ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m w.1)
    (stage_re_key _ hrec)

/-- Step 3 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`
(every stage is safe): if every row of `m` is a semimeasure then for every `j` the list
`stage m j` is row-safe (induction on `j`: the empty list is safe with `ρ = m (·, n)`, and a
request is only added if the enlarged list is safe). -/
private theorem exists_computable_lowerFreqPart_le_stage_safe
    {m : ℕ × ℕ → ℝ} (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1) (j : ℕ) :
    exists_computable_lowerFreqPart_le_liminf_bound_safe m
      (exists_computable_lowerFreqPart_le_liminf_bound_stage m j) := by
  induction j with
  | zero =>
    intro n
    exact ⟨fun k => m (k, n), fun k => le_rfl, by simp
      [exists_computable_lowerFreqPart_le_liminf_bound_stage], h1 n⟩
  | succ j ih =>
    simp only [exists_computable_lowerFreqPart_le_liminf_bound_stage]
    split_ifs with h
    · exact h
    · exact ih

/-- The stages of the run only grow. -/
private theorem exists_computable_lowerFreqPart_le_liminf_bound_stage_mono
    {m : ℕ × ℕ → ℝ} {t : ℕ × ℕ × ℚ} {j J : ℕ} (hjJ : j ≤ J)
    (ht : t ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j) :
    t ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m J := by
  induction J, hjJ using Nat.le_induction with
  | base => exact ht
  | succ J _ ih =>
    simp only [exists_computable_lowerFreqPart_le_liminf_bound_stage]
    split_ifs with h
    · exact List.mem_cons_of_mem _ ih
    · exact ih

/-- Every performed `ε` is at most `1`, so the set defining `q k` is bounded above. -/
private theorem exists_computable_lowerFreqPart_le_liminf_bound_bdd
    {m : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ m p) (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1)
    (k : ℕ) :
    BddAbove {x : ℝ | ∃ (j N : ℕ) (ε : ℚ),
      (N, k, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j ∧ x = ε} := by
  refine ⟨1, ?_⟩
  rintro x ⟨j, N, ε, hmem, rfl⟩
  obtain ⟨ρ, hρ0, hρ, hρs⟩ :=
    exists_computable_lowerFreqPart_le_stage_safe h1 j N
  have h2 : (ε : ℝ) ≤ ρ k := hρ _ hmem le_rfl
  have h3 : ρ k ≤ ∑ i ∈ Finset.range (k + 1), ρ i :=
    Finset.single_le_sum (f := ρ) (fun i _ => (h0 (i, N)).trans (hρ0 i))
      (Finset.mem_range.2 (Nat.lt_succ_self k))
  linarith [hρs (k + 1)]

/-- A request `(N, k, ε)` with `ε ≤ m (k, n)` for all `n ≥ N` is performed (at some stage). -/
private theorem exists_computable_lowerFreqPart_le_liminf_bound_performed
    {m : ℕ × ℕ → ℝ} (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1)
    (N k : ℕ) (ε : ℚ) (hε : ∀ n, N ≤ n → (ε : ℝ) ≤ m (k, n)) :
    ∃ j, (N, k, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j := by
  obtain ⟨j, hofNat⟩ : ∃ j, Denumerable.ofNat (ℕ × ℕ × ℚ) j = (N, k, ε) :=
    ⟨Denumerable.eqv (ℕ × ℕ × ℚ) (N, k, ε), (Denumerable.eqv (ℕ × ℕ × ℚ)).symm_apply_apply _⟩
  have hsafe : exists_computable_lowerFreqPart_le_liminf_bound_safe m
      ((N, k, ε) :: exists_computable_lowerFreqPart_le_liminf_bound_stage m j) := by
    intro n
    obtain ⟨ρ, hρ0, hρ, hρs⟩ :=
      exists_computable_lowerFreqPart_le_stage_safe h1 j n
    refine ⟨ρ, hρ0, fun s hs hsn => ?_, hρs⟩
    rcases List.mem_cons.1 hs with rfl | hs'
    · exact (hε n hsn).trans (hρ0 k)
    · exact hρ s hs' hsn
  refine ⟨j + 1, ?_⟩
  simp only [exists_computable_lowerFreqPart_le_liminf_bound_stage]
  rw [hofNat, ite_eq_left hsafe]
  exact List.mem_cons_self

/-- Step 4 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`
(the supremum `q`): `q k` is the supremum of a bounded nonempty set, so `r < q k` iff some
performed request `(N, k, ε)` has `r < ε`; also `q k ≥ 0`. (Boundedness: every performed `ε`
is `≤ 1` since the row `N` of the safe stage dominates `ε` at `k`, so the partial sum up to `k+1`
is `≥ ε`, using `m ≥ 0`. Nonemptiness: the request `(0, k, 0)` is performed at some stage `j`
(it is the `j`-th triple; raising to `0 ≤ m` changes nothing), and `ε = 0` witnesses `0 ≤ q k`.) -/
private theorem exists_computable_lowerFreqPart_le_cut
    {m : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ m p) (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1) :
    (∀ (k : ℕ) (r : ℚ), (r : ℝ) < exists_computable_lowerFreqPart_le_liminf_bound_q m k ↔
      ∃ (j N : ℕ) (ε : ℚ),
        (N, k, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j ∧ r < ε) ∧
    ∀ k, 0 ≤ exists_computable_lowerFreqPart_le_liminf_bound_q m k := by
  have hdummy : ∀ k, ∃ j, ((0 : ℕ), k, (0 : ℚ)) ∈
      exists_computable_lowerFreqPart_le_liminf_bound_stage m j := fun k =>
    exists_computable_lowerFreqPart_le_liminf_bound_performed h1 0 k 0
      (fun n _ => by simpa using h0 (k, n))
  have hne : ∀ k, {x : ℝ | ∃ (j N : ℕ) (ε : ℚ),
      (N, k, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j ∧
        x = ε}.Nonempty := fun k => by
    obtain ⟨j, hj⟩ := hdummy k
    exact ⟨0, j, 0, 0, hj, by simp⟩
  refine ⟨fun k r => ?_, fun k => ?_⟩
  · have hbdd := exists_computable_lowerFreqPart_le_liminf_bound_bdd h0 h1 k
    unfold exists_computable_lowerFreqPart_le_liminf_bound_q
    constructor
    · intro h
      obtain ⟨x, ⟨j, N, ε, hmem, rfl⟩, hrx⟩ := (lt_csSup_iff hbdd (hne k)).1 h
      exact ⟨j, N, ε, hmem, by exact_mod_cast hrx⟩
    · rintro ⟨j, N, ε, hmem, hr⟩
      exact lt_of_lt_of_le (by exact_mod_cast hr) (le_csSup hbdd ⟨j, N, ε, hmem, rfl⟩)
  · have hbdd := exists_computable_lowerFreqPart_le_liminf_bound_bdd h0 h1 k
    obtain ⟨j, hj⟩ := hdummy k
    unfold exists_computable_lowerFreqPart_le_liminf_bound_q
    exact le_csSup hbdd ⟨j, 0, 0, hj, by simp⟩

/-- Step 5 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`
(the sum bound): `∑_{i<N} q i ≤ 1`. Given `δ > 0`, for each `i < N` pick a performed request
`(N_i, i, ε_i)` with `ε_i > q i - δ` (stages only grow, so all of them lie in one stage `J`), and
take `n` beyond all `N_i`; the safe stage `J` gives a semimeasure `ρ` on row `n` dominating all
the `ε_i`, whence `∑_{i<N} (q i - δ) ≤ ∑ ρ ≤ 1`. -/
private theorem exists_computable_lowerFreqPart_le_sum
    {m : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ m p) (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1)
    (N : ℕ) :
    ∑ i ∈ Finset.range N, exists_computable_lowerFreqPart_le_liminf_bound_q m i ≤ 1 := by
  obtain ⟨hcut, hq0⟩ := exists_computable_lowerFreqPart_le_cut h0 h1
  set q := exists_computable_lowerFreqPart_le_liminf_bound_q m with hqdef
  have key : ∀ δ : ℝ, 0 < δ → ∑ i ∈ Finset.range N, q i ≤ 1 + N * δ := by
    intro δ hδ
    have hex : ∀ i : ℕ, ∃ (r : ℚ) (j N' : ℕ) (ε : ℚ), q i - δ < r ∧
        (N', i, ε) ∈ exists_computable_lowerFreqPart_le_liminf_bound_stage m j ∧ r < ε := by
      intro i
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show q i - δ < q i by linarith)
      obtain ⟨j, N', ε, h1', h2'⟩ := (hcut i r).1 hr2
      exact ⟨r, j, N', ε, hr1, h1', h2'⟩
    choose r j N' ε hr hmem hrε using hex
    set J := (Finset.range N).sup j
    set n := (Finset.range N).sup N'
    obtain ⟨ρ, -, hρ, hρs⟩ :=
      exists_computable_lowerFreqPart_le_stage_safe h1 J n
    have hle : ∀ i ∈ Finset.range N, q i - δ ≤ ρ i := by
      intro i hi
      have hmem' := exists_computable_lowerFreqPart_le_liminf_bound_stage_mono
        (Finset.le_sup (f := j) hi) (hmem i)
      have := hρ _ hmem' (Finset.le_sup (f := N') hi)
      simp only at this
      have h3 : (r i : ℝ) < ε i := by exact_mod_cast hrε i
      linarith [hr i]
    have := Finset.sum_le_sum hle
    rw [Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have := hρs N
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h2 := key (ε / (N + 1)) (by positivity)
  have h3 : (N : ℝ) * (ε / (N + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Step 6 of the proof of `exists_computable_lowerFreqPart_le_liminf_bound`
(the `liminf` bound): `liminf_n m (k, n) ≤ q k`. For a rational `ε` with
`0 < ε < liminf_n m (k, n)` there is `N` with `ε < m (k, n)` for all `n ≥ N`; the request
`(N, k, ε)` is the `j`-th triple for some `j`, and adding it to the (safe) stage `j` changes no
row (the same `ρ` dominates `m (k, n) > ε`), so it is performed and `ε ≤ q k`. Conclude by
density of the rationals and `q k ≥ 0`. -/
private theorem exists_computable_lowerFreqPart_le_liminf
    {m : ℕ × ℕ → ℝ} (h0 : ∀ p, 0 ≤ m p) (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1)
    (k : ℕ) :
    Filter.liminf (fun n => m (k, n)) Filter.atTop ≤
      exists_computable_lowerFreqPart_le_liminf_bound_q m k := by
  refine le_of_forall_rat_lt_imp_le fun r hr => ?_
  have hb : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n => m (k, n)) :=
    Filter.isBoundedUnder_of ⟨0, fun n => h0 _⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_lt_of_lt_liminf hr hb)
  obtain ⟨j, hj⟩ := exists_computable_lowerFreqPart_le_liminf_bound_performed h1 N k r
    (fun n hn => (hN n hn).le)
  exact le_csSup (exists_computable_lowerFreqPart_le_liminf_bound_bdd h0 h1 k)
    ⟨j, N, r, hj, rfl⟩

/-- Step 1 of the proof of `exists_computable_lowerFreqPart_le`: the construction from
the proof of SUV Theorem 133. Let `m (k, n)` be a lower semicomputable (without oracle) family of
non-negative reals such that for every `n` the sequence `k ↦ m (k, n)` is a semimeasure
(all finite partial sums `≤ 1`). Then the `liminf`s `k ↦ liminf_n m (k, n)` are bounded above by a
`0'`-lower-semicomputable semimeasure `q`.

Proof idea: consider triples `⟨N, k, ε⟩` (`ε` a positive rational). For a triple, try to raise
the values `m (k, n)` to `ε` for all `n ≥ N`, but only if every row `n` stays a semimeasure; the
violation is an enumerable event, so the test is `0'`-decidable. Go through all triples in
order, performing the raising when possible. Let `q k` be the supremum of the `ε` used together
with `k`. Then `q` is `0'`-lower-semicomputable, the raised rows are semimeasures (so
`∑_{k<N} q k ≤ 1`, by the row bound for `n` large), and `liminf_n m (k, n) ≤ q k` since for
`ε < liminf` the triple `⟨N, k, ε⟩` (for large `N`) can be performed. -/
private theorem exists_computable_lowerFreqPart_le_liminf_bound
    {m : ℕ × ℕ → ℝ} (hm : PointToSet.IsLowerSemicomputableIn (∅ : Set ℕ) m)
    (h0 : ∀ p, 0 ≤ m p) (h1 : ∀ n N, ∑ k ∈ Finset.range N, m (k, n) ≤ 1) :
    ∃ q : ℕ → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet q ∧ (∀ i, 0 ≤ q i) ∧
      (∀ N, ∑ i ∈ Finset.range N, q i ≤ 1) ∧
      ∀ k, Filter.liminf (fun n => m (k, n)) Filter.atTop ≤ q k := by
  have hU := exists_computable_lowerFreqPart_le_unsafe_re hm
  have hRE := exists_computable_lowerFreqPart_le_stage_re hU
  obtain ⟨hcut, hq0⟩ := exists_computable_lowerFreqPart_le_cut h0 h1
  refine ⟨exists_computable_lowerFreqPart_le_liminf_bound_q m, ?_, hq0,
    exists_computable_lowerFreqPart_le_sum h0 h1,
    exists_computable_lowerFreqPart_le_liminf h0 h1⟩
  -- the strict rational lower cut of `q` is a projection of an enumerable predicate
  have hF : PointToSet.IsREIn jumpSet
      (fun p : (ℕ × ℚ) × (ℕ × ℕ × ℚ) =>
        (p.2.2.1, p.1.1, p.2.2.2) ∈
          exists_computable_lowerFreqPart_le_liminf_bound_stage m p.2.1 ∧
          p.1.2 < p.2.2.2) := by
    refine PointToSet.IsREIn.and ?_ ?_
    · exact PointToSet.IsREIn.comp hRE (f := fun p : (ℕ × ℚ) × (ℕ × ℕ × ℚ) =>
        (p.2.1, (p.2.2.1, p.1.1, p.2.2.2))) (by
          refine Computable.computableIn ?_
          exact Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
              (Computable.pair (Computable.fst.comp Computable.fst)
                (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
    · refine PointToSet.isREIn_of_computable_decide (P := fun p : (ℕ × ℚ) × (ℕ × ℕ × ℚ) =>
        p.1.2 < p.2.2.2) ?_
      exact computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
        (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hF' := PointToSet.IsREIn.exists hF
  obtain ⟨f, hf, hdom⟩ := hF'
  refine ⟨f, hf, fun w => ?_⟩
  change ((w.2 : ℝ) < exists_computable_lowerFreqPart_le_liminf_bound_q m w.1) ↔ _
  rw [hcut w.1 w.2]
  refine Iff.trans ?_ (hdom w)
  constructor
  · rintro ⟨j, N, ε, h1, h2⟩
    exact ⟨(j, N, ε), h1, h2⟩
  · rintro ⟨⟨j, N, ε⟩, h1, h2⟩
    exact ⟨j, N, ε, h1, h2⟩

private lemma exists_computable_lowerFreqPart_le_freq_lsc_natCast :
    Computable (fun n : ℕ => (n : ℚ)) :=
  computable_of_num_den (N := fun n : ℕ => (n : ℤ)) (D := fun _ => 1)
    ComputableReals.primrec_natCastInt.to_comp (Computable.const 1) (fun _ => one_pos)
    (fun n => by simp)

private lemma exists_computable_lowerFreqPart_le_freq_lsc_card_rec
    (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((Finset.range n).filter p).card =
      n.rec (motive := fun _ => ℕ) 0 (fun i acc => acc + if p i then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      simp [ih, h]
    · rw [ite_eq_right h]
      simp [ih, h]

private lemma exists_computable_lowerFreqPart_le_freq_lsc_cnt (c : Nat.Partrec.Code) :
    Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ =>
      (((Finset.range w.1.1.2).filter
        (fun i => Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1)).card : ℕ)) := by
  have h : Primrec (fun w : ((ℕ × ℕ) × ℚ) × ℕ =>
      w.1.1.2.rec (motive := fun _ => ℕ) 0
        (fun i acc => acc + if Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1 then 1 else 0)) := by
    refine Primrec.nat_rec' (f := fun w : ((ℕ × ℕ) × ℚ) × ℕ => w.1.1.2) (g := fun _ => (0 : ℕ))
      (h := fun (w : ((ℕ × ℕ) × ℚ) × ℕ) (p : ℕ × ℕ) =>
        p.2 + if Nat.Partrec.Code.evaln w.2 c p.1 = some w.1.1.1 then 1 else 0)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const (0 : ℕ)) ?_
    have hev : Primrec (fun p : (((ℕ × ℕ) × ℚ) × ℕ) × ℕ × ℕ =>
        Nat.Partrec.Code.evaln p.1.2 c p.2.1) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (((Primrec.snd.comp Primrec.fst).pair (Primrec.const c)).pair
          (Primrec.fst.comp Primrec.snd))
    have hk : Primrec (fun p : (((ℕ × ℕ) × ℚ) × ℕ) × ℕ × ℕ => some p.1.1.1.1) :=
      Primrec.option_some.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    exact Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp hev hk) (Primrec.const 1) (Primrec.const 0))
  exact h.to_comp.of_eq fun w =>
    (exists_computable_lowerFreqPart_le_freq_lsc_card_rec _ _).symm

private lemma exists_computable_lowerFreqPart_le_freq_lsc_test (c : Nat.Partrec.Code) :
    Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ =>
      decide (w.1.2 < 0 ∨ w.1.2 * (w.1.1.2 : ℚ) <
        (((Finset.range w.1.1.2).filter
          (fun i => Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1)).card : ℚ))) := by
  have hr : Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ => w.1.2) := Computable.snd.comp Computable.fst
  have hn : Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ => ((w.1.1.2 : ℕ) : ℚ)) :=
    exists_computable_lowerFreqPart_le_freq_lsc_natCast.comp
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hcn : Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ =>
      ((((Finset.range w.1.1.2).filter
        (fun i => Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1)).card : ℕ) : ℚ)) :=
    exists_computable_lowerFreqPart_le_freq_lsc_natCast.comp
      (exists_computable_lowerFreqPart_le_freq_lsc_cnt c)
  have h1 : Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ => !decide ((0 : ℚ) ≤ w.1.2)) :=
    (Primrec.not.to_comp).comp
      (isLowerSemicomputableIn_jumpSet_liminf_ratLe.comp (Computable.const 0) hr)
  have h2 : Computable (fun w : ((ℕ × ℕ) × ℚ) × ℕ => !decide
      ((((Finset.range w.1.1.2).filter
        (fun i => Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1)).card : ℚ) ≤
        w.1.2 * (w.1.1.2 : ℚ))) :=
    (Primrec.not.to_comp).comp
      (isLowerSemicomputableIn_jumpSet_liminf_ratLe.comp hcn (computable₂_ratMul.comp hr hn))
  have h3 := Computable₂.comp ((Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp) h1 h2
  refine h3.of_eq fun w => ?_
  simp only [← decide_not, ← Bool.decide_or]
  exact decide_eq_decide.mpr (by simp only [not_le])

private lemma exists_computable_lowerFreqPart_le_freq_lsc_sem {f : ℕ →. ℕ}
    {c : Nat.Partrec.Code} (hc : Nat.Partrec.Code.eval c = f) (k n : ℕ) (r : ℚ) :
    (r : ℝ) < (countOccPart f k n : ℝ) / n ↔
      ∃ s, r < 0 ∨ r * (n : ℚ) <
        (((Finset.range n).filter
          (fun i => Nat.Partrec.Code.evaln s c i = some k)).card : ℚ) := by
  classical
  have hmem : ∀ i, k ∈ f i ↔ ∃ s, Nat.Partrec.Code.evaln s c i = some k := by
    intro i
    rw [← hc, Nat.Partrec.Code.evaln_complete]
    rfl
  have hsub : ∀ s, (Finset.range n).filter (fun i => Nat.Partrec.Code.evaln s c i = some k) ⊆
      (Finset.range n).filter (fun i => k ∈ f i) := by
    intro s i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, (hmem i).2 ⟨s, hi.2⟩⟩
  have hcard : ∀ s, (((Finset.range n).filter
      (fun i => Nat.Partrec.Code.evaln s c i = some k)).card : ℝ) ≤
      (countOccPart f k n : ℝ) := by
    intro s
    unfold countOccPart
    exact_mod_cast Finset.card_le_card (hsub s)
  have hnn : (0 : ℝ) ≤ (countOccPart f k n : ℝ) / n := by positivity
  constructor
  · intro h
    by_cases hr : r < 0
    · exact ⟨0, Or.inl hr⟩
    · have hr0 : 0 ≤ r := not_lt.1 hr
      have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp at h; linarith
        · exact hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [lt_div_iff₀ hn'] at h
      have hex : ∀ i ∈ (Finset.range n).filter (fun i => k ∈ f i),
          ∃ s, Nat.Partrec.Code.evaln s c i = some k :=
        fun i hi => (hmem i).1 (Finset.mem_filter.1 hi).2
      choose! g hg using hex
      set S := (Finset.range n).filter (fun i => k ∈ f i) with hS
      refine ⟨S.sup g, Or.inr ?_⟩
      have hsup : S ⊆ (Finset.range n).filter
          (fun i => Nat.Partrec.Code.evaln (S.sup g) c i = some k) := by
        intro i hi
        rw [Finset.mem_filter]
        refine ⟨(Finset.mem_filter.1 hi).1, ?_⟩
        exact Nat.Partrec.Code.evaln_mono (Finset.le_sup (f := g) hi) (hg i hi)
      have hle : (countOccPart f k n : ℝ) ≤ (((Finset.range n).filter
          (fun i => Nat.Partrec.Code.evaln (S.sup g) c i = some k)).card : ℝ) := by
        unfold countOccPart
        exact_mod_cast Finset.card_le_card hsup
      have : (r : ℝ) * n < (((Finset.range n).filter
          (fun i => Nat.Partrec.Code.evaln (S.sup g) c i = some k)).card : ℝ) :=
        lt_of_lt_of_le h hle
      exact_mod_cast this
  · rintro ⟨s, hs | hs⟩
    · exact lt_of_lt_of_le (by exact_mod_cast hs) hnn
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at hs
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [lt_div_iff₀ hn']
        have : (r : ℝ) * n < (((Finset.range n).filter
            (fun i => Nat.Partrec.Code.evaln s c i = some k)).card : ℝ) := by exact_mod_cast hs
        exact lt_of_lt_of_le this (hcard s)

/-- Step 2 of the proof of `exists_computable_lowerFreqPart_le`: for a partial computable
`f`, the family `(k, n) ↦ countOccPart f k n / n` of frequencies in the first `n` terms is lower
semicomputable (without oracle).

Proof idea: `r < countOccPart f k n / n` iff `r < 0` or `n > 0` and at least `⌊r n⌋ + 1` many
`i < n` have `k ∈ f i`, a semidecidable property (dovetail the halting computations of `f i`,
`i < n`). -/
private theorem exists_computable_lowerFreqPart_le_freq_lsc {f : ℕ →. ℕ}
    (hf : Partrec f) :
    PointToSet.IsLowerSemicomputableIn (∅ : Set ℕ)
      (fun p : ℕ × ℕ => (countOccPart f p.1 p.2 : ℝ) / p.2) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  have hRE := PointToSet.isREIn_of_computable_decide (A := (∅ : Set ℕ))
    (P := fun w : ((ℕ × ℕ) × ℚ) × ℕ => w.1.2 < 0 ∨ w.1.2 * (w.1.1.2 : ℚ) <
        (((Finset.range w.1.1.2).filter
          (fun i => Nat.Partrec.Code.evaln w.2 c i = some w.1.1.1)).card : ℚ))
    (exists_computable_lowerFreqPart_le_freq_lsc_test c)
  have hRE2 := PointToSet.IsREIn.exists hRE
  unfold PointToSet.IsLowerSemicomputableIn
  have : (fun w : (ℕ × ℕ) × ℚ => (w.2 : ℝ) < (countOccPart f w.1.1 w.1.2 : ℝ) / w.1.2) =
      (fun x : (ℕ × ℕ) × ℚ => ∃ y : ℕ, (x.2 < 0 ∨ x.2 * (x.1.2 : ℚ) <
        (((Finset.range x.1.2).filter
          (fun i => Nat.Partrec.Code.evaln y c i = some x.1.1)).card : ℚ))) := by
    funext w
    exact propext (exists_computable_lowerFreqPart_le_freq_lsc_sem hc w.1.1 w.1.2 w.2)
  rw [this]
  exact hRE2

/-- Step 3 of the proof of `exists_computable_lowerFreqPart_le`: the frequencies
`countOccPart f k n / n` are non-negative, and for every `n` they form a semimeasure in `k`: the
sets `{i < n | k ∈ f i}` for distinct `k` are disjoint subsets of `range n`. -/
private theorem exists_computable_lowerFreqPart_le_freq_semimeasure (f : ℕ →. ℕ) :
    (∀ p : ℕ × ℕ, (0 : ℝ) ≤ (countOccPart f p.1 p.2 : ℝ) / p.2) ∧
    (∀ n N : ℕ, ∑ k ∈ Finset.range N, (countOccPart f k n : ℝ) / n ≤ 1) := by
  classical
  refine ⟨fun p => by positivity, fun n N => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Finset.sum_div, div_le_one (by exact_mod_cast hn)]
  have : ∑ k ∈ Finset.range N, countOccPart f k n ≤ n := by
    unfold countOccPart
    rw [← Finset.card_sigma]
    calc _ ≤ (Finset.range n).card := by
          refine Finset.card_le_card_of_injOn (fun x => x.2) ?_ ?_
          · intro x hx
            simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_filter,
              Finset.mem_range] at hx
            simpa using hx.2.1
          · intro x hx y hy hxy
            simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_filter,
              Finset.mem_range] at hx hy
            have hxy' : x.2 = y.2 := hxy
            obtain ⟨a, b⟩ := x
            obtain ⟨c, d⟩ := y
            simp only at hxy'
            subst hxy'
            have : a = c := Part.mem_unique hx.2.2 hy.2.2
            subst this; rfl
      _ = n := Finset.card_range n
  exact_mod_cast this

/-- **SUV Problem 213 (Section 6.4.3, printed p. 211).** Theorem 136 also holds for partial
computable `f`: there is a total computable sequence `g` whose lower frequencies are at least
those of `f`. For a partial `f`, the frequency counts the `i < N` at which `f` is defined with
value `k`, divided by `N`.

Proof idea (book's hint): for every `N` the frequencies in the first `N` terms form a lower
semicomputable semimeasure. The construction in the proof of Theorem 133 bounds their
`liminf`s by a `0'`-lower-semicomputable semimeasure, to which Theorem 136 applies. -/
theorem exists_computable_lowerFreqPart_le {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ k, lowerFreqPart f k ≤ lowerFreq g k := by
  have hm := exists_computable_lowerFreqPart_le_freq_lsc hf
  obtain ⟨h0, h1⟩ := exists_computable_lowerFreqPart_le_freq_semimeasure f
  obtain ⟨q, hq, hq0, hq1, hle⟩ :=
    exists_computable_lowerFreqPart_le_liminf_bound hm h0 h1
  obtain ⟨g, hg, hgq⟩ := exists_computable_le_lowerFreq hq hq0 hq1
  exact ⟨g, hg, fun k => (hle k).trans (hgq k)⟩

end GeneralScheme

end Kolmogorov
