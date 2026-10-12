import KolmogorovMathlib.StrongMerging.Lower.ReservoirGame
import KolmogorovMathlib.StrongMerging.Lower.ReservoirComputable
import KolmogorovMathlib.StrongMerging.Lower.ReservoirTransport

/-!
# The moving-sphere reservoir game: hypotheses and the event stream

Blueprint node L14 of `sublinear-merging.tex`: the hypotheses `GameHyp` of the generic
game (with the equivalences between the integer and the paper's real forms of the four
game inequalities) and the properties of the effective event stream, collected in
`ValidHistory` (`reservoirEventEnumeration`).

Part of `KolmogorovMathlib.StrongMerging.Lower.Reservoir`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The hypotheses of the generic game -/

/-- **The hypotheses of the generic reservoir game** (the generic form of the hypotheses of the
paper's Lemma `lem:ham-reservoir` and of node L16).  The cube is `G.centers` (duplicate-free,
nonempty); spheres around centers have `N` points; each point lies in at most `N` spheres around
centers (L06); `heavy_bound` is the heavy-cell bound of L09 for every exact partition of the
cube, in multiplied-out form (`θ` is the bound on the probability of the heavy event); and the
four game inequalities `density`, `heavy`, `charge`, `arrivals`, with `|cube|` in place of `2^M`
in `density`. -/
structure GameHyp (G : ResGame α) (K τ S : ℕ) (θ : ℝ) : Prop where
  /-- The canonical center list has no repetitions. -/
  centers_nodup : G.centers.Nodup
  /-- The cube is nonempty. -/
  centers_ne_nil : G.centers ≠ []
  /-- Every sphere around a center has `N` points. -/
  sphere_card : ∀ z ∈ G.centers, (G.sphere z).card = G.N
  /-- Every point lies in at most `N` spheres around centers (L06). -/
  incidence : ∀ u, (G.centers.filter fun z => decide (u ∈ G.sphere z)).length ≤ G.N
  /-- The heavy-cell bound of L09 for every exact partition, multiplied out. -/
  heavy_bound : ∀ P, IsCellPartition G.cube P →
    ((∑ z ∈ G.cube, (tableHeavyPoints G P z).card : ℕ) : ℝ) ≤ (G.cube.card : ℝ) * G.N * θ
  /-- The heavy-cell constant is nonnegative. -/
  theta_nonneg : 0 ≤ θ
  /-- The density inequality, `256 (2^K + (K+τ+1) 2^(K+τ)) ≤ |cube|`. -/
  density : 256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) ≤ G.centers.length
  /-- The heavy inequality, `2^(S+1) θ ≤ 1/256`. -/
  heavy : (2 : ℝ) ^ (S + 1) * θ ≤ 1 / 256
  /-- The charge inequality, integer form `(K+τ+1) 2^(K+τ) ≤ 2^(K+δ)`. -/
  charge : (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + G.delta)
  /-- The arrival inequality, integer form `N 2^(S+1) ≤ 2^K`. -/
  arrivals : G.N * 2 ^ (S + 1) ≤ 2 ^ K

/-! #### The four game inequalities in the paper's real form -/

/-- **Density inequality, paper form.**  `2^K + (K+τ+1) 2^(K+τ) ≤ 2^M / 256` over the reals is
the integer inequality `256 (2^K + (K+τ+1) 2^(K+τ)) ≤ 2^M`.
Proof: multiply by `256 > 0` (`le_div_iff₀`) and cast (`exact_mod_cast`).
Reference: paper eq. `ham-game-density`; node L16. -/
theorem density_iff_div (K τ M : ℕ) :
    ((2 ^ K + (K + τ + 1) * 2 ^ (K + τ) : ℕ) : ℝ) ≤ (2 : ℝ) ^ M / 256 ↔
      256 * (2 ^ K + (K + τ + 1) * 2 ^ (K + τ)) ≤ 2 ^ M := by
  generalize 2 ^ K + (K + τ + 1) * 2 ^ (K + τ) = X
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
  constructor
  · intro h
    have : ((256 * X : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((256 * X : ℕ) : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

/-- **Heavy inequality, paper form.**  With `θ = 2^δ (V 2^(-ℓ) + β^h)`, the paper's
`2^(S+1+δ) (V 2^(-ℓ) + β^h) ≤ 1/256` is `2^(S+1) θ ≤ 1/256`. -/
theorem heavy_iff (S δ ℓ h : ℕ) (V β : ℝ) :
    (2 : ℝ) ^ (S + 1 + δ) * (V * (2 : ℝ) ^ (-(ℓ : ℤ)) + β ^ h) ≤ 1 / 256 ↔
      (2 : ℝ) ^ (S + 1) * ((2 : ℝ) ^ δ * (V * (2 : ℝ) ^ (-(ℓ : ℤ)) + β ^ h)) ≤ 1 / 256 := by
  rw [pow_add, mul_assoc]

/-- **Charge inequality, paper form.**  `(K+τ+1) 2^(τ-δ) ≤ 1`, with the rational power
`2^(τ-δ)` (an integer exponent, possibly negative), is the integer inequality
`(K+τ+1) 2^(K+τ) ≤ 2^(K+δ)`.
Proof: multiply both sides by `2^(K+δ) > 0`; `2^(τ-δ) 2^(K+δ) = 2^(K+τ)` by `zpow_add₀`; cast.
Reference: paper eq. `ham-game-charge`; blueprint L19 ("convenient integer form"). -/
theorem charge_iff_zpow (K τ δ : ℕ) :
    ((K + τ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((τ : ℤ) - δ) ≤ 1 ↔
      (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + δ) := by
  have key : (2 : ℝ) ^ ((τ : ℤ) - δ) * 2 ^ (K + δ) = 2 ^ (K + τ) := by
    rw [← zpow_natCast (2 : ℝ) (K + δ), ← zpow_natCast (2 : ℝ) (K + τ),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have h2 : (0 : ℝ) < 2 ^ (K + δ) := by positivity
  rw [← mul_le_mul_iff_of_pos_right h2, one_mul, mul_assoc, key]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- **Arrival inequality, paper form.**  For `N > 0`, `2^(S+1) ≤ 2^K / N` over the reals is the
integer inequality `N 2^(S+1) ≤ 2^K`.
Proof: `le_div_iff₀` with `(N : ℝ) > 0`, commute the product, cast.
Reference: paper eq. `ham-game-arrivals`. -/
theorem arrivals_iff_div (N K S : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (S + 1) ≤ (2 : ℝ) ^ K / N ↔ N * 2 ^ (S + 1) ≤ 2 ^ K := by
  rw [le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N), mul_comm]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- **The deletion-charge bound in rational form.**  Under the integer charge inequality,
`(K+τ+1) 2^(K+τ-δ) ≤ 2^K`, where `2^(K+τ-δ)` is a real power with an integer (possibly negative)
exponent; no truncated natural subtraction occurs.
Proof: `2^(K+τ-δ) = 2^(K+τ) / 2^δ` (`zpow_sub₀`, `zpow_natCast`); divide the cast integer
inequality by `2^δ > 0`.
Reference: blueprint L19. -/
theorem charge_rational {K τ δ : ℕ} (h : (K + τ + 1) * 2 ^ (K + τ) ≤ 2 ^ (K + δ)) :
    ((K + τ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((K : ℤ) + τ - δ) ≤ 2 ^ K := by
  have key : (2 : ℝ) ^ ((K : ℤ) + τ - δ) * 2 ^ δ = 2 ^ (K + τ) := by
    rw [← zpow_natCast (2 : ℝ) δ, ← zpow_natCast (2 : ℝ) (K + τ),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have h2 : (0 : ℝ) < 2 ^ δ := by positivity
  rw [← mul_le_mul_iff_of_pos_right h2, mul_assoc, key, ← pow_add]
  exact_mod_cast h

/-! ### L14: properties of the effective event stream -/

/-- A history validated at a longer stage is validated at every prefix.
Proof: every count (`countP`, `setMass`) of `l₁` is at most that of `l₁ ++ l₂`
(`List.countP_append`), and membership in `l₁` implies membership in `l₁ ++ l₂`.
Reference: L14 ("monotonic discovery"). -/
theorem ValidHistory.of_append {G : ResGame α} {K τ S : ℕ} {l₁ l₂ : List (ResEvent α)}
    (h : ValidHistory G K τ S (l₁ ++ l₂)) : ValidHistory G K τ S l₁ := by
  refine ⟨?_, fun Q i hQ => h.set_elig Q i (List.mem_append_left _ hQ), fun i => ?_, ?_,
    fun P hP => h.table_valid P (List.mem_append_left _ hP)⟩
  · have := h.point_count
    unfold pointCount at *
    rw [List.countP_append] at this
    omega
  · have := h.cost_count i
    unfold costCount at *
    rw [List.countP_append] at this
    omega
  · have := h.table_count
    unfold tableCount at *
    rw [List.countP_append] at this
    omega

/-- The event history grows by appending: `eventHistory s` is a prefix of `eventHistory t` for
`s ≤ t`.
Proof: `List.range t = List.range s ++ List.range' s (t - s)` (`List.range_eq_range'`,
`List.range'_append`), then `List.flatMap_append` and `List.prefix_append`.
Reference: L14 ("monotonic discovery"). -/
theorem eventHistory_prefix (G : ResGame α) (K τ : ℕ) (src : EventSources α) {s t : ℕ}
    (hst : s ≤ t) : eventHistory G K τ src s <+: eventHistory G K τ src t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    refine ih.trans ?_
    unfold eventHistory
    rw [List.range_succ, List.flatMap_append]
    exact List.prefix_append _ _

/-- `firstAt f` holds at most once: it marks the least stage at which `f` is available.
Proof: if `s < t` then `firstAt f t` requires `(f s).isNone`, contradicting `(f s).isSome`;
symmetrically for `t < s`. -/
theorem firstAt_unique {β : Type*} {f : ℕ → Option β} {s t : ℕ} (hs : firstAt f s = true)
    (ht : firstAt f t = true) : s = t := by
  unfold firstAt at hs ht
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs ht
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 := ht.2 s h
    have h2 := hs.1
    rw [Option.isNone_iff_eq_none] at h1
    rw [h1] at h2
    exact absurd h2 (by simp)
  · have h1 := hs.2 t h
    have h2 := ht.1
    rw [Option.isNone_iff_eq_none] at h1
    rw [h1] at h2
    exact absurd h2 (by simp)

/-- Every point candidate produces at most one event in the whole history, so the history has at
most `numPt` point events.
Proof: `pointCount (eventHistory s)` is the sum over candidates `c < numPt` of the number of
stages `t < s` at which `ptEventAt` emits for `c`; each such stage satisfies
`firstAt (ptEval c) t`, so there is at most one by `firstAt_unique` (rewrite with
`List.countP_flatMap`, swap the two finite sums).
Reference: L14 ("fewer than `2^K` point-program events"). -/
theorem pointCount_eventHistory_le (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s : ℕ) :
    pointCount (eventHistory G K τ src s) ≤ src.numPt := by
  have hls : ∀ (g : ℕ → ℕ) (n : ℕ), ((List.range n).map g).sum = ∑ t ∈ Finset.range n, g t := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  have hpt : ∀ t c, pointCount (ptEventAt G src t c) ≤
      if firstAt (src.ptEval c) t then 1 else 0 := by
    intro t c
    unfold ptEventAt
    split
    · split_ifs <;> simp_all [pointCount, ResEvent.isPoint]
    · simp [pointCount]
  have hset0 : ∀ t, pointCount ((List.range src.numSet).flatMap (setEventAt G K τ src t)) = 0 := by
    intro t
    unfold pointCount
    rw [List.countP_eq_zero]
    intro e he
    simp only [List.mem_flatMap, List.mem_range] at he
    obtain ⟨c, -, he⟩ := he
    unfold setEventAt at he
    split at he
    · split_ifs at he
      · simp only [List.mem_singleton] at he
        subst he
        simp [ResEvent.isPoint]
      · simp at he
    · simp at he
  have htab0 : ∀ t, pointCount ((List.range src.numTab).flatMap (tabEventAt G src t)) = 0 := by
    intro t
    unfold pointCount
    rw [List.countP_eq_zero]
    intro e he
    simp only [List.mem_flatMap, List.mem_range] at he
    obtain ⟨c, -, he⟩ := he
    unfold tabEventAt at he
    split_ifs at he
    · simp only [List.mem_singleton] at he
      subst he
      simp [ResEvent.isPoint]
    · simp at he
  have hstage : ∀ t, pointCount (stageEvents G K τ src t) =
      ∑ c ∈ Finset.range src.numPt, pointCount (ptEventAt G src t c) := by
    intro t
    have h1 := hset0 t
    have h2 := htab0 t
    unfold stageEvents
    unfold pointCount at h1 h2 ⊢
    rw [List.countP_append, List.countP_append, h1, h2, List.countP_flatMap, hls]
    rfl
  have hmain : pointCount (eventHistory G K τ src s) =
      ∑ t ∈ Finset.range s, ∑ c ∈ Finset.range src.numPt, pointCount (ptEventAt G src t c) := by
    unfold eventHistory
    unfold pointCount
    rw [List.countP_flatMap, hls]
    exact Finset.sum_congr rfl fun t _ => hstage t
  rw [hmain]
  calc ∑ t ∈ Finset.range s, ∑ c ∈ Finset.range src.numPt, pointCount (ptEventAt G src t c)
      ≤ ∑ t ∈ Finset.range s, ∑ c ∈ Finset.range src.numPt,
          (if firstAt (src.ptEval c) t then 1 else 0) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun c _ => hpt t c
    _ = ∑ c ∈ Finset.range src.numPt, ∑ t ∈ Finset.range s,
          (if firstAt (src.ptEval c) t then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _c ∈ Finset.range src.numPt, 1 := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Finset.sum_boole]
        simp only [Nat.cast_id]
        exact Finset.card_le_one.mpr fun a ha b hb =>
          firstAt_unique (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    _ = src.numPt := by simp

/-- The history has at most as many set events of certificate length `i` as there are set
candidates of cost `i`.
Proof: as in `pointCount_eventHistory_le`: a set event of candidate `c` carries the cost
`setCost c` and is emitted only at the unique stage `firstAt (setEval c)`.
Reference: L14 ("at most `∑ 2^i` set-program events"). -/
theorem costCount_eventHistory_le (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s i : ℕ) :
    costCount (eventHistory G K τ src s) i ≤
      ((List.range src.numSet).filter fun c => src.setCost c == i).length := by
  classical
  have hcf : ∀ (l : List ℕ) (f : ℕ → List (ResEvent α)),
      (l.flatMap f).countP (ResEvent.hasCost i) =
        (l.map fun a => (f a).countP (ResEvent.hasCost i)).sum := by
    intro l f
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.countP_append, ih, List.map_cons, List.sum_cons]
  have hlist : ∀ (n : ℕ) (f : ℕ → ℕ),
      ((List.range n).map f).sum = ∑ c ∈ Finset.range n, f c := by
    intro n f
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  have hpt0 : ∀ t, ((List.range src.numPt).flatMap (ptEventAt G src t)).countP
      (ResEvent.hasCost i) = 0 := by
    intro t
    rw [List.countP_eq_zero]
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨c, -, hc⟩ := he
    unfold ptEventAt at hc
    split at hc
    · split_ifs at hc
      · rw [List.mem_singleton] at hc
        subst hc
        simp [ResEvent.hasCost]
      · simp at hc
    · simp at hc
  have htab0 : ∀ t, ((List.range src.numTab).flatMap (tabEventAt G src t)).countP
      (ResEvent.hasCost i) = 0 := by
    intro t
    rw [List.countP_eq_zero]
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨c, -, hc⟩ := he
    unfold tabEventAt at hc
    split_ifs at hc
    · rw [List.mem_singleton] at hc
      subst hc
      simp [ResEvent.hasCost]
    · simp at hc
  have hterm : ∀ t c, (setEventAt G K τ src t c).countP (ResEvent.hasCost i) ≤
      if firstAt (src.setEval c) t = true then 1 else 0 := by
    intro t c
    unfold setEventAt
    split
    · split_ifs with h1 h2
      · exact List.countP_le_length.trans (by simp)
      · exact absurd h1.1 h2
      · simp
      · simp
    · simp
  have hzero : ∀ t c, src.setCost c ≠ i →
      (setEventAt G K τ src t c).countP (ResEvent.hasCost i) = 0 := by
    intro t c hci
    unfold setEventAt
    split
    · split_ifs
      · simp [ResEvent.hasCost, hci]
      · simp
    · simp
  have hcand : ∀ c, ∑ t ∈ Finset.range s, (setEventAt G K τ src t c).countP
      (ResEvent.hasCost i) ≤ if src.setCost c = i then 1 else 0 := by
    intro c
    split_ifs with hci
    · calc ∑ t ∈ Finset.range s, (setEventAt G K τ src t c).countP (ResEvent.hasCost i)
          ≤ ∑ t ∈ Finset.range s, if firstAt (src.setEval c) t = true then 1 else 0 :=
            Finset.sum_le_sum fun t _ => hterm t c
        _ = ((Finset.range s).filter fun t => firstAt (src.setEval c) t = true).card := by
            simp only [Finset.sum_boole, Nat.cast_id]
        _ ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
            firstAt_unique (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    · exact (Finset.sum_eq_zero fun t _ => hzero t c hci).le
  have hfin : ((Finset.range src.numSet).filter fun c => src.setCost c = i).card =
      ((List.range src.numSet).filter fun c => src.setCost c == i).length := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range ..).filter _)]
    congr 1
    ext c
    simp
  calc costCount (eventHistory G K τ src s) i
      = ∑ t ∈ Finset.range s, ∑ c ∈ Finset.range src.numSet,
          (setEventAt G K τ src t c).countP (ResEvent.hasCost i) := by
        unfold costCount eventHistory
        rw [hcf, hlist]
        refine Finset.sum_congr rfl fun t _ => ?_
        unfold stageEvents
        rw [List.countP_append, List.countP_append, hpt0, htab0, zero_add, add_zero, hcf,
          hlist]
    _ = ∑ c ∈ Finset.range src.numSet, ∑ t ∈ Finset.range s,
          (setEventAt G K τ src t c).countP (ResEvent.hasCost i) := Finset.sum_comm
    _ ≤ ∑ c ∈ Finset.range src.numSet, if src.setCost c = i then 1 else 0 :=
        Finset.sum_le_sum fun c _ => hcand c
    _ = _ := by
        simp only [Finset.sum_boole, Nat.cast_id]
        exact hfin

/-- The history has at most `numTab` table events.
Proof: as in `pointCount_eventHistory_le`, with the unique first completion stage.
Reference: L14 ("fewer than `2^(S+1)` table events"). -/
theorem tableCount_eventHistory_le (G : ResGame α) (K τ : ℕ) (src : EventSources α) (s : ℕ) :
    tableCount (eventHistory G K τ src s) ≤ src.numTab := by
  classical
  have hcf : ∀ (l : List ℕ) (f : ℕ → List (ResEvent α)),
      (l.flatMap f).countP ResEvent.isTable =
        (l.map fun a => (f a).countP ResEvent.isTable).sum := by
    intro l f
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.flatMap_cons, List.countP_append, ih, List.map_cons, List.sum_cons]
  have hlist : ∀ (n : ℕ) (f : ℕ → ℕ),
      ((List.range n).map f).sum = ∑ c ∈ Finset.range n, f c := by
    intro n f
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  have hpt0 : ∀ t, ((List.range src.numPt).flatMap (ptEventAt G src t)).countP
      ResEvent.isTable = 0 := by
    intro t
    rw [List.countP_eq_zero]
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨c, -, hc⟩ := he
    unfold ptEventAt at hc
    split at hc
    · split_ifs at hc
      · rw [List.mem_singleton] at hc
        subst hc
        simp [ResEvent.isTable]
      · simp at hc
    · simp at hc
  have hset0 : ∀ t, ((List.range src.numSet).flatMap (setEventAt G K τ src t)).countP
      ResEvent.isTable = 0 := by
    intro t
    rw [List.countP_eq_zero]
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨c, -, hc⟩ := he
    unfold setEventAt at hc
    split at hc
    · split_ifs at hc
      · rw [List.mem_singleton] at hc
        subst hc
        simp [ResEvent.isTable]
      · simp at hc
    · simp at hc
  have hterm : ∀ t c, (tabEventAt G src t c).countP ResEvent.isTable ≤
      if firstAt (fun t' => if tableDone G src c t' then some () else none) t = true
      then 1 else 0 := by
    intro t c
    unfold tabEventAt
    split_ifs with h1 h2
    · exact List.countP_le_length.trans (by simp)
    · exact absurd h1.1 h2
    · simp
    · simp
  have hcand : ∀ c, ∑ t ∈ Finset.range s, (tabEventAt G src t c).countP ResEvent.isTable ≤ 1 := by
    intro c
    calc ∑ t ∈ Finset.range s, (tabEventAt G src t c).countP ResEvent.isTable
        ≤ ∑ t ∈ Finset.range s,
            if firstAt (fun t' => if tableDone G src c t' then some () else none) t = true
            then 1 else 0 :=
          Finset.sum_le_sum fun t _ => hterm t c
      _ = ((Finset.range s).filter fun t =>
            firstAt (fun t' => if tableDone G src c t' then some () else none) t = true).card := by
          simp only [Finset.sum_boole, Nat.cast_id]
      _ ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
          firstAt_unique (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc tableCount (eventHistory G K τ src s)
      = ∑ t ∈ Finset.range s, ∑ c ∈ Finset.range src.numTab,
          (tabEventAt G src t c).countP ResEvent.isTable := by
        unfold tableCount eventHistory
        rw [hcf, hlist]
        refine Finset.sum_congr rfl fun t _ => ?_
        unfold stageEvents
        rw [List.countP_append, List.countP_append, hpt0, hset0, zero_add, zero_add, hcf,
          hlist]
    _ = ∑ c ∈ Finset.range src.numTab, ∑ t ∈ Finset.range s,
          (tabEventAt G src t c).countP ResEvent.isTable := Finset.sum_comm
    _ ≤ ∑ _c ∈ Finset.range src.numTab, 1 := Finset.sum_le_sum fun c _ => hcand c
    _ = src.numTab := by simp

/-- Every set event of the history is eligible.
Proof: unfold `eventHistory`, `stageEvents`, `setEventAt` (`List.mem_flatMap`); a set event is
emitted only under the test `SetEligible`. -/
theorem setEligible_of_mem_eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α)
    {s : ℕ} {Q : Finset α} {i : ℕ} (h : ResEvent.set Q i ∈ eventHistory G K τ src s) :
    SetEligible G K τ Q i := by
  simp only [eventHistory, stageEvents, List.mem_flatMap, List.mem_append,
    List.mem_range] at h
  obtain ⟨t, -, h⟩ := h
  rcases h with (⟨c, -, h⟩ | ⟨c, -, h⟩) | ⟨c, -, h⟩
  · unfold ptEventAt at h
    split at h
    · split_ifs at h <;> simp at h
    · simp at h
  · unfold setEventAt at h
    split at h
    · split_ifs at h with hc
      · simp only [List.mem_singleton, ResEvent.set.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc.2
      · simp at h
    · simp at h
  · unfold tabEventAt at h
    split_ifs at h <;> simp at h

/-- Every table event of the history is an exact partition of the cube.
Proof: a table event of candidate `c` at stage `s` passed `tableEntryOk` at every cube point:
each cell `Q = cell(u)` is a subset of the cube containing `u` (nonempty, covering), and if
`w ∈ cell(u) ∩ cell(u')` then `tabEval c w s = some cell(u)` and `= some cell(u')`, so the two
cells agree.  Reference: L14 ("finite decidable tests for an exact partition map"). -/
theorem isCellPartition_of_mem_eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α)
    {s : ℕ} {P : List (Finset α)} (h : ResEvent.table P ∈ eventHistory G K τ src s) :
    IsCellPartition G.cube P := by
  simp only [eventHistory, stageEvents, List.mem_flatMap, List.mem_append,
    List.mem_range] at h
  obtain ⟨t, -, h⟩ := h
  rcases h with (⟨c, -, h⟩ | ⟨c, -, h⟩) | ⟨c, -, h⟩
  · unfold ptEventAt at h
    split at h
    · split_ifs at h <;> simp at h
    · simp at h
  · unfold setEventAt at h
    split at h
    · split_ifs at h <;> simp at h
    · simp at h
  · unfold tabEventAt at h
    split_ifs at h with hc
    · simp only [List.mem_singleton, ResEvent.table.injEq] at h
      subst h
      have hall : ∀ u ∈ G.centers, tableEntryOk G src c t u = true := by
        have := hc.2
        rw [List.all_eq_true] at this
        exact this
      have hentry : ∀ u ∈ G.centers, ∃ Q, src.tabEval c u t = some Q ∧ Q ⊆ G.cube ∧ u ∈ Q ∧
          ∀ v ∈ Q, src.tabEval c v t = some Q := by
        intro u hu
        have h1 := hall u hu
        unfold tableEntryOk at h1
        split at h1
        · rename_i Q hQ
          exact ⟨Q, hQ, of_decide_eq_true h1⟩
        · exact absurd h1 (by simp)
      have hcell : ∀ Q ∈ tableCells G src c t, ∃ u ∈ G.centers,
          src.tabEval c u t = some Q ∧ Q ⊆ G.cube ∧ u ∈ Q ∧
            ∀ v ∈ Q, src.tabEval c v t = some Q := by
        intro Q hQ
        unfold tableCells at hQ
        rw [List.mem_map] at hQ
        obtain ⟨u, hu, rfl⟩ := hQ
        obtain ⟨Q', hQ', h2⟩ := hentry u hu
        rw [hQ', Option.getD_some]
        exact ⟨u, hu, hQ', h2⟩
      refine ⟨fun Q hQ => ?_, fun u hu => ?_, fun Q hQ Q' hQ' w hw hw' => ?_⟩
      · obtain ⟨u, -, -, hsub, hu, -⟩ := hcell Q hQ
        exact ⟨⟨u, hu⟩, hsub⟩
      · have hu' : u ∈ G.centers := List.mem_toFinset.mp hu
        obtain ⟨Q, hQ, -, hmem, -⟩ := hentry u hu'
        refine ⟨Q, ?_, hmem⟩
        unfold tableCells
        rw [List.mem_map]
        exact ⟨u, hu', by rw [hQ, Option.getD_some]⟩
      · obtain ⟨-, -, -, -, -, h1⟩ := hcell Q hQ
        obtain ⟨-, -, -, -, -, h2⟩ := hcell Q' hQ'
        have := (h1 w hw).symm.trans (h2 w hw')
        exact Option.some.inj this
    · simp at h

/-- **Completeness for points.**  If a point candidate with stable evaluations outputs a cube
point `u`, then a point event for `u` eventually appears.
Proof: take the least stage `s₁` with `(ptEval c s₁).isSome` (`Nat.find`); by stability its
output is `u`; `firstAt (ptEval c) s₁` holds, so `point u ∈ stageEvents s₁ ⊆ eventHistory
(s₁ + 1)`.  Reference: L14 ("prove completeness"). -/
theorem point_mem_eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α)
    (hstable : ∀ c s t u, s ≤ t → src.ptEval c s = some u → src.ptEval c t = some u)
    {c s : ℕ} {u : α} (hc : c < src.numPt) (hs : src.ptEval c s = some u) (hu : u ∈ G.cube) :
    ∃ t, ResEvent.point u ∈ eventHistory G K τ src t := by
  have hex : ∃ t, (src.ptEval c t).isSome = true := ⟨s, by rw [hs]; rfl⟩
  have h1 : (src.ptEval c (Nat.find hex)).isSome = true := Nat.find_spec hex
  have hmin : ∀ t < Nat.find hex, (src.ptEval c t).isNone = true := by
    intro t ht
    have := Nat.find_min hex ht
    simpa using this
  have hle : Nat.find hex ≤ s := Nat.find_min' hex (by rw [hs]; rfl)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp h1
  have huu : u' = u := by
    have := hstable c _ s u' hle hu'
    rw [hs] at this
    exact (Option.some.inj this).symm
  subst huu
  have hfirst : firstAt (src.ptEval c) (Nat.find hex) = true := by
    unfold firstAt
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    exact ⟨h1, fun t ht => hmin t ht⟩
  refine ⟨Nat.find hex + 1, ?_⟩
  unfold eventHistory
  rw [List.mem_flatMap]
  refine ⟨Nat.find hex, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  unfold stageEvents
  rw [List.mem_append, List.mem_append]
  left; left
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr hc, ?_⟩
  unfold ptEventAt
  rw [hu']
  simp [hfirst, hu]

/-- **Completeness for sets.**  If a set candidate with stable evaluations outputs an eligible
set `Q`, then the set event `(Q, setCost c)` eventually appears.
Proof: as for `point_mem_eventHistory`, at the least successful stage.
Reference: L14. -/
theorem set_mem_eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α)
    (hstable : ∀ c s t Q, s ≤ t → src.setEval c s = some Q → src.setEval c t = some Q)
    {c s : ℕ} {Q : Finset α} (hc : c < src.numSet) (hs : src.setEval c s = some Q)
    (hQ : SetEligible G K τ Q (src.setCost c)) :
    ∃ t, ResEvent.set Q (src.setCost c) ∈ eventHistory G K τ src t := by
  have hex : ∃ t, (src.setEval c t).isSome = true := ⟨s, by rw [hs]; rfl⟩
  have h1 : (src.setEval c (Nat.find hex)).isSome = true := Nat.find_spec hex
  have hmin : ∀ t < Nat.find hex, (src.setEval c t).isNone = true := by
    intro t ht
    have := Nat.find_min hex ht
    simpa using this
  have hle : Nat.find hex ≤ s := Nat.find_min' hex (by rw [hs]; rfl)
  obtain ⟨Q', hQ'⟩ := Option.isSome_iff_exists.mp h1
  have hQQ : Q' = Q := by
    have := hstable c _ s Q' hle hQ'
    rw [hs] at this
    exact (Option.some.inj this).symm
  subst hQQ
  have hfirst : firstAt (src.setEval c) (Nat.find hex) = true := by
    unfold firstAt
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    exact ⟨h1, fun t ht => hmin t ht⟩
  refine ⟨Nat.find hex + 1, ?_⟩
  unfold eventHistory
  rw [List.mem_flatMap]
  refine ⟨Nat.find hex, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  unfold stageEvents
  rw [List.mem_append, List.mem_append]
  left; right
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr hc, ?_⟩
  unfold setEventAt
  rw [hQ']
  simp [hfirst, hQ]

/-- **Completeness for tables.**  If a table candidate with stable evaluations computes, at some
stage, an exact partition map `out` on the whole cube, then the table event with cells
`G.centers.map out` eventually appears.  This applies to every candidate that halts on all cube
points, in particular to every globally total partition program; global totality is never
tested.
Proof: let `s₁ ≤ s` be the least stage with `tableDone`; by stability every evaluation at `s₁`
equals `out u`, so `tableEntryOk` holds at `s₁` and `tableCells c s₁ = G.centers.map out`.
Reference: L14, L21. -/
theorem table_mem_eventHistory (G : ResGame α) (K τ : ℕ) (src : EventSources α)
    (hstable : ∀ c u s t Q, s ≤ t → src.tabEval c u s = some Q → src.tabEval c u t = some Q)
    {c s : ℕ} {out : α → Finset α} (hc : c < src.numTab)
    (hs : ∀ u ∈ G.centers, src.tabEval c u s = some (out u))
    (hout : ∀ u ∈ G.centers, out u ⊆ G.cube ∧ u ∈ out u ∧ ∀ v ∈ out u, out v = out u) :
    ∃ t, ResEvent.table (G.centers.map out) ∈ eventHistory G K τ src t := by
  have hdone : ∀ t, (∀ u ∈ G.centers, (src.tabEval c u t).isSome = true) →
      tableDone G src c t = true := by
    intro t ht
    unfold tableDone
    rw [List.all_eq_true]
    exact ht
  have hex : ∃ t, tableDone G src c t = true :=
    ⟨s, hdone s fun u hu => by rw [hs u hu]; rfl⟩
  set s₁ := Nat.find hex with hs₁
  have h1 : tableDone G src c s₁ = true := Nat.find_spec hex
  have hmin : ∀ t < s₁, tableDone G src c t = false := by
    intro t ht
    have := Nat.find_min hex ht
    simpa using this
  have hle : s₁ ≤ s := Nat.find_min' hex (hdone s fun u hu => by rw [hs u hu]; rfl)
  have hval : ∀ u ∈ G.centers, src.tabEval c u s₁ = some (out u) := by
    intro u hu
    have hsome : (src.tabEval c u s₁).isSome = true := by
      unfold tableDone at h1
      rw [List.all_eq_true] at h1
      exact h1 u hu
    obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hsome
    have := hstable c u s₁ s Q hle hQ
    rw [hs u hu] at this
    rw [hQ, this]
  have hfirst : firstAt (fun t => if tableDone G src c t then some () else none) s₁ = true := by
    unfold firstAt
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    refine ⟨by simp [h1], fun t ht => by simp [hmin t ht]⟩
  have hok : G.centers.all (tableEntryOk G src c s₁) = true := by
    rw [List.all_eq_true]
    intro u hu
    unfold tableEntryOk
    rw [hval u hu]
    obtain ⟨hsub, hmem, hconst⟩ := hout u hu
    refine decide_eq_true ⟨hsub, hmem, fun v hv => ?_⟩
    have hvc : v ∈ G.centers := List.mem_toFinset.mp (hsub hv)
    rw [hval v hvc, hconst v hv]
  have hcells : tableCells G src c s₁ = G.centers.map out := by
    unfold tableCells
    refine List.map_congr_left fun u hu => ?_
    rw [hval u hu]
    rfl
  refine ⟨s₁ + 1, ?_⟩
  unfold eventHistory
  rw [List.mem_flatMap]
  refine ⟨s₁, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  unfold stageEvents
  rw [List.mem_append]
  right
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_range.mpr hc, ?_⟩
  unfold tabEventAt
  rw [hcells]
  split_ifs with h
  · exact List.mem_singleton_self _
  · exact absurd ⟨hfirst, hok⟩ h

/-- **Reservoir event enumeration** (blueprint node L14, generic form).  For abstract bounded
evaluators with fewer than `2^K` point candidates, at most `2^i` set candidates of cost `i`, and
fewer than `2^(S+1)` table candidates, the deterministic event history `eventHistory` grows by
appending, satisfies the count/certificate invariants `ValidHistory` at every stage, and is
complete: every stable point output in the cube, every stable eligible set output and every
stable table computing an exact partition map eventually produces its event. -/
theorem reservoirEventEnumeration (G : ResGame α) (K τ S : ℕ) (src : EventSources α)
    (hpt : src.numPt < 2 ^ K)
    (hset : ∀ i, ((List.range src.numSet).filter fun c => src.setCost c == i).length ≤ 2 ^ i)
    (htab : src.numTab < 2 ^ (S + 1)) :
    (∀ s t, s ≤ t → eventHistory G K τ src s <+: eventHistory G K τ src t) ∧
    (∀ s, ValidHistory G K τ S (eventHistory G K τ src s)) ∧
    ((∀ c s t u, s ≤ t → src.ptEval c s = some u → src.ptEval c t = some u) →
      ∀ c < src.numPt, ∀ s u, src.ptEval c s = some u → u ∈ G.cube →
        ∃ t, ResEvent.point u ∈ eventHistory G K τ src t) ∧
    ((∀ c s t Q, s ≤ t → src.setEval c s = some Q → src.setEval c t = some Q) →
      ∀ c < src.numSet, ∀ s Q, src.setEval c s = some Q → SetEligible G K τ Q (src.setCost c) →
        ∃ t, ResEvent.set Q (src.setCost c) ∈ eventHistory G K τ src t) ∧
    ((∀ c u s t Q, s ≤ t → src.tabEval c u s = some Q → src.tabEval c u t = some Q) →
      ∀ c < src.numTab, ∀ s (out : α → Finset α),
        (∀ u ∈ G.centers, src.tabEval c u s = some (out u)) →
        (∀ u ∈ G.centers, out u ⊆ G.cube ∧ u ∈ out u ∧ ∀ v ∈ out u, out v = out u) →
        ∃ t, ResEvent.table (G.centers.map out) ∈ eventHistory G K τ src t) := by
  refine ⟨fun s t hst => eventHistory_prefix G K τ src hst, fun s => ?_,
    fun hst c hc s u hs hu => point_mem_eventHistory G K τ src hst hc hs hu,
    fun hst c hc s Q hs hQ => set_mem_eventHistory G K τ src hst hc hs hQ,
    fun hst c hc s out hs hout => table_mem_eventHistory G K τ src hst hc hs hout⟩
  refine ⟨(pointCount_eventHistory_le G K τ src s).trans_lt hpt, fun Q i h => ?_,
    fun i => (costCount_eventHistory_le G K τ src s i).trans (hset i),
    (tableCount_eventHistory_le G K τ src s).trans_lt htab,
    fun P h => isCellPartition_of_mem_eventHistory G K τ src h⟩
  obtain ⟨-, h1, h2, h3⟩ := setEligible_of_mem_eventHistory G K τ src h
  exact ⟨h1, h2, h3⟩

end Kolmogorov.StrongMerging.Lower
