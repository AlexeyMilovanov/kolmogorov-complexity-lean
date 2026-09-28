import KolmogorovMathlib.StoppingComplexity.Game

/-!
# Legal local histories: disjoint answers and path loads

Two facts about the histories of the finite game (blueprint part 02, DEF-03 and LEM-ROUND-04)
used by the marker round: a legal answer keeps the answers at distinct comparable vertices
pairwise disjoint, and the load on a path of requests with pairwise distinct vertices and a
common exponent `E` is at most the number of possible vertices times `2^{-E}`.
-/

namespace Kolmogorov

/-- Counting the load on a path: if the requests of `A` have pairwise distinct vertices and every
request of `A` at a prefix of `v` has exponent `E` and its vertex in the list `V`, then the load
of `A` on `v` is at most `|V| 2^{-E}`. Blueprint 02 LEM-ROUND-04. -/
theorem load_le_length_mul_requestWeight {A : List Request} {v : BitString}
    {V : List BitString} {E : ℕ} (hA : (A.map Prod.fst).Nodup)
    (hV : ∀ r ∈ A, r.1 <+: v → r.1 ∈ V ∧ r.2 = E) :
    load A v ≤ V.length * requestWeight E := by
  unfold load
  set F := A.filter fun r => decide (r.1 <+: v)
  have hF : ∀ r ∈ F, r.1 ∈ V ∧ r.2 = E := fun r hr => by
    rw [List.mem_filter, decide_eq_true_iff] at hr
    exact hV r hr.1 hr.2
  have hsum : (F.map fun r => requestWeight r.2).sum = F.length * requestWeight E := by
    rw [List.map_congr_left fun r hr => by rw [(hF r hr).2], List.map_const', List.sum_replicate,
      nsmul_eq_mul]
  have hnd : (F.map Prod.fst).Nodup := hA.sublist ((List.filter_sublist).map _)
  have hlen : (F.map Prod.fst).length ≤ V.length :=
    (hnd.subperm fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact (hF r hr).1).length_le
  rw [List.length_map] at hlen
  rw [hsum]
  have hw : 0 ≤ requestWeight E := by
    unfold requestWeight
    positivity
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hw

/-- Legal play keeps the answers pairwise disjoint: if the answers of `H` at distinct comparable
vertices are disjoint and `a` is a legal answer to `r` after `H`, the same holds for
`H ++ [(r, a)]`. Blueprint 02 DEF-03. -/
theorem answers_disjoint_append {S : GameSchedule} {U : ℚ} {H : LocalHistory} {r : Request}
    {a : DyadicCell}
    (hH : ∀ e ∈ H, ∀ e' ∈ H, IsComparable e.1.1 e'.1.1 → e.1.1 ≠ e'.1.1 → CellsDisjoint e.2 e'.2)
    (ha : LegalAnswer S U H r a) :
    ∀ e ∈ H ++ [(r, a)], ∀ e' ∈ H ++ [(r, a)], IsComparable e.1.1 e'.1.1 → e.1.1 ≠ e'.1.1 →
      CellsDisjoint e.2 e'.2 := by
  intro e he e' he' hcomp hne
  rcases List.mem_append.1 he with he | he <;> rcases List.mem_append.1 he' with he' | he'
  · exact hH e he e' he' hcomp hne
  · rw [List.mem_singleton.1 he'] at hcomp hne ⊢
    exact ha.2.2 e he hcomp hne
  · rw [List.mem_singleton.1 he] at hcomp hne ⊢
    exact (ha.2.2 e' he' hcomp.symm (Ne.symm hne)).symm
  · rw [List.mem_singleton.1 he, List.mem_singleton.1 he'] at hne
    exact absurd rfl hne

end Kolmogorov
