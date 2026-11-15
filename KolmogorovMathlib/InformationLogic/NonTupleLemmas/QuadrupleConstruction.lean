import KolmogorovMathlib.InformationLogic.NonTupleComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Complexity.EnumerableFamilies.CountingBounds
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Quadruple Construction

Construction of quadruples of `n`-bit words `(a, b, e, d)` whose Kolmogorov profile is close to
that of a generic triple extended by a computable fourth word: a counting argument produces an
incompressible triple, and the complexities of all sub-tuples are then pinned down to
`min (|S|, 3) · n` up to a logarithmic slack, using the upper bounds of Problem 342 and symmetry
of information.  The main declarations are
`exists_quadruples_profileClose_problemK_quad_gap_count` and
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`.  This is part of the
non-tuple-complexity lemmas of the book of Shen, Uspensky and Vereshchagin.
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- Step 1 of the proof of `exists_quadruples_profileClose_problemK_quad_gap`:
counting.  If `T` is a set of triples of `n`-bit words with more than half of all `2^(3n)`
triples, then some triple of `T` is incompressible: the code `listCode [a, b, e]` has plain
complexity at least `3n − 1`.  (Fewer than `2^(3n-1)` strings have complexity `< 3n − 1`, and
`listCode` is injective on triples.) -/
theorem exists_quadruples_profileClose_problemK_quad_gap_count (D : Map) (n : ℕ)
    (T : Set (BitString × BitString × BitString))
    (hT : ∀ t ∈ T, t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n)
    (hcard : 2 ^ (3 * n) < 2 * T.ncard) :
    ∃ t ∈ T, ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [t.1, t.2.1, t.2.2]) := by
  classical
  have hpos : 0 < T.ncard := by
    have : 0 < 2 ^ (3 * n) := Nat.two_pow_pos _
    omega
  have hfin : T.Finite := Set.finite_of_ncard_pos hpos
  obtain ⟨t0, ht0⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
  by_cases hn : n = 0
  · subst hn
    exact ⟨t0, ht0, by simp⟩
  · have hcard' : 2 ^ (3 * n - 2 + 1) ≤ T.ncard := by
      have h1 : 2 ^ (3 * n - 2 + 1) = 2 ^ (3 * n - 1) := by congr 1; omega
      have h3 : 2 ^ (3 * n) = 2 * 2 ^ (3 * n - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    set S : Finset BitString :=
      hfin.toFinset.image (fun t => listCode [t.1, t.2.1, t.2.2]) with hS
    have hinj : Set.InjOn (fun t : BitString × BitString × BitString =>
        listCode [t.1, t.2.1, t.2.2]) (hfin.toFinset : Set _) := by
      intro x _ y _ hxy
      have := listCode_injective hxy
      simp only [List.cons.injEq, and_true] at this
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2)
    have hScard : S.card = T.ncard := by
      rw [hS, Finset.card_image_of_injOn hinj, Set.ncard_eq_toFinset_card T hfin]
    obtain ⟨s, hs, hK⟩ := exists_mem_condK_gt_of_card_le D [] (3 * n - 2) S (by omega)
    rw [hS, Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨t, hfin.mem_toFinset.mp ht, ?_⟩
    have h4 : ((3 * n - 2 : ℕ) : ℕ∞) < plainK D (listCode [t.1, t.2.1, t.2.2]) := hK
    have h5 : ((3 * n - 2 : ℕ) : ℕ∞) + 1 ≤ plainK D (listCode [t.1, t.2.1, t.2.2]) :=
      Order.add_one_le_of_lt h4
    have h6 : ((3 * n - 1 : ℕ) : ℕ∞) = ((3 * n - 2 : ℕ) : ℕ∞) + 1 := by
      have : 3 * n - 1 = (3 * n - 2) + 1 := by omega
      rw [this]; push_cast; rfl
    rw [h6]; exact h5

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_upper`:
appending one string `w` to a list costs at most `|w| + O(log |w|)` bits of complexity. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_upper_aux_append
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (L : List BitString) (w : BitString),
      plainK D (listCode (L ++ [w])) ≤
        plainK D (listCode L) + ((w.length + logSlack k w.length : ℕ) : ℕ∞) := by
  let f : BitString → BitString := fun p =>
    listCode (decodeListCode (decodeSecond p) ++ [decodeFirst p])
  have hf : Computable f :=
    listCode_computable.comp (Computable.list_concat.comp
      (decodeListCode_computable.comp decodeSecond_computable) decodeFirst_computable)
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD f hf
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 1 c2
  refine ⟨C + (c1 + k0 + c2), fun L w => ?_⟩
  have hfw : f (pairCode w (listCode L)) = listCode (L ++ [w]) := by
    simp [f, decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode]
  have hw : plainK D w ≤ ((w.length + c2 : ℕ) : ℕ∞) := by
    have := hc2 w; push_cast; exact this
  have hne : plainK D w ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hw
  have hcv : cVal D w ≤ w.length + c2 := by
    have h1 : plainK D w = (cVal D w : ℕ∞) := by
      unfold cVal; rw [ENat.natCast_toNat hne]
    rw [h1] at hw; exact_mod_cast hw
  have hlog : 2 * Nat.log 2 (cVal D w) ≤ logSlack C w.length := by
    have h1 : Nat.log 2 (cVal D w) ≤ (Nat.bits (1 * w.length + c2)).length := by
      rcases Nat.eq_zero_or_pos (cVal D w) with h0 | hpos
      · rw [h0]; simp
      · have h2 : 2 ^ Nat.log 2 (cVal D w) ≤ 1 * w.length + c2 := by
          have := Nat.pow_log_le_self 2 hpos.ne'
          omega
        have h3 : Nat.log 2 (cVal D w) < Nat.size (1 * w.length + c2) := Nat.lt_size.mpr h2
        rw [← Nat.size_eq_bits_len] at h3
        omega
    have h4 := hC w.length
    unfold logSlack at h4 ⊢
    omega
  have hnat : w.length + c2 + (logSlack C w.length + k0) + c1 ≤
      w.length + logSlack (C + (c1 + k0 + c2)) w.length := by
    have e1 := logSlack_add_constants C (c1 + k0 + c2) w.length
    have e2 : c1 + k0 + c2 ≤ logSlack (c1 + k0 + c2) w.length := by unfold logSlack; omega
    omega
  have hE : ((2 * Nat.log 2 (cVal D w) + k0 : ℕ) : ℕ∞) ≤
      ((logSlack C w.length + k0 : ℕ) : ℕ∞) := by
    exact_mod_cast (by omega : 2 * Nat.log 2 (cVal D w) + k0 ≤ logSlack C w.length + k0)
  calc plainK D (listCode (L ++ [w])) = plainK D (f (pairCode w (listCode L))) := by rw [hfw]
    _ ≤ plainK D (pairCode w (listCode L)) + (c1 : ℕ∞) := hc1 _
    _ ≤ (plainK D w + plainK D (listCode L) + ((2 * Nat.log 2 (cVal D w) + k0 : ℕ) : ℕ∞)) +
          (c1 : ℕ∞) := by gcongr; exact hk0 w (listCode L)
    _ ≤ (((w.length + c2 : ℕ) : ℕ∞) + plainK D (listCode L) +
          ((logSlack C w.length + k0 : ℕ) : ℕ∞)) + (c1 : ℕ∞) := by gcongr
    _ = plainK D (listCode L) +
          ((w.length + c2 + (logSlack C w.length + k0) + c1 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ plainK D (listCode L) +
          ((w.length + logSlack (C + (c1 + k0 + c2)) w.length : ℕ) : ℕ∞) := by
        gcongr

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_upper`:
the code of a list `M` of `n`-bit strings has complexity at most `|M| (n + O(log n)) + O(1)`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_upper_aux_list
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k c0 : ℕ, ∀ (n : ℕ) (M : List BitString), (∀ x ∈ M, x.length = n) →
      plainK D (listCode M) ≤ ((M.length * (n + logSlack k n) + c0 : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_upper_aux_append D hD
  obtain ⟨c0, hc0⟩ := plainK_le_length D hD
  refine ⟨k, c0, fun n M hM => ?_⟩
  induction M using List.reverseRecOn with
  | nil =>
    have := hc0 []
    simpa using this
  | append_singleton M w ih =>
    have hM' : ∀ x ∈ M, x.length = n := fun x hx => hM x (List.mem_append_left _ hx)
    have hw : w.length = n := hM w (by simp)
    calc plainK D (listCode (M ++ [w]))
        ≤ plainK D (listCode M) + ((w.length + logSlack k w.length : ℕ) : ℕ∞) := hk _ _
      _ ≤ ((M.length * (n + logSlack k n) + c0 : ℕ) : ℕ∞) +
            ((n + logSlack k n : ℕ) : ℕ∞) := by
          rw [hw]; gcongr; exact ih hM'
      _ = (((M ++ [w]).length * (n + logSlack k n) + c0 : ℕ) : ℕ∞) := by
          rw [List.length_append, List.length_singleton]; push_cast; ring

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_upper`:
the code of at most three `n`-bit strings has complexity `≤ |M| n + O(log n)`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_upper_aux_short
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (M : List BitString), (∀ x ∈ M, x.length = n) → M.length ≤ 3 →
      plainK D (listCode M) ≤ ((M.length * n : ℕ) : ℕ∞) + (logSlack k n : ℕ∞) := by
  obtain ⟨k, c0, h⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_upper_aux_list D hD
  refine ⟨3 * k + c0, fun n M hM hlen => ?_⟩
  refine (h n M hM).trans ?_
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  unfold logSlack
  have h1 : M.length * logSlack k n ≤ 3 * logSlack k n := Nat.mul_le_mul_right _ hlen
  unfold logSlack at h1
  rw [Nat.mul_add, add_assoc]
  nlinarith [Nat.zero_le (c0 * (Nat.bits n).length)]

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_upper`:
the length of the list of a sub-tuple is the cardinality of the index set. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_upper_aux_len :
    ∀ S : Finset (Fin 4), ((List.finRange 4).filter (fun i => decide (i ∈ S))).length = S.card := by
  decide

/-- Step 1 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
the upper bounds.  For `n`-bit words `a, b, e` and `d = Q n a b e` (also an `n`-bit word, `Q`
computable) every non-empty sub-tuple `S` of `(a, b, e, d)` has `C(S) ≤ min(|S|, 3) · n + O(log n)`.
Proof: `C(x) ≤ n + O(1)`, `C(x, y) ≤ C(x) + C(y) + O(log n)` (also for triples), and for the whole
quadruple `d` is computable from `n = |a|` and `(a, b, e)`, so `C(a, b, e, d) ≤ C(a, b, e) + O(1)
≤ 3n + O(log n)`. -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_upper
    (D : Map) (hD : isOptimalConditional D)
    (Q : ℕ → BitString → BitString → BitString → BitString)
    (hQ : Computable (fun t : ℕ × BitString × BitString × BitString =>
      Q t.1 t.2.1 t.2.2.1 t.2.2.2)) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e : BitString), a.length = n → b.length = n → e.length = n →
      (Q n a b e).length = n →
      ∀ S : Finset (Fin 4), S.Nonempty →
        plainK D (subtupleCode ![a, b, e, Q n a b e] S) ≤
          ((min S.card 3 * n : ℕ) : ℕ∞) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, h1⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_upper_aux_short D hD
  let g : BitString → BitString := fun x =>
    listCode (decodeListCode x ++ [Q (((decodeListCode x).getD 0 []).length)
      ((decodeListCode x).getD 0 []) ((decodeListCode x).getD 1 [])
      ((decodeListCode x).getD 2 [])])
  have hg : Computable g := by
    have hl : Computable decodeListCode := decodeListCode_computable
    have hget : ∀ i : ℕ, Computable fun x : BitString => (decodeListCode x).getD i [] := fun i =>
      ((Primrec.list_getD ([] : BitString)).to_comp.comp hl (Computable.const i) :)
    have hq : Computable fun x : BitString => Q (((decodeListCode x).getD 0 []).length)
        ((decodeListCode x).getD 0 []) ((decodeListCode x).getD 1 [])
        ((decodeListCode x).getD 2 []) :=
      hQ.comp (Computable.pair (Computable.list_length.comp (hget 0))
        (Computable.pair (hget 0) (Computable.pair (hget 1) (hget 2))))
    exact listCode_computable.comp (Computable.list_concat.comp hl hq)
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD g hg
  refine ⟨k1 + c1, fun n a b e ha hb he hd S hS => ?_⟩
  have hlen : ∀ i : Fin 4, (![a, b, e, Q n a b e] i).length = n := by
    intro i; fin_cases i <;> simp [ha, hb, he, hd]
  have hcard : S.card ≤ 4 := by simpa using Finset.card_le_univ S
  have hws : ∀ k' k'' : ℕ, k' ≤ k'' → (logSlack k' n : ℕ∞) ≤ (logSlack k'' n : ℕ∞) :=
    fun k' k'' h => by exact_mod_cast logSlack_mono_left h n
  by_cases h4 : S.card = 4
  · have hS' : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using h4)
    subst hS'
    have e0 : subtupleCode ![a, b, e, Q n a b e] (Finset.univ : Finset (Fin 4)) =
        listCode [a, b, e, Q n a b e] := by
      simp [subtupleCode, List.finRange]
    have hgx : g (listCode [a, b, e]) = listCode [a, b, e, Q n a b e] := by
      have hdl : decodeListCode (listCode [a, b, e]) = [a, b, e] := decodeListCode_listCode _
      simp only [g, hdl]
      simp [ha]
    have hm : min (Finset.univ : Finset (Fin 4)).card 3 * n = 3 * n := by simp
    rw [e0, hm, ← hgx]
    refine (hc1 _).trans ?_
    have := h1 n [a, b, e] (by
                intro x hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl | rfl <;> assumption)
      (by simp)
    simp only [List.length_cons, List.length_nil] at this
    calc plainK D (listCode [a, b, e]) + (c1 : ℕ∞)
        ≤ ((3 * n : ℕ) : ℕ∞) + (logSlack k1 n : ℕ∞) + (c1 : ℕ∞) := by gcongr
      _ ≤ ((3 * n : ℕ) : ℕ∞) + (logSlack (k1 + c1) n : ℕ∞) := by
          rw [add_assoc]
          gcongr
          have := logSlack_add_constants k1 c1 n
          have h2 : c1 ≤ logSlack c1 n := by unfold logSlack; omega
          rw [← Nat.cast_add]
          exact_mod_cast (by omega : logSlack k1 n + c1 ≤ logSlack (k1 + c1) n)
  · have h3 : S.card ≤ 3 := by omega
    have hM : (((List.finRange 4).filter (fun i => decide (i ∈ S))).map
        ![a, b, e, Q n a b e]).length = S.card := by
      rw [List.length_map]
      exact exists_quadruples_profileClose_problemK_quad_gap_upper_aux_len S
    have := h1 n (((List.finRange 4).filter (fun i => decide (i ∈ S))).map
        ![a, b, e, Q n a b e]) (by
          intro x hx
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          exact hlen i) (by omega)
    rw [hM] at this
    have hmin : min S.card 3 = S.card := by omega
    rw [hmin]
    exact (hws k1 (k1 + c1) (by omega)) |> fun hh => this.trans (by gcongr)

/-- Auxiliary for step 2: if `2n ≤ P0 + s2`, `P0 ≤ X + Y + s1` and `Y ≤ n + C`, then
`n ≤ X + (C + s1 + s2)` (cancelling the finite `n`). -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_u_aux_cancel
    (n C s1 s2 : ℕ) (P0 X Y : ℕ∞) (hP : ((2 * n : ℕ) : ℕ∞) ≤ P0 + (s2 : ℕ∞))
    (hPX : P0 ≤ X + Y + (s1 : ℕ∞)) (hY : Y ≤ (n : ℕ∞) + (C : ℕ∞)) :
    (n : ℕ∞) ≤ X + ((C + s1 + s2 : ℕ) : ℕ∞) := by
  have h : ((2 * n : ℕ) : ℕ∞) ≤ X + Y + (s1 : ℕ∞) + (s2 : ℕ∞) :=
    hP.trans (add_le_add hPX le_rfl)
  induction X using ENat.recTopCoe with
  | top => simp
  | coe x =>
    induction Y using ENat.recTopCoe with
    | top => exact absurd hY (by simp)
    | coe y =>
      have hy : y ≤ n + C := by exact_mod_cast hY
      have h' : 2 * n ≤ x + y + s1 + s2 := by exact_mod_cast h
      exact_mod_cast (by omega : n ≤ x + (C + s1 + s2))

/-- Step 2 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
the seven conditional lower bounds obtained from the three problem bounds.  For `n`-bit words
`a, b, e, d` with `2n ≤ C((x → y) ∧ (z → d)) + logSlack c n` for `(x, z, y)` equal to
`(a, b, e)`, `(e, a, b)`, `(b, e, a)`, each of `C(d)`, `C(d | a)`, `C(d | b)`, `C(d | e)`,
`C(a | b, d)`, `C(b | e, d)`, `C(e | a, d)` is `≥ n − O(log n)`.  Proof: by the three upper bounds
of Problem 342 (`problemK_quad_le_condK_add_condK`, `problemK_quad_le_condK_add_plainK_left`,
`problemK_quad_le_condK_add_plainK_right`), `2n − s ≤ C(e|a) + C(d|b)`, `≤ C(e|a,d) + C(d)`
for `(a, b, e, d)`, and the rotated tuples `(e, a, b, d)`: `C(b|e) + C(d|a)`, `C(b|e,d) + C(d)`;
`(b, e, a, d)`: `C(a|b) + C(d|e)`, `C(a|b,d) + C(d)`; and every conditional complexity of an
`n`-bit word is `≤ n + O(1)` (`condK_le_plainK`, `plainK_le_length`). -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_conditional
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e d : BitString), a.length = n → b.length = n → e.length = n →
      d.length = n →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![a, b, e, d]) + (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![e, a, b, d]) + (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![b, e, a, d]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D d + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D d a + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D d b + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D d e + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D a (pairCode b d) + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D b (pairCode e d) + (logSlack k n : ℕ∞) ∧
      (n : ℕ∞) ≤ condK D e (pairCode a d) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, h1⟩ := problemK_quad_le_condK_add_condK D hD P hP
  obtain ⟨k3, h3⟩ := problemK_quad_le_condK_add_plainK_right D hD P hP
  obtain ⟨ca, hca⟩ := condK_le_plainK D hD
  obtain ⟨cb, hcb⟩ := plainK_le_length D hD
  refine ⟨c + k1 + k3 + (ca + cb), ?_⟩
  intro n a b e d ha hb he hd hp1 hp2 hp3
  have hcond : ∀ x y : BitString, x.length = n →
      condK D x y ≤ (n : ℕ∞) + ((ca + cb : ℕ) : ℕ∞) := by
    intro x y hx
    calc condK D x y ≤ plainK D x + (ca : ℕ∞) := hca x y
      _ ≤ ((x.length : ℕ∞) + (cb : ℕ∞)) + (ca : ℕ∞) := by gcongr; exact hcb x
      _ = (n : ℕ∞) + ((ca + cb : ℕ) : ℕ∞) := by rw [hx]; push_cast; ring
  have hplain : ∀ x : BitString, x.length = n →
      plainK D x ≤ (n : ℕ∞) + ((ca + cb : ℕ) : ℕ∞) := by
    intro x hx
    calc plainK D x ≤ (x.length : ℕ∞) + (cb : ℕ∞) := hcb x
      _ ≤ (n : ℕ∞) + ((ca + cb : ℕ) : ℕ∞) := by
        rw [hx]; gcongr; exact_mod_cast Nat.le_add_left _ _
  have hm1 : (ca + cb) + logSlack k1 n + logSlack c n ≤ logSlack (c + k1 + k3 + (ca + cb)) n := by
    unfold logSlack
    nlinarith [Nat.zero_le (k3 * (Nat.bits n).length), Nat.zero_le ((ca + cb) *
        (Nat.bits n).length)]
  have hm3 : (ca + cb) + logSlack k3 n + logSlack c n ≤ logSlack (c + k1 + k3 + (ca + cb)) n := by
    unfold logSlack
    nlinarith [Nat.zero_le (k1 * (Nat.bits n).length), Nat.zero_le ((ca + cb) *
        (Nat.bits n).length)]
  have fin : ∀ (X : ℕ∞) (m : ℕ), m ≤ logSlack (c + k1 + k3 + (ca + cb)) n →
      (n : ℕ∞) ≤ X + (m : ℕ∞) →
      (n : ℕ∞) ≤ X + (logSlack (c + k1 + k3 + (ca + cb)) n : ℕ∞) := by
    intro X m hm h
    exact h.trans (add_le_add le_rfl (by exact_mod_cast hm))
  have aux := exists_quadruples_profileClose_problemK_quad_gap_profile_u_aux_cancel n
    (ca + cb)
  -- the three problems' upper bounds
  have u1 : problemK D (quadProblem P ![a, b, e, d]) ≤
      condK D e a + condK D d b + (logSlack k1 n : ℕ∞) :=
    h1 n ![a, b, e, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  have u2 : problemK D (quadProblem P ![e, a, b, d]) ≤
      condK D b e + condK D d a + (logSlack k1 n : ℕ∞) :=
    h1 n ![e, a, b, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  have u3 : problemK D (quadProblem P ![b, e, a, d]) ≤
      condK D a b + condK D d e + (logSlack k1 n : ℕ∞) :=
    h1 n ![b, e, a, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  have v1 : problemK D (quadProblem P ![a, b, e, d]) ≤
      condK D e (pairCode a d) + plainK D d + (logSlack k3 n : ℕ∞) :=
    h3 n ![a, b, e, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  have v2 : problemK D (quadProblem P ![e, a, b, d]) ≤
      condK D b (pairCode e d) + plainK D d + (logSlack k3 n : ℕ∞) :=
    h3 n ![e, a, b, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  have v3 : problemK D (quadProblem P ![b, e, a, d]) ≤
      condK D a (pairCode b d) + plainK D d + (logSlack k3 n : ℕ∞) :=
    h3 n ![b, e, a, d] (fun i => by fin_cases i <;> simp [ha, hb, he, hd])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fin _ _ hm3 (aux (logSlack k3 n) (logSlack c n) _ (plainK D d)
      (condK D e (pairCode a d)) hp1 (by rw [add_comm (plainK D d)]; exact v1) (hcond e _ he))
  · exact fin _ _ hm1 (aux (logSlack k1 n) (logSlack c n) _ (condK D d a) (condK D b e) hp2
      (by rw [add_comm (condK D d a)]; exact u2) (hcond b _ hb))
  · exact fin _ _ hm1 (aux (logSlack k1 n) (logSlack c n) _ (condK D d b) (condK D e a) hp1
      (by rw [add_comm (condK D d b)]; exact u1) (hcond e _ he))
  · exact fin _ _ hm1 (aux (logSlack k1 n) (logSlack c n) _ (condK D d e) (condK D a b) hp3
      (by rw [add_comm (condK D d e)]; exact u3) (hcond a _ ha))
  · exact fin _ _ hm3 (aux (logSlack k3 n) (logSlack c n) _ (condK D a (pairCode b d))
      (plainK D d) hp3 v3 (hplain d hd))
  · exact fin _ _ hm3 (aux (logSlack k3 n) (logSlack c n) _ (condK D b (pairCode e d))
      (plainK D d) hp2 v2 (hplain d hd))
  · exact fin _ _ hm3 (aux (logSlack k3 n) (logSlack c n) _ (condK D e (pairCode a d))
      (plainK D d) hp1 v1 (hplain d hd))

/-- Auxiliary for step 3: the selector.  From `w = ⟨X, q⟩` it decodes the list of words of `X`,
appends the two halves (length `|q| / m`) of `q`, and outputs the code of the triple of words at
positions `σ`. -/
private def exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel
    (m : ℕ) (σ : ℕ × ℕ × ℕ) (w : BitString) : BitString :=
  listCode [(decodeListCode (decodeFirst w) ++ [(decodeSecond w).take ((decodeSecond w).length / m),
      (decodeSecond w).drop ((decodeSecond w).length / m)]).getD σ.1 [],
    (decodeListCode (decodeFirst w) ++ [(decodeSecond w).take ((decodeSecond w).length / m),
      (decodeSecond w).drop ((decodeSecond w).length / m)]).getD σ.2.1 [],
    (decodeListCode (decodeFirst w) ++ [(decodeSecond w).take ((decodeSecond w).length / m),
      (decodeSecond w).drop ((decodeSecond w).length / m)]).getD σ.2.2 []]

/-- Auxiliary for step 3: the selector is computable. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_computable
    (m : ℕ) (σ : ℕ × ℕ × ℕ) :
    Computable (exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel m σ) := by
  have hq : Computable (fun w : BitString => decodeSecond w) := decodeSecond_computable
  have hlen : Computable (fun w : BitString => (decodeSecond w).length / m) :=
    Primrec.nat_div.to_comp.comp (Computable.list_length.comp hq) (Computable.const m)
  have hq2 : Computable (fun w : BitString => (decodeSecond w).take ((decodeSecond w).length / m))
      :=
    Primrec.list_take.to_comp.comp hlen hq
  have hq3 : Computable (fun w : BitString => (decodeSecond w).drop ((decodeSecond w).length / m))
      :=
    Primrec.list_drop.to_comp.comp hlen hq
  have hl : Computable (fun w : BitString => decodeListCode (decodeFirst w) ++
      [(decodeSecond w).take ((decodeSecond w).length / m),
        (decodeSecond w).drop ((decodeSecond w).length / m)]) :=
    Computable.list_append.comp (decodeListCode_computable.comp decodeFirst_computable)
      (Computable.list_cons.comp hq2 (Computable.list_cons.comp hq3 (Computable.const [])))
  have hg : ∀ i : ℕ, Computable (fun w : BitString => (decodeListCode (decodeFirst w) ++
      [(decodeSecond w).take ((decodeSecond w).length / m),
        (decodeSecond w).drop ((decodeSecond w).length / m)]).getD i []) := fun i =>
    (Primrec.list_getD []).to_comp.comp hl (Computable.const i)
  exact listCode_computable.comp (Computable.list_cons.comp (hg σ.1)
    (Computable.list_cons.comp (hg σ.2.1) (Computable.list_cons.comp (hg σ.2.2)
        (Computable.const []))))

/-- Auxiliary for step 3: `C(z, q) ≤ C(z) + |q| + O(log N)` when `C(z) ≤ N`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_lower_abe_pair
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (z q : BitString) (N : ℕ), plainK D z ≤ (N : ℕ∞) →
      cPair D z q ≤ plainK D z + (q.length : ℕ∞) + (logSlack k N : ℕ∞) := by
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cL, hcL⟩ := plainK_le_length D hD
  refine ⟨2 + k0 + cL, fun z q N hz => ?_⟩
  have hval : cVal D z ≤ N := by
    unfold cVal
    have := ENat.toNat_le_toNat hz (ENat.natCast_ne_top N)
    simpa using this
  have hlog : Nat.log 2 (cVal D z) ≤ (Nat.bits N).length := by
    have h1 : Nat.log 2 (cVal D z) ≤ Nat.log 2 N := Nat.log_mono_right hval
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp only [Nat.log_zero_right, Nat.le_zero] at h1
      omega
    · have h2 : Nat.log 2 N < Nat.size N := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
      have h3 : (Nat.bits N).length = Nat.size N := by rw [Nat.size_eq_bits_len]
      omega
  have h1 := hk0 z q
  have h2 := hcL q
  calc cPair D z q ≤ plainK D z + plainK D q + ((2 * Nat.log 2 (cVal D z) + k0 : ℕ) : ℕ∞) := h1
    _ ≤ plainK D z + ((q.length : ℕ∞) + (cL : ℕ∞)) + ((2 * (Nat.bits N).length + k0 : ℕ) : ℕ∞) := by
        refine add_le_add (add_le_add le_rfl h2) ?_
        exact_mod_cast (by omega : 2 * Nat.log 2 (cVal D z) + k0 ≤ 2 * (Nat.bits N).length + k0)
    _ = plainK D z + (q.length : ℕ∞) + (((cL + (2 * (Nat.bits N).length + k0) : ℕ)) : ℕ∞) := by
        push_cast
        ring
    _ ≤ plainK D z + (q.length : ℕ∞) + (logSlack (2 + k0 + cL) N : ℕ∞) := by
        refine add_le_add le_rfl ?_
        have : cL + (2 * (Nat.bits N).length + k0) ≤ logSlack (2 + k0 + cL) N := by
          unfold logSlack; nlinarith
        exact_mod_cast this

/-- Auxiliary for step 3: for a computable `f`, `C(f(⟨X, q⟩)) ≤ C(X) + |q| + O(log n)` when
`C(X) ≤ 3n`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_lower_abe_gen
    (D : Map) (hD : isOptimalConditional D) (f : BitString → BitString) (hf : Computable f) :
    ∃ k : ℕ, ∀ (n : ℕ) (X q : BitString), plainK D X ≤ ((3 * n : ℕ) : ℕ∞) →
      plainK D (f (pairCode X q)) ≤ plainK D X + (q.length : ℕ∞) + (logSlack k n : ℕ∞) := by
  obtain ⟨k0, h0⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_pair D hD
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  obtain ⟨C, hC⟩ := logSlack_linear_bound k0 3 0
  refine ⟨C + c, ?_⟩
  intro n X q hX
  have h1 := h0 X q (3 * n) hX
  have h2 : logSlack k0 (3 * n) ≤ logSlack C n := by simpa using hC n
  have h3 : logSlack k0 (3 * n) + c ≤ logSlack (C + c) n := by
    rw [logSlack_add_constants]
    have := Nat.le_add_left c (c * (Nat.bits n).length)
    unfold logSlack at *
    omega
  calc plainK D (f (pairCode X q)) ≤ plainK D (pairCode X q) + (c : ℕ∞) := hc _
    _ ≤ (plainK D X + (q.length : ℕ∞) + (logSlack k0 (3 * n) : ℕ∞)) + (c : ℕ∞) :=
        add_le_add_left h1 _
    _ = plainK D X + (q.length : ℕ∞) + ((logSlack k0 (3 * n) + c : ℕ) : ℕ∞) := by
        push_cast; ring
    _ ≤ plainK D X + (q.length : ℕ∞) + (logSlack (C + c) n : ℕ∞) := by
        gcongr

/-- Auxiliary for step 3: if the selector applied to `⟨X, q⟩` (`|q| = m n`) gives a string `t`
with `C(t) ≥ 3n − 1`, then `C(X) ≥ (3 − m) n − O(log n)`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case
    (D : Map) (hD : isOptimalConditional D) (m : ℕ) (σ : ℕ × ℕ × ℕ) (hm : m ≤ 3) :
    ∃ k : ℕ, ∀ (n : ℕ) (X q t : BitString), q.length = m * n →
      exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel m σ
        (pairCode X q) = t →
      ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D t →
      (((3 - m) * n : ℕ) : ℕ∞) ≤ plainK D X + (logSlack k n : ℕ∞) := by
  obtain ⟨k0, h0⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_gen D hD _
      (exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_computable
        m σ)
  refine ⟨k0 + 1, ?_⟩
  intro n X q t hq ht hC
  subst ht
  have hmn : (3 - m) * n + m * n = 3 * n := by
    rw [← Nat.add_mul]; congr 1; omega
  have hL : logSlack k0 n + 1 ≤ logSlack (k0 + 1) n := by
    rw [logSlack_add_constants]
    unfold logSlack
    omega
  by_cases hX : plainK D X ≤ ((3 * n : ℕ) : ℕ∞)
  · have h := h0 n X q hX
    rw [hq] at h
    have h' := hC.trans h
    induction hx : plainK D X using ENat.recTopCoe with
    | top => simp
    | coe x =>
      rw [hx] at h'
      have h'' : 3 * n - 1 ≤ x + m * n + logSlack k0 n := by exact_mod_cast h'
      have : (3 - m) * n ≤ x + logSlack (k0 + 1) n := by omega
      exact_mod_cast this
  · rw [not_le] at hX
    have h1 : (((3 - m) * n : ℕ) : ℕ∞) ≤ ((3 * n : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.mul_le_mul_right n (Nat.sub_le 3 m)
    exact h1.trans (hX.le.trans le_self_add)

/-- Auxiliary for step 3: evaluation of the selector on `⟨listCode L, q⟩`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval
    (m : ℕ) (σ : ℕ × ℕ × ℕ) (L : List BitString) (q : BitString) :
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel m σ
        (pairCode (listCode L) q) =
      listCode [(L ++ [q.take (q.length / m), q.drop (q.length / m)]).getD σ.1 [],
        (L ++ [q.take (q.length / m), q.drop (q.length / m)]).getD σ.2.1 [],
        (L ++ [q.take (q.length / m), q.drop (q.length / m)]).getD σ.2.2 []] := by
  unfold exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode]

/-- Step 3 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
lower bounds for the sub-tuples of `(a, b, e)`.  If `a, b, e` are `n`-bit words with
`C(a, b, e) ≥ 3n − 1`, then every non-empty sub-tuple `S` of `(a, b, e, d)` not containing the
index `3` (so `S ⊆ {0, 1, 2}`; `d` is arbitrary) has `C(S) ≥ |S| · n − O(log n)`.
Proof: the string `(a, b, e)` is computable from `S` and the `3 − |S|` missing words, so
`C(a, b, e) ≤ C(S) + (3 − |S|) n + O(log n)` (the missing words are `n`-bit, `C ≤ n + O(1)`,
and `C(x, y) ≤ C(x) + C(y) + O(log n)`; the order of the components is irrelevant up to `O(1)`). -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_lower_abe
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e d : BitString), a.length = n → b.length = n → e.length = n →
      ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e]) →
      ∀ S : Finset (Fin 4), S.Nonempty → (3 : Fin 4) ∉ S →
        ((min S.card 3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode ![a, b, e, d] S) + (logSlack k n : ℕ∞) := by
  obtain ⟨k0, h0⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 0
      (0, 1, 2) (by norm_num)
  obtain ⟨k1, h1⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 2
      (0, 1, 2) (by norm_num)
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 2
      (1, 0, 2) (by norm_num)
  obtain ⟨k3, h3⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 2
      (1, 2, 0) (by norm_num)
  obtain ⟨k4, h4⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 1
      (0, 1, 2) (by norm_num)
  obtain ⟨k5, h5⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 1
      (0, 2, 1) (by norm_num)
  obtain ⟨k6, h6⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe_case D hD 1
      (2, 0, 1) (by norm_num)
  refine ⟨k0 + k1 + k2 + k3 + k4 + k5 + k6, ?_⟩
  intro n a b e d ha hb he hC S hS h3S
  have hw : ∀ k : ℕ, k ≤ k0 + k1 + k2 + k3 + k4 + k5 + k6 → ∀ x y : ℕ∞,
      x ≤ y + (logSlack k n : ℕ∞) →
      x ≤ y + (logSlack (k0 + k1 + k2 + k3 + k4 + k5 + k6) n : ℕ∞) := fun k hk x y h =>
    h.trans (add_le_add le_rfl
      (by exact_mod_cast logSlack_mono_left hk n))
  have hS' : ∀ S : Finset (Fin 4), S.Nonempty → (3 : Fin 4) ∉ S →
      S = {0, 1, 2} ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} := by
    decide
  have split2 : ∀ x y : BitString, x.length = y.length →
      (x ++ y).take ((x ++ y).length / 2) = x ∧ (x ++ y).drop ((x ++ y).length / 2) = y := by
    intro x y h
    have : (x ++ y).length / 2 = x.length := by rw [List.length_append]; omega
    rw [this]
    exact ⟨List.take_left, List.drop_left⟩
  have split1 : ∀ x : BitString, x.take (x.length / 1) = x ∧ x.drop (x.length / 1) = [] := by
    intro x; simp
  rcases hS' S hS h3S with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hmin : min ({0, 1, 2} : Finset (Fin 4)).card 3 * n = (3 - 0) * n := by
      have : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k0 (by omega) _ _ (h0 n (listCode [a, b, e]) [] (listCode [a, b, e]) (by simp)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval]
          simp) hC)
  · have hmin : min ({0} : Finset (Fin 4)).card 3 * n = (3 - 2) * n := by
      have : ({0} : Finset (Fin 4)).card = 1 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k1 (by omega) _ _ (h1 n (listCode [a]) (b ++ e) (listCode [a, b, e])
      (by rw [List.length_append, hb, he]; omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split2 b e (by omega)).1, (split2 b e (by omega)).2]; rfl) hC)
  · have hmin : min ({1} : Finset (Fin 4)).card 3 * n = (3 - 2) * n := by
      have : ({1} : Finset (Fin 4)).card = 1 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k2 (by omega) _ _ (h2 n (listCode [b]) (a ++ e) (listCode [a, b, e])
      (by rw [List.length_append, ha, he]; omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split2 a e (by omega)).1, (split2 a e (by omega)).2]; rfl) hC)
  · have hmin : min ({2} : Finset (Fin 4)).card 3 * n = (3 - 2) * n := by
      have : ({2} : Finset (Fin 4)).card = 1 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k3 (by omega) _ _ (h3 n (listCode [e]) (a ++ b) (listCode [a, b, e])
      (by rw [List.length_append, ha, hb]; omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split2 a b (by omega)).1, (split2 a b (by omega)).2]; rfl) hC)
  · have hmin : min ({0, 1} : Finset (Fin 4)).card 3 * n = (3 - 1) * n := by
      have : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k4 (by omega) _ _ (h4 n (listCode [a, b]) e (listCode [a, b, e])
      (by omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split1 e).1, (split1 e).2]; rfl) hC)
  · have hmin : min ({0, 2} : Finset (Fin 4)).card 3 * n = (3 - 1) * n := by
      have : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k5 (by omega) _ _ (h5 n (listCode [a, e]) b (listCode [a, b, e])
      (by omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split1 b).1, (split1 b).2]; rfl) hC)
  · have hmin : min ({1, 2} : Finset (Fin 4)).card 3 * n = (3 - 1) * n := by
      have : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [hmin]
    exact hw k6 (by omega) _ _ (h6 n (listCode [b, e]) a (listCode [a, b, e])
      (by omega)
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_lower_abe_sel_eval,
            (split1 a).1, (split1 a).2]; rfl) hC)

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_pairs`:
the singleton `n ≤ C(d) + s` transfers to `listCode [d]` at `O(1)` cost. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_pairs_single
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (d : BitString),
      (n : ℕ∞) ≤ plainK D d + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D (listCode [d]) + (logSlack k n : ℕ∞) := by
  have hf : Computable (fun p : BitString => (decodeListCode p).getD 0 []) :=
    (Primrec.list_getD ([] : BitString)).to_comp.comp decodeListCode_computable
      (Computable.const _)
  obtain ⟨c1, h1⟩ := plainK_map_le D hD _ hf
  refine ⟨c + c1, fun n d h => ?_⟩
  have e : (decodeListCode (listCode [d])).getD 0 [] = d := by
    rw [decodeListCode_listCode]; rfl
  have h1' := h1 (listCode [d])
  rw [e] at h1'
  have hs : (logSlack c n : ℕ∞) + (c1 : ℕ∞) ≤ (logSlack (c + c1) n : ℕ∞) := by
    exact_mod_cast logSlack_add_nat_le c c1 n
  calc (n : ℕ∞) ≤ plainK D d + (logSlack c n : ℕ∞) := h
    _ ≤ (plainK D (listCode [d]) + (c1 : ℕ∞)) + (logSlack c n : ℕ∞) := by gcongr
    _ = plainK D (listCode [d]) + ((logSlack c n : ℕ∞) + (c1 : ℕ∞)) := by ring
    _ ≤ plainK D (listCode [d]) + (logSlack (c + c1) n : ℕ∞) := by gcongr

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_pairs`:
for `n`-bit `x, d` with `n ≤ C([x]) + s` and `n ≤ C(d | x) + s`, `2n ≤ C([x, d]) + O(log n)`
(symmetry of information). -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_pairs_pair
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (x d : BitString), x.length = n → d.length = n →
      (n : ℕ∞) ≤ plainK D (listCode [x]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D d x + (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [x, d]) + (logSlack k n : ℕ∞) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨C, hC⟩ := plainK_add_condK_le_plainK_pair D U hD hU
  obtain ⟨cL, hcL⟩ := plainK_le_length D hD
  have hsing : Primrec (fun p : BitString => [p]) :=
    Primrec.list_cons.comp Primrec.id (Primrec.const [])
  have hf1 : Computable (fun p : BitString => listCode [p]) :=
    listCode_computable.comp hsing.to_comp
  obtain ⟨c1, h1⟩ := plainK_map_le D hD _ hf1
  have hg : ∀ i : ℕ, Computable (fun p : BitString => (decodeListCode p).getD i []) := fun i =>
    (Primrec.list_getD ([] : BitString)).to_comp.comp decodeListCode_computable
      (Computable.const i)
  have hf2 : Computable (fun p : BitString =>
      pairCode ((decodeListCode p).getD 0 []) ((decodeListCode p).getD 1 [])) :=
    Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
      (g := fun p : BitString => ((decodeListCode p).getD 0 [], (decodeListCode p).getD 1 []))
      pairCode_computable ((hg 0).pair (hg 1))
  obtain ⟨c2, h2⟩ := plainK_map_le D hD _ hf2
  obtain ⟨K, hK⟩ := logSlack_linear_bound C 3 (1 + cL)
  refine ⟨K + c1 + c2 + 2 * c, ?_⟩
  intro n x d hx hd hxs hds
  have e2 : pairCode ((decodeListCode (listCode [x, d])).getD 0 [])
      ((decodeListCode (listCode [x, d])).getD 1 []) = pairCode x d := by
    rw [decodeListCode_listCode]; rfl
  have h2' := h2 (listCode [x, d])
  rw [e2] at h2'
  have h1' := h1 x
  have hlen : ∀ w : BitString, plainK D w ≤ ((w.length + cL : ℕ) : ℕ∞) := fun w =>
    (hcL w).trans (by push_cast; exact le_rfl)
  have hxN : plainK D x ≤ ((3 * n + (1 + cL) : ℕ) : ℕ∞) :=
    (hlen x).trans (by exact_mod_cast (by omega : x.length + cL ≤ 3 * n + (1 + cL)))
  have hpN : plainK D (pairCode x d) ≤ ((3 * n + (1 + cL) : ℕ) : ℕ∞) :=
    (hlen _).trans (by
      rw [length_pairCode]
      exact_mod_cast (by omega : x.length + 1 + x.length + d.length + cL ≤ 3 * n + (1 + cL)))
  have hsoi := hC x d _ hxN hpN
  have hKs : (logSlack C (3 * n + (1 + cL)) : ℕ∞) ≤ (logSlack K n : ℕ∞) := by
    exact_mod_cast hK n
  have hsum : (logSlack K n : ℕ∞) + (c1 : ℕ∞) + (c2 : ℕ∞) + 2 * (logSlack c n : ℕ∞) ≤
      (logSlack (K + c1 + c2 + 2 * c) n : ℕ∞) := by
    have : logSlack K n + c1 + c2 + 2 * logSlack c n ≤ logSlack (K + c1 + c2 + 2 * c) n := by
      unfold logSlack
      nlinarith [Nat.zero_le (c1 * (Nat.bits n).length), Nat.zero_le (c2 * (Nat.bits n).length)]
    exact_mod_cast this
  calc ((2 * n : ℕ) : ℕ∞) = (n : ℕ∞) + (n : ℕ∞) := by push_cast; ring
    _ ≤ (plainK D (listCode [x]) + (logSlack c n : ℕ∞)) +
        (condK D d x + (logSlack c n : ℕ∞)) := add_le_add hxs hds
    _ ≤ ((plainK D x + (c1 : ℕ∞)) + (logSlack c n : ℕ∞)) +
        (condK D d x + (logSlack c n : ℕ∞)) := by gcongr
    _ = (plainK D x + condK D d x) + ((c1 : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by ring
    _ ≤ (plainK D (pairCode x d) + (logSlack C (3 * n + (1 + cL)) : ℕ∞)) +
        ((c1 : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by gcongr
    _ ≤ ((plainK D (listCode [x, d]) + (c2 : ℕ∞)) + (logSlack K n : ℕ∞)) +
        ((c1 : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by gcongr
    _ = plainK D (listCode [x, d]) +
        ((logSlack K n : ℕ∞) + (c1 : ℕ∞) + (c2 : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by ring
    _ ≤ plainK D (listCode [x, d]) + (logSlack (K + c1 + c2 + 2 * c) n : ℕ∞) := by gcongr

/-- Step 4 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
lower bounds for the sub-tuples of size `≤ 2` containing `d` (index `3`), by symmetry of
information.  Hypotheses (all with the slack `logSlack c n`): `C(x) ≥ n`, `C(d) ≥ n`,
`C(d | x) ≥ n` for `x ∈ {a, b, e}`.  Conclusion: `C(d) ≥ n`, `C(x, d) ≥ 2n − O(log n)`.
Proof: `C(x, d) ≥ C(x) + C(d | x) − O(log n)` (symmetry of information, applied to `x`, `d`
and the code `[x, d]` of the sub-tuple, `x` first or second according to the index of `x`). -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_pairs
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e d : BitString), a.length = n → b.length = n → e.length = n →
      d.length = n →
      (n : ℕ∞) ≤ plainK D (listCode [a]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D (listCode [b]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D (listCode [e]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ plainK D d + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D d a + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D d b + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D d e + (logSlack c n : ℕ∞) →
      ∀ S : Finset (Fin 4), (3 : Fin 4) ∈ S → S.card ≤ 2 →
        ((min S.card 3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode ![a, b, e, d] S) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, h1⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_pairs_single D hD c
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_pairs_pair D hD c
  refine ⟨max k1 k2, fun n a b e d ha hb he hd sa sb se sd da db de S h3 hcard => ?_⟩
  have hw : ∀ (k k' : ℕ), k ≤ k' → ∀ x y : ℕ∞, x ≤ y + (logSlack k n : ℕ∞) →
      x ≤ y + (logSlack k' n : ℕ∞) := fun k k' hk x y h =>
    h.trans (add_le_add le_rfl
      (by exact_mod_cast logSlack_mono_left hk n : (logSlack k n : ℕ∞) ≤ (logSlack k' n : ℕ∞)))
  have hcases : ∀ S : Finset (Fin 4), (3 : Fin 4) ∈ S → S.card ≤ 2 →
      S = {3} ∨ S = {0, 3} ∨ S = {1, 3} ∨ S = {2, 3} := by decide
  rcases hcases S h3 hcard with rfl | rfl | rfl | rfl
  · have e0 : subtupleCode ![a, b, e, d] ({3} : Finset (Fin 4)) = listCode [d] := rfl
    have c0 : min ({3} : Finset (Fin 4)).card 3 * n = n := by simp
    rw [e0, c0]
    exact hw k1 _ (le_max_left _ _) _ _ (h1 n d sd)
  · have e0 : subtupleCode ![a, b, e, d] ({0, 3} : Finset (Fin 4)) = listCode [a, d] := rfl
    have c0 : min ({0, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0]
    exact hw k2 _ (le_max_right _ _) _ _ (h2 n a d ha hd sa da)
  · have e0 : subtupleCode ![a, b, e, d] ({1, 3} : Finset (Fin 4)) = listCode [b, d] := rfl
    have c0 : min ({1, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0]
    exact hw k2 _ (le_max_right _ _) _ _ (h2 n b d hb hd sb db)
  · have e0 : subtupleCode ![a, b, e, d] ({2, 3} : Finset (Fin 4)) = listCode [e, d] := rfl
    have c0 : min ({2, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0]
    exact hw k2 _ (le_max_right _ _) _ _ (h2 n e d he hd se de)

/-- Auxiliary for step 5: symmetry of information for `x = ⟨q, r⟩` and `y = p`, with all words
of length at most `n` (budget `7n + O(1)` absorbed into the slack). -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_triples_aux_sym
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k0 : ℕ, ∀ (n : ℕ) (p q r : BitString), p.length ≤ n → q.length ≤ n → r.length ≤ n →
      plainK D (pairCode q r) + condK D p (pairCode q r) ≤
        plainK D (pairCode (pairCode q r) p) + (logSlack k0 n : ℕ∞) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cS, hS⟩ := plainK_add_condK_le_plainK_pair D U hD hU
  obtain ⟨cL, hcL⟩ := plainK_le_length D hD
  obtain ⟨K, hK⟩ := logSlack_absorb_of_le_linear cS 7 (cL + 3)
  refine ⟨K, fun n p q r hp hq hr => ?_⟩
  have hlen : ∀ w : BitString, w.length ≤ 7 * n + 3 →
      plainK D w ≤ ((7 * n + (cL + 3) : ℕ) : ℕ∞) := fun w hw =>
    (hcL w).trans (by
      have : w.length + cL ≤ 7 * n + (cL + 3) := by omega
      exact_mod_cast this)
  have h1 := hlen (pairCode q r) (by simp only [length_pairCode]; omega)
  have h2 := hlen (pairCode (pairCode q r) p) (by simp only [length_pairCode]; omega)
  have := hS (pairCode q r) p (7 * n + (cL + 3)) h1 h2
  exact this.trans (add_le_add le_rfl (by exact_mod_cast hK n _ le_rfl))

/-- Auxiliary for step 5: the pair `⟨⟨q, r⟩, p⟩` and the list codes `[p, q, r]`, `[q, p, r]`,
and `[q, r]` versus `⟨q, r⟩`, are computable from each other. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_triples_aux_transport
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ p q r : BitString,
      plainK D (pairCode (pairCode q r) p) ≤ plainK D (listCode [p, q, r]) + (c : ℕ∞) ∧
      plainK D (pairCode (pairCode q r) p) ≤ plainK D (listCode [q, p, r]) + (c : ℕ∞) ∧
      plainK D (listCode [q, r]) ≤ plainK D (pairCode q r) + (c : ℕ∞) := by
  have pc : ∀ {f g : BitString → BitString}, Computable f → Computable g →
      Computable (fun x => pairCode (f x) (g x)) := fun hf hg =>
    pairCode_computable.comp (hf.pair hg)
  have hd1 : Computable (fun w : BitString => decodeFirst w) := decodeFirst_computable
  have hd2 : Computable (fun w : BitString => decodeSecond w) := decodeSecond_computable
  have c2 : Computable (fun w : BitString => decodeSecond (decodeSecond w)) := hd2.comp hd2
  have g1 : Computable (fun w : BitString => decodeFirst (decodeSecond w)) := hd1.comp hd2
  have g2 : Computable (fun w : BitString => decodeFirst (decodeSecond (decodeSecond w))) :=
    hd1.comp c2
  let f1 : BitString → BitString := fun w =>
    pairCode (pairCode (decodeFirst (decodeSecond w)) (decodeFirst (decodeSecond (decodeSecond w))))
      (decodeFirst w)
  let f2 : BitString → BitString := fun w =>
    pairCode (pairCode (decodeFirst w) (decodeFirst (decodeSecond (decodeSecond w))))
      (decodeFirst (decodeSecond w))
  let f3 : BitString → BitString := fun w => pairCode (decodeFirst w) (pairCode (decodeSecond w) [])
  have hf1 : Computable f1 := pc (pc g1 g2) hd1
  have hf2 : Computable f2 := pc (pc hd1 g2) g1
  have hf3 : Computable f3 := pc hd1 (pc hd2 (Computable.const []))
  obtain ⟨c1, h1⟩ := plainK_map_le D hD f1 hf1
  obtain ⟨c2', h2⟩ := plainK_map_le D hD f2 hf2
  obtain ⟨c3, h3⟩ := plainK_map_le D hD f3 hf3
  refine ⟨c1 + c2' + c3, fun p q r => ⟨?_, ?_, ?_⟩⟩
  · have := h1 (listCode [p, q, r])
    simp only [f1, listCode_cons, listCode_nil, decodeFirst_pairCode, decodeSecond_pairCode] at this
    exact this.trans (add_le_add le_rfl (by exact_mod_cast (by omega : c1 ≤ c1 + c2' + c3)))
  · have := h2 (listCode [q, p, r])
    simp only [f2, listCode_cons, listCode_nil, decodeFirst_pairCode, decodeSecond_pairCode] at this
    exact this.trans (add_le_add le_rfl (by exact_mod_cast (by omega : c2' ≤ c1 + c2' + c3)))
  · have := h3 (pairCode q r)
    simp only [f3, decodeFirst_pairCode, decodeSecond_pairCode] at this
    exact (by simpa using this : plainK D (listCode [q, r]) ≤ _).trans
      (add_le_add le_rfl (by exact_mod_cast (by omega : c3 ≤ c1 + c2' + c3)))

/-- Step 5 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
lower bounds for the sub-tuples of size `3` containing `d` (index `3`), by symmetry of
information.  Hypotheses (slack `logSlack c n`): `C(x, d) ≥ 2n` for `x ∈ {a, b, e}` and
`C(a | b, d) ≥ n`, `C(b | e, d) ≥ n`, `C(e | a, d) ≥ n`.  Conclusion: `C(S) ≥ 3n − O(log n)` for
`S = {a, b, d}, {a, e, d}, {b, e, d}`.  Proof: e.g. `C(a, b, d) ≥ C(b, d) + C(a | b, d) − O(log n)`
(symmetry of information; `[a, b, d]` and the pair `(a, (b, d))` are computable from each other,
so their complexities agree up to `O(1)`), and similarly `C(a, e, d) ≥ C(a, d) + C(e | a, d)`,
`C(b, e, d) ≥ C(e, d) + C(b | e, d)`. -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_triples
    (D : Map) (hD : isOptimalConditional D) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e d : BitString), a.length = n → b.length = n → e.length = n →
      d.length = n →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [a, d]) + (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [b, d]) + (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [e, d]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D a (pairCode b d) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D b (pairCode e d) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D e (pairCode a d) + (logSlack c n : ℕ∞) →
      ∀ S : Finset (Fin 4), (3 : Fin 4) ∈ S → S.card = 3 →
        ((min S.card 3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode ![a, b, e, d] S) + (logSlack k n : ℕ∞) := by
  obtain ⟨k0, hsym⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_triples_aux_sym D hD
  obtain ⟨cT, hT⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_triples_aux_transport
      D hD
  refine ⟨k0 + 2 * cT + 2 * c, fun n a b e d ha hb he hd h1 h2 h3 h4 h5 h6 S h3S hS => ?_⟩
  have hslack : logSlack k0 n + 2 * cT + 2 * logSlack c n ≤ logSlack (k0 + 2 * cT + 2 * c) n := by
    unfold logSlack
    nlinarith [Nat.zero_le (cT * (Nat.bits n).length)]
  have hfin : ∀ (X : ℕ∞), X + ((logSlack k0 n + 2 * cT + 2 * logSlack c n : ℕ) : ℕ∞) ≤
      X + (logSlack (k0 + 2 * cT + 2 * c) n : ℕ∞) := fun X =>
    add_le_add le_rfl (by exact_mod_cast hslack)
  have key : ∀ (p q r L : BitString), p.length = n → q.length = n → r.length = n →
      ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [q, r]) + (logSlack c n : ℕ∞) →
      (n : ℕ∞) ≤ condK D p (pairCode q r) + (logSlack c n : ℕ∞) →
      plainK D (pairCode (pairCode q r) p) ≤ plainK D L + (cT : ℕ∞) →
      plainK D (listCode [q, r]) ≤ plainK D (pairCode q r) + (cT : ℕ∞) →
      ((3 * n : ℕ) : ℕ∞) ≤ plainK D L + (logSlack (k0 + 2 * cT + 2 * c) n : ℕ∞) := by
    intro p q r L hp hq hr g1 g2 g3 g4
    have hs := hsym n p q r hp.le hq.le hr.le
    calc ((3 * n : ℕ) : ℕ∞) = ((2 * n : ℕ) : ℕ∞) + (n : ℕ∞) := by
          rw [show 3 * n = 2 * n + n by ring, Nat.cast_add]
      _ ≤ (plainK D (listCode [q, r]) + (logSlack c n : ℕ∞)) +
          (condK D p (pairCode q r) + (logSlack c n : ℕ∞)) := add_le_add g1 g2
      _ ≤ ((plainK D (pairCode q r) + (cT : ℕ∞)) + (logSlack c n : ℕ∞)) +
          (condK D p (pairCode q r) + (logSlack c n : ℕ∞)) := by gcongr
      _ = (plainK D (pairCode q r) + condK D p (pairCode q r)) +
          ((cT : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by ring
      _ ≤ (plainK D (pairCode (pairCode q r) p) + (logSlack k0 n : ℕ∞)) +
          ((cT : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by gcongr
      _ ≤ ((plainK D L + (cT : ℕ∞)) + (logSlack k0 n : ℕ∞)) +
          ((cT : ℕ∞) + 2 * (logSlack c n : ℕ∞)) := by gcongr
      _ = plainK D L + ((logSlack k0 n + 2 * cT + 2 * logSlack c n : ℕ) : ℕ∞) := by
          push_cast; ring
      _ ≤ _ := hfin _
  have hS' : S = {0, 1, 3} ∨ S = {0, 2, 3} ∨ S = {1, 2, 3} := by
    clear key hfin hslack h1 h2 h3 h4 h5 h6
    revert S; decide
  have hcard : min S.card 3 * n = 3 * n := by rw [hS]; simp
  rw [hcard]
  rcases hS' with rfl | rfl | rfl
  · have e0 : subtupleCode ![a, b, e, d] ({0, 1, 3} : Finset (Fin 4)) = listCode [a, b, d] := rfl
    rw [e0]
    obtain ⟨t1, -, t3⟩ := hT a b d
    exact key a b d _ ha hb hd h2 h4 t1 t3
  · have e0 : subtupleCode ![a, b, e, d] ({0, 2, 3} : Finset (Fin 4)) = listCode [a, e, d] := rfl
    rw [e0]
    obtain ⟨-, t2, t3⟩ := hT e a d
    exact key e a d _ he ha hd h1 h6 t2 t3
  · have e0 : subtupleCode ![a, b, e, d] ({1, 2, 3} : Finset (Fin 4)) = listCode [b, e, d] := rfl
    rw [e0]
    obtain ⟨t1, -, t3⟩ := hT b e d
    exact key b e d _ hb he hd h3 h5 t1 t3

/-- Step 6 of the proof of
`exists_quadruples_profileClose_problemK_quad_gap_profile_u`:
the whole quadruple.  If `C(a, b, e) ≥ 3n − 1` then `C(a, b, e, d) ≥ 3n − 1 − O(1)` for every `d`
(the code `[a, b, e]` is computable from `[a, b, e, d]`), i.e. `3n ≤ C(a, b, e, d) + O(1)`. -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_quad
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e d : BitString),
      ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e]) →
      ∀ S : Finset (Fin 4), S.card = 4 →
        ((min S.card 3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode ![a, b, e, d] S) + (logSlack k n : ℕ∞) := by
  have hf : Computable (fun w : BitString => listCode ((decodeListCode w).take 3)) :=
    listCode_computable.comp
      (Primrec.list_take.comp (Primrec.const 3) decodeListCode_primrec).to_comp
  obtain ⟨c, hc⟩ := plainK_map_le D hD _ hf
  refine ⟨c + 1, fun n a b e d hC S hS => ?_⟩
  have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hS)
  subst hSu
  have e0 : subtupleCode ![a, b, e, d] (Finset.univ : Finset (Fin 4)) = listCode [a, b, e, d] :=
    rfl
  rw [e0]
  have h := hc (listCode [a, b, e, d])
  rw [decodeListCode_listCode] at h
  have hl : (c + 1 : ℕ) ≤ logSlack (c + 1) n := by unfold logSlack; nlinarith
  have hl' : ((c + 1 : ℕ) : ℕ∞) ≤ (logSlack (c + 1) n : ℕ∞) := by exact_mod_cast hl
  have h3 : ((min (Finset.univ : Finset (Fin 4)).card 3 * n : ℕ) : ℕ∞) ≤
      ((3 * n - 1 : ℕ) : ℕ∞) + 1 := by
    have : min (Finset.univ : Finset (Fin 4)).card 3 * n = 3 * n := by simp
    rw [this]
    have : 3 * n ≤ (3 * n - 1) + 1 := by omega
    exact_mod_cast this
  calc _ ≤ ((3 * n - 1 : ℕ) : ℕ∞) + 1 := h3
    _ ≤ plainK D (listCode [a, b, e]) + 1 := add_le_add_left hC _
    _ ≤ (plainK D (listCode [a, b, e, d]) + (c : ℕ∞)) + 1 := by
        gcongr; simpa using h
    _ ≤ plainK D (listCode [a, b, e, d]) + (logSlack (c + 1) n : ℕ∞) := by
        rw [add_assoc]; gcongr
        calc (c : ℕ∞) + 1 = ((c + 1 : ℕ) : ℕ∞) := by push_cast; rfl
          _ ≤ _ := hl'

/-- Step 2 of the proof of `exists_quadruples_profileClose_problemK_quad_gap`:
the complexity profile of the probabilistic quadruple `ũ = (a, b, e, Q(a, b, e))` is
`(n, 2n, 3n, 3n)`, i.e. every sub-tuple `S` has complexity `min(|S|, 3) · n` up to `O(log n)`
(the constant `k` depends on `D`, `P`, `Q` and the slack constant `c` of the lower bounds only).
Hypotheses: `a, b, e, Q(a, b, e)` are `n`-bit words, `C(a, b, e) ≥ 3n − 1`, `Q` is computable
(so `Q(a, b, e)` is computable from `n` and the triple), and the three problems
`(a → e) ∧ (b → d)`, `(e → b) ∧ (a → d)`, `(b → a) ∧ (e → d)` have complexity `≥ 2n − O(log n)`.
Book's proof: upper bounds from lengths and from `d = Q(a, b, e)`; lower bounds from the three
problem bounds, the upper bounds of Problem 342 (`C(e|a) + C(d|b)`, `C(d|b,e) + C(e)`,
`C(e|a,d) + C(d)` and the same for the two rotated tuples; each of `C(e|a), C(d|b), …`
is `≤ n + O(1)`, so each is `≥ n − O(log n)`) and symmetry of information
(`C(x, y) = C(x) + C(y | x) ± O(log n)`); e.g. `C(a, b, d) ≥ C(b, d) + C(a | b, d)` with
`C(a | b, d) ≥ n − O(log n)` from the third bound of the tuple `(b, e, a, d)`. -/
theorem exists_quadruples_profileClose_problemK_quad_gap_profile_u (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible)
    (Q : ℕ → BitString → BitString → BitString → BitString)
    (hQ : Computable (fun t : ℕ × BitString × BitString × BitString =>
      Q t.1 t.2.1 t.2.2.1 t.2.2.2)) (c : ℕ) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e : BitString), a.length = n → b.length = n → e.length = n →
      (Q n a b e).length = n →
      ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e]) →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![a, b, e, Q n a b e]) +
        (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![e, a, b, Q n a b e]) +
        (logSlack c n : ℕ∞) →
      ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![b, e, a, Q n a b e]) +
        (logSlack c n : ℕ∞) →
      ∀ S : Finset (Fin 4), S.Nonempty →
        plainK D (subtupleCode ![a, b, e, Q n a b e] S) ≤
            ((min S.card 3 * n : ℕ) : ℕ∞) + (logSlack k n : ℕ∞) ∧
          ((min S.card 3 * n : ℕ) : ℕ∞) ≤
            plainK D (subtupleCode ![a, b, e, Q n a b e] S) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, h1⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_upper D hD Q hQ
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_conditional D hD P hP c
  obtain ⟨k3, h3⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_lower_abe D hD
  obtain ⟨k4, h4⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_pairs D hD (max k2 k3)
  obtain ⟨k5, h5⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_triples D hD
      (max k4 k2)
  obtain ⟨k6, h6⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_quad D hD
  obtain ⟨K, hK1, hK3, hK4, hK5, hK6⟩ :
      ∃ K : ℕ, k1 ≤ K ∧ k3 ≤ K ∧ k4 ≤ K ∧ k5 ≤ K ∧ k6 ≤ K :=
    ⟨k1 + k3 + k4 + k5 + k6, by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨K, fun n a b e ha hb he hd hC hp1 hp2 hp3 S hS => ?_⟩
  have hw : ∀ k k' : ℕ, k ≤ k' → ∀ x y : ℕ∞, x ≤ y + (logSlack k n : ℕ∞) →
      x ≤ y + (logSlack k' n : ℕ∞) := fun k k' hk x y h =>
    h.trans (add_le_add le_rfl
      (by exact_mod_cast logSlack_mono_left hk n : (logSlack k n : ℕ∞) ≤ (logSlack k' n : ℕ∞)))
  have hup := h1 n a b e ha hb he hd S hS
  refine ⟨hup.trans (add_le_add le_rfl
    (by exact_mod_cast logSlack_mono_left hK1 n : (logSlack k1 n : ℕ∞) ≤ (logSlack K n : ℕ∞))), ?_⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6⟩ := h2 n a b e (Q n a b e) ha hb he hd hp1 hp2 hp3
  generalize Q n a b e = d at *
  -- the singletons `{0}`, `{1}`, `{2}` (step 3)
  have sa : (n : ℕ∞) ≤ plainK D (listCode [a]) + (logSlack (max k2 k3) n : ℕ∞) := by
    have h := h3 n a b e d ha hb he hC {0} ⟨0, by simp⟩ (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({0} : Finset (Fin 4)) = listCode [a] := rfl
    have c0 : min ({0} : Finset (Fin 4)).card 3 * n = n := by simp
    rw [e0, c0] at h
    exact hw k3 _ (le_max_right _ _) _ _ h
  have sb : (n : ℕ∞) ≤ plainK D (listCode [b]) + (logSlack (max k2 k3) n : ℕ∞) := by
    have h := h3 n a b e d ha hb he hC {1} ⟨1, by simp⟩ (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({1} : Finset (Fin 4)) = listCode [b] := rfl
    have c0 : min ({1} : Finset (Fin 4)).card 3 * n = n := by simp
    rw [e0, c0] at h
    exact hw k3 _ (le_max_right _ _) _ _ h
  have se : (n : ℕ∞) ≤ plainK D (listCode [e]) + (logSlack (max k2 k3) n : ℕ∞) := by
    have h := h3 n a b e d ha hb he hC {2} ⟨2, by simp⟩ (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({2} : Finset (Fin 4)) = listCode [e] := rfl
    have c0 : min ({2} : Finset (Fin 4)).card 3 * n = n := by simp
    rw [e0, c0] at h
    exact hw k3 _ (le_max_right _ _) _ _ h
  have hk2 : k2 ≤ max k2 k3 := le_max_left _ _
  have H4 := h4 n a b e d ha hb he hd sa sb se (hw k2 _ hk2 _ _ d0) (hw k2 _ hk2 _ _ d1)
    (hw k2 _ hk2 _ _ d2) (hw k2 _ hk2 _ _ d3)
  -- the pairs `{0, 3}`, `{1, 3}`, `{2, 3}` (step 4)
  have pa : ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [a, d]) + (logSlack (max k4 k2) n : ℕ∞) := by
    have h := H4 {0, 3} (by decide) (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({0, 3} : Finset (Fin 4)) = listCode [a, d] := rfl
    have c0 : min ({0, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({0, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0] at h
    exact hw k4 _ (le_max_left _ _) _ _ h
  have pb : ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [b, d]) + (logSlack (max k4 k2) n : ℕ∞) := by
    have h := H4 {1, 3} (by decide) (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({1, 3} : Finset (Fin 4)) = listCode [b, d] := rfl
    have c0 : min ({1, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0] at h
    exact hw k4 _ (le_max_left _ _) _ _ h
  have pe : ((2 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [e, d]) + (logSlack (max k4 k2) n : ℕ∞) := by
    have h := H4 {2, 3} (by decide) (by decide)
    have e0 : subtupleCode ![a, b, e, d] ({2, 3} : Finset (Fin 4)) = listCode [e, d] := rfl
    have c0 : min ({2, 3} : Finset (Fin 4)).card 3 * n = 2 * n := by
      have : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
      rw [this]; norm_num
    rw [e0, c0] at h
    exact hw k4 _ (le_max_left _ _) _ _ h
  have hk2' : k2 ≤ max k4 k2 := le_max_right _ _
  have H5 := h5 n a b e d ha hb he hd pa pb pe (hw k2 _ hk2' _ _ d4) (hw k2 _ hk2' _ _ d5)
    (hw k2 _ hk2' _ _ d6)
  have hcard : S.card ≤ 4 := by simpa using Finset.card_le_univ S
  have hpos : 0 < S.card := hS.card_pos
  by_cases h3S : (3 : Fin 4) ∈ S
  · rcases (by omega : S.card ≤ 2 ∨ S.card = 3 ∨ S.card = 4) with h | h | h
    · exact hw k4 _ (by omega) _ _ (H4 S h3S h)
    · exact hw k5 _ (by omega) _ _ (H5 S h3S h)
    · exact hw k6 _ (by omega) _ _ (h6 n a b e d hC S h)
  · exact hw k3 _ (by omega) _ _ (h3 n a b e d ha hb he hC S hS h3S)

end InformationLogic
end Kolmogorov
