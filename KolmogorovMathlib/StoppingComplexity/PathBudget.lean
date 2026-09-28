import KolmogorovMathlib.StoppingComplexity.Words
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable

/-!
# Requests, path loads and budgets

Alice's declarations in the stopping-allocation game and their path loads (blueprint part 01,
section F2; part 02, DEF-01). A request `(x, n)` puts the rational weight `2^{-n}` at the
vertex `x`; the load of a finite request list at a word `v` is the total weight of the
requests at prefixes of `v`, and `HasBudget A B` bounds every load by `B`. A pending request
is included in the list by the caller (DEF-01). The module states the finite-word /
infinite-path equivalence (F2.1), finite verification at the declared vertices with the
executable checker `budgetCheck` (F2.2), and the fresh-root translation of a local history
below a root `u` (F2.3, `IsFreshRoot`).

Weights are exact rationals `(1 / 2 : ℚ) ^ n` (recorded deviation F2-DEF).
-/

namespace Kolmogorov

/-! ### Requests and loads -/

/-- Alice's declaration `(x, n)`: weight `2^{-n}` at the vertex `x` (`n ≥ 1` is a legality
condition imposed by the game, not by the type). Blueprint 01 F2 / 02 DEF-01. -/
abbrev Request := BitString × ℕ

/-- The weight `w(n) = 2^{-n}` of a request with exponent `n`, as a rational.
Blueprint 01 F2 / 02 DEF-01. -/
def requestWeight (n : ℕ) : ℚ := (1 / 2 : ℚ) ^ n

/-- `load A v = Σ { w(n) | (x, n) ∈ A, x ≤p v }`: the total weight of the requests of `A`
at prefixes of `v`. The list may contain a pending request. Blueprint 01 F2 / 02 DEF-01. -/
def load (A : List Request) (v : BitString) : ℚ :=
  ((A.filter fun r => decide (r.1 <+: v)).map fun r => requestWeight r.2).sum

/-- `HasBudget A B`: every finite word carries load at most `B`.
Blueprint 01 F2 / 02 DEF-01. -/
def HasBudget (A : List Request) (B : ℚ) : Prop := ∀ v, load A v ≤ B

/-- The load of `A` along an infinite path `w`: the total weight of the requests whose
vertices are prefixes of `w`. The prefix test is the decidable form
`cantorPrefix w |x| = x` of `IsCantorPrefix x w` (`isCantorPrefix_iff_cantorPrefix_eq`).
Blueprint 01 F2.1. -/
def pathLoad (A : List Request) (w : CantorSeq) : ℚ :=
  ((A.filter fun r => decide (cantorPrefix w r.1.length = r.1)).map
    fun r => requestWeight r.2).sum

/-- Request weights are nonnegative. -/
private theorem requestWeight_nonneg (n : ℕ) : 0 ≤ requestWeight n := by
  unfold requestWeight
  positivity

/-- Selecting more requests never lowers the total weight: if every request selected by `p`
is selected by `q`, the total weight of the `p`-requests is at most that of the `q`-requests. -/
private theorem sum_weight_filter_le (A : List Request) {p q : Request → Bool}
    (hpq : ∀ r, p r = true → q r = true) :
    ((A.filter p).map fun r => requestWeight r.2).sum ≤
      ((A.filter q).map fun r => requestWeight r.2).sum := by
  refine ((List.monotone_filter_right A hpq).map _).sum_le_sum fun x hx => ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact requestWeight_nonneg r.2

/-- Loads are nonnegative. Blueprint 01 F2. -/
theorem load_nonneg (A : List Request) (v : BitString) : 0 ≤ load A v := by
  unfold load
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact requestWeight_nonneg r.2

/-- The load of a concatenation is the sum of the loads. Blueprint 01 F2. -/
theorem load_append (A A' : List Request) (v : BitString) :
    load (A ++ A') v = load A v + load A' v := by
  simp [load, List.filter_append]

/-- The load of `r :: A` adds the weight of `r` when its vertex is a prefix of `v`.
Blueprint 01 F2. -/
theorem load_cons (r : Request) (A : List Request) (v : BitString) :
    load (r :: A) v = (if r.1 <+: v then requestWeight r.2 else 0) + load A v := by
  unfold load
  rw [List.filter_cons]
  by_cases h : r.1 <+: v <;> simp [h]

/-- Loads are monotone along the prefix order. Blueprint 01 F2. -/
theorem load_le_load_of_prefix (A : List Request) {v v' : BitString} (h : v <+: v') :
    load A v ≤ load A v' := by
  unfold load
  refine sum_weight_filter_le A fun r hr => ?_
  rw [decide_eq_true_iff] at hr ⊢
  exact hr.trans h

/-! ### Finite-word / infinite-path equivalence and finite verification -/

/-- The load of a word is at most the path load of any stream extending it. -/
private theorem load_le_pathLoad (A : List Request) {v : BitString} {w : CantorSeq}
    (hv : IsCantorPrefix v w) : load A v ≤ pathLoad A w := by
  unfold load pathLoad
  refine sum_weight_filter_le A fun r hr => ?_
  rw [decide_eq_true_iff] at hr ⊢
  exact (isCantorPrefix_iff_cantorPrefix_eq _ _).1 (cantorCylinder_subset_of_prefix hr hv)

/-- A stream carries exactly the load of its prefix of length `N` once `N` bounds the lengths
of all declared vertices. -/
private theorem pathLoad_eq_load_cantorPrefix (A : List Request) (w : CantorSeq) {N : ℕ}
    (hN : ∀ r ∈ A, r.1.length ≤ N) : pathLoad A w = load A (cantorPrefix w N) := by
  unfold load pathLoad
  congr 2
  refine List.filter_congr fun r hr => decide_eq_decide.2 ⟨fun h => ?_, fun h => ?_⟩
  · have hmono := cantorPrefix_mono w (hN r hr)
    rwa [h] at hmono
  · exact ((List.prefix_iff_eq_take.1 h).trans (cantorPrefix_take w _ N (hN r hr))).symm

/-- Finite-word / infinite-path equivalence: a finite request list has budget `B` exactly
when every infinite path carries load at most `B`. Blueprint 01 F2.1. -/
theorem hasBudget_iff_forall_pathLoad (A : List Request) (B : ℚ) :
    HasBudget A B ↔ ∀ w : CantorSeq, pathLoad A w ≤ B := by
  constructor
  · intro h w
    have hN : ∀ r ∈ A, r.1.length ≤ (A.map fun r => r.1.length).sum := fun r hr =>
      List.le_sum_of_mem (List.mem_map_of_mem hr)
    rw [pathLoad_eq_load_cantorPrefix A w hN]
    exact h _
  · intro h v
    exact (load_le_pathLoad A (isCantorPrefix_prepend v fun _ => false)).trans (h _)

/-- The load at a word with a declared prefix is the load at its longest declared prefix: the
declared prefixes of the word form a chain, so they are exactly the declared prefixes of the
longest one (the proof of F2.2). -/
private theorem exists_load_eq_load_mem (A : List Request) {v : BitString}
    (h : ∃ r ∈ A, r.1 <+: v) : ∃ r ∈ A, load A v = load A r.1 := by
  obtain ⟨r₀, hr₀A, hr₀v⟩ := h
  have hne : (A.filter fun r => decide (r.1 <+: v)).toFinset.Nonempty :=
    ⟨r₀, by simp [hr₀A, hr₀v]⟩
  obtain ⟨r, hrT, hmax⟩ := Finset.exists_max_image _ (fun r : Request => r.1.length) hne
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hrT hmax
  refine ⟨r, hrT.1, ?_⟩
  unfold load
  congr 2
  refine List.filter_congr fun r' hr' => decide_eq_decide.2 ⟨fun h' => ?_, fun h' => ?_⟩
  · exact List.prefix_of_prefix_length_le h' hrT.2 (hmax r' ⟨hr', h'⟩)
  · exact h'.trans hrT.2

/-- Finite verification: for `B ≥ 0` it suffices to test the load at the declared vertices
themselves. Blueprint 01 F2.2. -/
theorem hasBudget_iff_forall_mem {A : List Request} {B : ℚ} (hB : 0 ≤ B) :
    HasBudget A B ↔ ∀ r ∈ A, load A r.1 ≤ B := by
  refine ⟨fun h r _ => h r.1, fun h v => ?_⟩
  by_cases hS : ∃ r ∈ A, r.1 <+: v
  · obtain ⟨r, hrA, hr⟩ := exists_load_eq_load_mem A hS
    rw [hr]
    exact h r hrA
  · push_neg at hS
    have hzero : load A v = 0 := by
      unfold load
      rw [List.filter_eq_nil_iff.2 fun r hr => by simpa using hS r hr]
      simp
    rw [hzero]
    exact hB

/-- The executable budget checker: test the load at every declared vertex.
Blueprint 01 F2.2. -/
def budgetCheck (A : List Request) (B : ℚ) : Bool :=
  A.all fun r => decide (load A r.1 ≤ B)

/-- For `B ≥ 0` the checker decides the budget property. Blueprint 01 F2.2. -/
theorem budgetCheck_iff {A : List Request} {B : ℚ} (hB : 0 ≤ B) :
    budgetCheck A B = true ↔ HasBudget A B := by
  rw [hasBudget_iff_forall_mem hB, budgetCheck, List.all_eq_true]
  simp only [decide_eq_true_eq]

/-- A list of request weights as one dyadic fraction: when every exponent of `S` is at most
`E`, the total weight of `S` is `(Σ 2^(E - n)) / 2^E`. -/
private theorem sum_requestWeight_eq (S : List Request) {E : ℕ} (hE : ∀ r ∈ S, r.2 ≤ E) :
    (S.map fun r => requestWeight r.2).sum =
      ((S.map fun r => 2 ^ (E - r.2)).sum : ℕ) / 2 ^ E := by
  induction S with
  | nil => simp
  | cons r S ih =>
    have hr := hE r List.mem_cons_self
    rw [List.map_cons, List.sum_cons, ih fun r' hr' => hE r' (List.mem_cons_of_mem _ hr'),
      List.map_cons, List.sum_cons, Nat.cast_add, add_div]
    congr 1
    rw [requestWeight, one_div_pow, Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ two_ne_zero hr]
    field_simp

/-- The load is the dyadic fraction `M / 2^E`, where `E` is the sum of all exponents of `A` and
`M` the sum of `2^(E - n)` over the requests at prefixes of `v`. -/
private theorem load_eq_natCast_div_two_pow (A : List Request) (v : BitString) :
    load A v = (((A.filter fun r => decide (r.1 <+: v)).map fun r =>
      2 ^ ((A.map fun r => r.2).sum - r.2)).sum : ℕ) / 2 ^ (A.map fun r => r.2).sum := by
  unfold load
  refine sum_requestWeight_eq _ fun r hr => ?_
  exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_filter.1 hr).1)

/-- The nonnegative dyadic rationals `M / 2^E` are primitive recursive in `(M, E)`: the code of
`M / 2^E` is computed from the reduced numerator and denominator by a gcd. -/
private theorem primrec_natCast_div_two_pow : Primrec₂ fun (M E : ℕ) => (M : ℚ) / 2 ^ E := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have h2E : Primrec fun p : ℕ × ℕ => 2 ^ p.2 := hpow.comp (Primrec.const 2) Primrec.snd
  have hg : Primrec fun p : ℕ × ℕ => Nat.gcd (2 ^ p.2) p.1 :=
    ComputableReals.primrec_natGcd.comp h2E Primrec.fst
  have hcode : Primrec fun p : ℕ × ℕ =>
      ratCount (Nat.pair (2 * (p.1 / Nat.gcd (2 ^ p.2) p.1)) (2 ^ p.2 / Nat.gcd (2 ^ p.2) p.1)) :=
    primrec_ratCount.comp (Primrec₂.natPair.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_div.comp Primrec.fst hg))
      (Primrec.nat_div.comp h2E hg))
  refine Primrec.encode_iff.1 (hcode.of_eq fun p => ?_)
  have hq : (p.1 : ℚ) / 2 ^ p.2 = mkRat (p.1 : ℤ) (2 ^ p.2) := by
    rw [Rat.mkRat_eq_div]
    push_cast
    rfl
  have hne : 2 ^ p.2 ≠ 0 := by positivity
  have hnum : ((p.1 : ℚ) / 2 ^ p.2).num = ((p.1 / Nat.gcd (2 ^ p.2) p.1 : ℕ) : ℤ) := by
    rw [hq, Rat.num_mkRat, if_neg hne, Int.natAbs_natCast, Int.natCast_div]
  have hden : ((p.1 : ℚ) / 2 ^ p.2).den = 2 ^ p.2 / Nat.gcd (2 ^ p.2) p.1 := by
    rw [hq, Rat.den_mkRat, if_neg hne, Int.natAbs_natCast]
  rw [encode_eq_ratCount]
  dsimp only
  rw [ratCode, hnum, hden]
  rfl

/-- The load is primitive recursive in the request list and the word.
Blueprint 01 F2.2. -/
theorem primrec_load : Primrec₂ load := by
  have hpow : Primrec₂ fun a b : ℕ => a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
  have hsum : ∀ {f : List Request × BitString → List ℕ}, Primrec f →
      Primrec fun p => (f p).sum := fun hf =>
    (Primrec.list_foldr hf (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl
  have hpre : Primrec₂ fun x v : BitString => decide (x <+: v) :=
    (Primrec.eq.decide.comp Primrec.fst
      (Primrec.list_take.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))).of_eq
      fun p => decide_eq_decide.2 List.prefix_iff_eq_take.symm
  have hE : Primrec fun p : List Request × BitString => (p.1.map fun r => r.2).sum :=
    hsum (Primrec.list_map Primrec.fst (Primrec.snd.comp Primrec.snd).to₂)
  have hsel : Primrec fun p : List Request × BitString =>
      p.1.filter fun r => decide (r.1 <+: p.2) :=
    Primrec.list_filter Primrec.fst
      (hpre.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
  have hM : Primrec fun p : List Request × BitString =>
      ((p.1.filter fun r => decide (r.1 <+: p.2)).map fun r =>
        2 ^ ((p.1.map fun r => r.2).sum - r.2)).sum :=
    hsum (Primrec.list_map hsel
      (hpow.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (hE.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂)
  exact Primrec₂.mk ((primrec_natCast_div_two_pow.comp hM hE).of_eq fun p =>
    (load_eq_natCast_div_two_pow p.1 p.2).symm)

/-- The budget checker is primitive recursive. Blueprint 01 F2.2. -/
theorem primrec_budgetCheck : Primrec₂ budgetCheck := by
  exact Primrec₂.mk (list_all_primrec Primrec.fst
    (ComputableReals.primrec_ratLe.decide.comp
      (primrec_load.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)).to₂)

/-! ### Fresh-root translation -/

/-- Translate a local request list below the root `u`: `(x, n) ↦ (u ++ x, n)`.
Blueprint 01 F2.3. -/
def translateRequests (u : BitString) (A : List Request) : List Request :=
  A.map fun r => (u ++ r.1, r.2)

/-- On a word entering `u`, the translated requests carry exactly the local load of the word
with `u` removed. Blueprint 01 F2.3. -/
theorem load_translateRequests_of_prefix (u : BitString) (A : List Request) {v : BitString}
    (h : u <+: v) : load (translateRequests u A) v = load A (v.drop u.length) := by
  obtain ⟨w, rfl⟩ := h
  rw [List.drop_left]
  unfold load translateRequests
  rw [List.filter_map, List.map_map]
  congr 2
  refine List.filter_congr fun r _ => ?_
  simp only [Function.comp_apply, List.prefix_append_right_inj]

/-- On a word not entering `u`, the translated requests carry no load.
Blueprint 01 F2.3. -/
theorem load_translateRequests_of_not_prefix (u : BitString) (A : List Request)
    {v : BitString} (h : ¬ u <+: v) : load (translateRequests u A) v = 0 := by
  unfold load translateRequests
  rw [List.filter_map, List.filter_eq_nil_iff.2 fun r _ => ?_]
  · simp
  · simp only [Function.comp_apply, decide_eq_true_eq]
    exact fun hr => h ((List.prefix_append u r.1).trans hr)

/-- `u` is a *fresh root* for `A`: no declaration of `A` is `u` or lies below `u`.
Blueprint 01 F2.3 (remark on fresh roots). -/
def IsFreshRoot (A : List Request) (u : BitString) : Prop := ∀ r ∈ A, ¬ u <+: r.1

end Kolmogorov
