import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayBinaryEncoding
import KolmogorovMathlib.MonotoneComplexity.GacsDayBlockCode
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding.Part01

/-!
# From the wide Gács–Day game to the binary one

The reduction itself: `binaryGacsDay_of_gacsDay` and its sharp form
`binaryGacsDay_of_gacsDay_sharp` deduce the binary game statement from the statement on arbitrary
branching. A binary strategy is read as a `b`-ary one by grouping bits into blocks; the requests
at the intermediate binary nodes are prescribed by `intermediateRequestSum`, the sum of the
requests of the block completions, and `sumExtensions` with its recursion and nonnegativity
lemmas evaluates those sums. `treeSupported_truncStrategy` shows truncating to the first `b`
children keeps the depth support. The final section records what the frozen game interface still
leaves open in the passage from a simulating strategy to a computable one.
-/

namespace Kolmogorov

private def sumExtensions (k : ℕ) (f : List ℕ → ℚ) (pre : List ℕ) : ℚ :=
  match k with
  | 0 => f pre
  | k + 1 => sumExtensions k f (pre ++ [0]) + sumExtensions k f (pre ++ [1])

/-- In the binary embedding, the request at an intermediate binary node must
be the sum of the requests at its children, so that request coherence is preserved. -/
def intermediateRequestSum (m : ℕ) (baseReq : GacsDayNode → ℚ) (y : GacsDayNode) : ℚ :=
  let r := y.length % m
  if m = 0 then 0 else
  let k := if r = 0 then 0 else m - r
  sumExtensions k (fun w => baseReq (chunkNat m w)) y

private lemma sum_range_two_mul (N : ℕ) (h : ℕ → ℚ) :
    ∑ n ∈ Finset.range (2 * N), h n = ∑ j ∈ Finset.range N, (h (2 * j) + h (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : 2 * (N + 1) = (2 * N + 1) + 1 := by ring
    rw [hN, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

private lemma sumExtensions_zero (f : List ℕ → ℚ) (pre : List ℕ) :
    sumExtensions 0 f pre = f pre := rfl

private lemma sumExtensions_succ (k : ℕ) (f : List ℕ → ℚ) (pre : List ℕ) :
    sumExtensions (k + 1) f pre
      = sumExtensions k f (pre ++ [0]) + sumExtensions k f (pre ++ [1]) := rfl

private lemma sumExtensions_nonneg (f : List ℕ → ℚ) (hf : ∀ w, 0 ≤ f w) :
    ∀ (k : ℕ) (pre : List ℕ), 0 ≤ sumExtensions k f pre := by
  intro k
  induction k with
  | zero => intro pre; exact hf pre
  | succ k ih => intro pre; exact add_nonneg (ih _) (ih _)

/-- `sumExtensions k f pre` really is the sum of `f` over all `2 ^ k` binary
extensions of `pre` by `k` further bits. -/
private lemma sumExtensions_eq_sum (k : ℕ) (f : List ℕ → ℚ) (pre : List ℕ) :
    sumExtensions k f pre = ∑ n ∈ Finset.range (2 ^ k), f (pre ++ bitsOfNat k n) := by
  induction k generalizing pre with
  | zero => simp [sumExtensions, bitsOfNat]
  | succ k ih =>
    rw [sumExtensions_succ, ih, ih]
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow, sum_range_two_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [bitsOfNat_succ]
      simp [Nat.mul_mod_right]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [bitsOfNat_succ]
      have h1 : (2 * j + 1) % 2 = 1 := by omega
      have h2 : (2 * j + 1) / 2 = j := by omega
      rw [h1, h2]
      simp

private lemma intermediateRequestSum_eq (m : ℕ) (hm : 0 < m) (f : GacsDayNode → ℚ)
    (y : GacsDayNode) :
    intermediateRequestSum m f y
      = sumExtensions (if y.length % m = 0 then 0 else m - y.length % m)
          (fun w => f (chunkNat m w)) y := by
  unfold intermediateRequestSum
  rw [if_neg hm.ne']

/-- Off-block-boundary, the number of remaining bits to a block boundary drops by one. -/
private lemma child_blockGap (l m : ℕ) (hm : 0 < m) :
    (if (l + 1) % m = 0 then 0 else m - (l + 1) % m) = m - l % m - 1 := by
  have key : (l + 1) % m = (l % m + 1) % m := by
    conv_lhs => rw [← Nat.mod_add_div l m]
    rw [Nat.add_right_comm, Nat.add_mul_mod_self_left]
  have hlt : l % m < m := Nat.mod_lt _ hm
  rcases Nat.lt_or_ge (l % m + 1) m with h | h
  · rw [key, Nat.mod_eq_of_lt h, if_neg (by omega)]
    omega
  · have h' : l % m + 1 = m := by omega
    rw [key, h', Nat.mod_self, if_pos rfl]
    omega

/-- A nonnegative weight function that vanishes outside `[0, b)` has all its
range sums bounded by the sum over `Fin b`. -/
private lemma sum_range_le_of_vanishing (b N : ℕ) (F : ℕ → ℚ) (M : ℚ)
    (hF0 : ∀ n, 0 ≤ F n) (hFb : ∀ n, b ≤ n → F n = 0)
    (hM : ∑ c : Fin b, F c.val ≤ M) :
    ∑ n ∈ Finset.range N, F n ≤ M := by
  have h1 : ∑ n ∈ Finset.range N, F n ≤ ∑ n ∈ Finset.range (b + N), F n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i _ _ => hF0 i)
  have h2 : ∑ n ∈ Finset.range b, F n = ∑ n ∈ Finset.range (b + N), F n := by
    refine Finset.sum_subset
      (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega) (fun i hi hni => ?_)
    simp only [Finset.mem_range] at hi hni
    exact hFb i (by omega)
  have h3 : ∑ c : Fin b, F c.val = ∑ n ∈ Finset.range b, F n := Fin.sum_univ_eq_sum_range _ _
  linarith

/-- At a block boundary, the total request of the `2 ^ m` binary descendants at
the next boundary is bounded by the request of the node itself. -/
private lemma sumExtensions_block_le (m b : ℕ) (hm : 0 < m) (req : ClientMove)
    (hpos : ∀ x : GacsDayNode, 0 ≤ getReq req x)
    (hchild : ∀ x : GacsDayNode, getReq req x ≥ ∑ c : Fin b, getReq req (x ++ [c.val]))
    (h_range : ∀ (x : GacsDayNode) (i : ℕ), b ≤ i → getReq req (x ++ [i]) = 0)
    (y : GacsDayNode) (hy : m ∣ y.length) :
    sumExtensions m (fun w => getReq req (chunkNat m w)) y ≤ getReq req (chunkNat m y) := by
  rw [sumExtensions_eq_sum]
  have hrw : ∀ n ∈ Finset.range (2 ^ m),
      getReq req (chunkNat m (y ++ bitsOfNat m n)) = getReq req (chunkNat m y ++ [n]) := by
    intro n hn
    rw [chunkNat_append m hm y _ hy, chunkNat_of_length m hm _ (bitsOfNat_length m n),
      bitsToNatLocal_bitsOfNat m n (Finset.mem_range.mp hn)]
  rw [Finset.sum_congr rfl hrw]
  exact sum_range_le_of_vanishing b (2 ^ m) (fun n => getReq req (chunkNat m y ++ [n])) _
    (fun n => hpos _) (fun n hn => h_range _ n hn) (hchild _)

/-- The embedding needs that the base game's requests vanish at child indices
outside the branching factor `b`. Without this the lemma is false:
take `b = 1`, `d = 1`, `req = [([], 1/2), ([0], 1/4), ([1], 1/2)]`;
then `requestCoherent 1 1 req` holds (sums only over `Fin 1`) but
the binary child sum `1/4 + 1/2 > 1/2` violates binary coherence. -/
lemma requestCoherent_intermediate (m b d : ℕ) (req req_bin : ClientMove)
    (h_coh : requestCoherent b d req)
    (h_range : ∀ x : GacsDayNode, ∀ i, b ≤ i → getReq req (x ++ [i]) = 0)
    (h_bin : ∀ x, getReq req_bin x = intermediateRequestSum m (getReq req) x) :
    requestCoherent 2 d req_bin := by
  obtain ⟨hpos, hroot, hchild⟩ := h_coh
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ x, getReq req_bin x = 0 := by
      intro x; rw [h_bin]; simp [intermediateRequestSum]
    refine ⟨fun x => ?_, ?_, fun x => ?_⟩
    · rw [h0]
    · rw [h0]
      positivity
    · rw [Fin.sum_univ_two, h0, h0, h0]
      norm_num
  · have hfnn : ∀ w : List ℕ, 0 ≤ getReq req (chunkNat m w) := fun w => hpos _
    refine ⟨fun x => ?_, ?_, fun x => ?_⟩
    · rw [h_bin, intermediateRequestSum_eq m hm]
      exact sumExtensions_nonneg _ hfnn _ _
    · rw [h_bin, intermediateRequestSum_eq m hm]
      have hnil : ([] : GacsDayNode).length % m = 0 := by simp
      rw [if_pos hnil, sumExtensions_zero, chunkNat_nil]
      exact hroot
    · rw [Fin.sum_univ_two]
      simp only [h_bin]
      rw [intermediateRequestSum_eq m hm, intermediateRequestSum_eq m hm,
        intermediateRequestSum_eq m hm]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Fin.isValue, Fin.val_zero, Fin.val_one]
      rw [child_blockGap x.length m hm]
      by_cases hr : x.length % m = 0
      · rw [if_pos hr, sumExtensions_zero, hr]
        have hm1 : m - 0 - 1 + 1 = m := by omega
        rw [ge_iff_le, ← sumExtensions_succ (m - 0 - 1), hm1]
        exact sumExtensions_block_le m b hm req hpos hchild h_range x (Nat.dvd_of_mod_eq_zero hr)
      · rw [if_neg hr]
        have hlt : x.length % m < m := Nat.mod_lt _ hm
        have hm1 : m - x.length % m - 1 + 1 = m - x.length % m := by omega
        rw [ge_iff_le, ← sumExtensions_succ (m - x.length % m - 1), hm1]

private lemma lookup_map_pair (g : GacsDayNode → ℚ) :
    ∀ (l : List GacsDayNode) (y : GacsDayNode), y ∈ l →
      (l.map (fun k => (k, g k))).lookup y = some (g y) := by
  intro l
  induction l with
  | nil => intro y hy; cases hy
  | cons k ks ih =>
      intro y hy
      by_cases hk : y = k
      · subst hk; simp
      · have hne : (y == k) = false := beq_eq_false_iff_ne.mpr hk
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h hk
        · simp [List.lookup_cons, hne, ih y h]

private lemma lookup_map_pair_none (g : GacsDayNode → ℚ) :
    ∀ (l : List GacsDayNode) (y : GacsDayNode), y ∉ l →
      (l.map (fun k => (k, g k))).lookup y = none := by
  intro l
  induction l with
  | nil => intro y _; simp
  | cons k ks ih =>
      intro y hy
      have hk : y ≠ k := fun h => hy (h ▸ List.mem_cons_self ..)
      have hne : (y == k) = false := beq_eq_false_iff_ne.mpr hk
      have hys : y ∉ ks := fun h => hy (List.mem_cons_of_mem _ h)
      simp [List.lookup_cons, hne, ih y hys]

private lemma mem_keys_of_lookup_eq_some {β : Type} :
    ∀ (l : List (GacsDayNode × β)) (a : GacsDayNode) (v : β),
      l.lookup a = some v → a ∈ l.map Prod.fst := by
  intro l
  induction l with
  | nil => intro a v h; simp at h
  | cons p ps ih =>
      intro a v h
      by_cases ha : a = p.1
      · subst ha; simp
      · have hne : (a == p.1) = false := beq_eq_false_iff_ne.mpr ha
        rw [List.lookup_cons, hne] at h
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih a v h)

private lemma mem_keys_of_getReq_ne_zero (req : ClientMove) (w : GacsDayNode)
    (hw : getReq req w ≠ 0) : w ∈ req.map Prod.fst := by
  unfold getReq at hw
  cases hl : req.lookup w with
  | none => rw [hl] at hw; exact absurd rfl hw
  | some q => exact mem_keys_of_lookup_eq_some req w q hl

private lemma mem_natListsLen (M : ℕ) :
    ∀ (y : List ℕ), (∀ a ∈ y, a ≤ M) → y ∈ natListsLen M y.length := by
  intro y
  induction y with
  | nil => intro _; simp [natListsLen]
  | cons a t ih =>
      intro h
      have ha : a ≤ M := h a (List.mem_cons_self ..)
      have ht : t ∈ natListsLen M t.length :=
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
      simp only [List.length_cons, natListsLen, List.mem_flatMap]
      exact ⟨a, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨t, ht, rfl⟩⟩

private lemma mem_natListsUpTo (M L : ℕ) (y : List ℕ) (h1 : y.length ≤ L)
    (h2 : ∀ a ∈ y, a ≤ M) : y ∈ natListsUpTo M L := by
  simp only [natListsUpTo, List.mem_flatMap, List.mem_range]
  exact ⟨y.length, by omega, mem_natListsLen M y h2⟩

private lemma le_foldr_max : ∀ (l : List ℕ) (v : ℕ), v ∈ l → v ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro v hv; cases hv
  | cons a t ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih v h) (le_max_right _ _)

private lemma keyMaxLen_bound (req : ClientMove) (x : GacsDayNode)
    (hx : x ∈ req.map Prod.fst) : x.length ≤ keyMaxLen req := by
  apply le_foldr_max
  simp only [List.mem_map] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, hp, rfl⟩

private lemma keyMaxEntry_bound (req : ClientMove) (x : GacsDayNode)
    (hx : x ∈ req.map Prod.fst) (a : ℕ) (ha : a ∈ x) : a ≤ keyMaxEntry req := by
  have h1 : a ≤ x.foldr max 0 := le_foldr_max x a ha
  have h2 : x.foldr max 0 ≤ keyMaxEntry req := by
    apply le_foldr_max
    simp only [List.mem_map] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩
  omega

private lemma exists_blockCount (m : ℕ) (hm : 0 < m) (l : ℕ) :
    ∃ q, l + (if l % m = 0 then 0 else m - l % m) = m * q := by
  have hmod : m * (l / m) + l % m = l := Nat.div_add_mod l m
  have hrlt : l % m < m := Nat.mod_lt _ hm
  by_cases hr : l % m = 0
  · exact ⟨l / m, by rw [if_pos hr]; omega⟩
  · refine ⟨l / m + 1, ?_⟩
    have hexp : m * (l / m + 1) = m * (l / m) + m := by ring
    rw [if_neg hr, hexp]
    omega

/-- Off the finite support determined by the base client move, the intermediate
request assignment vanishes. -/
private lemma intermediateRequestSum_eq_zero_of_not_mem (m : ℕ) (hm : 0 < m)
    (req : ClientMove) (y : GacsDayNode)
    (hy : y ∉ natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)) :
    intermediateRequestSum m (getReq req) y = 0 := by
  rw [intermediateRequestSum_eq m hm, sumExtensions_eq_sum]
  refine Finset.sum_eq_zero (fun n _ => ?_)
  by_contra hne
  obtain ⟨q, hq0⟩ := exists_blockCount m hm y.length
  set k := (if y.length % m = 0 then 0 else m - y.length % m) with hk
  set w := y ++ bitsOfNat k n with hw
  have hq : w.length = m * q := by
    rw [hw, List.length_append, bitsOfNat_length]
    exact hq0
  have hx : chunkNat m w ∈ req.map Prod.fst := mem_keys_of_getReq_ne_zero req _ hne
  have hlq : (chunkNat m w).length = q := chunkNat_length_eq m hm q w hq
  apply hy
  refine mem_natListsUpTo _ _ _ ?_ ?_
  · have hqle : q ≤ keyMaxLen req := by
      rw [← hlq]; exact keyMaxLen_bound req _ hx
    have hylen : y.length ≤ w.length := by
      rw [hw, List.length_append]; omega
    calc y.length ≤ w.length := hylen
      _ = m * q := hq
      _ ≤ m * keyMaxLen req := Nat.mul_le_mul_left _ hqle
  · intro a ha
    have haw : a ∈ w := by rw [hw]; exact List.mem_append_left _ ha
    obtain ⟨v, hv, hav⟩ := exists_ge_mem_chunkNat m hm q w hq a haw
    exact le_trans hav (keyMaxEntry_bound req _ hx v hv)

/-- The intermediate (block-interpolated) request assignment is realized by an
honest `ClientMove`: a finite association list whose request function agrees with
`intermediateRequestSum` at *every* node, and which is coherent for the binary
tree. -/
lemma exists_intermediateClientMove (m b d : ℕ) (req : ClientMove)
    (hcoh : requestCoherent b d req)
    (hrange : ∀ (x : GacsDayNode) (i : ℕ), b ≤ i → getReq req (x ++ [i]) = 0) :
    ∃ reqBin : ClientMove,
      (∀ y, getReq reqBin y = intermediateRequestSum m (getReq req) y) ∧
      requestCoherent 2 d reqBin := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hbin : ∀ y, getReq ([] : ClientMove) y = intermediateRequestSum 0 (getReq req) y := by
      intro y; simp [getReq, intermediateRequestSum]
    exact ⟨[], hbin, requestCoherent_intermediate 0 b d req [] hcoh hrange hbin⟩
  · refine ⟨(natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)).map
      (fun k => (k, intermediateRequestSum m (getReq req) k)), ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)
      · unfold getReq
        rw [lookup_map_pair _ _ y hy]
      · unfold getReq
        rw [lookup_map_pair_none _ _ y hy]
        exact (intermediateRequestSum_eq_zero_of_not_mem m hm req y hy).symm
    · refine requestCoherent_intermediate m b d req _ hcoh hrange (fun y => ?_)
      by_cases hy : y ∈ natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)
      · unfold getReq
        rw [lookup_map_pair _ _ y hy]
      · unfold getReq
        rw [lookup_map_pair_none _ _ y hy]
        exact (intermediateRequestSum_eq_zero_of_not_mem m hm req y hy).symm

/-- At a node that sits on a block boundary the interpolated request is exactly
the request of the decoded base node. -/
lemma intermediateRequestSum_blockCode (m : ℕ) (hm : 0 < m) (f : GacsDayNode → ℚ)
    (x : GacsDayNode) (hx : ∀ a ∈ x, a < 2 ^ m) :
    intermediateRequestSum m f (blockCode m x) = f x := by
  rw [intermediateRequestSum_eq m hm]
  have hlen : (blockCode m x).length % m = 0 := by
    rw [blockCode_length]
    simp [Nat.mul_mod_right]
  rw [if_pos hlen, sumExtensions_zero, chunkNat_blockCode m hm x hx]

/-- The interpolated request assignment is monotone in the base assignment. -/
lemma intermediateRequestSum_mono (m : ℕ) {f g : GacsDayNode → ℚ} (hfg : ∀ x, f x ≤ g x)
    (y : GacsDayNode) :
    intermediateRequestSum m f y ≤ intermediateRequestSum m g y := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [intermediateRequestSum]
  · rw [intermediateRequestSum_eq m hm, intermediateRequestSum_eq m hm,
      sumExtensions_eq_sum, sumExtensions_eq_sum]
    exact Finset.sum_le_sum (fun n _ => hfg _)

/-!
### Status of the binary-embedding reduction

The main reduction: the Gacs-Day statement implies the binary version.
This is a reduction only; Theorem 88 is not asserted to be proved here.

The mathematical core of this reduction is proved above:
`serverPlayLegal_baseServerMove` (a legal binary server play induces a legal
`b`-ary one), `exists_intermediateClientMove` (the interpolated requests are an
honest finite client move) and `isWinningStrategyUnserved_binary_of_base` (a
simulating binary strategy inherits the win).  What is still missing is a
*computable* binary strategy `τ` simulating `σ` uniformly in `d`, and here the
current frozen interface obstructs the construction: `IsWinningStrategy` only
asserts `∃ h0 ≤ h, ∃ b0 ≤ b, IsWinningStrategyUnserved h0 b0 d σ`, so the branching
factor `b0` for which the base play is coherent is not known -- and not
necessarily a computable function of `d`.  Since `requestCoherent b0 d` says
nothing about requests at branch indices `≥ b0`, the interpolated binary requests
need those out-of-range requests to be deleted (hypothesis `hrange` above), which
cannot be done uniformly without knowing `b0`.  With a uniform interface (winning
for the stated `h` and `b` themselves) the argument above closes the reduction.
-/

/-- The interpolation of a `b`-ary client move to the binary tree: every binary node of
depth at most `m * keyMaxLen req`, with branch indices bounded by `keyMaxEntry req`, is
given the request `intermediateRequestSum m (getReq req)`, i.e. the request `req` puts on
the block-coded node it lies above. -/
def intermediateClientMove (m : ℕ) (req : ClientMove) : ClientMove :=
  (natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)).map
    (fun k => (k, intermediateRequestSum m (getReq req) k))

/-- The strategy `σ` played on the binary tree: the history is read back through the block code
and the resulting move is spread over the blocks of width `m`. -/
def embeddedClientStrategy (m : ℕ) (σ : ClientStrategy) : ClientStrategy :=
  fun hist => intermediateClientMove m (replayStrategy σ (hist.1, hist.2.map (baseServerMove m)))



/-- The embedded move requests at a node the intermediate sum of the original requests over the
nodes it covers. -/
lemma getReq_intermediateClientMove (m : ℕ) (req : ClientMove) (y : GacsDayNode) :
    getReq (intermediateClientMove m req) y = intermediateRequestSum m (getReq req) y := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [getReq, intermediateClientMove, intermediateRequestSum, ↓reduceIte, natListsUpTo,
      zero_mul, zero_add, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    cases y with
    | nil => simp [natListsLen]
    | cons a as => simp [natListsLen, List.lookup]
  · by_cases hy : y ∈ natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)
    · unfold intermediateClientMove getReq
      rw [lookup_map_pair _ _ y hy]
    · unfold intermediateClientMove getReq
      rw [lookup_map_pair_none _ _ y hy]
      exact (intermediateRequestSum_eq_zero_of_not_mem m hm req y hy).symm

/-- Spreading a coherent move supported on the first `b` children over blocks of width `m` gives
a coherent move on the binary tree. -/
lemma requestCoherent_intermediateClientMove (m b d : ℕ) (hm : 0 < m) (req : ClientMove)
    (h_coh : requestCoherent b d req)
    (h_range : ∀ x : GacsDayNode, ∀ i, b ≤ i → getReq req (x ++ [i]) = 0) :
    requestCoherent 2 d (intermediateClientMove m req) := by
  refine requestCoherent_intermediate m b d req _ h_coh h_range (fun y => ?_)
  by_cases hy : y ∈ natListsUpTo (keyMaxEntry req) (m * keyMaxLen req)
  · unfold intermediateClientMove getReq
    rw [lookup_map_pair _ _ y hy]
  · unfold intermediateClientMove getReq
    rw [lookup_map_pair_none _ _ y hy]
    exact (intermediateRequestSum_eq_zero_of_not_mem m hm req y hy).symm

private lemma intermediateRequestSum_eq_rangeSum (m : ℕ) (f : GacsDayNode → ℚ)
    (y : GacsDayNode) :
    intermediateRequestSum m f y =
      if m = 0 then 0 else
        ∑ n ∈ Finset.range (2 ^ (if y.length % m = 0 then 0 else m - y.length % m)),
          f (chunkNat m
            (y ++ bitsOfNat (if y.length % m = 0 then 0 else m - y.length % m) n)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [intermediateRequestSum]
  · rw [if_neg (by omega), intermediateRequestSum_eq m hm f y, sumExtensions_eq_sum]

private lemma primrec_padLen : Primrec (fun z : (ℕ × ClientMove) × GacsDayNode =>
    if z.2.length % z.1.1 = 0 then 0 else z.1.1 - z.2.length % z.1.1) := by
  have hmod : Primrec (fun z : (ℕ × ClientMove) × GacsDayNode => z.2.length % z.1.1) :=
    Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact Primrec.ite (Primrec.eq.comp hmod (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) hmod)

private lemma computable_decideEqZero {α : Type} [Primcodable α] {f : α → ℕ}
    (hf : Primrec f) : Computable (fun a => decide (f a = 0)) := by
  have h : PrimrecPred (fun a => f a = 0) := Primrec.eq.comp hf (Primrec.const 0)
  obtain ⟨_, h⟩ := h
  exact (h.of_eq (fun a => by simp)).to_comp

private lemma natRec_ratAdd_eq_sumRange (N : ℕ) (f : ℕ → ℚ) :
    Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) N =
      ∑ n ∈ Finset.range N, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep : Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) (N + 1) =
          Nat.rec (motive := fun _ => ℚ) 0 (fun n acc => acc + f n) N + f N := rfl
      rw [hstep, Finset.sum_range_succ, ih]

private lemma computable_ratRangeSum_local {α : Type} [Primcodable α]
    {N : α → ℕ} {f : α → ℕ → ℚ} (hN : Computable N) (hf : Computable₂ f) :
    Computable (fun a => ∑ n ∈ Finset.range (N a), f a n) := by
  have hstep : Computable₂ (fun (a : α) (p : ℕ × ℚ) => p.2 + f a p.1) :=
    (Computable₂.comp computable₂_ratAdd (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  refine (Computable.nat_rec hN (Computable.const (0 : ℚ)) hstep).of_eq (fun a => ?_)
  exact natRec_ratAdd_eq_sumRange (N a) (f a)

/-- The intermediate request sum is computable in the block width, the move and the node. -/
lemma computable₂_intermediateRequestSum : Computable₂ (fun (p : ℕ × ClientMove) y =>
    intermediateRequestSum p.1 (getReq p.2) y) := by
  have hk := primrec_padLen
  have hN : Primrec (fun z : (ℕ × ClientMove) × GacsDayNode =>
      2 ^ (if z.2.length % z.1.1 = 0 then 0 else z.1.1 - z.2.length % z.1.1)) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) hk
  have hg : Primrec₂ (fun (z : (ℕ × ClientMove) × GacsDayNode) (n : ℕ) =>
      getReq z.1.2 (chunkNat z.1.1 (z.2 ++ bitsOfNat
        (if z.2.length % z.1.1 = 0 then 0 else z.1.1 - z.2.length % z.1.1) n))) :=
    Primrec₂.mk (primrec_getReq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (primrec_chunkNat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
          (primrec_bitsOfNat.comp (hk.comp Primrec.fst) Primrec.snd))))
  have hsum := computable_ratRangeSum_local hN.to_comp hg.to_comp
  have hcond := computable_decideEqZero (Primrec.fst.comp
    (Primrec.fst : Primrec (fun z : (ℕ × ClientMove) × GacsDayNode => z.1)))
  refine Computable₂.mk
    ((Computable.cond hcond (Computable.const (0 : ℚ)) hsum).of_eq (fun z => ?_))
  rw [intermediateRequestSum_eq_rangeSum]
  by_cases h : z.1.1 = 0 <;> simp [h]

/-- A strategy supported to depth `h` embeds into a binary strategy supported to depth `m * h`. -/
theorem treeSupported_embeddedClientStrategy {h b m : ℕ} {σ : ClientStrategy}
    (h_supp : TreeSupported h b σ) : TreeSupported (m * h) 2 (embeddedClientStrategy m σ) := by
  intro hist y hy
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [embeddedClientStrategy, getReq_intermediateClientMove, intermediateRequestSum]
  rw [embeddedClientStrategy, getReq_intermediateClientMove,
    intermediateRequestSum_eq_rangeSum, if_neg hm.ne']
  refine Finset.sum_eq_zero fun n _ => ?_
  set k : ℕ := if y.length % m = 0 then 0 else m - y.length % m with hk
  have hdm : y.length = m * (y.length / m) + y.length % m := (Nat.div_add_mod _ _).symm
  have hrm : y.length % m < m := Nat.mod_lt _ hm
  obtain ⟨q, hq, hhq⟩ :
      ∃ q, (y ++ bitsOfNat k n).length = m * q ∧ h < q := by
    by_cases hr : y.length % m = 0
    · refine ⟨y.length / m, ?_, ?_⟩
      · simp [hk, hr]
        omega
      · exact lt_of_mul_lt_mul_left (by omega) (Nat.zero_le m)
    · refine ⟨y.length / m + 1, ?_, ?_⟩
      · simp only [hk, hr, ↓reduceIte, List.length_append, bitsOfNat_length]
        have : m * (y.length / m + 1) = m * (y.length / m) + m := by ring
        omega
      · refine lt_of_mul_lt_mul_left (a := m) ?_ (Nat.zero_le m)
        have : m * (y.length / m + 1) = m * (y.length / m) + m := by ring
        omega
  have hlen := chunkNat_length_eq m hm q (y ++ bitsOfNat k n) hq
  exact h_supp _ _ (by rw [hlen]; exact hhq)

/-- **The core of the binary embedding.**  Let `σ` be a client strategy that wins
the Gács–Day game of height `h` and branching factor `b ≤ 2 ^ m`, and whose
requests vanish at out-of-range branch indices.  If a binary client strategy `τ`
simulates `σ` -- its requests are the block interpolation of the requests `σ`
makes against the induced `b`-ary server play -- then `τ` wins the binary game of
height `m * h`.

Only the *existence of a computable such* `τ` is missing for the full reduction
`binaryGacsDay_of_gacsDay`; see the discussion there. -/
theorem isWinningStrategyUnserved_binary_of_base
    (m b d h : ℕ) (hm : 0 < m) (hb : b ≤ 2 ^ m) (σ τ : ClientStrategy)
    (hrange : ∀ (hist : GameHistory) (x : GacsDayNode) (i : ℕ), b ≤ i →
      getReq (σ hist) (x ++ [i]) = 0)
    (hsim : ∀ (sms : ℕ → ServerMove) (t : ℕ) (y : GacsDayNode),
      getReq (playClient τ sms t) y
        = intermediateRequestSum m
            (getReq (playClient σ (fun s => baseServerMove m (sms s)) t)) y)
    (hwin : IsWinningStrategyUnserved (h := h) (b := b) d σ) :
    IsWinningStrategyUnserved (h := m * h) (b := 2) d τ := by
  intro sms hsms
  obtain ⟨hlegal, hwins⟩ := hwin _ (serverPlayLegal_baseServerMove m b hm hb sms hsms)
  refine ⟨⟨fun t => ?_, fun t y => ?_⟩, ?_⟩
  · obtain ⟨hist, hhist⟩ := exists_history_playClient σ (fun s => baseServerMove m (sms s)) t
    refine requestCoherent_intermediate m b d _ _ (hlegal.1 t) (fun x i hi => ?_) (hsim sms t)
    rw [hhist]
    exact hrange hist x i hi
  · rw [hsim sms t y, hsim sms (t + 1) y]
    exact intermediateRequestSum_mono m (fun x => hlegal.2 t x) y
  · obtain ⟨T, x, hxlen, hxrange, hxunserved⟩ := hwins
    have hx2 : ∀ a ∈ x, a < 2 ^ m := fun a ha => lt_of_lt_of_le (hxrange a ha) hb
    refine ⟨T, blockCode m x, ?_, blockCode_lt_two m x, fun t => ?_⟩
    · rw [blockCode_length]
      exact Nat.mul_le_mul_left _ hxlen
    · rw [hsim sms T (blockCode m x), intermediateRequestSum_blockCode m hm _ x hx2,
        ← getAlloc_baseServerMove m hm (sms t) x hx2]
      exact hxunserved t

/-- The embedded strategy plays the spread of the move the original strategy plays against the
block-coded server. -/
lemma playClient_embeddedClientStrategy (m : ℕ) (σ : ClientStrategy) (sms : ℕ
  → ServerMove) (t : ℕ) :
    playClient (embeddedClientStrategy m σ) sms t = intermediateClientMove m (playClient σ (fun s =>
      baseServerMove m (sms s)) t) := by
  have h1 : playClient (embeddedClientStrategy m σ) sms t
    = intermediateClientMove m (playClient (replayStrategy σ) (fun s =>
    baseServerMove m (sms s)) t) := by
    cases t with
    | zero =>
      rw [playClient, playClient]
      unfold embeddedClientStrategy
      rfl
    | succ t =>
      rw [playClient, playClient]
      unfold embeddedClientStrategy replayStrategy
      dsimp
      congr 1
      congr 1
      rw [List.map_ofFn]
      rfl
  rw [h1, playClient_replayStrategy]

/-- The request of the embedded play at a node is the intermediate sum of the requests of the
original play. -/
lemma getReq_playClient_embedded (m : ℕ) (σ : ClientStrategy) (sms : ℕ
  → ServerMove) (t : ℕ) (y : GacsDayNode) :
    getReq (playClient (embeddedClientStrategy m σ) sms t) y
      = intermediateRequestSum m (getReq (playClient σ (fun s => baseServerMove m (sms s)) t)) y :=
      by
  rw [playClient_embeddedClientStrategy]
  apply getReq_intermediateClientMove

/-- Spreading a move over blocks of width `m` is computable in the width and the move. -/
lemma computable₂_intermediateClientMove :
    Computable₂ (fun (m : ℕ) (req : ClientMove) => intermediateClientMove m req) := by
  have hL : Primrec (fun z : ℕ × ClientMove =>
      natListsUpTo (keyMaxEntry z.2) (z.1 * keyMaxLen z.2)) :=
    primrec_natListsUpTo.comp (primrec_keyMaxEntry.comp Primrec.snd)
      (Primrec.nat_mul.comp Primrec.fst (primrec_keyMaxLen.comp Primrec.snd))
  have hg : Computable₂ (fun (z : ℕ × ClientMove) (k : GacsDayNode) =>
      (k, intermediateRequestSum z.1 (getReq z.2) k)) :=
    Computable.pair Computable.snd computable₂_intermediateRequestSum
  exact Computable₂.mk (Computable.list_map hL.to_comp hg)

/-- Embedding a computable family of strategies with a computable width keeps it computable. -/
lemma computable₂_embeddedClientStrategy {σ' : ℕ → ClientStrategy} {m : ℕ → ℕ}
    (hcomp_σ : Computable₂ σ') (hcomp_m : Computable m) :
    Computable₂ (fun d hist => embeddedClientStrategy (m d) (σ' d) hist) := by
  have hm : Computable (fun z : ℕ × GameHistory => m z.1) := hcomp_m.comp Computable.fst
  have hmapS : Computable (fun z : ℕ × GameHistory => z.2.2.map (baseServerMove (m z.1))) :=
    Computable.list_map (Computable.snd.comp Computable.snd)
      (Computable₂.comp primrec₂_baseServerMove.to_comp (hm.comp Computable.fst) Computable.snd)
  have hR : Computable (fun p : ℕ × GameHistory => replayStrategy (σ' p.1) p.2) :=
    computable₂_replayStrategy hcomp_σ
  have harg : Computable (fun z : ℕ × GameHistory =>
      ((z.1 : ℕ), ((z.2.1, z.2.2.map (baseServerMove (m z.1))) : GameHistory))) :=
    Computable.pair Computable.fst
      (Computable.pair (Computable.fst.comp Computable.snd) hmapS)
  have hI : Computable (fun p : ℕ × ClientMove => intermediateClientMove p.1 p.2) :=
    computable₂_intermediateClientMove
  exact Computable₂.mk (hI.comp (Computable.pair hm (hR.comp harg)))

/-- The Gács–Day game statement on arbitrary branching implies the binary statement with the
sharp height bound. -/
theorem binaryGacsDay_of_gacsDay_sharp
    (hGD : GacsDayGameStatement) :
    BinaryGacsDayStatement := by
  obtain ⟨C, σ, hcomp, hwin⟩ := hGD
  obtain ⟨C', hC'⟩ := gacsDay_binary_height_bound C
  use C', fun d => truncStrategy 2 (embeddedClientStrategy ((C * d) ^ (C * d)) (σ d))
  refine ⟨computable₂_truncStrategy (computable₂_embeddedClientStrategy hcomp
    (computable_gacsDay_blockWidth C)), fun d hd => ?_⟩
  have hw := hwin d hd
  have hpos : 0 < ((C * d) ^ (C * d)) := by
    cases C * d
    · exact by decide
    · apply Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (Nat.zero_lt_succ _)))
  have hwin2 :=
    isWinningStrategyUnserved_binary_of_base ((C * d) ^ (C * d)) (2 ^ ((C * d) ^ (C * d))) d (C * d)
    hpos (by rfl) (σ d) (embeddedClientStrategy ((C * d) ^ (C * d)) (σ d)) hw.2
    (getReq_playClient_embedded ((C * d) ^ (C * d)) (σ d)) hw.1
  have hwin2_comm : IsWinningStrategyUnserved (h := C * d * ((C * d) ^ (C
    * d))) (b := 2) d (embeddedClientStrategy ((C * d) ^ (C * d)) (σ d)) := by
    have h_eq : (C * d) ^ (C * d) * (C * d) = C * d * ((C * d) ^ (C * d)) := Nat.mul_comm _ _
    rwa [h_eq] at hwin2
  have hwin3 := isWinningStrategyUnserved_mono_height (hC' d) hwin2_comm
  exact ⟨isWinningStrategyUnserved_truncStrategy _ _ _ _ hwin3, rangeSupported_truncStrategy _ _⟩

/-- The Gács–Day game statement on arbitrary branching implies the binary statement with a height
bound of the form `2 ^ (C * (c + 1) * 2 ^ c)`. -/
theorem binaryGacsDay_of_gacsDay
    (hGD : GacsDayGameStatement) :
    BinaryGacsDayStatement_pow := by
  obtain ⟨C, σ, hcomp, hwin⟩ := binaryGacsDay_of_gacsDay_sharp hGD
  use C, σ, hcomp
  intro d hd
  have hw := hwin d hd
  exact ⟨isWinningStrategyUnserved_mono_height (Nat.le_two_pow_self _) hw.1, hw.2⟩


/-- Truncating to the first `b` children preserves support to depth `h`. -/
theorem treeSupported_truncStrategy {h b : ℕ} {σ : ClientStrategy}
    (h_supp : TreeSupported h b σ) : TreeSupported h b (truncStrategy b σ) := by
  intro hist x hx
  unfold truncStrategy replayStrategy
  rw [getReq_truncMove]
  split_ifs
  · exact h_supp (selfPlay σ hist.2, hist.2) x hx
  · rfl

end Kolmogorov
