import KolmogorovMathlib.StrongMerging.Lower.Peeling
import KolmogorovMathlib.StrongMerging.Lower.Analysis
import KolmogorovMathlib.StrongMerging.Lower.CenterCode

/-!
# The sharp lower bound: a large projection, the exact partition and its score

Blueprint nodes L33 (`coreHasLargeProjection`), L34 (`labelProjectionPartition`) and L35
(`projectionScoreCode`) of the formalization of `sublinear-merging.tex` (main text "A large
projection forced by the distance bound", tex lines 1718-1758, and "The projected core is a
forbidden partition cell", lines 1759-1820; appendix paragraphs "L33" to "L35--L36", lines
4941-5026).  The primary distance count is the small-set-expansion bound L13
(`distanceCountFromSSE`).

* **L33.**  If the peeled core is nonempty and the threshold beats the distance count,
  `θ > 2 (M + 1) D_a 2^(-3r/2)`, then one projection of the core has at least `2^(M/8)` points:
  otherwise their union `U` has at most `2^(M/4)` points, every core edge is an ordered
  distance-`2r` pair in `U`, minimum degree gives `θ |U| ≤ 2 |core|`, and L13 gives
  `|core| ≤ |U| (M + 1) D_a 2^(-3r/2)`.
* **L34.**  `projCell` is an actual total map on all words: on an `M`-word `y` it reads the label
  of `y` from its own star, peels the graph of that label and returns the projection of the core
  on `y`'s side if it contains `y`, and `{y}` otherwise; other lengths give `{y}`.  It is an exact
  partition of the cube (`projCell_spec`), realized by one compiled total program of length
  `|p_A| + |p_B| + c_t m` (one fixed packet-reading decoder through the structural compiler of
  S01, `exists_compiled_totalProgram`).  Admission to the game budget `S = 3T` needs the
  explicit premise `c_t m ≤ T`, discharged only in the assembly.
* **L35.**  A projection `Q` of the core of the graph of `code D` has `2^q |Q| ≤ |D|` and
  `C(Q) ≤ C(D) + |p_A| + |p_B| + c_q m`: an ordinary program for `D` is the unframed last
  component of the packet, so no delimiter of its length is paid.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### L33: a large projection -/

/-- **Two small projections have a small union**: if `a, b < 2^ℓ`, `ℓ ≥ 1` and `M = 8 ℓ`, then
`a + b ≤ 2^(M/4)` (real power).

Proof sketch: `a + b ≤ 2^(ℓ+1) - 2 < 2^(2ℓ)` since `ℓ + 1 ≤ 2ℓ`; and
`(2 : ℝ) ^ ((M : ℝ) / 4) = 2 ^ (2 ℓ)` by `M = 8 ℓ` and `Real.rpow_natCast`.
Reference: tex 1740-1744 (`|U| < 2^(ℓ+1) ≤ 2^(h(1/16) M)`), blueprint L33. -/
theorem add_le_rpow_quarter {a b ℓ M : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ) (hℓ : 1 ≤ ℓ)
    (hM : M = 8 * ℓ) : ((a + b : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) / 4) := by
  have h1 : a + b ≤ 2 ^ (2 * ℓ) := by
    have : 2 ^ (ℓ + 1) ≤ 2 ^ (2 * ℓ) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    omega
  have h2 : (M : ℝ) / 4 = ((2 * ℓ : ℕ) : ℝ) := by
    rw [hM]
    push_cast
    ring
  rw [h2, Real.rpow_natCast]
  exact_mod_cast h1

/-- **Node L33, `coreHasLargeProjection`.**  Let every edge of `E` be an ordered pair of `M`-words
at distance `2r`, with `1 ≤ r`, `4r ≤ M` and `M = 8 (M / 8) ≥ 8`.  If the core of `E` at
threshold `θ` is nonempty and `2 (M + 1) (M choose 2r) 2^(-3r/2) < θ`, then one of the two
projections of the core has at least `2^(M/8)` points. -/
theorem coreHasLargeProjection {M r θ : ℕ} {E : Finset (BitString × BitString)}
    (hE : ∀ e ∈ E, e.1.length = M ∧ e.2.length = M ∧ hammingDist e.1 e.2 = 2 * r)
    (hr : 1 ≤ r) (hrM : 4 * r ≤ M) (h8 : M = 8 * (M / 8)) (hM8 : 8 ≤ M)
    (hne : (peelCore θ E).Nonempty)
    (hgap : 2 * ((M : ℝ) + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) < θ) :
    2 ^ (M / 8) ≤ ((peelCore θ E).image Prod.fst).card ∨
      2 ^ (M / 8) ≤ ((peelCore θ E).image Prod.snd).card := by
  by_contra hsmall
  simp only [not_or, not_le] at hsmall
  obtain ⟨hL, hR⟩ := hsmall
  set F := peelCore θ E with hFdef
  set U := F.image Prod.fst ∪ F.image Prod.snd with hUdef
  have hFE : ∀ e ∈ F, e.1.length = M ∧ e.2.length = M ∧ hammingDist e.1 e.2 = 2 * r :=
    fun e he => hE e (peelCore_subset θ E he)
  have hUM : U ⊆ stringsOfLength M := by
    intro y hy
    rw [mem_stringsOfLength]
    rcases mem_union.1 hy with h | h
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      exact (hFE e he).1
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      exact (hFE e he).2.1
  obtain ⟨e₀, he₀⟩ := hne
  have hUne : U.Nonempty := ⟨e₀.1, mem_union_left _ (mem_image_of_mem _ he₀)⟩
  have hFsub : F ⊆ distancePairs U (2 * r) := by
    intro e he
    unfold distancePairs
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_union_left _ (mem_image_of_mem _ he),
      mem_union_right _ (mem_image_of_mem _ he)⟩, (hFE e he).2.2⟩
  have hdegL : θ * (F.image Prod.fst).card ≤ F.card :=
    mul_card_image_fst_le fun e he => (le_deg_of_mem_peelCore he).1
  have hdegR : θ * (F.image Prod.snd).card ≤ F.card :=
    mul_card_image_snd_le fun e he => (le_deg_of_mem_peelCore he).2
  have hUle : U.card ≤ (F.image Prod.fst).card + (F.image Prod.snd).card := card_union_le _ _
  have hℓ : 1 ≤ M / 8 := by omega
  have hUreal : (U.card : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) / 4) := by
    have h := add_le_rpow_quarter hL hR hℓ h8
    have hc : (U.card : ℝ) ≤ (((F.image Prod.fst).card + (F.image Prod.snd).card : ℕ) : ℝ) := by
      exact_mod_cast hUle
    linarith
  have hdist := (distanceCountFromSSE M U hUM hUne).2 r hr hrM hUreal
  have hFcard : (F.card : ℝ) ≤ (distancePairs U (2 * r)).card := by
    exact_mod_cast card_le_card hFsub
  have hθU : (θ : ℝ) * U.card ≤ 2 * F.card := by
    have h : θ * U.card ≤ 2 * F.card := by
      calc θ * U.card ≤ θ * ((F.image Prod.fst).card + (F.image Prod.snd).card) :=
            Nat.mul_le_mul_left _ hUle
        _ = θ * (F.image Prod.fst).card + θ * (F.image Prod.snd).card := by ring
        _ ≤ 2 * F.card := by omega
    exact_mod_cast h
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hUne.card_pos
  set X : ℝ := ((M : ℝ) + 1) * M.choose (2 * r) * (2 : ℝ) ^ (-(3 * (r : ℝ) / 2)) with hX
  have hdist' : (F.card : ℝ) ≤ U.card * X := by
    rw [hX]
    nlinarith [hdist, hFcard]
  have hgap' : 2 * X < θ := by
    rw [hX]
    linarith [hgap]
  nlinarith [mul_lt_mul_of_pos_left hgap' hUpos]

/-! ### L34: the exact partition of the projected cores -/

/-- The label read by a vertex `y` from its own star: `fA (code A_y)` on the left side
(`side = false`) and `fB (code B_y)` on the right side (`side = true`). -/
noncomputable def sideLabel (fA fB : BitString → BitString) (j : ℕ) (side : Bool)
    (y : BitString) : BitString :=
  if side then fB (canonicalFiniteSetCode (colStar j y))
  else fA (canonicalFiniteSetCode (rowStar j y))

/-- The projection on the side `side` of the core of the graph of the label `z`: its left
vertices for `side = false`, its right vertices for `side = true`. -/
noncomputable def coreProj (fA fB : BitString → BitString) (M j θ : ℕ) (side : Bool)
    (z : BitString) : Finset BitString :=
  if side then (peelCore θ (labelGraph fA fB M j z)).image Prod.snd
  else (peelCore θ (labelGraph fA fB M j z)).image Prod.fst

/-- **The projected-core cell map** (node L34): on an `M`-word `y`, the projection of the core of
the graph of `y`'s own label on `y`'s side if it contains `y`; otherwise, and on words of other
lengths, the singleton `{y}`. -/
noncomputable def projCell (fA fB : BitString → BitString) (M j θ : ℕ) (side : Bool)
    (y : BitString) : Finset BitString :=
  if y.length = M ∧ y ∈ coreProj fA fB M j θ side (sideLabel fA fB j side y) then
    coreProj fA fB M j θ side (sideLabel fA fB j side y)
  else {y}

/-- Every member of a projected core is an `M`-word reading the label of that core. -/
theorem coreProj_label {fA fB : BitString → BitString} {M j θ : ℕ} {side : Bool}
    {z y : BitString} (hy : y ∈ coreProj fA fB M j θ side z) :
    y.length = M ∧ sideLabel fA fB j side y = z := by
  cases side
  · simp only [coreProj, Bool.false_eq_true, ↓reduceIte, mem_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    obtain ⟨h1, -, -, -, h5, -⟩ := mem_labelGraph.1 (peelCore_subset _ _ he)
    exact ⟨h1, by simp [sideLabel, h5]⟩
  · simp only [coreProj, ↓reduceIte, mem_image] at hy
    obtain ⟨e, he, rfl⟩ := hy
    obtain ⟨-, h2, -, -, -, h6⟩ := mem_labelGraph.1 (peelCore_subset _ _ he)
    exact ⟨h2, by simp [sideLabel, h6]⟩

/-- **The cell map is an exact partition of the cube** (node L34): on an `M`-word `y` its cell
contains `y`, consists of `M`-words, and every member of the cell has the same cell.  Distinct
labels give disjoint projections because every member of a projection reads its label, and a
singleton default `{y}` never meets another cell (a member `y` of a projection would read that
projection's label and so lie in its own projection). -/
theorem projCell_spec (fA fB : BitString → BitString) (M j θ : ℕ) (side : Bool)
    {y : BitString} (hy : y.length = M) :
    y ∈ projCell fA fB M j θ side y ∧ ∀ y' ∈ projCell fA fB M j θ side y,
      y'.length = M ∧ projCell fA fB M j θ side y' = projCell fA fB M j θ side y := by
  by_cases hin : y ∈ coreProj fA fB M j θ side (sideLabel fA fB j side y)
  · have hcell : projCell fA fB M j θ side y =
        coreProj fA fB M j θ side (sideLabel fA fB j side y) := by
      rw [projCell, ite_eq_left (show y.length = M ∧ _ from ⟨hy, hin⟩)]
    refine ⟨hcell ▸ hin, fun y' hy' => ?_⟩
    rw [hcell] at hy'
    obtain ⟨hlen, hlab⟩ := coreProj_label hy'
    have hin' : y' ∈ coreProj fA fB M j θ side (sideLabel fA fB j side y') := by
      rw [hlab]
      exact hy'
    refine ⟨hlen, ?_⟩
    rw [hcell, projCell, ite_eq_left (show y'.length = M ∧ _ from ⟨hlen, hin'⟩), hlab]
  · have hcell : projCell fA fB M j θ side y = {y} := by
      rw [projCell, ite_eq_right (fun h : y.length = M ∧ _ => hin h.2)]
    refine ⟨hcell ▸ mem_singleton_self y, fun y' hy' => ?_⟩
    rw [hcell, mem_singleton] at hy'
    subst hy'
    exact ⟨hy, rfl⟩

/-- The packet of the partition decoder: the numeric fields `M, j, q` and the side flag in front
of the length-framed pair of witness bodies. -/
def projPacket (pA pB : BitString) (M j q : ℕ) (side : Bool) : BitString :=
  numPacket [M, j, q, side.toNat] (totalProgramPairCode pA pB)

/-- **The partition decoder is partial recursive** (node L34).  One fixed partial recursive map
`D`, reading `projPacket` and taking the queried word as condition, prints the code of
`projCell` at threshold `2^q` on every word, for every packet whose witness bodies are total
programs of `universalDecompressor`.  In particular `D` halts on every condition for such
packets.

Proof: `D` is the search decoder of `DecoderLists` (`searchDecoder`) reading four numeric
fields: the witness of the queried word's side, run on the code of its star (`labelQuery`), gives
its label `z`; the graph search (`exists_graphSearch`) returns the list graph of `z` built from
the actual witness outputs; `projPost` peels it on lists and codes the cell
(`projCodeList_eq`, `labelGraphList_toFinset`, `labelGraphList_nodup`).
Reference: tex 1759-1772, blueprint L34 (lines 4979-5012). -/
theorem exists_projDecoder :
    ∃ D : Map, isDecompressor D ∧ ∀ (pA pB : BitString) (M j q : ℕ) (side : Bool),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      ∀ y : BitString, canonicalFiniteSetCode
        (projCell (progOut pA) (progOut pB) M j (2 ^ q) side y) ∈
          D (projPacket pA pB M j q side, y) := by
  obtain ⟨S, hS, hSval⟩ := exists_graphSearch
  refine ⟨searchDecoder universalDecompressor S (labelQuery 4) (graphQuery 4) projPost,
    partrec_searchDecoder isDecompressor_universalDecompressor hS (computable_labelQuery 4)
      (computable_graphQuery 4) computable_projPost, ?_⟩
  intro pA pB M j q side hA hB y
  have h0 : fieldAt 0 (projPacket pA pB M j q side) = M :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 0 (by simp)
  have h1 : fieldAt 1 (projPacket pA pB M j q side) = j :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 1 (by simp)
  have h2 : fieldAt 2 (projPacket pA pB M j q side) = q :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 2 (by simp)
  have h3 : fieldAt 3 (projPacket pA pB M j q side) = side.toNat :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 3 (by simp)
  have hbody : popField^[4] (projPacket pA pB M j q side) = totalProgramPairCode pA pB :=
    popField_iterate_numPacket [M, j, q, side.toNat] _
  have hlq : labelQuery 4 (projPacket pA pB M j q side, y) =
      (if side then pB else pA, sideStarCode j side y) := by
    simp only [labelQuery, h1, h3, sideOf_toNat, hbody, decodeTotalProgramPairFirst_pair,
      decodeTotalProgramPairSecond_pair]
  have hzl : progOut (if side then pB else pA) (sideStarCode j side y) =
      sideLabel (progOut pA) (progOut pB) j side y := by
    unfold sideLabel sideStarCode
    cases side <;> rfl
  have hz : sideLabel (progOut pA) (progOut pB) j side y ∈
      universalDecompressor (labelQuery 4 (projPacket pA pB M j q side, y)) := by
    rw [hlq, ← hzl]
    exact progOut_mem (by cases side <;> assumption) _
  have hgq : graphQuery 4 (projPacket pA pB M j q side, y)
      (sideLabel (progOut pA) (progOut pB) j side y) =
      (pA, pB, M, j, sideLabel (progOut pA) (progOut pB) j side y) := by
    simp only [graphQuery, hbody, h0, h1, decodeTotalProgramPairFirst_pair,
      decodeTotalProgramPairSecond_pair]
  have hL := hSval pA pB M j (sideLabel (progOut pA) (progOut pB) j side y)
    (progOut pA) (progOut pB) (progOut_mem hA) (progOut_mem hB)
  rw [← hgq] at hL
  have hmem := mem_searchDecoder (post := projPost) hz hL
  have hval : projPost (projPacket pA pB M j q side, y) (labelGraphList (progOut pA)
      (progOut pB) M j (sideLabel (progOut pA) (progOut pB) j side y)) =
      canonicalFiniteSetCode (projCell (progOut pA) (progOut pB) M j (2 ^ q) side y) := by
    simp only [projPost, h0, h2, h3, sideOf_toNat]
    rw [projCodeList_eq (labelGraphList_nodup _ _ _ _ _), labelGraphList_toFinset]
    rfl
  rw [← hval]
  exact hmem

/-- **Length of the partition packet**: with bodies and numeric fields at most `M`, the packet
costs `|p_A| + |p_B| + c ⌈log₂ (M + 2)⌉`.

Proof sketch: `length_numPacket_le 1 4` bounds the four fields (`side.toNat ≤ 1 ≤ M + 1`) by
`c₀ headerLog M`; `length_totalProgramPairCode` adds `2 |bits |p_A|| + 1`, and
`|bits |p_A|| = size |p_A| ≤ size M ≤ headerLog M`; `1 ≤ headerLog M`.
Reference: tex 1770-1772 ("its length is at most `2T + O(m)`"), blueprint L34. -/
theorem length_projPacket_le :
    ∃ c : ℕ, ∀ (pA pB : BitString) (M j q : ℕ) (side : Bool),
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M →
        (projPacket pA pB M j q side).length ≤ pA.length + pB.length + c * headerLog M := by
  obtain ⟨c, hc⟩ := length_numPacket_le 1 4
  refine ⟨c + 3, fun pA pB M j q side hA hB hj hq => ?_⟩
  have hks : ∀ k ∈ [M, j, q, side.toNat], k ≤ 1 * (M + 1) := by
    intro k hk
    have hs : side.toNat ≤ 1 := by cases side <;> decide
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  have h1 := hc M [M, j, q, side.toNat] (totalProgramPairCode pA pB) (by simp) hks
  have h2 := length_totalProgramPairCode pA pB
  have h3 := natBits_length_le_headerLog hA
  have h4 := one_le_headerLog M
  have h5 : (c + 3) * headerLog M = c * headerLog M + 3 * headerLog M := Nat.add_mul _ _ _
  unfold projPacket
  omega

/-- **Node L34, `labelProjectionPartition`.**  There is a uniform constant `c_t` such that for
total witness bodies `p_A, p_B` of length at most `M`, numeric fields `j, q ≤ M` and either
side, one compiled program `p` of length at most `|p_A| + |p_B| + c_t m` is a total program of
`universalDecompressor`, an exact partition program of the `M`-cube, and prints the code of
`projCell` at threshold `2^q` on every word.  The compiler constant is fixed before the witness
bodies and the numeric fields. -/
theorem labelProjectionPartition :
    ∃ ct : ℕ, ∀ (M j q : ℕ) (side : Bool) (pA pB : BitString),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M →
      ∃ p : BitString, p.length ≤ pA.length + pB.length + ct * headerLog M ∧
        IsTotalProgram universalDecompressor p ∧ IsCubePartitionProgram M p ∧
        ∀ y : BitString, produces universalDecompressor p y
          (canonicalFiniteSetCode (projCell (progOut pA) (progOut pB) M j (2 ^ q) side y)) := by
  obtain ⟨D, hD, hDval⟩ := exists_projDecoder
  obtain ⟨pre, hpre⟩ := exists_compiled_totalProgram D hD
  obtain ⟨cL, hcL⟩ := length_projPacket_le
  refine ⟨pre.length + cL, fun M j q side pA pB hA hB hAM hBM hjM hqM => ?_⟩
  set w := projPacket pA pB M j q side
  have hval := hDval pA pB M j q side hA hB
  have hdom : ∀ y : BitString, (D (w, y)).Dom := fun y => Part.dom_iff_mem.2 ⟨_, hval y⟩
  obtain ⟨htot, hlen, hprod⟩ := hpre w hdom
  have hprod' : ∀ y : BitString, produces universalDecompressor (pre ++ w) y
      (canonicalFiniteSetCode (projCell (progOut pA) (progOut pB) M j (2 ^ q) side y)) :=
    fun y => hprod y _ (hval y)
  refine ⟨pre ++ w, ?_, htot, fun y hy => ?_, hprod'⟩
  · have h1 := hcL pA pB M j q side hAM hBM hjM hqM
    have h2 := one_le_headerLog M
    rw [hlen]
    nlinarith
  · obtain ⟨hmem, hcell⟩ := projCell_spec (progOut pA) (progOut pB) M j (2 ^ q) side hy
    refine ⟨_, hprod' y, hmem, fun y' hy' => ⟨(hcell y' hy').1, ?_⟩⟩
    have h := hprod' y'
    rwa [(hcell y' hy').2] at h

/-! ### L35: the score of a projection -/

/-- The packet of the projection-description decoder: the numeric fields `M, j, q`, the side
flag, the length-framed first witness body, then the second body, then (unframed, last) an
ordinary program `p_D` for the model `D`. -/
def qPacket (pA pB pD : BitString) (M j q : ℕ) (side : Bool) : BitString :=
  numPacket [M, j, q, side.toNat] (totalProgramPairCode pA (totalProgramPairCode pB pD))

/-- **The projection-description decoder is partial recursive** (node L35).  For a partial
recursive plain machine `V` there is one fixed partial recursive `D` which, on the packet
`qPacket p_A p_B p_D M j q side` (empty condition), runs `V` on `p_D` to obtain a label `z` and
prints the code of the projection on `side` of the core at threshold `2^q` of the graph of `z`,
whenever the witness bodies are total programs of `universalDecompressor` and `V` prints `z`
from `p_D`.

Proof: `D` is the search decoder of `DecoderLists` (`searchDecoder`) with label query `V (p_D, [])`
(`coreLabelQuery`, `p_D` is the unframed tail of the packet), the graph search
(`exists_graphSearch`) and the post-processing `corePost`, which peels the list graph and codes
the projection of its core (`coreCodeList_eq`, `labelGraphList_toFinset`,
`labelGraphList_nodup`).
Reference: tex 1798-1806 ("a program for `D`, both witnesses, and numerical fields"),
blueprint L35. -/
theorem exists_coreDecoder (V : Map) (hV : isDecompressor V) :
    ∃ D : Map, isDecompressor D ∧ ∀ (pA pB pD : BitString) (M j q : ℕ) (side : Bool)
      (z : BitString), IsTotalProgram universalDecompressor pA →
        IsTotalProgram universalDecompressor pB → produces V pD [] z →
        canonicalFiniteSetCode (coreProj (progOut pA) (progOut pB) M j (2 ^ q) side z) ∈
          D (qPacket pA pB pD M j q side, []) := by
  obtain ⟨S, hS, hSval⟩ := exists_graphSearch
  refine ⟨searchDecoder V S coreLabelQuery coreGraphQuery corePost,
    partrec_searchDecoder hV hS computable_coreLabelQuery computable_coreGraphQuery
      computable_corePost, ?_⟩
  intro pA pB pD M j q side z hA hB hz
  have h0 : fieldAt 0 (qPacket pA pB pD M j q side) = M :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 0 (by simp)
  have h1 : fieldAt 1 (qPacket pA pB pD M j q side) = j :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 1 (by simp)
  have h2 : fieldAt 2 (qPacket pA pB pD M j q side) = q :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 2 (by simp)
  have h3 : fieldAt 3 (qPacket pA pB pD M j q side) = side.toNat :=
    fieldAt_numPacket [M, j, q, side.toNat] _ 3 (by simp)
  have hbody : popField^[4] (qPacket pA pB pD M j q side) =
      totalProgramPairCode pA (totalProgramPairCode pB pD) :=
    popField_iterate_numPacket [M, j, q, side.toNat] _
  have hlq : coreLabelQuery (qPacket pA pB pD M j q side, []) = (pD, []) := by
    simp only [coreLabelQuery, hbody, decodeTotalProgramPairSecond_pair]
  have hz' : z ∈ V (coreLabelQuery (qPacket pA pB pD M j q side, [])) := by
    rw [hlq]
    exact hz
  have hgq : coreGraphQuery (qPacket pA pB pD M j q side, []) z = (pA, pB, M, j, z) := by
    simp only [coreGraphQuery, hbody, h0, h1, decodeTotalProgramPairFirst_pair,
      decodeTotalProgramPairSecond_pair]
  have hL := hSval pA pB M j z (progOut pA) (progOut pB) (progOut_mem hA) (progOut_mem hB)
  rw [← hgq] at hL
  have hmem := mem_searchDecoder (post := corePost) hz' hL
  have hval : corePost (qPacket pA pB pD M j q side, [])
      (labelGraphList (progOut pA) (progOut pB) M j z) =
      canonicalFiniteSetCode (coreProj (progOut pA) (progOut pB) M j (2 ^ q) side z) := by
    simp only [corePost, h2, h3, sideOf_toNat]
    rw [coreCodeList_eq (labelGraphList_nodup _ _ _ _ _), labelGraphList_toFinset]
    rfl
  rw [← hval]
  exact hmem

/-- **Length of the projection-description packet**: with bodies and numeric fields at most `M`,
the packet costs `|p_A| + |p_B| + |p_D| + c ⌈log₂ (M + 2)⌉`, for an arbitrary (unframed) `p_D`.

Proof sketch: as `length_projPacket_le`, with two applications of `length_totalProgramPairCode`
(framing `|p_A|` and `|p_B|`, both at most `M`); `p_D` is the unframed tail.
Reference: tex 1803-1806 ("Its delimiters cost `O(m)`"), blueprint L35. -/
theorem length_qPacket_le :
    ∃ c : ℕ, ∀ (pA pB pD : BitString) (M j q : ℕ) (side : Bool),
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M →
        (qPacket pA pB pD M j q side).length ≤
          pA.length + pB.length + pD.length + c * headerLog M := by
  obtain ⟨c, hc⟩ := length_numPacket_le 1 4
  refine ⟨c + 6, fun pA pB pD M j q side hA hB hj hq => ?_⟩
  have hks : ∀ k ∈ [M, j, q, side.toNat], k ≤ 1 * (M + 1) := by
    intro k hk
    have hs : side.toNat ≤ 1 := by cases side <;> decide
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  have h1 := hc M [M, j, q, side.toNat]
    (totalProgramPairCode pA (totalProgramPairCode pB pD)) (by simp) hks
  have h2 := length_totalProgramPairCode pA (totalProgramPairCode pB pD)
  have h2' := length_totalProgramPairCode pB pD
  have h3 := natBits_length_le_headerLog hA
  have h3' := natBits_length_le_headerLog hB
  have h4 := one_le_headerLog M
  have h5 : (c + 6) * headerLog M = c * headerLog M + 6 * headerLog M := Nat.add_mul _ _ _
  unfold qPacket
  omega

/-- **Projections are thin in the model**: a projection `Q` of the core at threshold `θ` of the
graph of the code of `D` has `θ |Q| ≤ |D|`, since every vertex of `Q` has at least `θ` core
edges, the core lies in the graph, and the graph injects into `D`. -/
theorem mul_card_coreProj_le (fA fB : BitString → BitString) (M j θ : ℕ) (side : Bool)
    (D : Finset BitString) :
    θ * (coreProj fA fB M j θ side (canonicalFiniteSetCode D)).card ≤ D.card := by
  have hcore : (peelCore θ (labelGraph fA fB M j (canonicalFiniteSetCode D))).card ≤ D.card :=
    (card_le_card (peelCore_subset _ _)).trans (card_labelGraph_le fA fB M j D)
  cases side
  · simp only [coreProj, Bool.false_eq_true, ↓reduceIte]
    exact (mul_card_image_fst_le fun e he => (le_deg_of_mem_peelCore he).1).trans hcore
  · simp only [coreProj, ↓reduceIte]
    exact (mul_card_image_snd_le fun e he => (le_deg_of_mem_peelCore he).2).trans hcore

/-- **Node L35, `projectionScoreCode`.**  For an optimal plain machine `V` there is a constant
`c_q` such that for total witness bodies of length at most `M`, `j, q ≤ M`, either side and every
finite model `D`, the projection `Q` of the core at threshold `2^q` of the graph of `code D` has
`2^q |Q| ≤ |D|` and `C(Q) ≤ C(D) + |p_A| + |p_B| + c_q m`. -/
theorem projectionScoreCode (V : Map) (hV : isOptimalConditional V) :
    ∃ cq : ℕ, ∀ (M j q : ℕ) (side : Bool) (pA pB : BitString) (D : Finset BitString),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M →
      2 ^ q * (coreProj (progOut pA) (progOut pB) M j (2 ^ q) side
          (canonicalFiniteSetCode D)).card ≤ D.card ∧
        setC V (coreProj (progOut pA) (progOut pB) M j (2 ^ q) side (canonicalFiniteSetCode D)) ≤
          setC V D + pA.length + pB.length + cq * headerLog M := by
  obtain ⟨Dq, hDq, hDqval⟩ := exists_coreDecoder V hV.1
  obtain ⟨cD, hcD⟩ := condC_le_of_decoder V hV Dq hDq
  obtain ⟨cL, hcL⟩ := length_qPacket_le
  refine ⟨cL + cD, fun M j q side pA pB D hA hB hAM hBM hjM hqM =>
    ⟨mul_card_coreProj_le _ _ M j (2 ^ q) side D, ?_⟩⟩
  obtain ⟨pD, hpD, hlenD⟩ := Lower.exists_program_of_condC V hV (canonicalFiniteSetCode D) []
  have hmem := hDqval pA pB pD M j q side _ hA hB hpD
  have h1 := hcD _ [] _ hmem
  have h2 := hcL pA pB pD M j q side hAM hBM hjM hqM
  have h3 : ((qPacket pA pB pD M j q side).length : ℝ) ≤
      pA.length + pB.length + pD.length + cL * headerLog M := by exact_mod_cast h2
  have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  have hsetD : setC V D = condC V (canonicalFiniteSetCode D) [] := rfl
  have hsetQ : setC V (coreProj (progOut pA) (progOut pB) M j (2 ^ q) side
      (canonicalFiniteSetCode D)) = condC V (canonicalFiniteSetCode (coreProj (progOut pA)
        (progOut pB) M j (2 ^ q) side (canonicalFiniteSetCode D))) [] := rfl
  rw [hsetQ, hsetD, ← hlenD]
  push_cast
  nlinarith [(Nat.cast_nonneg cD : (0 : ℝ) ≤ cD)]

end Kolmogorov.StrongMerging.Lower
