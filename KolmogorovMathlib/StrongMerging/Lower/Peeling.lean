import KolmogorovMathlib.StrongMerging.Lower.DecoderLists

/-!
# The sharp lower bound: the assigned-edge decoder and survival of the actual edge

Blueprint nodes L31 (`assignedEdgeDecoder`) and L32 (`actualEdgeSurvives`) of the
formalization of `sublinear-merging.tex` (main text "Peeling a hypothetical common model", tex
lines 1698-1716; appendix paragraph "L31--L32", lines 4921-4940).

* `progOut p c` is the output of a program `p` on the condition `c` under the canonical total
  interpreter `universalDecompressor` (S01); for total witness programs it is their actual
  output (`progOut_mem`).
* **L31.**  One fixed partial recursive decoder (`exists_peelDecoder`) reads a packet consisting
  of the numeric fields `M, j, q`, a side flag and a rank, followed by the length-framed pair of
  the two witness bodies (`peelPacket`, built with `totalProgramPairCode`, which does not double
  the first body).  On the owning endpoint it recomputes the label from the endpoint's own star,
  rebuilds and peels the labelled graph, and prints the ranked opposite endpoint among the edges
  assigned to the owner.  No description of the model `D` is supplied.  Hence
  `C(v | u) ≤ |p_A| + |p_B| + q + c_p m` (and symmetrically), `m = ⌈log₂ (M + 2)⌉`.
* **L32.**  If both conditional complexities of the actual edge are at least a threshold `κ`
  and the decoder budget is below `κ`, the actual edge survives the peeling.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### Outputs of total witness programs -/

/-- The output of the program `p` on the condition `c` under the canonical total interpreter
`universalDecompressor`, and the empty word if that computation does not halt (never the case
for a total program). -/
noncomputable def progOut (p c : BitString) : BitString := by
  classical
  exact if h : (universalDecompressor (p, c)).Dom then (universalDecompressor (p, c)).get h
    else []

/-- A total program produces `progOut` on every condition. -/
theorem progOut_mem {p : BitString} (hp : IsTotalProgram universalDecompressor p)
    (c : BitString) : progOut p c ∈ universalDecompressor (p, c) := by
  unfold progOut
  rw [dite_eq_left (hp c)]
  exact Part.get_mem _

/-- For a total program, `progOut` is its output. -/
theorem progOut_eq_of_produces {p c u : BitString} (hp : IsTotalProgram universalDecompressor p)
    (h : produces universalDecompressor p c u) : progOut p c = u :=
  Part.mem_unique (progOut_mem hp c) h

/-! ### L31: the assigned-edge decoder -/

/-- The packet of the peeling decoder: the numeric fields `M, j, q`, the side flag
(`0` = left/`A` side, `1` = right/`B` side) and the rank, in front of the length-framed pair of
witness bodies. -/
def peelPacket (pA pB : BitString) (M j q : ℕ) (side : Bool) (rank : ℕ) : BitString :=
  numPacket [M, j, q, side.toNat, rank] (totalProgramPairCode pA pB)

/-- The value printed by the peeling decoder on the owner `y` (node L31).  On the left side: the
label `z = p_A(A_y)` read from the owner's own row star, the graph `G_z`, the edges assigned to
`y` by the peeling at threshold `2^q`, and the entry of rank `rank` in the canonical list of
their right endpoints.  The right side is symmetric.  Out-of-range ranks print `[]`. -/
noncomputable def peelDecodeValue (pA pB : BitString) (M j q : ℕ) (side : Bool) (rank : ℕ)
    (y : BitString) : BitString :=
  if side then
    (canonicalFinsetList ((ownedR (2 ^ q) (labelGraph (progOut pA) (progOut pB) M j
      (progOut pB (canonicalFiniteSetCode (colStar j y)))) y).image Prod.fst)).getD rank []
  else
    (canonicalFinsetList ((ownedL (2 ^ q) (labelGraph (progOut pA) (progOut pB) M j
      (progOut pA (canonicalFiniteSetCode (rowStar j y)))) y).image Prod.snd)).getD rank []

/-- **Stage search** (shared tool for the decoders of L31, L34, L35).  For a computable stage
attempt `att a s`, the map `a ↦ Nat.rfindOpt (att a)` is partial recursive, and it returns `v`
whenever some stage succeeds with `v` and no stage succeeds with another value. -/
theorem stageSearch {α σ : Type*} [Primcodable α] [Primcodable σ] (att : α → ℕ → Option σ)
    (hatt : Computable₂ att) :
    Partrec (fun a => Nat.rfindOpt (att a)) ∧
      ∀ (a : α) (v : σ), (∃ s, att a s = some v) → (∀ s w, att a s = some w → w = v) →
        v ∈ Nat.rfindOpt (att a) := by
  refine ⟨Partrec.rfindOpt hatt, fun a v hex huniq => ?_⟩
  obtain ⟨s, hs⟩ := hex
  have hdom : (Nat.rfindOpt (att a)).Dom := Nat.rfindOpt_dom.2 ⟨s, v, hs⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
  have hw := huniq n _ hn
  rw [← hw]
  exact Part.get_mem hdom

/-- **The peeling decoder is partial recursive** (node L31).  One fixed partial recursive map
`D` prints `peelDecodeValue` on every peeling packet whose two witness bodies are total programs
of `universalDecompressor`, with the owner as condition.

Proof: `D` is the search decoder of `DecoderLists` (`searchDecoder`) reading five numeric fields:
it runs the witness of the owner's side on the code of the owner's star (`labelQuery`), which
gives the label `z`; the graph search (`exists_graphSearch`) returns the list graph of `z`
built from the actual witness outputs; the post-processing `peelPost` peels it on lists and
reads the ranked entry.  The list computations agree with the `Finset` definitions
(`labelGraphList_toFinset`, `labelGraphList_nodup`, `peelValueList_eq`).
Reference: tex 1698-1713, blueprint L31 (lines 4921-4935). -/
theorem exists_peelDecoder :
    ∃ D : Map, isDecompressor D ∧ ∀ (pA pB : BitString) (M j q : ℕ) (side : Bool) (rank : ℕ)
      (y : BitString), IsTotalProgram universalDecompressor pA →
        IsTotalProgram universalDecompressor pB →
        peelDecodeValue pA pB M j q side rank y ∈ D (peelPacket pA pB M j q side rank, y) := by
  obtain ⟨S, hS, hSval⟩ := exists_graphSearch
  refine ⟨searchDecoder universalDecompressor S (labelQuery 5) (graphQuery 5) peelPost,
    partrec_searchDecoder isDecompressor_universalDecompressor hS (computable_labelQuery 5)
      (computable_graphQuery 5) computable_peelPost, ?_⟩
  intro pA pB M j q side rank y hA hB
  have h0 : fieldAt 0 (peelPacket pA pB M j q side rank) = M :=
    fieldAt_numPacket [M, j, q, side.toNat, rank] _ 0 (by simp)
  have h1 : fieldAt 1 (peelPacket pA pB M j q side rank) = j :=
    fieldAt_numPacket [M, j, q, side.toNat, rank] _ 1 (by simp)
  have h2 : fieldAt 2 (peelPacket pA pB M j q side rank) = q :=
    fieldAt_numPacket [M, j, q, side.toNat, rank] _ 2 (by simp)
  have h3 : fieldAt 3 (peelPacket pA pB M j q side rank) = side.toNat :=
    fieldAt_numPacket [M, j, q, side.toNat, rank] _ 3 (by simp)
  have h4 : fieldAt 4 (peelPacket pA pB M j q side rank) = rank :=
    fieldAt_numPacket [M, j, q, side.toNat, rank] _ 4 (by simp)
  have hbody : popField^[5] (peelPacket pA pB M j q side rank) = totalProgramPairCode pA pB :=
    popField_iterate_numPacket [M, j, q, side.toNat, rank] _
  have hlq : labelQuery 5 (peelPacket pA pB M j q side rank, y) =
      (if side then pB else pA, sideStarCode j side y) := by
    simp only [labelQuery, h1, h3, sideOf_toNat, hbody, decodeTotalProgramPairFirst_pair,
      decodeTotalProgramPairSecond_pair]
  have hz : progOut (if side then pB else pA) (sideStarCode j side y) ∈
      universalDecompressor (labelQuery 5 (peelPacket pA pB M j q side rank, y)) := by
    rw [hlq]
    exact progOut_mem (by cases side <;> assumption) _
  have hgq : graphQuery 5 (peelPacket pA pB M j q side rank, y)
      (progOut (if side then pB else pA) (sideStarCode j side y)) =
      (pA, pB, M, j, progOut (if side then pB else pA) (sideStarCode j side y)) := by
    simp only [graphQuery, hbody, h0, h1, decodeTotalProgramPairFirst_pair,
      decodeTotalProgramPairSecond_pair]
  have hL := hSval pA pB M j (progOut (if side then pB else pA) (sideStarCode j side y))
    (progOut pA) (progOut pB) (progOut_mem hA) (progOut_mem hB)
  rw [← hgq] at hL
  have hmem := mem_searchDecoder (post := peelPost) hz hL
  have hval : peelPost (peelPacket pA pB M j q side rank, y) (labelGraphList (progOut pA)
      (progOut pB) M j (progOut (if side then pB else pA) (sideStarCode j side y))) =
      peelDecodeValue pA pB M j q side rank y := by
    simp only [peelPost, h2, h3, h4, sideOf_toNat]
    rw [peelValueList_eq (labelGraphList_nodup _ _ _ _ _), labelGraphList_toFinset]
    unfold peelDecodeValue sideStarCode
    cases side <;> rfl
  rw [← hval]
  exact hmem

/-- **Length of the peeling packet**: with bodies and numeric fields at most `M` and a rank below
`2^q`, the packet costs `|p_A| + |p_B| + q + c ⌈log₂ (M + 2)⌉`.

Proof sketch: unfold `numPacket` (five `numField`s) and `length_totalProgramPairCode`; each field
`k ≤ M` costs `|bits k| + 2 |bits |bits k|| + 1 ≤ 3 headerLog M + 1` (`Nat.size_le`, as in
`length_numPacket_le`); the rank field costs `|bits rank| + 2 |bits |bits rank|| + 1` with
`|bits rank| ≤ q` (`rank < 2^q`) and `|bits |bits rank|| ≤ size q ≤ headerLog M`; the body
framing costs `2 |bits |p_A|| + 1 ≤ 2 headerLog M + 1`; and `1 ≤ headerLog M`
(`one_le_headerLog`).
Reference: tex 1706-1711 ("`2T + log θ + O(m)`"), blueprint L31. -/
theorem length_peelPacket_le :
    ∃ c : ℕ, ∀ (pA pB : BitString) (M j q : ℕ) (side : Bool) (rank : ℕ),
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M → rank < 2 ^ q →
        (peelPacket pA pB M j q side rank).length ≤
          pA.length + pB.length + q + c * headerLog M := by
  obtain ⟨c, hc⟩ := length_numPacket_le 1 4
  refine ⟨c + 6, fun pA pB M j q side rank hA hB hj hq hrank => ?_⟩
  have hks : ∀ k ∈ [M, j, q, side.toNat], k ≤ 1 * (M + 1) := by
    intro k hk
    have hs : side.toNat ≤ 1 := by cases side <;> decide
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  have hsplit : peelPacket pA pB M j q side rank =
      numPacket [M, j, q, side.toNat] (numField rank (totalProgramPairCode pA pB)) := rfl
  have h1 := hc M [M, j, q, side.toNat] (numField rank (totalProgramPairCode pA pB)) (by simp) hks
  have h2 : (numField rank (totalProgramPairCode pA pB)).length = (Nat.bits rank).length +
      (totalProgramPairCode pA pB).length + 2 * (Nat.bits (Nat.bits rank).length).length + 1 :=
    length_totalProgramPairCode _ _
  have h2' := length_totalProgramPairCode pA pB
  have h3 := natBits_length_le_headerLog hA
  have hr1 : (Nat.bits rank).length ≤ q := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact hrank
  have hr2 := natBits_length_le_headerLog (hr1.trans hq)
  have h4 := one_le_headerLog M
  have h5 : (c + 6) * headerLog M = c * headerLog M + 6 * headerLog M := Nat.add_mul _ _ _
  rw [hsplit]
  omega

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Ranks in a canonical list**: a member `x` of a finite set `S` has an index below `|S|` in
the canonical list of `S`, and the entry at that index is `x`.

Proof sketch: `List.findIdx_lt_length_of_exists` with `mem_canonicalFinsetList` and
`length_canonicalFinsetList`; the entry is `x` by `List.findIdx_getElem` (the predicate
`(· == x)` holds there) and `List.getD_eq_getElem?_getD`.
Reference: blueprint L31 ("its rank among edges assigned to its owning endpoint"). -/
theorem canonicalFinsetList_findIdx {S : Finset BitString} {x : BitString} (hx : x ∈ S) :
    (canonicalFinsetList S).findIdx (· == x) < S.card ∧
      (canonicalFinsetList S).getD ((canonicalFinsetList S).findIdx (· == x)) [] = x := by
  have hmem : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.2 hx
  have hlt : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length :=
    List.findIdx_lt_length.2 ⟨x, hmem, by simp⟩
  refine ⟨by rwa [length_canonicalFinsetList] at hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt]
  have := List.findIdx_getElem (w := hlt)
  simpa using this

/-- **Node L31, `assignedEdgeDecoder`.**  For an optimal plain machine `V` there is a constant
`c_p` such that for total witness bodies `p_A, p_B` of length at most `M`, `j, q ≤ M`, every
label `z` and every edge `(u, v)`: if `(u, v)` is assigned to its left endpoint `u` by the peeling
of `G_z` at threshold `2^q`, and `u` reads the label `z` from its own row star, then
`C(v | u) ≤ |p_A| + |p_B| + q + c_p m`; symmetrically on the right side. -/
theorem assignedEdgeDecoder (V : Map) (hV : isOptimalConditional V) :
    ∃ cp : ℕ, ∀ (M j q : ℕ) (pA pB : BitString), IsTotalProgram universalDecompressor pA →
      IsTotalProgram universalDecompressor pB → pA.length ≤ M → pB.length ≤ M → j ≤ M →
      q ≤ M → ∀ z u v : BitString,
        ((u, v) ∈ ownedL (2 ^ q) (labelGraph (progOut pA) (progOut pB) M j z) u →
          progOut pA (canonicalFiniteSetCode (rowStar j u)) = z →
          condC V v u ≤ pA.length + pB.length + q + cp * headerLog M) ∧
        ((u, v) ∈ ownedR (2 ^ q) (labelGraph (progOut pA) (progOut pB) M j z) v →
          progOut pB (canonicalFiniteSetCode (colStar j v)) = z →
          condC V u v ≤ pA.length + pB.length + q + cp * headerLog M) := by
  obtain ⟨D, hD, hDval⟩ := exists_peelDecoder
  obtain ⟨cD, hcD⟩ := condC_le_of_decoder V hV D hD
  obtain ⟨cL, hcL⟩ := length_peelPacket_le
  refine ⟨cL + cD, fun M j q pA pB hA hB hAM hBM hjM hqM z u v => ⟨fun hown hz => ?_,
    fun hown hz => ?_⟩⟩
  · set G := labelGraph (progOut pA) (progOut pB) M j z
    set O := (ownedL (2 ^ q) G u).image Prod.snd
    have hvO : v ∈ O := mem_image.2 ⟨(u, v), hown, rfl⟩
    obtain ⟨hrank, hget⟩ := canonicalFinsetList_findIdx hvO
    set rank := (canonicalFinsetList O).findIdx (· == v)
    have hOcard : O.card < 2 ^ q :=
      lt_of_le_of_lt card_image_le (card_ownedL_lt (Nat.two_pow_pos q) G u)
    have hval : peelDecodeValue pA pB M j q false rank u = v := by
      unfold peelDecodeValue
      rw [hz]
      exact hget
    have hmem := hDval pA pB M j q false rank u hA hB
    rw [hval] at hmem
    have h1 := hcD _ u v hmem
    have h2 := hcL pA pB M j q false rank hAM hBM hjM hqM (hrank.trans hOcard)
    have h3 : ((peelPacket pA pB M j q false rank).length : ℝ) ≤
        pA.length + pB.length + q + cL * headerLog M := by exact_mod_cast h2
    have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
    push_cast
    nlinarith [(Nat.cast_nonneg cD : (0 : ℝ) ≤ cD)]
  · set G := labelGraph (progOut pA) (progOut pB) M j z
    set O := (ownedR (2 ^ q) G v).image Prod.fst
    have huO : u ∈ O := mem_image.2 ⟨(u, v), hown, rfl⟩
    obtain ⟨hrank, hget⟩ := canonicalFinsetList_findIdx huO
    set rank := (canonicalFinsetList O).findIdx (· == u)
    have hOcard : O.card < 2 ^ q :=
      lt_of_le_of_lt card_image_le (card_ownedR_lt (Nat.two_pow_pos q) G v)
    have hval : peelDecodeValue pA pB M j q true rank v = u := by
      unfold peelDecodeValue
      rw [hz]
      exact hget
    have hmem := hDval pA pB M j q true rank v hA hB
    rw [hval] at hmem
    have h1 := hcD _ v u hmem
    have h2 := hcL pA pB M j q true rank hAM hBM hjM hqM (hrank.trans hOcard)
    have h3 : ((peelPacket pA pB M j q true rank).length : ℝ) ≤
        pA.length + pB.length + q + cL * headerLog M := by exact_mod_cast h2
    have hm : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
    push_cast
    nlinarith [(Nat.cast_nonneg cD : (0 : ℝ) ≤ cD)]

/-! ### L32: the actual edge survives -/

/-- **Node L32, `actualEdgeSurvives`.**  For an optimal plain machine `V`, with the constant
`c_p` of L31: let `p_A, p_B` be total witness bodies of length at most `M` mapping the stars of
`u` and `v` to the code of a model `D`, let `(u, v)` be an edge of the graph of that label, and
suppose `C(v | u), C(u | v) ≥ κ` while `|p_A| + |p_B| + q + c_p m < κ`.  Then the actual edge
survives the peeling at threshold `2^q`: otherwise the decoder of L31, run from the endpoint
owning it, would describe the opposite endpoint too cheaply. -/
theorem actualEdgeSurvives (V : Map) (hV : isOptimalConditional V) :
    ∃ cp : ℕ, ∀ (M j q : ℕ) (pA pB u v : BitString) (D : Finset BitString) (κ : ℝ),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      pA.length ≤ M → pB.length ≤ M → j ≤ M → q ≤ M →
      progOut pA (canonicalFiniteSetCode (rowStar j u)) = canonicalFiniteSetCode D →
      progOut pB (canonicalFiniteSetCode (colStar j v)) = canonicalFiniteSetCode D →
      (u, v) ∈ labelGraph (progOut pA) (progOut pB) M j (canonicalFiniteSetCode D) →
      κ ≤ condC V v u → κ ≤ condC V u v →
      (pA.length + pB.length + q + cp * headerLog M : ℝ) < κ →
      (u, v) ∈ peelCore (2 ^ q) (labelGraph (progOut pA) (progOut pB) M j
        (canonicalFiniteSetCode D)) := by
  obtain ⟨cp, hcp⟩ := assignedEdgeDecoder V hV
  refine ⟨cp, fun M j q pA pB u v D κ hA hB hAM hBM hjM hqM hzA hzB hedge hvu huv hbud => ?_⟩
  by_contra hcore
  rcases mem_owned_of_not_mem_peelCore hedge hcore with hown | hown
  · have h := (hcp M j q pA pB hA hB hAM hBM hjM hqM _ u v).1 hown hzA
    linarith
  · have h := (hcp M j q pA pB hA hB hAM hBM hjM hqM _ u v).2 hown hzB
    linarith

end Kolmogorov.StrongMerging.Lower
