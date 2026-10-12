import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.StrongMerging.Basic

/-!
# The finite incidence graph of the square-root merger (blueprint G00, G01)

`sublinear-merging.tex`, section "The finite incidence graph" (tex ~180) and appendix
`bp-upper-graph-orientation`.

* **G00 (`UpperFiniteIncidenceGraph`).**  A finite edge-labelled multigraph is a finite set of edge
  labels `E : Finset α` with two endpoint maps `src tgt : α → V`.  Distinct labels are distinct
  edges, so parallel edges are preserved.  We define degrees (`degIn`), incident vertices
  (`incidentVerts`), induced edge sets (`inducedEdges`), capacitated cores (`IsCore`) and
  core-freeness (`CoreFree`), the hypothesis of the online orientation lemma, and prove the
  peeling density bound `card_inducedEdges_le_of_coreFree`.  `upperFiniteIncidenceGraph`: the
  shape graph is loopless and its generic degrees are the row/column degrees.
* **G01 (`UpperBuildShape`).**  The shape graph of two witness-output maps `outA outB` at data
  length `n` and floor size buckets `a, b` (`ShapeParams`): its edges are the strings `z` of
  length `n` whose two outputs list finite sets containing `z` with buckets `a` and `b`
  (`shapeEdges`).  The row endpoint of `z` is the tagged output `Sum.inl (outA z)` and the column
  endpoint `Sum.inr (outB z)`, so the graph is loopless (`shapeSrc_ne_shapeTgt`).  Theorem
  `upperBuildShape` gives `|G| ≤ 2ⁿ` and the degree bounds `deg(U) < 2^(a+1)`, `deg(V) < 2^(b+1)`;
  `mem_shapeEdges_of` shows that the actual string is an edge; `shapeEdges_code_primrec` is the
  totality/computability statement.  Decoders should read the witness outputs from a finite
  output table (`tableOut`), which agrees with the witnesses at the data length
  (`ShapeParams.AgreeOn`, `shapeEdges_congr`).

The witness outputs are raw strings; they are read as finite sets by the total syntactic parser
`parseModel` (`canonicalPointListOfCode`), which inverts `canonicalFiniteSetCode`.  Endpoint
labels are the raw output codes, so the actual endpoints of `x` are the codes of `A` and `B`.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### G00: finite edge-labelled multigraphs -/

section Multigraph

variable {α V : Type*} [DecidableEq V]

/-- The degree of the vertex `v` in the edge set `F` of the multigraph with endpoint maps
`src, tgt`: the number of edge labels of `F` incident to `v`. -/
def degIn (src tgt : α → V) (F : Finset α) (v : V) : ℕ :=
  (F.filter fun e => src e = v ∨ tgt e = v).card

/-- The vertices incident to the edge set `F`. -/
def incidentVerts (src tgt : α → V) (F : Finset α) : Finset V :=
  F.image src ∪ F.image tgt

/-- The edges of `E` with both endpoints in the vertex set `U`. -/
def inducedEdges (src tgt : α → V) (E : Finset α) (U : Finset V) : Finset α :=
  E.filter fun e => src e ∈ U ∧ tgt e ∈ U

/-- `F` is a `d`-core: it is nonempty and every vertex incident to `F` has degree in `F` at
least its capacity `d v`. -/
def IsCore (src tgt : α → V) (d : V → ℕ) (F : Finset α) : Prop :=
  F.Nonempty ∧ ∀ v ∈ incidentVerts src tgt F, d v ≤ degIn src tgt F v

/-- `E` is `d`-core-free: no subset of `E` is a `d`-core (`lem:orientation`, hypothesis). -/
def CoreFree (src tgt : α → V) (d : V → ℕ) (E : Finset α) : Prop :=
  ∀ F ⊆ E, ¬ IsCore src tgt d F

/-- Membership in the incident-vertex set. -/
theorem mem_incidentVerts {src tgt : α → V} {F : Finset α} {v : V} :
    v ∈ incidentVerts src tgt F ↔ ∃ e ∈ F, src e = v ∨ tgt e = v := by
  simp only [incidentVerts, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, he, Or.inl h⟩
    · exact ⟨e, he, Or.inr h⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩

/-- **Peeling density bound.**  In a `d`-core-free edge set `E`, every subset `F ⊆ E` has at
most `∑_{v incident to F} d v` edges.

Proof sketch: strong induction on `F.card`.  An empty `F` is trivial.  A nonempty `F` is not a
core, so some incident `v` has `degIn F v < d v`.  Remove the edges at `v`:
`F' = F.filter (¬ incident to v)` has `F.card = F'.card + degIn F v` and its incident vertices lie
in `incidentVerts F \ {v}`; apply the induction hypothesis to `F'` and add `d v`.
(`lem:orientation`, proof, eq. `density`; blueprint G02 obligation 1.) -/
theorem card_le_sum_incident_of_coreFree {src tgt : α → V} {d : V → ℕ} {E : Finset α}
    (hfree : CoreFree src tgt d E) {F : Finset α} (hF : F ⊆ E) :
    F.card ≤ ∑ v ∈ incidentVerts src tgt F, d v := by
  suffices key : ∀ n, ∀ F ⊆ E, F.card ≤ n → F.card ≤ ∑ v ∈ incidentVerts src tgt F, d v from
    key F.card F hF le_rfl
  intro n
  induction n with
  | zero =>
    intro F _ hn
    omega
  | succ n ih =>
    intro F hFE hn
    rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hex : ∃ v ∈ incidentVerts src tgt F, degIn src tgt F v < d v := by
        by_contra hcon
        exact hfree F hFE ⟨hne, fun v hv => not_lt.mp fun hlt => hcon ⟨v, hv, hlt⟩⟩
      obtain ⟨v, hv, hlt⟩ := hex
      have hsplit := Finset.card_filter_add_card_filter_not (s := F)
        (fun e => src e = v ∨ tgt e = v)
      have hdeg_pos : 0 < degIn src tgt F v := by
        obtain ⟨e, he, hev⟩ := mem_incidentVerts.mp hv
        exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
      have hdeg : degIn src tgt F v = (F.filter fun e => src e = v ∨ tgt e = v).card := rfl
      have h1 := ih (F.filter fun e => ¬ (src e = v ∨ tgt e = v))
        ((Finset.filter_subset _ _).trans hFE) (by omega)
      have hinc : incidentVerts src tgt (F.filter fun e => ¬ (src e = v ∨ tgt e = v)) ⊆
          (incidentVerts src tgt F).erase v := by
        intro u hu
        obtain ⟨e, he, heu⟩ := mem_incidentVerts.mp hu
        have he' := Finset.mem_filter.mp he
        refine Finset.mem_erase.mpr ⟨?_, mem_incidentVerts.mpr ⟨e, he'.1, heu⟩⟩
        rintro rfl
        exact he'.2 heu
      have h2 := Finset.sum_le_sum_of_subset (f := d) hinc
      have h3 := Finset.sum_erase_add (incidentVerts src tgt F) d hv
      omega

/-- **Induced density bound** `|E[U]| ≤ ∑_{v ∈ U} d v` for a `d`-core-free `E`
(`lem:orientation`, eq. `density`). -/
theorem card_inducedEdges_le_of_coreFree {src tgt : α → V} {d : V → ℕ} {E : Finset α}
    (hfree : CoreFree src tgt d E) (U : Finset V) :
    (inducedEdges src tgt E U).card ≤ ∑ v ∈ U, d v := by
  refine (card_le_sum_incident_of_coreFree hfree (Finset.filter_subset _ _)).trans ?_
  apply Finset.sum_le_sum_of_subset
  intro v hv
  obtain ⟨e, he, h | h⟩ := mem_incidentVerts.mp hv
  · rw [← h]
    exact (Finset.mem_filter.mp he).2.1
  · rw [← h]
    exact (Finset.mem_filter.mp he).2.2

/-- **Application size bound for the total capacity.**  If `E` has at most `2ⁿ` edges and every
capacity is at most `2ᵐ`, then `W = ∑_{v incident to E} d v ≤ 2^(n+1+m)`.

Proof sketch: `incidentVerts E` is a union of two images of `E`, so it has at most
`2 |E| ≤ 2^(n+1)` elements; bound the sum by `card • 2ᵐ` (`Finset.sum_le_card_nsmul`).
(Blueprint G03 obligation "W ≤ 2^(3n+c)"; tex ~285.) -/
theorem sum_incidentVerts_le_pow {src tgt : α → V} {d : V → ℕ} {E : Finset α} {n m : ℕ}
    (hE : E.card ≤ 2 ^ n) (hd : ∀ v, d v ≤ 2 ^ m) :
    ∑ v ∈ incidentVerts src tgt E, d v ≤ 2 ^ (n + 1 + m) := by
  have hcardI : (incidentVerts src tgt E).card ≤ 2 ^ (n + 1) := by
    calc (incidentVerts src tgt E).card ≤ (E.image src).card + (E.image tgt).card :=
          Finset.card_union_le _ _
      _ ≤ E.card + E.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add hE hE
      _ = 2 ^ (n + 1) := by ring
  calc ∑ v ∈ incidentVerts src tgt E, d v ≤ ∑ _v ∈ incidentVerts src tgt E, 2 ^ m :=
        Finset.sum_le_sum fun v _ => hd v
    _ = (incidentVerts src tgt E).card * 2 ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ (n + 1) * 2 ^ m := Nat.mul_le_mul_right _ hcardI
    _ = 2 ^ (n + 1 + m) := (pow_add _ _ _).symm

/-- The binary logarithm of the total capacity in the application: `⌊log₂ W⌋ ≤ n + 1 + m`. -/
theorem log_sum_incidentVerts_le {src tgt : α → V} {d : V → ℕ} {E : Finset α} {n m : ℕ}
    (hE : E.card ≤ 2 ^ n) (hd : ∀ v, d v ≤ 2 ^ m) :
    Nat.log 2 (∑ v ∈ incidentVerts src tgt E, d v) ≤ n + 1 + m :=
  (Nat.log_mono_right (sum_incidentVerts_le_pow hE hd)).trans
    (Nat.log_pow (by norm_num) _).le

end Multigraph

/-! ### G01: the shape graph -/

/-- The finite model listed by a witness output `w`: the set of strings of the total syntactic
decoder `canonicalPointListOfCode w`.  It inverts `canonicalFiniteSetCode`
(`parseModel_canonicalFiniteSetCode`); malformed outputs are read as some finite set, which the
shape test then treats like any other output. -/
noncomputable def parseModel (w : BitString) : Finset BitString :=
  (canonicalPointListOfCode w).toFinset

/-- `parseModel` recovers a finite model from its canonical code. -/
theorem parseModel_canonicalFiniteSetCode (S : Finset BitString) :
    parseModel (canonicalFiniteSetCode S) = S := by
  rw [parseModel, canonicalPointListOfCode_canonicalFiniteSetCode, canonicalFinsetList_toFinset]

/-- The parameters of the shape graph: the two witness-output maps (the outputs of the total
witnesses `p_A`, `p_B` on every string), the data length `n` and the floor size buckets
`a = ⌊log₂ |A|⌋`, `b = ⌊log₂ |B|⌋`. -/
structure ShapeParams where
  /-- The row witness output on each string. -/
  outA : BitString → BitString
  /-- The column witness output on each string. -/
  outB : BitString → BitString
  /-- The data length `n`. -/
  n : ℕ
  /-- The row size bucket `a`. -/
  a : ℕ
  /-- The column size bucket `b`. -/
  b : ℕ

/-- The retention test of a string `z`: both outputs list finite sets containing `z`, whose sizes
lie in `[2^a, 2^(a+1))` and `[2^b, 2^(b+1))` respectively (floor buckets `a`, `b`). -/
def IsShapeEdge (P : ShapeParams) (z : BitString) : Prop :=
  z ∈ parseModel (P.outA z) ∧ z ∈ parseModel (P.outB z) ∧
    Nat.log 2 (parseModel (P.outA z)).card = P.a ∧ Nat.log 2 (parseModel (P.outB z)).card = P.b

noncomputable instance (P : ShapeParams) : DecidablePred (IsShapeEdge P) := fun z => by
  unfold IsShapeEdge
  infer_instance

/-- The edge labels of the shape graph `G`: the retained strings of length `n`. -/
noncomputable def shapeEdges (P : ShapeParams) : Finset BitString :=
  (stringsOfLength P.n).filter (IsShapeEdge P)

/-- The row endpoint of an edge: its row output, tagged as a row. -/
def shapeSrc (P : ShapeParams) (z : BitString) : BitString ⊕ BitString :=
  Sum.inl (P.outA z)

/-- The column endpoint of an edge: its column output, tagged as a column. -/
def shapeTgt (P : ShapeParams) (z : BitString) : BitString ⊕ BitString :=
  Sum.inr (P.outB z)

/-- Tagged sides make the shape graph loopless (blueprint G00). -/
theorem shapeSrc_ne_shapeTgt (P : ShapeParams) (z : BitString) : shapeSrc P z ≠ shapeTgt P z :=
  Sum.inl_ne_inr

/-- The degree of the row labelled `w` in the edge set `F`. -/
def rowDeg (P : ShapeParams) (F : Finset BitString) (w : BitString) : ℕ :=
  (F.filter fun z => P.outA z = w).card

/-- The degree of the column labelled `w` in the edge set `F`. -/
def colDeg (P : ShapeParams) (F : Finset BitString) (w : BitString) : ℕ :=
  (F.filter fun z => P.outB z = w).card

/-- The generic degree of a row vertex of the shape graph is its row degree.

Proof sketch: `shapeTgt z = Sum.inr _` never equals `Sum.inl w`, and `Sum.inl` is injective;
`simp [degIn, rowDeg, shapeSrc, shapeTgt]`. -/
theorem degIn_shape_inl (P : ShapeParams) (F : Finset BitString) (w : BitString) :
    degIn (shapeSrc P) (shapeTgt P) F (Sum.inl w) = rowDeg P F w := by
  simp [degIn, rowDeg, shapeSrc, shapeTgt]

/-- The generic degree of a column vertex of the shape graph is its column degree.

Proof sketch: as `degIn_shape_inl`, with the roles of the tags exchanged. -/
theorem degIn_shape_inr (P : ShapeParams) (F : Finset BitString) (w : BitString) :
    degIn (shapeSrc P) (shapeTgt P) F (Sum.inr w) = colDeg P F w := by
  simp [degIn, colDeg, shapeSrc, shapeTgt]

/-- **The finite incidence graph (blueprint G00, `UpperFiniteIncidenceGraph`).**  The shape graph
is a finite edge-labelled multigraph on tagged vertices: it is loopless, and the generic degree of
a row or column vertex in any edge set is the number of edge labels with that row or column
output, so parallel edges (distinct strings with equal endpoints) are counted separately. -/
theorem upperFiniteIncidenceGraph (P : ShapeParams) :
    (∀ z, shapeSrc P z ≠ shapeTgt P z) ∧
      ∀ (F : Finset BitString) (w : BitString),
        degIn (shapeSrc P) (shapeTgt P) F (Sum.inl w) = rowDeg P F w ∧
          degIn (shapeSrc P) (shapeTgt P) F (Sum.inr w) = colDeg P F w :=
  ⟨shapeSrc_ne_shapeTgt P, fun F w => ⟨degIn_shape_inl P F w, degIn_shape_inr P F w⟩⟩

/-- The shape graph has at most `2ⁿ` edges: its edges are strings of length `n`. -/
theorem card_shapeEdges_le (P : ShapeParams) : (shapeEdges P).card ≤ 2 ^ P.n :=
  (Finset.card_filter_le _ _).trans (card_stringsOfLength P.n).le

/-- **Row degree bound** `deg_G(U) < 2^(a+1)` (tex eq. `degrees`).

Proof sketch: if no edge has row `w` the degree is `0`.  Otherwise pick such an edge `z`; every
edge `y` with row `w` satisfies `y ∈ parseModel w` (retention test), so the degree is at most
`(parseModel w).card`, which is nonzero (it contains `z`) and has `Nat.log 2` equal to `a`; conclude
with `Nat.lt_pow_succ_log_self`. -/
theorem rowDeg_shapeEdges_lt (P : ShapeParams) (w : BitString) :
    rowDeg P (shapeEdges P) w < 2 ^ (P.a + 1) := by
  by_cases h : ∃ z ∈ shapeEdges P, P.outA z = w
  · obtain ⟨z, hz, rfl⟩ := h
    have hz' : IsShapeEdge P z := (Finset.mem_filter.mp hz).2
    unfold IsShapeEdge at hz'
    have hsub : (shapeEdges P).filter (fun y => P.outA y = P.outA z) ⊆
        parseModel (P.outA z) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hy' : IsShapeEdge P y := (Finset.mem_filter.mp hy.1).2
      unfold IsShapeEdge at hy'
      rw [hy.2] at hy'
      exact hy'.1
    calc rowDeg P (shapeEdges P) (P.outA z) ≤ (parseModel (P.outA z)).card :=
          Finset.card_le_card hsub
      _ < 2 ^ (Nat.log 2 (parseModel (P.outA z)).card + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num) _
      _ = 2 ^ (P.a + 1) := by rw [hz'.2.2.1]
  · simp only [not_exists, not_and] at h
    have h0 : rowDeg P (shapeEdges P) w = 0 := by
      rw [rowDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun z hz => h z hz
    rw [h0]
    positivity

/-- **Column degree bound** `deg_G(V) < 2^(b+1)` (tex eq. `degrees`).

Proof sketch: as `rowDeg_shapeEdges_lt`, using the column output and the bucket `b`. -/
theorem colDeg_shapeEdges_lt (P : ShapeParams) (w : BitString) :
    colDeg P (shapeEdges P) w < 2 ^ (P.b + 1) := by
  by_cases h : ∃ z ∈ shapeEdges P, P.outB z = w
  · obtain ⟨z, hz, rfl⟩ := h
    have hz' : IsShapeEdge P z := (Finset.mem_filter.mp hz).2
    unfold IsShapeEdge at hz'
    have hsub : (shapeEdges P).filter (fun y => P.outB y = P.outB z) ⊆
        parseModel (P.outB z) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hy' : IsShapeEdge P y := (Finset.mem_filter.mp hy.1).2
      unfold IsShapeEdge at hy'
      rw [hy.2] at hy'
      exact hy'.2.1
    calc colDeg P (shapeEdges P) (P.outB z) ≤ (parseModel (P.outB z)).card :=
          Finset.card_le_card hsub
      _ < 2 ^ (Nat.log 2 (parseModel (P.outB z)).card + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num) _
      _ = 2 ^ (P.b + 1) := by rw [hz'.2.2.2]
  · simp only [not_exists, not_and] at h
    have h0 : colDeg P (shapeEdges P) w = 0 := by
      rw [colDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun z hz => h z hz
    rw [h0]
    positivity

/-- **The shape graph (blueprint G01, `UpperBuildShape`).**  `|G| ≤ 2ⁿ`, every row has degree
`< 2^(a+1)` and every column degree `< 2^(b+1)`. -/
theorem upperBuildShape (P : ShapeParams) :
    (shapeEdges P).card ≤ 2 ^ P.n ∧ (∀ w, rowDeg P (shapeEdges P) w < 2 ^ (P.a + 1)) ∧
      ∀ w, colDeg P (shapeEdges P) w < 2 ^ (P.b + 1) :=
  ⟨card_shapeEdges_le P, rowDeg_shapeEdges_lt P, colDeg_shapeEdges_lt P⟩

/-- **The actual string is an edge (blueprint G01).**  If `|x| = n`, the witnesses output the
canonical codes of finite sets `A, B ∋ x`, and `a, b` are their floor size buckets, then `x` is an
edge of the shape graph, with row `canonicalFiniteSetCode A` and column `canonicalFiniteSetCode B`
(by definition of `shapeSrc`, `shapeTgt`). -/
theorem mem_shapeEdges_of (P : ShapeParams) {x : BitString} {A B : Finset BitString}
    (hx : x.length = P.n) (hA : P.outA x = canonicalFiniteSetCode A)
    (hB : P.outB x = canonicalFiniteSetCode B) (hxA : x ∈ A) (hxB : x ∈ B)
    (ha : Nat.log 2 A.card = P.a) (hb : Nat.log 2 B.card = P.b) : x ∈ shapeEdges P := by
  rw [shapeEdges, Finset.mem_filter, mem_stringsOfLength]
  refine ⟨hx, ?_⟩
  unfold IsShapeEdge
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA, parseModel_canonicalFiniteSetCode]
    exact hxA
  · rw [hB, parseModel_canonicalFiniteSetCode]
    exact hxB
  · rw [hA, parseModel_canonicalFiniteSetCode]
    exact ha
  · rw [hB, parseModel_canonicalFiniteSetCode]
    exact hb

/-- Two shape parameter sets agree at the data length: the same `n, a, b`, and the same outputs on
every string of length `n`.  The shape graph and the hierarchy only read outputs on such strings
(`shapeEdges_congr`, `level_congr`), so a decoder may replace the witness runs by a finite output
table (`tableOut`). -/
def ShapeParams.AgreeOn (P Q : ShapeParams) : Prop :=
  P.n = Q.n ∧ P.a = Q.a ∧ P.b = Q.b ∧
    ∀ z : BitString, z.length = P.n → P.outA z = Q.outA z ∧ P.outB z = Q.outB z

/-- **Congruence of the shape graph.**  Parameter sets that agree at the data length have the
same shape edges.

Proof sketch: `ext z`; membership requires `z.length = n`, where the outputs agree, and the
buckets agree. -/
theorem shapeEdges_congr {P Q : ShapeParams} (h : P.AgreeOn Q) : shapeEdges P = shapeEdges Q := by
  obtain ⟨hn, ha, hb, hout⟩ := h
  ext z
  simp only [shapeEdges, Finset.mem_filter, mem_stringsOfLength, IsShapeEdge]
  constructor
  · rintro ⟨hz, h1⟩
    obtain ⟨hA, hB⟩ := hout z hz
    rw [← hn, ← ha, ← hb, ← hA, ← hB]
    exact ⟨hz, h1⟩
  · rintro ⟨hz, h1⟩
    obtain ⟨hA, hB⟩ := hout z (hz.trans hn.symm)
    rw [hn, ha, hb, hA, hB]
    exact ⟨hz, h1⟩

/-- The output read from a finite table of `(input, output)` pairs: the output of the first entry
with the given input, and the default `[]` if there is none. -/
def tableOut (T : List (BitString × BitString)) (z : BitString) : BitString :=
  ((T.find? fun p => decide (p.1 = z)).map Prod.snd).getD []

/-- Table lookup is primitive recursive.

Proof: rewrite `List.find?` as `T[T.findIdx _]?` (`List.find?_eq_getElem?_findIdx`), then
`Primrec.list_findIdx`, `Primrec.list_getElem?`, `Primrec.option_map`, `Primrec.option_getD`. -/
theorem tableOut_primrec : Primrec₂ tableOut := by
  have hp : Primrec₂ fun (q : List (BitString × BitString) × BitString)
      (x : BitString × BitString) => decide (x.1 = q.2) :=
    (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).to₂
  have hidx : Primrec fun q : List (BitString × BitString) × BitString =>
      q.1.findIdx fun x => decide (x.1 = q.2) :=
    Primrec.list_findIdx Primrec.fst hp
  have hget : Primrec fun q : List (BitString × BitString) × BitString =>
      q.1[q.1.findIdx fun x => decide (x.1 = q.2)]? :=
    Primrec.list_getElem?.comp Primrec.fst hidx
  have hmap : Primrec fun q : List (BitString × BitString) × BitString =>
      (q.1[q.1.findIdx fun x => decide (x.1 = q.2)]?).map Prod.snd :=
    Primrec.option_map hget (Primrec.snd.comp Primrec.snd).to₂
  have hfin : Primrec₂ fun (T : List (BitString × BitString)) (z : BitString) =>
      ((T[T.findIdx fun x => decide (x.1 = z)]?).map Prod.snd).getD [] :=
    Primrec.option_getD.comp hmap (Primrec.const [])
  refine hfin.of_eq fun T z => ?_
  rw [tableOut, List.find?_eq_getElem?_findIdx]

/-- The output table of a function on the strings of length `n` reads back the function there.

Proof sketch: `z ∈ allStrings n` (`mem_allStrings`), and the first entry of the mapped list with
first component `z` is `(z, f z)` (`List.find?_map`, or induction on the list). -/
theorem tableOut_outputTable (f : BitString → BitString) (n : ℕ) {z : BitString}
    (hz : z.length = n) : tableOut ((allStrings n).map fun y => (y, f y)) z = f z := by
  have key : ∀ l : List BitString, z ∈ l →
      ((l.map fun y => (y, f y)).find? fun p => decide (p.1 = z)).map Prod.snd = some (f z) := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons y l ih =>
      intro h
      by_cases hy : y = z
      · subst hy
        rw [List.map_cons, List.find?_cons_of_pos (by simp)]
        rfl
      · have hz' : z ∈ l := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hy
          · exact h
        rw [List.map_cons, List.find?_cons_of_neg (by simpa using hy)]
        exact ih hz'
  unfold tableOut
  rw [key _ ((mem_allStrings n z).mpr hz)]
  rfl

/-- The canonical code of the set of a list is primitive recursive in the list. -/
theorem canonicalFiniteSetCode_toFinset_primrec :
    Primrec fun l : List BitString => canonicalFiniteSetCode l.toFinset :=
  canonicalUniformCodeOfList_primrec.comp canonicalFinsetList_toFinset_primrec

/-- A parametric list filter with a primitive recursive test is primitive recursive.

Proof: `(f a).filter (p a)` is `(f a).filterMap fun b => bif p a b then some b else none`
(induction on the list), and `Primrec.listFilterMap` with `Primrec.cond`. -/
theorem primrec_list_filter {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have h : Primrec₂ fun a b => bif p a b then some b else none :=
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  refine (Primrec.listFilterMap hf h).of_eq fun a => ?_
  generalize f a = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases hb : p a b
    · simp only [List.filterMap_cons, List.filter_cons, hb, Bool.cond_false, Bool.false_eq_true,
        ↓reduceIte, ih]
    · simp only [List.filterMap_cons, List.filter_cons, hb, Bool.cond_true, ↓reduceIte, ih]

/-- The list of all strings of length `n` is primitive recursive in `n`.

Proof: `allStrings` is `Nat.rec` with step `l ↦ l.map (false :: ·) ++ l.map (true :: ·)`;
`Primrec.nat_rec₁`, `Primrec.list_map`, `Primrec.list_cons` and `Primrec.list_append`. -/
theorem allStrings_primrec : Primrec allStrings := by
  have hstep : Primrec₂ fun (_ : ℕ) (l : List BitString) =>
      l.map (fun b => false :: b) ++ l.map (fun b => true :: b) :=
    (Primrec.list_append.comp
      (Primrec.list_map Primrec.snd (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)
      (Primrec.list_map Primrec.snd
        (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)).to₂
  refine (Primrec.nat_rec₁ [[]] hstep).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allStrings, ← ih]

/-- The shape edge set as a filtered list of all strings of length `n`.

Proof: `ext z`; `mem_stringsOfLength`, `List.mem_toFinset`, `List.mem_filter`,
`mem_allStrings` and `decide_eq_true_eq`. -/
theorem shapeEdges_eq_toFinset_filter (P : ShapeParams) :
    shapeEdges P = ((allStrings P.n).filter fun z => decide (IsShapeEdge P z)).toFinset := by
  ext z
  simp only [shapeEdges, Finset.mem_filter, mem_stringsOfLength, List.mem_toFinset,
    List.mem_filter, mem_allStrings, decide_eq_true_eq]

/-- Powers of natural numbers are primitive recursive. -/
theorem shapePR_pow_primrec : Primrec₂ fun (m k : ℕ) => m ^ k :=
  Primrec.nat_iff.mpr Nat.Primrec.pow

/-- The binary logarithm as a greatest-witness search: `⌊log₂ m⌋` is the largest `k ≤ m` with
`2^k ≤ m` (and `0` for `m = 0`, where no `k` qualifies). -/
theorem shapePR_log_eq_findGreatest (m : ℕ) :
    Nat.log 2 m = Nat.findGreatest (fun k => 2 ^ k ≤ m) m := by
  symm
  rw [Nat.findGreatest_eq_iff]
  refine ⟨Nat.log_le_self 2 m, fun h => ?_, fun k hk _ hle => ?_⟩
  · have hm : m ≠ 0 := by
      rintro rfl
      exact h (Nat.log_zero_right 2)
    exact Nat.pow_log_le_self 2 hm
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    have h2 : 2 ^ (Nat.log 2 m + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

/-- The binary logarithm `m ↦ ⌊log₂ m⌋` is primitive recursive. -/
theorem shapePR_log_primrec : Primrec fun m : ℕ => Nat.log 2 m := by
  have hp : PrimrecRel fun (m k : ℕ) => 2 ^ k ≤ m :=
    Primrec.nat_le.comp (shapePR_pow_primrec.comp (Primrec.const 2) Primrec.snd) Primrec.fst
  exact (Primrec.nat_findGreatest Primrec.id hp).of_eq fun m =>
    (shapePR_log_eq_findGreatest m).symm

/-- Membership in a parsed model is membership in the canonical point list. -/
theorem shapePR_mem_parseModel {w z : BitString} :
    z ∈ parseModel w ↔ z ∈ canonicalPointListOfCode w :=
  List.mem_toFinset

/-- The size of a parsed model is the length of the canonical point list, which is
duplicate-free. -/
theorem shapePR_card_parseModel (w : BitString) :
    (parseModel w).card = (canonicalPointListOfCode w).length := by
  rw [parseModel, List.toFinset_card_of_nodup]
  unfold canonicalPointListOfCode
  exact canonicalFinsetList_nodup _

/-- The retention test in Boolean form on the canonical point lists `lA`, `lB` of the two
outputs: membership of `z` in both, and the floor buckets of their lengths. -/
def shapeTestBool (lA lB : List BitString) (a b : ℕ) (z : BitString) : Bool :=
  decide (z ∈ lA) && decide (z ∈ lB) && decide (Nat.log 2 lA.length = a) &&
    decide (Nat.log 2 lB.length = b)

/-- The retention test agrees with its Boolean form on the canonical point lists. -/
theorem decide_isShapeEdge_eq (P : ShapeParams) (z : BitString) :
    decide (IsShapeEdge P z) = shapeTestBool (canonicalPointListOfCode (P.outA z))
      (canonicalPointListOfCode (P.outB z)) P.a P.b z := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [IsShapeEdge, shapePR_mem_parseModel, shapePR_card_parseModel, shapeTestBool,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The retention test is primitive recursive when the witness outputs are.

Proof: `decide_isShapeEdge_eq` turns the test into `shapeTestBool` on the canonical point lists
(`canonicalPointListOfCode_primrec`); membership is `bitString_mem_primrec`, the buckets use
`shapePR_log_primrec` and `Primrec.list_length`, and the conjunctions `Primrec.and`. -/
theorem shapeEdgeTest_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec₂ fun (q : β × ℕ × ℕ × ℕ) (z : BitString) =>
      decide (IsShapeEdge ⟨fA q.1, fB q.1, q.2.1, q.2.2.1, q.2.2.2⟩ z) := by
  have hlA : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      canonicalPointListOfCode (fA p.1.1 p.2) :=
    canonicalPointListOfCode_primrec.comp (hA.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hlB : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      canonicalPointListOfCode (fB p.1.1 p.2) :=
    canonicalPointListOfCode_primrec.comp (hB.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hm1 : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      decide (p.2 ∈ canonicalPointListOfCode (fA p.1.1 p.2)) :=
    bitString_mem_primrec.comp Primrec.snd hlA
  have hm2 : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      decide (p.2 ∈ canonicalPointListOfCode (fB p.1.1 p.2)) :=
    bitString_mem_primrec.comp Primrec.snd hlB
  have hl1 : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      decide (Nat.log 2 (canonicalPointListOfCode (fA p.1.1 p.2)).length = p.1.2.2.1) :=
    Primrec.eq.decide.comp (shapePR_log_primrec.comp (Primrec.list_length.comp hlA))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hl2 : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      decide (Nat.log 2 (canonicalPointListOfCode (fB p.1.1 p.2)).length = p.1.2.2.2) :=
    Primrec.eq.decide.comp (shapePR_log_primrec.comp (Primrec.list_length.comp hlB))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have h : Primrec fun p : (β × ℕ × ℕ × ℕ) × BitString =>
      shapeTestBool (canonicalPointListOfCode (fA p.1.1 p.2))
        (canonicalPointListOfCode (fB p.1.1 p.2)) p.1.2.2.1 p.1.2.2.2 p.2 :=
    Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hm1 hm2) hl1) hl2
  have h2 : Primrec₂ fun (q : β × ℕ × ℕ × ℕ) (z : BitString) =>
      shapeTestBool (canonicalPointListOfCode (fA q.1 z))
        (canonicalPointListOfCode (fB q.1 z)) q.2.2.1 q.2.2.2 z := h.to₂
  refine h2.of_eq fun q z => ?_
  exact (decide_isShapeEdge_eq ⟨fA q.1, fB q.1, q.2.1, q.2.2.1, q.2.2.2⟩ z).symm

/-- **The shape builder is a total computable function (blueprint G01, totality).**  For witness
output maps depending primitive recursively on a parameter `p : β`, the canonical code of the shape
edge set is a primitive recursive (hence computable, `Primrec.to_comp`) function of
`(p, n, a, b)`.  In the application `p` is the finite output table of the two total witnesses on
the strings of length `n` (`tableOut`, `tableOut_primrec`, `tableOut_outputTable`,
`shapeEdges_congr`); producing that table by complete runs is a partial recursive step that halts
because the witnesses are total. -/
theorem shapeEdges_code_primrec {β : Type} [Primcodable β]
    (fA fB : β → BitString → BitString) (hA : Primrec₂ fA) (hB : Primrec₂ fB) :
    Primrec fun q : β × ℕ × ℕ × ℕ =>
      canonicalFiniteSetCode (shapeEdges ⟨fA q.1, fB q.1, q.2.1, q.2.2.1, q.2.2.2⟩) := by
  have h1 : Primrec fun q : β × ℕ × ℕ × ℕ => (allStrings q.2.1).filter fun z =>
      decide (IsShapeEdge ⟨fA q.1, fB q.1, q.2.1, q.2.2.1, q.2.2.2⟩ z) :=
    primrec_list_filter (allStrings_primrec.comp (Primrec.fst.comp Primrec.snd))
      (shapeEdgeTest_primrec fA fB hA hB)
  refine (canonicalFiniteSetCode_toFinset_primrec.comp h1).of_eq fun q => ?_
  rw [shapeEdges_eq_toFinset_filter]

end Kolmogorov.StrongMerging.Upper
