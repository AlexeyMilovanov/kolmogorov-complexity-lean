import KolmogorovMathlib.StrongMerging.Coding
import KolmogorovMathlib.StrongMerging.Lower.Cube
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability

/-!
# The sharp lower bound: ambient stars, labelled model graphs and canonical peeling

Blueprint nodes L28 (`ambientStarModels`), L29 (`labelledModelGraph`) and L30 (`canonicalPeel`)
of the formalization of `sublinear-merging.tex` (main text "Calibrating an internal edge and its
ambient stars", tex lines 1613-1670, and "Peeling a hypothetical common model", lines 1671-1717;
appendix "Arbitrary proposed models, canonical peeling, and exact partitions", lines 4885-4920).

* **L28.**  For a word `y` the row star `rowStar j y = {y w : |w| = |y|, dist(y, w) = j}` and
  for a word `w` the column star `colStar j w = {y w : |y| = |w|, dist(y, w) = j}`.  For an edge
  `x = u v` with `|u| = |v| = M` and `dist(u, v) = j` both stars contain `x`, have
  `(M choose j)` points and meet exactly in `{x}`.  Fixed total point programs
  (`pointRowStar`, `pointColStar`) compute the stars from `x` by reading the actual distance of
  its halves, so both point strengths are bounded by one constant.  An ordinary description of a
  star costs `C(u) + O(log M)` (the radius `j` is advice).
* **L29.**  For arbitrary output maps `fA, fB` (later the outputs of two total witness programs)
  and every label `z`, `labelGraph fA fB M j z` is the finite bipartite graph of the ordered pairs
  `(y, w)` of `M`-words with `y w ∈ decodeModel z`, `dist(y, w) = j` and
  `fA (A_y) = z = fB (B_w)` (equality of output codes with the label).  Its edges inject into the
  decoded model; the actual edge lies in the graph of the actual label.
* **L30.**  Canonical peeling by rounds: a round deletes every edge having an endpoint of degree
  below `θ` (`peelRound`).  After `|E|` rounds the edge set is stable (`peelCore`), every surviving
  edge has both endpoint degrees at least `θ`, every deleted edge is assigned to an endpoint which
  was low in the round of its deletion (`ownedL`, `ownedR`), and a vertex owns fewer than `θ`
  edges.  Deleting all low vertices of a round simultaneously replaces the blueprint's
  one-vertex-at-a-time order; only these four properties are used downstream.
-/

namespace Kolmogorov.StrongMerging.Lower

open Finset

/-! ### L28: the ambient stars -/

/-- The row star `A_y = {y w : |w| = |y|, dist(y, w) = j}` of radius `j` around the left half
`y` (manuscript `eq:ham-stars`). -/
def rowStar (j : ℕ) (y : BitString) : Finset BitString :=
  (hammingSphere y.length y j).image fun w => y ++ w

/-- The column star `B_w = {y w : |y| = |w|, dist(y, w) = j}` of radius `j` around the right half
`w` (manuscript `eq:ham-stars`). -/
def colStar (j : ℕ) (w : BitString) : Finset BitString :=
  (hammingSphere w.length w j).image fun y => y ++ w

/-- Membership in a row star. -/
theorem mem_rowStar {j : ℕ} {y x : BitString} :
    x ∈ rowStar j y ↔ ∃ w : BitString, w.length = y.length ∧ hammingDist y w = j ∧ x = y ++ w := by
  simp only [rowStar, hammingSphere, mem_image, mem_filter, mem_stringsOfLength]
  constructor
  · rintro ⟨w, ⟨hw, hd⟩, rfl⟩
    exact ⟨w, hw, hd, rfl⟩
  · rintro ⟨w, hw, hd, rfl⟩
    exact ⟨w, ⟨hw, hd⟩, rfl⟩

/-- Membership in a column star. -/
theorem mem_colStar {j : ℕ} {w x : BitString} :
    x ∈ colStar j w ↔ ∃ y : BitString, y.length = w.length ∧ hammingDist w y = j ∧ x = y ++ w := by
  simp only [colStar, hammingSphere, mem_image, mem_filter, mem_stringsOfLength]
  constructor
  · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
    exact ⟨y, hy, hd, rfl⟩
  · rintro ⟨y, hy, hd, rfl⟩
    exact ⟨y, ⟨hy, hd⟩, rfl⟩

/-- The edge `u v` lies in the row star of `u` at radius `dist(u, v)`. -/
theorem append_mem_rowStar {u v : BitString} (huv : u.length = v.length) :
    u ++ v ∈ rowStar (hammingDist u v) u :=
  mem_rowStar.2 ⟨v, huv.symm, rfl, rfl⟩

/-- The edge `u v` lies in the column star of `v` at radius `dist(u, v)`. -/
theorem append_mem_colStar {u v : BitString} (huv : u.length = v.length) :
    u ++ v ∈ colStar (hammingDist u v) v :=
  mem_colStar.2 ⟨u, huv, hammingDist_comm v u, rfl⟩

/-- **Star size**: a row star of radius `j` around an `M`-word has `(M choose j)` points.

Proof sketch: `rowStar` is the image of `hammingSphere M y j` under the injective map
`w ↦ y ++ w` (`List.append_cancel_left`), so `card_image_of_injective` and
`hammingSphere_card M y j rfl` give `(M choose j)`.
Reference: tex 1641-1646 ("They have size `D_a`"); node L28. -/
theorem card_rowStar (j : ℕ) (y : BitString) : (rowStar j y).card = y.length.choose j := by
  rw [rowStar, card_image_of_injective _ fun a b h => List.append_cancel_left h,
    hammingSphere_card y.length y j rfl]

/-- **Star size**: a column star of radius `j` around an `M`-word has `(M choose j)` points.

Proof sketch: as `card_rowStar`, with the injective map `y ↦ y ++ w`
(`List.append_cancel_right`).
Reference: tex 1641-1646; node L28. -/
theorem card_colStar (j : ℕ) (w : BitString) : (colStar j w).card = w.length.choose j := by
  rw [colStar, card_image_of_injective _ fun a b h => List.append_cancel_right h,
    hammingSphere_card w.length w j rfl]

/-- **Singleton intersection**: for `M`-words `u, v` the row star of `u` and the column star of
`v` (same radius) meet exactly in `{u v}`.

Proof sketch: `⊇` by `append_mem_rowStar`, `append_mem_colStar` after rewriting the radius.  For
`⊆`, a common member is `u ++ w = y ++ v` with `|w| = |u|` and `|y| = |v| = |u|`;
`append_inj_of_length` gives `y = u` and `w = v`.
Reference: tex 1641-1646 ("meet exactly in `{x}`"); node L28. -/
theorem rowStar_inter_colStar {j : ℕ} {u v : BitString} (huv : u.length = v.length)
    (hd : hammingDist u v = j) : rowStar j u ∩ colStar j v = {u ++ v} := by
  ext x
  simp only [mem_inter, mem_singleton]
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨w, hw, -, rfl⟩ := mem_rowStar.1 hA
    obtain ⟨y, hy, -, hyx⟩ := mem_colStar.1 hB
    obtain ⟨-, h2⟩ := append_inj_of_length (M := u.length) rfl (hy.trans huv.symm) hyx
    rw [h2]
  · rintro rfl
    exact ⟨hd ▸ append_mem_rowStar huv, hd ▸ append_mem_colStar huv⟩

/-- The left half `take ⌊|x| / 2⌋ x` of a word. -/
def leftHalf (x : BitString) : BitString :=
  x.take (x.length / 2)

/-- The right half `drop ⌊|x| / 2⌋ x` of a word. -/
def rightHalf (x : BitString) : BitString :=
  x.drop (x.length / 2)

/-- The halves of a concatenation of two words of equal length are the two words. -/
theorem halves_append {u v : BitString} (huv : u.length = v.length) :
    leftHalf (u ++ v) = u ∧ rightHalf (u ++ v) = v := by
  have h : (u ++ v).length / 2 = u.length := by
    rw [List.length_append, ← huv]
    omega
  unfold leftHalf rightHalf
  rw [h]
  exact ⟨List.take_left, List.drop_left⟩

/-- The fixed point-to-row-star map: on a word of even length it returns the row star around the
left half at the actual distance of the two halves; on odd lengths the containing singleton.  It
receives no radius, center or numeric field. -/
def pointRowStar (x : BitString) : Finset BitString :=
  if x.length % 2 = 0 then rowStar (hammingDist (leftHalf x) (rightHalf x)) (leftHalf x) else {x}

/-- The fixed point-to-column-star map, analogous to `pointRowStar`. -/
def pointColStar (x : BitString) : Finset BitString :=
  if x.length % 2 = 0 then colStar (hammingDist (leftHalf x) (rightHalf x)) (rightHalf x)
  else {x}

/-- On an edge `u v` with halves of equal length the point map returns the row star of `u`. -/
theorem pointRowStar_append {u v : BitString} (huv : u.length = v.length) :
    pointRowStar (u ++ v) = rowStar (hammingDist u v) u := by
  have h2 : (u ++ v).length % 2 = 0 := by
    rw [List.length_append, ← huv]
    omega
  obtain ⟨hl, hr⟩ := halves_append huv
  rw [pointRowStar, ite_eq_left h2, hl, hr]

/-- On an edge `u v` with halves of equal length the point map returns the column star of `v`. -/
theorem pointColStar_append {u v : BitString} (huv : u.length = v.length) :
    pointColStar (u ++ v) = colStar (hammingDist u v) v := by
  have h2 : (u ++ v).length % 2 = 0 := by
    rw [List.length_append, ← huv]
    omega
  obtain ⟨hl, hr⟩ := halves_append huv
  rw [pointColStar, ite_eq_left h2, hl, hr]

/-- The explicit list enumerating a row star. -/
def rowStarList (j : ℕ) (y : BitString) : List BitString :=
  (allStrings y.length).filterMap fun w => if hammingDist y w = j then some (y ++ w) else none

/-- The explicit list enumerating a column star. -/
def colStarList (j : ℕ) (w : BitString) : List BitString :=
  (allStrings w.length).filterMap fun y => if hammingDist w y = j then some (y ++ w) else none

/-- The row-star list enumerates the row star. -/
theorem rowStarList_toFinset (j : ℕ) (y : BitString) :
    (rowStarList j y).toFinset = rowStar j y := by
  ext x
  simp only [rowStarList, List.mem_toFinset, List.mem_filterMap, mem_rowStar, mem_allStrings]
  constructor
  · rintro ⟨w, hw, hx⟩
    by_cases hd : hammingDist y w = j
    · rw [ite_eq_left hd] at hx
      exact ⟨w, hw, hd, (Option.some.inj hx).symm⟩
    · rw [ite_eq_right hd] at hx
      exact absurd hx (by simp)
  · rintro ⟨w, hw, hd, rfl⟩
    exact ⟨w, hw, by rw [ite_eq_left hd]⟩

/-- The column-star list enumerates the column star. -/
theorem colStarList_toFinset (j : ℕ) (w : BitString) :
    (colStarList j w).toFinset = colStar j w := by
  ext x
  simp only [colStarList, List.mem_toFinset, List.mem_filterMap, mem_colStar, mem_allStrings]
  constructor
  · rintro ⟨y, hy, hx⟩
    by_cases hd : hammingDist w y = j
    · rw [ite_eq_left hd] at hx
      exact ⟨y, hy, hd, (Option.some.inj hx).symm⟩
    · rw [ite_eq_right hd] at hx
      exact absurd hx (by simp)
  · rintro ⟨y, hy, hd, rfl⟩
    exact ⟨y, hy, by rw [ite_eq_left hd]⟩

/-- The row-star list is primitive recursive in the radius and the center. -/
theorem primrec_rowStarList : Primrec₂ rowStarList := by
  have hlist : Primrec fun p : ℕ × BitString => allStrings p.2.length :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.list_length.comp Primrec.snd)
  have hg : Primrec₂ fun (p : ℕ × BitString) (w : BitString) =>
      if hammingDist p.2 w = p.1 then some (p.2 ++ w) else none := by
    change Primrec fun q : (ℕ × BitString) × BitString =>
      if hammingDist q.1.2 q.2 = q.1.1 then some (q.1.2 ++ q.2) else none
    refine Primrec.ite ?_ ?_ (Primrec.const none)
    · exact Primrec.eq.comp (hammingDist_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    · exact Primrec.option_some.comp
        (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact Primrec.listFilterMap hlist hg

/-- The column-star list is primitive recursive in the radius and the center. -/
theorem primrec_colStarList : Primrec₂ colStarList := by
  have hlist : Primrec fun p : ℕ × BitString => allStrings p.2.length :=
    CodedFiniteDistribution.allStrings_primrec.comp (Primrec.list_length.comp Primrec.snd)
  have hg : Primrec₂ fun (p : ℕ × BitString) (y : BitString) =>
      if hammingDist p.2 y = p.1 then some (y ++ p.2) else none := by
    change Primrec fun q : (ℕ × BitString) × BitString =>
      if hammingDist q.1.2 q.2 = q.1.1 then some (q.2 ++ q.1.2) else none
    refine Primrec.ite ?_ ?_ (Primrec.const none)
    · exact Primrec.eq.comp (hammingDist_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.fst.comp Primrec.fst)
    · exact Primrec.option_some.comp
        (Primrec.list_append.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
  exact Primrec.listFilterMap hlist hg

/-- The code of a row star is computable in the radius and the center. -/
theorem computable_rowStar_code :
    Computable₂ fun (j : ℕ) (y : BitString) => canonicalFiniteSetCode (rowStar j y) :=
  (listModelCode_computable.comp primrec_rowStarList.to_comp).of_eq fun p =>
    listModelCode_eq _ _ (rowStarList_toFinset p.1 p.2)

/-- The code of a column star is computable in the radius and the center. -/
theorem computable_colStar_code :
    Computable₂ fun (j : ℕ) (w : BitString) => canonicalFiniteSetCode (colStar j w) :=
  (listModelCode_computable.comp primrec_colStarList.to_comp).of_eq fun p =>
    listModelCode_eq _ _ (colStarList_toFinset p.1 p.2)

/-- The two halves of a word are primitive recursive. -/
theorem primrec_halves : Primrec leftHalf ∧ Primrec rightHalf := by
  have hhalf : Primrec fun w : BitString => w.length / 2 :=
    Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)
  exact ⟨Primrec.list_take.comp hhalf Primrec.id, Primrec.list_drop.comp hhalf Primrec.id⟩

/-- The code of a singleton model is computable. -/
theorem computable_singleton_code :
    Computable fun x : BitString => canonicalFiniteSetCode ({x} : Finset BitString) :=
  (listModelCode_computable.comp (Computable.list_cons.comp Computable.id
    (Computable.const []))).of_eq fun x => listModelCode_eq _ _ (by simp)

/-- **The point-to-row-star code is computable.**

Proof sketch: `rowStar j y` is `l.toFinset` for the explicit list
`((allStrings |y|).filter (hammingDist y · = j)).map (y ++ ·)`, so its code is
`listModelCode l` (`listModelCode_eq`, `listModelCode_computable`); `allStrings` is defined by
primitive recursion on the length, `hammingDist_primrec` handles the filter, and `leftHalf`,
`rightHalf`, the parity test and `canonicalSingletonSetCode` (`canonicalSingletonSetCode_eq`) are
primitive recursive.
Reference: tex 1647-1651 ("a fixed total program parses its halves"); node L28. -/
theorem computable_pointRowStar_code :
    Computable fun x : BitString => canonicalFiniteSetCode (pointRowStar x) := by
  obtain ⟨hl, hr⟩ := primrec_halves
  have hrow : Computable fun x => canonicalFiniteSetCode
      (rowStar (hammingDist (leftHalf x) (rightHalf x)) (leftHalf x)) :=
    computable_rowStar_code.comp (hammingDist_primrec.comp hl hr).to_comp hl.to_comp
  have hpar : Primrec fun x : BitString => decide (x.length % 2 = 0) :=
    PrimrecPred.decide (Primrec.eq.comp
      (Primrec.nat_mod.comp Primrec.list_length (Primrec.const 2)) (Primrec.const 0))
  refine (Computable.cond hpar.to_comp hrow computable_singleton_code).of_eq fun x => ?_
  unfold pointRowStar
  by_cases h : x.length % 2 = 0 <;> simp [h]

/-- **The point-to-column-star code is computable.**

Proof sketch: as `computable_pointRowStar_code`, with the list
`((allStrings |w|).filter (hammingDist w · = j)).map (· ++ w)`.
Reference: tex 1647-1651; node L28. -/
theorem computable_pointColStar_code :
    Computable fun x : BitString => canonicalFiniteSetCode (pointColStar x) := by
  obtain ⟨hl, hr⟩ := primrec_halves
  have hcol : Computable fun x => canonicalFiniteSetCode
      (colStar (hammingDist (leftHalf x) (rightHalf x)) (rightHalf x)) :=
    computable_colStar_code.comp (hammingDist_primrec.comp hl hr).to_comp hr.to_comp
  have hpar : Primrec fun x : BitString => decide (x.length % 2 = 0) :=
    PrimrecPred.decide (Primrec.eq.comp
      (Primrec.nat_mod.comp Primrec.list_length (Primrec.const 2)) (Primrec.const 0))
  refine (Computable.cond hpar.to_comp hcol computable_singleton_code).of_eq fun x => ?_
  unfold pointColStar
  by_cases h : x.length % 2 = 0 <;> simp [h]

/-- A computable image of the condition has total conditional complexity bounded by a constant
at the canonical total interpreter: `CT(f x | x) ≤ c`. -/
theorem totalC_map_self_le (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ x : BitString, totalC (f x) x ≤ c := by
  obtain ⟨c, hc⟩ := totalCondK_map_self_le_const universalDecompressor
    isOptimalTotalConditional_universalDecompressor f hf
  refine ⟨c, fun x => ?_⟩
  unfold totalC
  exact_mod_cast toNat_le_of_le_natCast (hc x)

/-- The binary digits of a number `k ≤ M` number at most `headerLog M = ⌈log₂ (M + 2)⌉`. -/
theorem natBits_length_le_headerLog {k M : ℕ} (h : k ≤ M) :
    (Nat.bits k).length ≤ headerLog M := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  unfold headerLog
  exact lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (M + 2))

/-- A computable map raises plain complexity by at most a constant: `C(f x) ≤ C(x) + c`. -/
theorem plainC_map_le_add (V : Map) (hV : isOptimalConditional V) (f : BitString → BitString)
    (hf : Computable f) : ∃ c : ℕ, ∀ x : BitString, plainC V (f x) ≤ plainC V x + c := by
  obtain ⟨c, hc⟩ := plainK_map_le V hV f hf
  refine ⟨c, fun x => ?_⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV x)
  have h1 : plainK V (f x) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact hc x
  have h2 : plainC V x = k := by rw [plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- The plain decoder prefixing a numeric field: on the packet `totalProgramPairCode a p` it runs
`V` on `p` and frames the output behind `a`. -/
def numFieldPrefixDecoder (V : Map) : Map := fun p =>
  (V (decodeTotalProgramPairSecond p.1, p.2)).map
    fun w => totalProgramPairCode (decodeTotalProgramPairFirst p.1) w

/-- The numeric-field prefix decoder is partial recursive. -/
theorem numFieldPrefixDecoder_partrec (V : Map) (hV : isDecompressor V) :
    isDecompressor (numFieldPrefixDecoder V) := by
  have hp : Computable fun p : BitString × BitString => (decodeTotalProgramPairSecond p.1, p.2) :=
    (decodeTotalProgramPairSecond_computable.comp Computable.fst).pair Computable.snd
  have hf : Partrec fun p : BitString × BitString => V (decodeTotalProgramPairSecond p.1, p.2) :=
    (Partrec.comp hV hp).of_eq fun _ => rfl
  have h2 : Computable fun q : (BitString × BitString) × BitString =>
      (decodeTotalProgramPairFirst q.1.1, q.2) :=
    (decodeTotalProgramPairFirst_computable.comp (Computable.fst.comp Computable.fst)).pair
      Computable.snd
  have hg : Computable₂ fun (p : BitString × BitString) (w : BitString) =>
      totalProgramPairCode (decodeTotalProgramPairFirst p.1) w :=
    (totalProgramPairCode_computable.comp h2).of_eq fun _ => rfl
  have hm := Partrec.map hf hg
  exact hm.of_eq fun _ => rfl

/-- **Prefixing a numeric field costs its length**:
`C(numField k w) ≤ C(w) + |bits k| + 2 |bits |bits k|| + 1 + c`. -/
theorem plainC_numField_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (k : ℕ) (w : BitString), plainC V (numField k w) ≤
      plainC V w + (Nat.bits k).length + 2 * (Nat.bits (Nat.bits k).length).length + 1 + c := by
  obtain ⟨c, hc⟩ := condC_le_of_decoder V hV (numFieldPrefixDecoder V)
    (numFieldPrefixDecoder_partrec V hV.1)
  refine ⟨c, fun k w => ?_⟩
  obtain ⟨pw, hpw, hlen⟩ := exists_program_of_condC V hV w []
  have hmem : numField k w ∈
      numFieldPrefixDecoder V (totalProgramPairCode (Nat.bits k) pw, []) := by
    simp only [numFieldPrefixDecoder, decodeTotalProgramPairSecond_pair,
      decodeTotalProgramPairFirst_pair]
    exact Part.mem_map _ hpw
  have h1 := hc _ [] _ hmem
  rw [length_totalProgramPairCode] at h1
  have h2 : plainC V (numField k w) = condC V (numField k w) [] := rfl
  have h3 : plainC V w = condC V w [] := rfl
  rw [h2, h3, ← hlen]
  push_cast at h1 ⊢
  linarith

/-- **Ordinary description of a row star**: `C(A_y) ≤ C(y) + c ⌈log₂ (M + 2)⌉` for an `M`-word
`y` and a radius `j ≤ M`.

Proof sketch: the map `w ↦ code (rowStar k y)` with `(k, y) = numFieldDecode w` is computable
(`computable_rowStar_code`, `numFieldDecode_computable`), so `plainK_map_le` bounds
`C(A_y) ≤ C(numField j y) + c₁`; the plain decoder `totalProgramPairCode a p ↦
totalProgramPairCode a (V p)` (`Partrec.map`; in our attempt the composition with
`totalProgramPairCode_computable` hit a `whnf` timeout, so state it through `Primrec` pieces)
and `condC_le_of_decoder` give `C(numField j y) ≤ C(y) + |numField j []| + c₂`, and the field costs
`|bits j| + 2 |bits |bits j|| + 1 ≤ 3 headerLog M + 1` since `j ≤ M`
(`length_numPacket_le` with one field).
Reference: tex 1645-1646 ("ordinary complexities at most `C(u) + O(m)`"), blueprint L28
("`r` may be supplied in `O(m)` advice"). -/
theorem setC_rowStar_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (M j : ℕ) (y : BitString), y.length = M → j ≤ M →
      setC V (rowStar j y) ≤ plainC V y + c * headerLog M := by
  have hf : Computable fun w : BitString =>
      canonicalFiniteSetCode (rowStar (numFieldDecode w).1 (numFieldDecode w).2) :=
    computable_rowStar_code.comp (Computable.fst.comp numFieldDecode_computable)
      (Computable.snd.comp numFieldDecode_computable)
  obtain ⟨c₁, h₁⟩ := plainC_map_le_add V hV _ hf
  obtain ⟨c₂, h₂⟩ := plainC_numField_le V hV
  refine ⟨c₁ + c₂ + 4, fun M j y _ hj => ?_⟩
  have e1 : setC V (rowStar j y) = plainC V (canonicalFiniteSetCode
      (rowStar (numFieldDecode (numField j y)).1 (numFieldDecode (numField j y)).2)) := by
    rw [numFieldDecode_numField]
    rfl
  have hb1 : (Nat.bits j).length ≤ headerLog M := natBits_length_le_headerLog hj
  have hbj : (Nat.bits j).length ≤ j := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  have hb2 : (Nat.bits (Nat.bits j).length).length ≤ headerLog M :=
    natBits_length_le_headerLog (hbj.trans hj)
  have k1 := h₁ (numField j y)
  have k2 := h₂ j y
  rw [e1]
  have hb1' : ((Nat.bits j).length : ℝ) ≤ headerLog M := by exact_mod_cast hb1
  have hb2' : ((Nat.bits (Nat.bits j).length).length : ℝ) ≤ headerLog M := by exact_mod_cast hb2
  have hm' : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  have k3 : (c₁ : ℝ) ≤ c₁ * headerLog M := le_mul_of_one_le_right (Nat.cast_nonneg _) hm'
  have k4 : (c₂ : ℝ) ≤ c₂ * headerLog M := le_mul_of_one_le_right (Nat.cast_nonneg _) hm'
  push_cast
  nlinarith

/-- **Ordinary description of a column star**: `C(B_w) ≤ C(w) + c ⌈log₂ (M + 2)⌉`.

Proof sketch: as `setC_rowStar_le`, with `computable_colStar_code`.
Reference: tex 1645-1646; node L28. -/
theorem setC_colStar_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (M j : ℕ) (w : BitString), w.length = M → j ≤ M →
      setC V (colStar j w) ≤ plainC V w + c * headerLog M := by
  have hf : Computable fun u : BitString =>
      canonicalFiniteSetCode (colStar (numFieldDecode u).1 (numFieldDecode u).2) :=
    computable_colStar_code.comp (Computable.fst.comp numFieldDecode_computable)
      (Computable.snd.comp numFieldDecode_computable)
  obtain ⟨c₁, h₁⟩ := plainC_map_le_add V hV _ hf
  obtain ⟨c₂, h₂⟩ := plainC_numField_le V hV
  refine ⟨c₁ + c₂ + 4, fun M j w _ hj => ?_⟩
  have e1 : setC V (colStar j w) = plainC V (canonicalFiniteSetCode
      (colStar (numFieldDecode (numField j w)).1 (numFieldDecode (numField j w)).2)) := by
    rw [numFieldDecode_numField]
    rfl
  have hb1 : (Nat.bits j).length ≤ headerLog M := natBits_length_le_headerLog hj
  have hbj : (Nat.bits j).length ≤ j := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  have hb2 : (Nat.bits (Nat.bits j).length).length ≤ headerLog M :=
    natBits_length_le_headerLog (hbj.trans hj)
  have k1 := h₁ (numField j w)
  have k2 := h₂ j w
  rw [e1]
  have hb1' : ((Nat.bits j).length : ℝ) ≤ headerLog M := by exact_mod_cast hb1
  have hb2' : ((Nat.bits (Nat.bits j).length).length : ℝ) ≤ headerLog M := by exact_mod_cast hb2
  have hm' : (1 : ℝ) ≤ headerLog M := by exact_mod_cast one_le_headerLog M
  have k3 : (c₁ : ℝ) ≤ c₁ * headerLog M := le_mul_of_one_le_right (Nat.cast_nonneg _) hm'
  have k4 : (c₂ : ℝ) ≤ c₂ * headerLog M := le_mul_of_one_le_right (Nat.cast_nonneg _) hm'
  push_cast
  nlinarith

/-- **Node L28, `ambientStarModels`.**  For an optimal plain machine `V` there are a point-strength
constant `cpt` and a description constant `cs` such that for all `M`-words `u, v` at distance `j`,
with `x = u v`: both stars contain `x`, meet exactly in `{x}`, have `(M choose j)` points, have
point strength `CT(A | x), CT(B | x) ≤ cpt`, and ordinary complexities
`C(A) ≤ C(u) + cs m`, `C(B) ≤ C(v) + cs m` with `m = ⌈log₂ (M + 2)⌉`.  The sufficiency bound
`≤ 32 E` is assembled in `Assembly` from these and the calibration of cluster F (L24, L27). -/
theorem ambientStarModels (V : Map) (hV : isOptimalConditional V) :
    ∃ cpt cs : ℕ, ∀ (M j : ℕ) (u v : BitString), u.length = M → v.length = M →
      hammingDist u v = j →
        u ++ v ∈ rowStar j u ∧ u ++ v ∈ colStar j v ∧ rowStar j u ∩ colStar j v = {u ++ v} ∧
        (rowStar j u).card = M.choose j ∧ (colStar j v).card = M.choose j ∧
        pointTotalC (rowStar j u) (u ++ v) ≤ cpt ∧ pointTotalC (colStar j v) (u ++ v) ≤ cpt ∧
        setC V (rowStar j u) ≤ plainC V u + cs * headerLog M ∧
        setC V (colStar j v) ≤ plainC V v + cs * headerLog M := by
  obtain ⟨c₁, h₁⟩ := totalC_map_self_le _ computable_pointRowStar_code
  obtain ⟨c₂, h₂⟩ := totalC_map_self_le _ computable_pointColStar_code
  obtain ⟨c₃, h₃⟩ := setC_rowStar_le V hV
  obtain ⟨c₄, h₄⟩ := setC_colStar_le V hV
  refine ⟨c₁ + c₂, c₃ + c₄, fun M j u v hu hv hd => ?_⟩
  have huv : u.length = v.length := hu.trans hv.symm
  have hjM : j ≤ M := by
    rw [← hd, ← hv]
    exact hammingDist_le_right_length u v
  have hm : (0 : ℝ) ≤ headerLog M := Nat.cast_nonneg _
  refine ⟨hd ▸ append_mem_rowStar huv, hd ▸ append_mem_colStar huv,
    rowStar_inter_colStar huv hd, by rw [card_rowStar, hu], by rw [card_colStar, hv],
    ?_, ?_, ?_, ?_⟩
  · have h := h₁ (u ++ v)
    rw [pointRowStar_append huv, hd] at h
    unfold pointTotalC
    push_cast
    linarith [(Nat.cast_nonneg c₂ : (0 : ℝ) ≤ c₂)]
  · have h := h₂ (u ++ v)
    rw [pointColStar_append huv, hd] at h
    unfold pointTotalC
    push_cast
    linarith [(Nat.cast_nonneg c₁ : (0 : ℝ) ≤ c₁)]
  · have h := h₃ M j u hu hjM
    push_cast
    nlinarith [(Nat.cast_nonneg c₄ : (0 : ℝ) ≤ c₄)]
  · have h := h₄ M j v hv hjM
    push_cast
    nlinarith [(Nat.cast_nonneg c₃ : (0 : ℝ) ≤ c₃)]

/-! ### L29: the labelled model graph -/

/-- **The labelled model graph** (node L29).  For output maps `fA, fB` (the outputs of the two
total witness programs on model codes), dimension `M`, radius `j` and an arbitrary label `z`: the
ordered pairs `(y, w)` of `M`-words with `y w ∈ decodeModel z`, `dist(y, w) = j` and
`fA (code A_y) = z = fB (code B_w)`.  Equality is literal equality of the output codes with the
label.  The left vertex is `y` (the `A`-side) and the right vertex is `w` (the `B`-side). -/
noncomputable def labelGraph (fA fB : BitString → BitString) (M j : ℕ) (z : BitString) :
    Finset (BitString × BitString) :=
  (stringsOfLength M ×ˢ stringsOfLength M).filter fun e =>
    e.1 ++ e.2 ∈ decodeModel z ∧ hammingDist e.1 e.2 = j ∧
      fA (canonicalFiniteSetCode (rowStar j e.1)) = z ∧
      fB (canonicalFiniteSetCode (colStar j e.2)) = z

/-- Membership in the labelled model graph. -/
theorem mem_labelGraph {fA fB : BitString → BitString} {M j : ℕ} {z : BitString}
    {e : BitString × BitString} :
    e ∈ labelGraph fA fB M j z ↔ e.1.length = M ∧ e.2.length = M ∧
      e.1 ++ e.2 ∈ decodeModel z ∧ hammingDist e.1 e.2 = j ∧
      fA (canonicalFiniteSetCode (rowStar j e.1)) = z ∧
      fB (canonicalFiniteSetCode (colStar j e.2)) = z := by
  simp only [labelGraph, mem_filter, mem_product, mem_stringsOfLength, and_assoc]

/-- **The edges of the graph of a model inject into the model**: the graph of the label
`code D` has at most `|D|` edges, since `(y, w) ↦ y w` is injective on pairs of `M`-words and
lands in `D`.  No bound on the length of the encoding of `D` is used. -/
theorem card_labelGraph_le (fA fB : BitString → BitString) (M j : ℕ) (D : Finset BitString) :
    (labelGraph fA fB M j (canonicalFiniteSetCode D)).card ≤ D.card := by
  classical
  have hinj : Set.InjOn (fun e : BitString × BitString => e.1 ++ e.2)
      (labelGraph fA fB M j (canonicalFiniteSetCode D) : Set (BitString × BitString)) := by
    intro e he e' he' h
    have h1 := mem_labelGraph.1 he
    have h2 := mem_labelGraph.1 he'
    obtain ⟨ha, hb⟩ := append_inj_of_length h1.1 h2.1 h
    exact Prod.ext ha hb
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro x hx
  obtain ⟨e, he, rfl⟩ := mem_image.1 hx
  have h := (mem_labelGraph.1 he).2.2.1
  rwa [decodeModel_canonicalFiniteSetCode] at h

/-- **The actual edge lies in the graph of the actual label** (node L29): if `u v ∈ D`,
`|u| = |v| = M`, `dist(u, v) = j` and both witnesses map the stars of `u` and `v` to the code of
`D`, then `(u, v)` is an edge of the graph of the label `code D`. -/
theorem mem_labelGraph_actual {fA fB : BitString → BitString} {M j : ℕ} {u v : BitString}
    {D : Finset BitString} (hu : u.length = M) (hv : v.length = M) (hx : u ++ v ∈ D)
    (hd : hammingDist u v = j) (hA : fA (canonicalFiniteSetCode (rowStar j u)) =
      canonicalFiniteSetCode D) (hB : fB (canonicalFiniteSetCode (colStar j v)) =
      canonicalFiniteSetCode D) : (u, v) ∈ labelGraph fA fB M j (canonicalFiniteSetCode D) := by
  rw [mem_labelGraph]
  exact ⟨hu, hv, by rwa [decodeModel_canonicalFiniteSetCode], hd, hA, hB⟩

/-- **Node L29, `labelledModelGraph`.**  For arbitrary output maps and every label the graph is
a finite set of ordered pairs of `M`-words at distance `j`, every edge carries the label on both
sides, the graph of a model's code injects into the model, and the actual edge lies in the graph
of the actual label. -/
theorem labelledModelGraph (fA fB : BitString → BitString) (M j : ℕ) :
    (∀ (z : BitString) (e : BitString × BitString), e ∈ labelGraph fA fB M j z →
        e.1.length = M ∧ e.2.length = M ∧ hammingDist e.1 e.2 = j ∧
          fA (canonicalFiniteSetCode (rowStar j e.1)) = z ∧
          fB (canonicalFiniteSetCode (colStar j e.2)) = z) ∧
      (∀ D : Finset BitString, (labelGraph fA fB M j (canonicalFiniteSetCode D)).card ≤ D.card) ∧
      (∀ (u v : BitString) (D : Finset BitString), u.length = M → v.length = M → u ++ v ∈ D →
        hammingDist u v = j →
        fA (canonicalFiniteSetCode (rowStar j u)) = canonicalFiniteSetCode D →
        fB (canonicalFiniteSetCode (colStar j v)) = canonicalFiniteSetCode D →
        (u, v) ∈ labelGraph fA fB M j (canonicalFiniteSetCode D)) := by
  refine ⟨fun z e he => ?_, card_labelGraph_le fA fB M j,
    fun u v D hu hv hx hd hA hB => mem_labelGraph_actual hu hv hx hd hA hB⟩
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := mem_labelGraph.1 he
  exact ⟨h1, h2, h4, h5, h6⟩

/-! ### L30: canonical peeling -/

section Peel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The degree of the left vertex `a` in the bipartite edge set `E`. -/
def degL (E : Finset (α × β)) (a : α) : ℕ :=
  (E.filter fun e => e.1 = a).card

/-- The degree of the right vertex `b` in the bipartite edge set `E`. -/
def degR (E : Finset (α × β)) (b : β) : ℕ :=
  (E.filter fun e => e.2 = b).card

/-- One peeling round at threshold `θ`: keep exactly the edges both of whose endpoints have degree
at least `θ`; every edge at a vertex of (positive) degree below `θ` is deleted. -/
def peelRound (θ : ℕ) (E : Finset (α × β)) : Finset (α × β) :=
  E.filter fun e => θ ≤ degL E e.1 ∧ θ ≤ degR E e.2

/-- The edge set after `k` peeling rounds. -/
def peelStage (θ : ℕ) (E : Finset (α × β)) (k : ℕ) : Finset (α × β) :=
  (peelRound θ)^[k] E

/-- **The canonical core** (node L30): the edge set after `|E|` peeling rounds, which is stable
(`peelRound_peelCore`). -/
def peelCore (θ : ℕ) (E : Finset (α × β)) : Finset (α × β) :=
  peelStage θ E E.card

/-- The edges assigned to the left vertex `a`: its incident edges in the (unique) round in which
it is low, i.e. has degree below `θ`. -/
def ownedL (θ : ℕ) (E : Finset (α × β)) (a : α) : Finset (α × β) :=
  (range E.card).biUnion fun k =>
    if degL (peelStage θ E k) a < θ then (peelStage θ E k).filter (fun e => e.1 = a) else ∅

/-- The edges assigned to the right vertex `b`, analogous to `ownedL`. -/
def ownedR (θ : ℕ) (E : Finset (α × β)) (b : β) : Finset (α × β) :=
  (range E.card).biUnion fun k =>
    if degR (peelStage θ E k) b < θ then (peelStage θ E k).filter (fun e => e.2 = b) else ∅

/-- A peeling round only deletes edges. -/
theorem peelRound_subset (θ : ℕ) (E : Finset (α × β)) : peelRound θ E ⊆ E :=
  filter_subset _ _

/-- The stages decrease: stage `k + 1` is the peeling round of stage `k`. -/
theorem peelStage_succ (θ : ℕ) (E : Finset (α × β)) (k : ℕ) :
    peelStage θ E (k + 1) = peelRound θ (peelStage θ E k) := by
  unfold peelStage
  rw [Function.iterate_succ_apply']

/-- Later stages are contained in earlier ones. -/
theorem peelStage_antitone (θ : ℕ) (E : Finset (α × β)) {k l : ℕ} (hkl : k ≤ l) :
    peelStage θ E l ⊆ peelStage θ E k := by
  induction l, hkl using Nat.le_induction with
  | base => exact Subset.rfl
  | succ l _ ih =>
    rw [peelStage_succ]
    exact (peelRound_subset θ _).trans ih

/-- The core is contained in the original edge set. -/
theorem peelCore_subset (θ : ℕ) (E : Finset (α × β)) : peelCore θ E ⊆ E :=
  peelStage_antitone θ E (Nat.zero_le _)

/-- **Stability of the core**: after `|E|` rounds a further round deletes nothing.

Proof sketch: if `peelRound θ (peelStage θ E k) ≠ peelStage θ E k` then, the round being a
subset (`peelRound_subset`), `|peelStage θ E (k + 1)| < |peelStage θ E k|`
(`card_lt_card`, `ssubset_of_subset_of_ne`).  Once a stage is fixed all later ones equal it.  So
if stage `|E|` were not fixed, all stages `0, …, |E|` would be strictly decreasing in
cardinality, giving `|peelStage θ E |E|| + |E| ≤ |E|` and then a `|E| + 1`-th strict decrease
below zero (induction on `k`: `|peelStage θ E k| + k ≤ |E|` while no fixed point is reached).
Reference: tex 1695-1698 ("until none remains"), blueprint L30 ("termination by decreasing edge
count"). -/
theorem peelRound_peelCore (θ : ℕ) (E : Finset (α × β)) :
    peelRound θ (peelCore θ E) = peelCore θ E := by
  by_contra hne
  have hstable : ∀ k, peelStage θ E (k + 1) = peelStage θ E k →
      ∀ l, k ≤ l → peelStage θ E (l + 1) = peelStage θ E l := by
    intro k hk l hl
    induction l, hl using Nat.le_induction with
    | base => exact hk
    | succ l _ ih =>
      rw [peelStage_succ θ E (l + 1), ih, ← peelStage_succ]
      exact ih
  have hstrict : ∀ k ≤ E.card, peelStage θ E (k + 1) ≠ peelStage θ E k := by
    intro k hk heq
    exact hne (by rw [peelCore, ← peelStage_succ]; exact hstable k heq E.card hk)
  have hcard : ∀ k ≤ E.card + 1, (peelStage θ E k).card + k ≤ E.card := by
    intro k hk
    induction k with
    | zero => simp [peelStage]
    | succ k ih =>
      have h1 := ih (by omega)
      have hsub : peelStage θ E (k + 1) ⊂ peelStage θ E k := by
        refine ssubset_of_subset_of_ne ?_ (hstrict k (by omega))
        rw [peelStage_succ]
        exact peelRound_subset θ _
      have := card_lt_card hsub
      omega
  have := hcard (E.card + 1) le_rfl
  omega

/-- **Minimum degree of the core**: every surviving edge has both endpoint degrees in the core at
least `θ`. -/
theorem le_deg_of_mem_peelCore {θ : ℕ} {E : Finset (α × β)} {e : α × β}
    (he : e ∈ peelCore θ E) : θ ≤ degL (peelCore θ E) e.1 ∧ θ ≤ degR (peelCore θ E) e.2 := by
  rw [← peelRound_peelCore θ E] at he
  exact (mem_filter.1 he).2

/-- **A deleted edge has a deletion round**: an edge of `E` outside the core lies in some stage
`k < |E|` but not in stage `k + 1`.

Proof sketch: the predicate `e ∉ peelStage θ E k` holds at `k = |E|` and fails at `k = 0`; take
the least `k₁` where it holds (`Nat.find`), so `k₁ ≥ 1`, and put `k = k₁ - 1`.
Reference: blueprint L30 ("record its incident edges as assigned to that vertex"). -/
theorem exists_deletion_round {θ : ℕ} {E : Finset (α × β)} {e : α × β} (he : e ∈ E)
    (hcore : e ∉ peelCore θ E) :
    ∃ k < E.card, e ∈ peelStage θ E k ∧ e ∉ peelStage θ E (k + 1) := by
  classical
  have hex : ∃ k, e ∉ peelStage θ E k := ⟨E.card, hcore⟩
  have hk₁ : e ∉ peelStage θ E (Nat.find hex) := Nat.find_spec hex
  have hk₁0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hk₁
    exact hk₁ he
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk₁0
  refine ⟨k, ?_, ?_, by rw [show k + 1 = Nat.find hex by omega]; exact hk₁⟩
  · have : Nat.find hex ≤ E.card := Nat.find_min' hex hcore
    omega
  · have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this

/-- **Every deleted edge is assigned to an endpoint** that was low in its deletion round. -/
theorem mem_owned_of_not_mem_peelCore {θ : ℕ} {E : Finset (α × β)} {e : α × β} (he : e ∈ E)
    (hcore : e ∉ peelCore θ E) : e ∈ ownedL θ E e.1 ∨ e ∈ ownedR θ E e.2 := by
  obtain ⟨k, hk, hin, hout⟩ := exists_deletion_round he hcore
  rw [peelStage_succ] at hout
  have hlow : degL (peelStage θ E k) e.1 < θ ∨ degR (peelStage θ E k) e.2 < θ := by
    by_contra h
    simp only [not_or, not_lt] at h
    exact hout (mem_filter.2 ⟨hin, h⟩)
  rcases hlow with h | h
  · left
    refine mem_biUnion.2 ⟨k, mem_range.2 hk, ?_⟩
    rw [ite_eq_left h]
    exact mem_filter.2 ⟨hin, rfl⟩
  · right
    refine mem_biUnion.2 ⟨k, mem_range.2 hk, ?_⟩
    rw [ite_eq_left h]
    exact mem_filter.2 ⟨hin, rfl⟩

/-- Owned edges of a left vertex are edges of `E` at that vertex. -/
theorem mem_ownedL {θ : ℕ} {E : Finset (α × β)} {a : α} {e : α × β} (he : e ∈ ownedL θ E a) :
    e ∈ E ∧ e.1 = a := by
  obtain ⟨k, -, hk⟩ := mem_biUnion.1 he
  split_ifs at hk with h
  · obtain ⟨h1, h2⟩ := mem_filter.1 hk
    exact ⟨peelStage_antitone θ E (Nat.zero_le k) h1, h2⟩
  · simp at hk

/-- Owned edges of a right vertex are edges of `E` at that vertex. -/
theorem mem_ownedR {θ : ℕ} {E : Finset (α × β)} {b : β} {e : α × β} (he : e ∈ ownedR θ E b) :
    e ∈ E ∧ e.2 = b := by
  obtain ⟨k, -, hk⟩ := mem_biUnion.1 he
  split_ifs at hk with h
  · obtain ⟨h1, h2⟩ := mem_filter.1 hk
    exact ⟨peelStage_antitone θ E (Nat.zero_le k) h1, h2⟩
  · simp at hk

/-- **A left vertex owns fewer than `θ` edges** (for `θ > 0`).

Proof sketch: if `a` has positive degree below `θ` at stage `k`, the round deletes all its edges
(`peelRound` keeps only edges with `θ ≤ degL`), so its degree is `0` at every later stage
(`peelStage_antitone`).  Hence at most one index `k` of the `biUnion` contributes a nonempty
set (`card_biUnion_le` plus the vanishing of the other terms), and that set has
`degL (peelStage θ E k) a < θ` elements; if none contributes, the card is `0 < θ`.
Reference: tex 1703-1706 ("deleted only once, with fewer than `θ` assigned edges"); blueprint
L30. -/
theorem card_ownedL_lt {θ : ℕ} (hθ : 0 < θ) (E : Finset (α × β)) (a : α) :
    (ownedL θ E a).card < θ := by
  classical
  set t : ℕ → Finset (α × β) := fun k => if degL (peelStage θ E k) a < θ then
    (peelStage θ E k).filter (fun e => e.1 = a) else ∅ with ht
  have hown : ownedL θ E a = (range E.card).biUnion t := rfl
  have hempty : ∀ k, degL (peelStage θ E k) a = 0 ∨ θ ≤ degL (peelStage θ E k) a →
      t k = ∅ := by
    intro k hk
    simp only [ht]
    split_ifs with hlt
    · rcases hk with h0 | hge
      · exact card_eq_zero.1 h0
      · omega
    · rfl
  have hcard : ∀ k, (t k).card ≤ degL (peelStage θ E k) a := by
    intro k
    simp only [ht]
    split_ifs
    · exact le_rfl
    · simp
  have hlater : ∀ k l, degL (peelStage θ E k) a < θ → k < l →
      degL (peelStage θ E l) a = 0 := by
    intro k l hk hkl
    have hsub : peelStage θ E l ⊆ peelStage θ E (k + 1) := peelStage_antitone θ E hkl
    have h0 : (peelStage θ E (k + 1)).filter (fun e => e.1 = a) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he hea
      rw [peelStage_succ] at he
      have := (mem_filter.1 he).2.1
      rw [hea] at this
      omega
    have := card_le_card (filter_subset_filter (fun e : α × β => e.1 = a) hsub)
    rw [h0, card_empty] at this
    unfold degL
    omega
  by_cases h : ∃ k, k < E.card ∧ 0 < degL (peelStage θ E k) a ∧ degL (peelStage θ E k) a < θ
  · obtain ⟨hk₀E, hk₀pos, hk₀lt⟩ := Nat.find_spec h
    have hsub : ownedL θ E a ⊆ t (Nat.find h) := by
      rw [hown]
      apply biUnion_subset.2
      intro k hk
      rcases lt_trichotomy k (Nat.find h) with hlt | heq | hgt
      · have hmin := Nat.find_min h hlt
        rw [hempty k ?_]
        · exact empty_subset _
        · have hkE : k < E.card := mem_range.1 hk
          by_contra hc
          simp only [not_or, not_le] at hc
          exact hmin ⟨hkE, Nat.pos_of_ne_zero hc.1, hc.2⟩
      · rw [heq]
      · rw [hempty k (Or.inl (hlater _ k hk₀lt hgt))]
        exact empty_subset _
    calc (ownedL θ E a).card ≤ (t (Nat.find h)).card := card_le_card hsub
      _ ≤ degL (peelStage θ E (Nat.find h)) a := hcard _
      _ < θ := hk₀lt
  · have : ownedL θ E a = ∅ := by
      rw [hown]
      refine subset_empty.1 fun e he => ?_
      obtain ⟨k, hk, hek⟩ := mem_biUnion.1 he
      rwa [hempty k ?_] at hek
      by_contra hc
      simp only [not_or, not_le] at hc
      exact h ⟨k, mem_range.1 hk, Nat.pos_of_ne_zero hc.1, hc.2⟩
    rw [this, card_empty]
    exact hθ

/-- **A right vertex owns fewer than `θ` edges** (for `θ > 0`).

Proof sketch: symmetric to `card_ownedL_lt` with `degR` and the second coordinate.
Reference: tex 1703-1706; blueprint L30. -/
theorem card_ownedR_lt {θ : ℕ} (hθ : 0 < θ) (E : Finset (α × β)) (b : β) :
    (ownedR θ E b).card < θ := by
  classical
  set t : ℕ → Finset (α × β) := fun k => if degR (peelStage θ E k) b < θ then
    (peelStage θ E k).filter (fun e => e.2 = b) else ∅ with ht
  have hown : ownedR θ E b = (range E.card).biUnion t := rfl
  have hempty : ∀ k, degR (peelStage θ E k) b = 0 ∨ θ ≤ degR (peelStage θ E k) b →
      t k = ∅ := by
    intro k hk
    simp only [ht]
    split_ifs with hlt
    · rcases hk with h0 | hge
      · exact card_eq_zero.1 h0
      · omega
    · rfl
  have hcard : ∀ k, (t k).card ≤ degR (peelStage θ E k) b := by
    intro k
    simp only [ht]
    split_ifs
    · exact le_rfl
    · simp
  have hlater : ∀ k l, degR (peelStage θ E k) b < θ → k < l →
      degR (peelStage θ E l) b = 0 := by
    intro k l hk hkl
    have hsub : peelStage θ E l ⊆ peelStage θ E (k + 1) := peelStage_antitone θ E hkl
    have h0 : (peelStage θ E (k + 1)).filter (fun e => e.2 = b) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he hea
      rw [peelStage_succ] at he
      have := (mem_filter.1 he).2.2
      rw [hea] at this
      omega
    have := card_le_card (filter_subset_filter (fun e : α × β => e.2 = b) hsub)
    rw [h0, card_empty] at this
    unfold degR
    omega
  by_cases h : ∃ k, k < E.card ∧ 0 < degR (peelStage θ E k) b ∧ degR (peelStage θ E k) b < θ
  · obtain ⟨hk₀E, hk₀pos, hk₀lt⟩ := Nat.find_spec h
    have hsub : ownedR θ E b ⊆ t (Nat.find h) := by
      rw [hown]
      apply biUnion_subset.2
      intro k hk
      rcases lt_trichotomy k (Nat.find h) with hlt | heq | hgt
      · have hmin := Nat.find_min h hlt
        rw [hempty k ?_]
        · exact empty_subset _
        · have hkE : k < E.card := mem_range.1 hk
          by_contra hc
          simp only [not_or, not_le] at hc
          exact hmin ⟨hkE, Nat.pos_of_ne_zero hc.1, hc.2⟩
      · rw [heq]
      · rw [hempty k (Or.inl (hlater _ k hk₀lt hgt))]
        exact empty_subset _
    calc (ownedR θ E b).card ≤ (t (Nat.find h)).card := card_le_card hsub
      _ ≤ degR (peelStage θ E (Nat.find h)) b := hcard _
      _ < θ := hk₀lt
  · have : ownedR θ E b = ∅ := by
      rw [hown]
      refine subset_empty.1 fun e he => ?_
      obtain ⟨k, hk, hek⟩ := mem_biUnion.1 he
      rwa [hempty k ?_] at hek
      by_contra hc
      simp only [not_or, not_le] at hc
      exact h ⟨k, mem_range.1 hk, Nat.pos_of_ne_zero hc.1, hc.2⟩
    rw [this, card_empty]
    exact hθ

/-- **Node L30, `canonicalPeel`.**  The core is contained in `E`; every core edge has both endpoint
degrees in the core at least `θ`; every deleted edge is owned by one of its endpoints; owned edges
are edges of `E` at their owner; and for `θ > 0` every vertex owns fewer than `θ` edges. -/
theorem canonicalPeel (θ : ℕ) (E : Finset (α × β)) :
    peelCore θ E ⊆ E ∧
      (∀ e ∈ peelCore θ E, θ ≤ degL (peelCore θ E) e.1 ∧ θ ≤ degR (peelCore θ E) e.2) ∧
      (∀ e ∈ E, e ∉ peelCore θ E → e ∈ ownedL θ E e.1 ∨ e ∈ ownedR θ E e.2) ∧
      (∀ (a : α) (e : α × β), e ∈ ownedL θ E a → e ∈ E ∧ e.1 = a) ∧
      (∀ (b : β) (e : α × β), e ∈ ownedR θ E b → e ∈ E ∧ e.2 = b) ∧
      (0 < θ → ∀ a : α, (ownedL θ E a).card < θ) ∧ (0 < θ → ∀ b : β, (ownedR θ E b).card < θ) :=
  ⟨peelCore_subset θ E, fun _ he => le_deg_of_mem_peelCore he,
    fun _ he hc => mem_owned_of_not_mem_peelCore he hc, fun _ _ he => mem_ownedL he,
    fun _ _ he => mem_ownedR he, fun hθ a => card_ownedL_lt hθ E a,
    fun hθ b => card_ownedR_lt hθ E b⟩

omit [DecidableEq β] in
/-- **Minimum degree counting**: if every edge of `F` has left degree at least `θ` then
`θ |F.image fst| ≤ |F|`.

Proof sketch: `card_eq_sum_card_image Prod.fst F` writes `|F|` as the sum over left vertices `a`
of `|F.filter (·.1 = a)| = degL F a ≥ θ` (each `a` is the first coordinate of some edge); compare
with `sum_const` (`card_nsmul_le_sum`).
Reference: tex 1745-1747 ("Minimum degree implies"); node L33. -/
theorem mul_card_image_fst_le {θ : ℕ} {F : Finset (α × β)}
    (h : ∀ e ∈ F, θ ≤ degL F e.1) : θ * (F.image Prod.fst).card ≤ F.card := by
  rw [card_eq_sum_card_image Prod.fst F, mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro a ha
  obtain ⟨e, he, rfl⟩ := mem_image.1 ha
  exact h e he

omit [DecidableEq α] in
/-- **Minimum degree counting, right side**: `θ |F.image snd| ≤ |F|`.

Proof sketch: symmetric to `mul_card_image_fst_le`.
Reference: tex 1745-1747; node L33. -/
theorem mul_card_image_snd_le {θ : ℕ} {F : Finset (α × β)}
    (h : ∀ e ∈ F, θ ≤ degR F e.2) : θ * (F.image Prod.snd).card ≤ F.card := by
  rw [card_eq_sum_card_image Prod.snd F, mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro b hb
  obtain ⟨e, he, rfl⟩ := mem_image.1 hb
  exact h e he

end Peel

end Kolmogorov.StrongMerging.Lower
