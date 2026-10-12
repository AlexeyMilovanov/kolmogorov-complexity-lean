import KolmogorovMathlib.StrongMerging.Basic
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CanonicalImage
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2

/-!
# Strong merging, coding foundation I: finite encodings (nodes U01, L01)

The finite-object layer of the strong-merging formalization (`sublinear-merging.tex`, appendix
"Interfaces, conventions, and the trusted foundation boundary", and lower-bound blueprint
paragraph "L01: `cubeModelEncoding`").

* **U01, `UpperFiniteEncodings`.**  Models are finite sets of binary strings of arbitrary
  lengths.  Their canonical code is the library's `canonicalFiniteSetCode` (the same code under
  `setC`, `plainSetComplexity` and `IsStrongSetModel`, see `StrongMerging.Basic`).  We add the
  total decoder `decodeModel`, the computable list encoder `listModelCode`, the computable
  membership test `modelMem` and the side-tagged endpoint labels `endpointCode` of the
  incidence graph.  Malformed codes decode through the library's total syntactic decoder
  `canonicalPointListOfCode`, which is the explicit default.
* **L01, `cubeModelEncoding`.**  The cube `Fin M → Bool` is read as binary words of length `M`
  (`cubeWord`, `wordCube`), concatenation of two `M`-words is inverted by `splitWord`, and a
  finite subset of the cube is encoded as the ordinary model of its words (`cubeModelCode`), so
  cube models are ordinary models and not a parallel type.
-/

namespace Kolmogorov.StrongMerging

/-! ### U01: canonical model encoding and decoding -/

/-- **The total model decoder** (node U01).  A binary word decodes to the finite set of the points
listed by the library's total syntactic decoder `canonicalPointListOfCode`.  It is defined on every
word: on a malformed word it returns the set of whatever that decoder lists, which is the explicit
malformed-input default. -/
noncomputable def decodeModel (w : BitString) : Finset BitString :=
  (canonicalPointListOfCode w).toFinset

/-- Parsing the canonical code of a model recovers the model. -/
@[simp] theorem decodeModel_canonicalFiniteSetCode (F : Finset BitString) :
    decodeModel (canonicalFiniteSetCode F) = F := by
  rw [decodeModel, canonicalPointListOfCode_canonicalFiniteSetCode, canonicalFinsetList_toFinset]

/-- The membership test of a string `x` in the model decoded from the word `w`. -/
noncomputable def modelMem (w x : BitString) : Bool :=
  decide (x ∈ canonicalPointListOfCode w)

/-- `modelMem w x` tests membership of `x` in `decodeModel w`. -/
theorem modelMem_eq_true_iff (w x : BitString) : modelMem w x = true ↔ x ∈ decodeModel w := by
  simp [modelMem, decodeModel]

/-- The canonical model encoder read on a list of points: the code of the set of its entries.
Duplicates and the order of the list do not matter (`listModelCode_eq`). -/
noncomputable def listModelCode (l : List BitString) : BitString :=
  canonicalFiniteSetCode l.toFinset

/-- The list encoder computes the canonical code of the set of the listed points. -/
theorem listModelCode_eq (l : List BitString) (F : Finset BitString) (h : l.toFinset = F) :
    listModelCode l = canonicalFiniteSetCode F := by
  rw [listModelCode, h]

/-- The canonical model encoder, read on lists, is computable.

Reference: blueprint node U01 ("canonical encoders and parsers"). -/
theorem listModelCode_computable : Computable listModelCode := by
  exact (canonicalUniformCodeOfList_primrec.comp canonicalFinsetList_toFinset_primrec).to_comp

/-- The membership test `modelMem` is computable. -/
theorem modelMem_computable : Computable₂ modelMem := by
  exact (bitString_mem_primrec.comp Primrec.snd
    (canonicalPointListOfCode_primrec.comp Primrec.fst)).to_comp

/-! ### U01: side-tagged endpoint labels -/

/-- The endpoint labels of the bipartite incidence graph: `Sum.inl w` is the left (`A`-side)
vertex with model code `w` and `Sum.inr w` the right (`B`-side) vertex.  The tag keeps the two
sides apart even when their underlying codes coincide. -/
abbrev EndpointLabel := BitString ⊕ BitString

/-- The binary code of an endpoint label: a side bit followed by the model code. -/
def endpointCode : EndpointLabel → BitString
  | .inl w => false :: w
  | .inr w => true :: w

/-- The total decoder of endpoint labels; the empty word decodes to the explicit default
`Sum.inl []`. -/
def endpointDecode : BitString → EndpointLabel
  | [] => .inl []
  | false :: w => .inl w
  | true :: w => .inr w

/-- Decoding inverts the endpoint code. -/
@[simp] theorem endpointDecode_endpointCode (l : EndpointLabel) :
    endpointDecode (endpointCode l) = l := by
  cases l <;> rfl

/-- The endpoint code is injective: the two sides are distinguished. -/
theorem endpointCode_injective : Function.Injective endpointCode :=
  Function.LeftInverse.injective endpointDecode_endpointCode

/-- **Node U01, `UpperFiniteEncodings`.**  The canonical model code is injective and parsed by
the total decoder `decodeModel`; the list encoder, the point decoder and the membership test are
computable; endpoint labels are side-tagged by an injective code with a total left inverse. -/
theorem upperFiniteEncodings :
    Function.Injective canonicalFiniteSetCode ∧
      (∀ F : Finset BitString, decodeModel (canonicalFiniteSetCode F) = F) ∧
      Computable listModelCode ∧ Computable canonicalPointListOfCode ∧
      Computable₂ modelMem ∧ (∀ w x : BitString, modelMem w x = true ↔ x ∈ decodeModel w) ∧
      Function.Injective endpointCode ∧
      (∀ l : EndpointLabel, endpointDecode (endpointCode l) = l) :=
  ⟨canonicalFiniteSetCode_injective, decodeModel_canonicalFiniteSetCode, listModelCode_computable,
    canonicalPointListOfCode_computable, modelMem_computable, modelMem_eq_true_iff,
    endpointCode_injective, endpointDecode_endpointCode⟩

/-! ### L01: the cube and its model encoding -/

namespace Lower

/-- A point of the `M`-cube `Fin M → Bool`, read as a binary word of length `M`. -/
def cubeWord {M : ℕ} (f : Fin M → Bool) : BitString :=
  List.ofFn f

/-- A binary word read as a point of the `M`-cube; positions beyond the end of the word read
`false`, the explicit default for words of the wrong length. -/
def wordCube (M : ℕ) (w : BitString) : Fin M → Bool :=
  fun i => w.getD i false

/-- A cube point is a word of length `M`. -/
@[simp] theorem length_cubeWord {M : ℕ} (f : Fin M → Bool) : (cubeWord f).length = M :=
  List.length_ofFn

/-- Reading back a cube word recovers the cube point. -/
theorem wordCube_cubeWord {M : ℕ} (f : Fin M → Bool) : wordCube M (cubeWord f) = f := by
  funext i
  simp [wordCube, cubeWord, List.getD_eq_getElem?_getD]

/-- A word of length `M` is the cube word of its cube reading. -/
theorem cubeWord_wordCube {M : ℕ} (w : BitString) (hw : w.length = M) :
    cubeWord (wordCube M w) = w := by
  subst hw
  apply List.ext_getElem (by simp [cubeWord])
  intro i h1 h2
  simp [cubeWord, wordCube, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The cube word map is injective. -/
theorem cubeWord_injective {M : ℕ} : Function.Injective (cubeWord (M := M)) :=
  Function.LeftInverse.injective (wordCube_cubeWord (M := M))

/-- Splitting a word after its first `M` letters; on a concatenation of an `M`-word with another
word it recovers the two factors (`splitWord_append`). -/
def splitWord (M : ℕ) (w : BitString) : BitString × BitString :=
  (w.take M, w.drop M)

/-- Splitting a concatenation after the length of its first factor recovers the factors. -/
@[simp] theorem splitWord_append {M : ℕ} {u v : BitString} (hu : u.length = M) :
    splitWord M (u ++ v) = (u, v) := by
  subst hu
  simp [splitWord]

/-- Concatenation of two words, the first of a fixed length `M`, is injective. -/
theorem append_inj_of_length {M : ℕ} {u v u' v' : BitString} (hu : u.length = M)
    (hu' : u'.length = M) (h : u ++ v = u' ++ v') : u = u' ∧ v = v' := by
  have h1 := splitWord_append (v := v) hu
  have h2 := splitWord_append (v := v') hu'
  rw [h] at h1
  rw [h1] at h2
  exact Prod.mk.inj h2

/-- The length of a concatenation of two `M`-words is `2 M`. -/
theorem length_append_of_length {M : ℕ} {u v : BitString} (hu : u.length = M)
    (hv : v.length = M) : (u ++ v).length = 2 * M := by
  rw [List.length_append, hu, hv]
  ring

/-- The ordinary model code of a finite subset of the `M`-cube: the canonical code of the set of
its words.  Cube models are thus ordinary finite models of binary strings. -/
noncomputable def cubeModelCode {M : ℕ} (S : Finset (Fin M → Bool)) : BitString :=
  canonicalFiniteSetCode (S.image cubeWord)

/-- The model decoder recovers the words of an encoded cube model. -/
theorem decodeModel_cubeModelCode {M : ℕ} (S : Finset (Fin M → Bool)) :
    decodeModel (cubeModelCode S) = S.image cubeWord :=
  decodeModel_canonicalFiniteSetCode _

/-- The cube model code is injective. -/
theorem cubeModelCode_injective {M : ℕ} : Function.Injective (cubeModelCode (M := M)) := by
  intro S T h
  have h' := congrArg decodeModel h
  rw [decodeModel_cubeModelCode, decodeModel_cubeModelCode] at h'
  exact (Finset.image_injective cubeWord_injective) h'

/-- **Node L01, `cubeModelEncoding`.**  The cube word map has the left inverse `wordCube` and is a
bijection onto the words of length `M`; concatenation of `M`-words is split by `splitWord`; cube
models are encoded injectively as ordinary models, recovered by `decodeModel`; the endpoint sides
are tagged (`endpointCode_injective`). -/
theorem cubeModelEncoding (M : ℕ) :
    (∀ f : Fin M → Bool, wordCube M (cubeWord f) = f ∧ (cubeWord f).length = M) ∧
      (∀ w : BitString, w.length = M → cubeWord (wordCube M w) = w) ∧
      (∀ u v : BitString, u.length = M → splitWord M (u ++ v) = (u, v)) ∧
      Function.Injective (cubeModelCode (M := M)) ∧
      (∀ S : Finset (Fin M → Bool), decodeModel (cubeModelCode S) = S.image cubeWord) ∧
      Function.Injective endpointCode :=
  ⟨fun f => ⟨wordCube_cubeWord f, length_cubeWord f⟩, fun w hw => cubeWord_wordCube w hw,
    fun _ _ hu => splitWord_append hu, cubeModelCode_injective, decodeModel_cubeModelCode,
    endpointCode_injective⟩

end Lower

end Kolmogorov.StrongMerging
