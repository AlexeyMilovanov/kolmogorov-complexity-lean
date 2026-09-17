import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.SufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseTruncation

/-!
# Padding a model with uniform noise

`finiteSetPairUniformExtension A l` is the set of pair codes of a member of `A` with an
arbitrary string of length `l`: the model `A` padded with `l` bits of uniform noise.  Its
elementary properties — nonemptiness, cardinality `|A| * 2 ^ l`, log-cardinality
(`finiteSetPairUniformExtension_card`, `…_logCard_le`) — are what the add-noise argument uses
on the size side.

On the complexity side, `finiteSetPairUniformExtensionCode` computes the canonical code of the
extension from the code of `A` and the number `l`, and the plain decompressor
`finiteSetPairUniformExtensionPlainDecompressor` runs a program for the code of `A` and
outputs the code of its extension, giving `plainK_finiteSetPairUniformExtensionCode_le` and
`finiteSetPairUniformExtension_plainSetComplexity_le`: padding costs the complexity of `A`
plus the bits of `l`.  `logSlack_visible_scale_of_bounds` is the slack arithmetic that keeps
the estimate at one visible budget.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- Logarithmic slack in a sum of five quantities bounded by `M` is at most
logarithmic slack in `M` with constant `5 * c + 5`. -/
lemma logSlack_visible_scale_of_bounds (c M xlen ylen i j k : ℕ)
    (hx : xlen ≤ M) (hy : ylen ≤ M) (hi : i ≤ M) (hj : j ≤ M) (hk : k ≤ M) :
    logSlack c (xlen + ylen + i + j + k) ≤ logSlack (5 * c + 5) M := by
  calc
    logSlack c (xlen + ylen + i + j + k)
      ≤ logSlack c (xlen + ylen + i + j) + logSlack c k := logSlack_add_le c _ _
    _ ≤ logSlack c (xlen + ylen + i) + logSlack c j + logSlack c k := by
        gcongr; exact logSlack_add_le c _ _
    _ ≤ logSlack c (xlen + ylen) + logSlack c i + logSlack c j + logSlack c k := by
        gcongr; exact logSlack_add_le c _ _
    _ ≤ logSlack c xlen + logSlack c ylen + logSlack c i + logSlack c j + logSlack c k := by
        gcongr; exact logSlack_add_le c _ _
    _ ≤ logSlack c M + logSlack c M + logSlack c M + logSlack c M + logSlack c M := by
        gcongr
        · exact logSlack_mono_right c hx
        · exact logSlack_mono_right c hy
        · exact logSlack_mono_right c hi
        · exact logSlack_mono_right c hj
        · exact logSlack_mono_right c hk
    _ = 5 * logSlack c M := by ring
    _ ≤ logSlack (5 * c + 5) M := by
        dsimp [logSlack]
        nlinarith [Nat.zero_le (Nat.bits M).length, Nat.zero_le c]

/-- The set of pair codes of a member of `A` with an arbitrary string of length `l`. -/
def finiteSetPairUniformExtension (A : Finset BitString) (l : ℕ) : Finset BitString :=
  (A ×ˢ stringsOfLength l).image (fun p => pairCode p.1 p.2)

/-- Pairing a member of `A` with a string of length `l` lands in the extension. -/
theorem finiteSetPairUniformExtension_mem
    {A : Finset BitString} {x y : BitString} {l : ℕ}
    (hx : x ∈ A) (hy : y.length = l) :
    pairCode x y ∈ finiteSetPairUniformExtension A l := by
  rw [finiteSetPairUniformExtension, Finset.mem_image]
  refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, ?_⟩, rfl⟩
  exact mem_stringsOfLength _ _ |>.mpr hy

/-- The extension of a nonempty set is nonempty. -/
theorem finiteSetPairUniformExtension_nonempty
    {A : Finset BitString} (hA : A.Nonempty) (l : ℕ) :
    (finiteSetPairUniformExtension A l).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  have hy : (List.replicate l false).length = l := by simp
  exact ⟨_, finiteSetPairUniformExtension_mem hx hy⟩

/-- The extension has `|A| * 2 ^ l` elements. -/
theorem finiteSetPairUniformExtension_card
    (A : Finset BitString) (l : ℕ) :
    (finiteSetPairUniformExtension A l).card = A.card * 2 ^ l := by
  rw [finiteSetPairUniformExtension, Finset.card_image_of_injective]
  · rw [Finset.card_product, card_stringsOfLength]
  · intro p1 p2 hp
    exact pairCode_injective hp

/-- The log-cardinality of the extension is at most that of `A` plus `l`. -/
theorem finiteSetPairUniformExtension_logCard_le
    (A : Finset BitString) (l : ℕ) :
    finiteSetLogCard (finiteSetPairUniformExtension A l) ≤ finiteSetLogCard A + l := by
  rw [finiteSetLogCard_le_iff, finiteSetPairUniformExtension_card, pow_add]
  exact Nat.mul_le_mul_right (2 ^ l) (finiteSetLogCard_spec A)

/-- The canonical code of the extension, computed from the code of `A` and the code
of `l`. -/
noncomputable def finiteSetPairUniformExtensionCode (w l_code : BitString) : BitString :=
  canonicalImageCodeOfList
    ((canonicalPointListOfCode w).flatMap
      (fun x => (allStrings (bitsToNat l_code)).map
        (fun y => pairCode x y)))

/-- Computing the code of the extension is computable in the two arguments. -/
theorem finiteSetPairUniformExtensionCode_computable :
    Computable₂ finiteSetPairUniformExtensionCode := by
  have hpoints : Primrec (fun p : BitString × BitString =>
      canonicalPointListOfCode p.1) :=
    canonicalPointListOfCode_primrec.comp Primrec.fst
  have hlength : Primrec (fun p : BitString × BitString => bitsToNat p.2) :=
    bitsToNat_primrec.comp Primrec.snd
  have hblock : Primrec (fun q : (BitString × BitString) × BitString =>
      (allStrings (bitsToNat q.1.2)).map (fun y => pairCode q.2 y)) := by
    refine Primrec.list_map
      (allStrings_primrec.comp (hlength.comp Primrec.fst)) ?_
    exact (pairCode_primrec.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hflat : Primrec (fun p : BitString × BitString =>
      (canonicalPointListOfCode p.1).flatMap
        (fun x => (allStrings (bitsToNat p.2)).map
          (fun y => pairCode x y))) :=
    Primrec.list_flatMap hpoints hblock.to₂
  exact (canonicalImageCodeOfList_primrec.comp hflat).to_comp.to₂

/-- Listing all pairs of a member of `A` with a length-`l` string yields exactly the
extension. -/
theorem finiteSetPairUniformExtension_list_toFinset
    (A : Finset BitString) (l : ℕ) :
    ((canonicalFinsetList A).flatMap
      (fun x => (allStrings l).map (fun y => pairCode x y))).toFinset =
        finiteSetPairUniformExtension A l := by
  ext z
  simp only [finiteSetPairUniformExtension, List.mem_toFinset,
    List.mem_flatMap, mem_canonicalFinsetList, List.mem_map, mem_allStrings,
    Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, (mem_stringsOfLength l b).mpr hb⟩, rfl⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, (mem_stringsOfLength l b).mp hb, rfl⟩

/-- On the canonical code of `A` the extension function returns the canonical code
of the extension. -/
theorem finiteSetPairUniformExtensionCode_codedUniformOn
    (A : Finset BitString) (hA : A.Nonempty) (l : ℕ) :
    finiteSetPairUniformExtensionCode
        (codedUniformOn A hA).code (Nat.bits l) =
      (codedUniformOn (finiteSetPairUniformExtension A l)
        (finiteSetPairUniformExtension_nonempty hA l)).code := by
  let L := (canonicalFinsetList A).flatMap
    (fun x => (allStrings l).map (fun y => pairCode x y))
  have hL : L.toFinset.Nonempty := by
    rw [finiteSetPairUniformExtension_list_toFinset]
    exact finiteSetPairUniformExtension_nonempty hA l
  unfold finiteSetPairUniformExtensionCode
  simp only [canonicalPointListOfCode_codedUniformOn, bitsToNat_bits]
  change canonicalImageCodeOfList L = _
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hL]
  exact codedUniformOn_code_congr hL
    (finiteSetPairUniformExtension_nonempty hA l)
    (finiteSetPairUniformExtension_list_toFinset A l)

/-- The decompressor that runs a program for the code of `A` and outputs the code of
its length-`l` extension. -/
noncomputable def finiteSetPairUniformExtensionPlainDecompressor (V : Map) : Map :=
  fun pr => (V (decodeSecond pr.1, [])).map (fun Acode =>
    finiteSetPairUniformExtensionCode Acode (decodeFirst pr.1))

/-- That decompressor is a decompressor. -/
theorem finiteSetPairUniformExtensionPlainDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (finiteSetPairUniformExtensionPlainDecompressor V) := by
  unfold finiteSetPairUniformExtensionPlainDecompressor
  refine Partrec.map ?_ ?_
  · exact Partrec.comp hV
      (Computable.pair (decodeSecond_computable.comp Computable.fst)
        (Computable.const []))
  · exact finiteSetPairUniformExtensionCode_computable.comp Computable.snd
      (decodeFirst_computable.comp (Computable.fst.comp Computable.fst))

/-- A program producing the code of `A`, prefixed by `l`, produces the code of the
extension. -/
theorem finiteSetPairUniformExtensionPlainDecompressor_produces
    (V : Map) (Acode p : BitString) (l : ℕ)
    (h : produces V p [] Acode) :
    produces (finiteSetPairUniformExtensionPlainDecompressor V)
      (pairCode (Nat.bits l) p) []
      (finiteSetPairUniformExtensionCode Acode (Nat.bits l)) := by
  unfold produces finiteSetPairUniformExtensionPlainDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode]
  exact (Part.mem_map_iff _).2 ⟨Acode, h, rfl⟩

/-- The code of the extension has plain complexity at most that of the code of `A`
plus logarithmic slack in `l`. -/
theorem plainK_finiteSetPairUniformExtensionCode_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (Acode : BitString) (l : ℕ),
      plainK V (finiteSetPairUniformExtensionCode Acode (Nat.bits l)) ≤
        plainK V Acode + (logSlack c l : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2
    (finiteSetPairUniformExtensionPlainDecompressor V)
    (finiteSetPairUniformExtensionPlainDecompressor_partrec V hV.1)
  refine ⟨cSim + 2, fun Acode l => ?_⟩
  set M : ℕ := 2 * (Nat.bits l).length + 1 with hM
  clear_value M
  have hbound :
      condK (finiteSetPairUniformExtensionPlainDecompressor V)
          (finiteSetPairUniformExtensionCode Acode (Nat.bits l)) [] ≤
        condK V Acode [] + (M : ENat) := by
    apply sInfLeSInfAdd
    rintro s₂ ⟨p, hp, rfl⟩
    refine ⟨(programLength (pairCode (Nat.bits l) p) : ENat),
      ⟨pairCode (Nat.bits l) p,
        finiteSetPairUniformExtensionPlainDecompressor_produces
          V Acode p l hp, rfl⟩, ?_⟩
    have hlen : (pairCode (Nat.bits l) p).length ≤ p.length + M := by
      rw [length_pairCode, hM]
      omega
    exact_mod_cast hlen
  calc
    plainK V (finiteSetPairUniformExtensionCode Acode (Nat.bits l))
        ≤ condK (finiteSetPairUniformExtensionPlainDecompressor V)
            (finiteSetPairUniformExtensionCode Acode (Nat.bits l)) [] +
            (cSim : ENat) := hSim _ _
    _ ≤ (condK V Acode [] + (M : ENat)) + (cSim : ENat) := by gcongr
    _ = plainK V Acode + ((M : ENat) + (cSim : ENat)) := by
        change (condK V Acode [] + (M : ENat)) + (cSim : ENat) =
          condK V Acode [] + ((M : ENat) + (cSim : ENat))
        rw [add_assoc]
    _ ≤ plainK V Acode + (logSlack (cSim + 2) l : ENat) := by
        gcongr
        have hle : M + cSim ≤ logSlack (cSim + 2) l := by
          rw [hM]
          unfold logSlack
          nlinarith [Nat.zero_le (cSim * (Nat.bits l).length)]
        calc
          (M : ENat) + (cSim : ENat) = ((M + cSim : ℕ) : ENat) := by norm_cast
          _ ≤ (logSlack (cSim + 2) l : ENat) := by exact_mod_cast hle

/-- The extension has plain set complexity at most that of `A` plus logarithmic
slack in `l`. -/
theorem finiteSetPairUniformExtension_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (l : ℕ),
      plainSetComplexity V (finiteSetPairUniformExtension A l)
          (finiteSetPairUniformExtension_nonempty hA l) ≤
        plainSetComplexity V A hA + logSlack c l := by
  obtain ⟨c, hc⟩ := plainK_finiteSetPairUniformExtensionCode_le V hV
  refine ⟨c, fun A hA l => ?_⟩
  unfold plainSetComplexity
  rw [← finiteSetPairUniformExtensionCode_codedUniformOn A hA l]
  exact hc (codedUniformOn A hA).code l

end Kolmogorov
