import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseProduct

/-!
# Strong models of a canonical pair

Two families of strong (total-computable) finite-set models of the canonical
pair `pairCode y z` are built here.

* the *uniform noise extension* `S ⊗ {0,1}^{|z|}` of a strong model `S` of the
  head `y`;
* the *tail cube* `{pairCode y (w ++ u) : |u| = t}` obtained by keeping a
  prefix `w` of the tail `z` and letting the last `t` bits vary.

Both are accompanied by the transport lemmas for total conditional complexity
that make them strong models with only a logarithmic strength overhead.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### Generic transport lemmas for total conditional complexity -/

/-- Run a total program at a computable image of the context and post-process
its output with a computable function of the output and the context. -/
def totalTransportDecompressor (T : Map) (f : BitString → BitString)
    (F : BitString → BitString → BitString) : Map :=
  fun pr => (T (pr.1, f pr.2)).map (fun a => F a pr.2)

lemma totalTransportDecompressor_partrec
    (T : Map) (hT : isDecompressor T)
    (f : BitString → BitString) (hf : Computable f)
    (F : BitString → BitString → BitString) (hF : Computable₂ F) :
    isDecompressor (totalTransportDecompressor T f F) := by
  unfold totalTransportDecompressor
  refine Partrec.map ?_ ?_
  · exact Partrec.comp hT
      (Computable.pair Computable.fst (hf.comp Computable.snd))
  · exact hF.comp Computable.snd (Computable.snd.comp Computable.fst)

lemma IsTotalProgram.transport
    {T : Map} {p : BitString} (hp : IsTotalProgram T p)
    (f : BitString → BitString) (F : BitString → BitString → BitString) :
    IsTotalProgram (totalTransportDecompressor T f F) p := by
  intro y
  exact hp (f y)

lemma totalCondK_transport_le
    (T : Map) (f : BitString → BitString)
    (F : BitString → BitString → BitString) (a x : BitString) :
    totalCondK (totalTransportDecompressor T f F) (F a x) x ≤
      totalCondK T a (f x) := by
  apply sInf_le_sInf
  rintro _ ⟨p, hp_total, hp_prod, rfl⟩
  refine ⟨p, hp_total.transport f F, ?_, rfl⟩
  change F a x ∈ Part.map (fun b => F b x) (T (p, f x))
  exact (Part.mem_map_iff _).2 ⟨a, hp_prod, rfl⟩

/-- **Transport of strong models.**  A total description of `a` from `f x`
yields a total description of `F a x` from `x`, at the cost of one uniform
additive constant. -/
theorem totalCondK_transport_bound
    (T : Map) (hT : IsOptimalTotalConditional T)
    (f : BitString → BitString) (hf : Computable f)
    (F : BitString → BitString → BitString) (hF : Computable₂ F) :
    ∃ c : Nat, ∀ a x : BitString,
      totalCondK T (F a x) x ≤ totalCondK T a (f x) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hT.2 (totalTransportDecompressor T f F)
    (totalTransportDecompressor_partrec T hT.1 f hf F hF)
  refine ⟨c, fun a x => ?_⟩
  calc totalCondK T (F a x) x
      ≤ totalCondK (totalTransportDecompressor T f F) (F a x) x + (c : ENat) :=
        hc _ _
    _ ≤ totalCondK T a (f x) + (c : ENat) := by
        gcongr
        exact totalCondK_transport_le T f F a x

/-- A decompressor that computes a fixed computable function of its program
and its context. -/
def totalParamDecompressor (G : BitString → BitString → BitString) : Map :=
  fun pr => Part.some (G pr.1 pr.2)

lemma totalParamDecompressor_partrec
    (G : BitString → BitString → BitString) (hG : Computable₂ G) :
    isDecompressor (totalParamDecompressor G) :=
  Computable.partrec (hG.comp Computable.fst Computable.snd)

/-- **Parameterized computable models are strong.**  Any computable function of
a short parameter and the displayed string has total conditional complexity at
most the length of the parameter, up to a uniform constant. -/
theorem totalCondK_param_le
    (T : Map) (hT : IsOptimalTotalConditional T)
    (G : BitString → BitString → BitString) (hG : Computable₂ G) :
    ∃ c : Nat, ∀ p x : BitString,
      totalCondK T (G p x) x ≤ (programLength p : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hT.2 (totalParamDecompressor G)
    (totalParamDecompressor_partrec G hG)
  refine ⟨c, fun p x => ?_⟩
  have hle : totalCondK (totalParamDecompressor G) (G p x) x ≤
      (programLength p : ENat) := by
    refine totalCondK_le_programLength (D := totalParamDecompressor G)
      (p := p) (x := G p x) (y := x) (fun _ => trivial) ?_
    exact ⟨trivial, rfl⟩
  calc totalCondK T (G p x) x
      ≤ totalCondK (totalParamDecompressor G) (G p x) x + (c : ENat) := hc _ _
    _ ≤ (programLength p : ENat) + (c : ENat) := by gcongr

/-! ### The uniform noise extension is a strong model of the pair -/

/-- **Strong version of the uniform noise extension.**  Extending a strong
model `A` of the head `y` by the full noise cube of length `|z|` gives a strong
model of `pairCode y z` with only a constant strength overhead: the extension
is computed from `A` and the pair itself. -/
theorem finiteSetPairUniformExtension_isStrongSetModel
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (A : Finset BitString) (hA : A.Nonempty) (y z : BitString)
        (e : Nat),
      IsStrongSetModel T y A hA e →
      IsStrongSetModel T (pairCode y z)
        (finiteSetPairUniformExtension A z.length)
        (finiteSetPairUniformExtension_nonempty hA z.length) (e + c) := by
  have hbits : Computable (fun x : BitString => Nat.bits (decodeSecond x).length) :=
    (primrecNatBits.comp (Primrec.list_length.comp decodeSecond_primrec)).to_comp
  have hF : Computable₂ (fun a x : BitString =>
      finiteSetPairUniformExtensionCode a (Nat.bits (decodeSecond x).length)) :=
    finiteSetPairUniformExtensionCode_computable.comp Computable.fst
      (hbits.comp Computable.snd)
  obtain ⟨c, hc⟩ := totalCondK_transport_bound T hT decodeFirst
    decodeFirst_computable _ hF
  refine ⟨c, ?_⟩
  intro A hA y z e hS
  have hcode :
      finiteSetPairUniformExtensionCode (codedUniformOn A hA).code
          (Nat.bits (decodeSecond (pairCode y z)).length) =
        (codedUniformOn (finiteSetPairUniformExtension A z.length)
          (finiteSetPairUniformExtension_nonempty hA z.length)).code := by
    rw [decodeSecond_pairCode]
    exact finiteSetPairUniformExtensionCode_codedUniformOn A hA z.length
  unfold IsStrongSetModel
  rw [← hcode]
  calc totalCondK T
        (finiteSetPairUniformExtensionCode (codedUniformOn A hA).code
          (Nat.bits (decodeSecond (pairCode y z)).length)) (pairCode y z)
      ≤ totalCondK T (codedUniformOn A hA).code
          (decodeFirst (pairCode y z)) + (c : ENat) := hc _ _
    _ = totalCondK T (codedUniformOn A hA).code y + (c : ENat) := by
        rw [decodeFirst_pairCode]
    _ ≤ (e : ENat) + (c : ENat) := by gcongr; exact hS
    _ = ((e + c : Nat) : ENat) := by push_cast; ring

/-! ### Tail cubes -/

/-- The tail cube: the head `y` and the prefix `w` of the tail are fixed, the
last `t` bits of the tail range over the full cube. -/
def pairTailCube (y w : BitString) (t : ℕ) : Finset BitString :=
  (stringsOfLength t).image (fun u => pairCode y (w ++ u))

theorem pairTailCube_mem {y w u : BitString} {t : ℕ} (hu : u.length = t) :
    pairCode y (w ++ u) ∈ pairTailCube y w t := by
  rw [pairTailCube, Finset.mem_image]
  exact ⟨u, (memStringsOfLength t u).mpr hu, rfl⟩

theorem pairTailCube_nonempty (y w : BitString) (t : ℕ) :
    (pairTailCube y w t).Nonempty :=
  ⟨_, pairTailCube_mem (u := List.replicate t false) (by simp)⟩

theorem pairTailCube_card_le (y w : BitString) (t : ℕ) :
    (pairTailCube y w t).card ≤ 2 ^ t := by
  refine le_trans (Finset.card_image_le) ?_
  rw [cardStringsOfLength]

/-- Canonical code of the tail cube described by
`pairCode (pairCode y w) (Nat.bits t)`. -/
noncomputable def pairTailCubeCode (v : BitString) : BitString :=
  canonicalImageCodeOfList
    ((allStrings (bitsToNat (decodeSecond v))).map
      (fun u => pairCode (decodeFirst (decodeFirst v))
        (decodeSecond (decodeFirst v) ++ u)))

theorem pairTailCubeCode_computable : Computable pairTailCubeCode := by
  have hlist : Primrec (fun v : BitString =>
      allStrings (bitsToNat (decodeSecond v))) :=
    allStrings_primrec.comp (bitsToNat_primrec.comp decodeSecond_primrec)
  have hmapf : Primrec₂ (fun (v u : BitString) =>
      pairCode (decodeFirst (decodeFirst v))
        (decodeSecond (decodeFirst v) ++ u)) :=
    pairCode_primrec.comp
      ((decodeFirst_primrec.comp decodeFirst_primrec).comp Primrec.fst)
      (Primrec.list_append.comp
        ((decodeSecond_primrec.comp decodeFirst_primrec).comp Primrec.fst)
        Primrec.snd)
  exact (canonicalImageCodeOfList_primrec.comp
    (Primrec.list_map hlist hmapf)).to_comp

theorem pairTailCube_toFinset (y w : BitString) (t : ℕ) :
    ((allStrings t).map (fun u => pairCode y (w ++ u))).toFinset =
      pairTailCube y w t := by
  ext v
  simp only [List.mem_toFinset, List.mem_map, mem_allStrings, pairTailCube,
    Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, (memStringsOfLength t u).mpr hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, (memStringsOfLength t u).mp hu, rfl⟩

theorem pairTailCubeCode_eq (y w : BitString) (t : ℕ) :
    pairTailCubeCode (pairCode (pairCode y w) (Nat.bits t)) =
      (codedUniformOn (pairTailCube y w t) (pairTailCube_nonempty y w t)).code := by
  unfold pairTailCubeCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]
  set L := (allStrings t).map (fun u => pairCode y (w ++ u)) with hL
  have hLne : L.toFinset.Nonempty := by
    rw [hL, pairTailCube_toFinset]
    exact pairTailCube_nonempty y w t
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hLne]
  exact codedUniformOn_code_congr hLne (pairTailCube_nonempty y w t)
    (by rw [hL, pairTailCube_toFinset])

/-- The plain set complexity of a tail cube is bounded by the plain complexity
of the pair `((y, w), t)`. -/
theorem pairTailCube_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (y w : BitString) (t : ℕ),
      plainSetComplexity V (pairTailCube y w t) (pairTailCube_nonempty y w t) ≤
        plainK V (pairCode (pairCode y w) (Nat.bits t)) + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe V hV pairTailCubeCode pairTailCubeCode_computable
  refine ⟨c, fun y w t => ?_⟩
  unfold plainSetComplexity
  rw [← pairTailCubeCode_eq y w t]
  exact hc _

/-- Tail cubes of the displayed pair are strong models: they are computed from
the pair and the number `t` of varying bits. -/
theorem pairTailCube_isStrongSetModel
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : ℕ, ∀ (y z : BitString) (t : ℕ),
      IsStrongSetModel T (pairCode y z)
        (pairTailCube y (z.take (z.length - t)) t)
        (pairTailCube_nonempty _ _ _) ((Nat.bits t).length + c) := by
  have hG : Computable₂ (fun p x : BitString =>
      pairTailCubeCode (pairCode (pairCode (decodeFirst x)
        ((decodeSecond x).take ((decodeSecond x).length - bitsToNat p))) p)) := by
    have hinner : Primrec (fun q : BitString × BitString =>
        pairCode (decodeFirst q.2)
          ((decodeSecond q.2).take
            ((decodeSecond q.2).length - bitsToNat q.1))) :=
      pairCode_primrec.comp (decodeFirst_primrec.comp Primrec.snd)
        (Primrec.list_take.comp (decodeSecond_primrec.comp Primrec.snd)
          (Primrec.nat_sub.comp
            (Primrec.list_length.comp (decodeSecond_primrec.comp Primrec.snd))
            (bitsToNat_primrec.comp Primrec.fst)))
    have houter : Computable (fun q : BitString × BitString =>
        pairTailCubeCode (pairCode (pairCode (decodeFirst q.2)
          ((decodeSecond q.2).take
            ((decodeSecond q.2).length - bitsToNat q.1))) q.1)) :=
      pairTailCubeCode_computable.comp
        (pairCode_primrec.comp hinner Primrec.fst).to_comp
    exact houter.to₂
  obtain ⟨c, hc⟩ := totalCondK_param_le T hT _ hG
  refine ⟨c, fun y z t => ?_⟩
  have hval := hc (Nat.bits t) (pairCode y z)
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits] at hval
  rw [pairTailCubeCode_eq] at hval
  unfold IsStrongSetModel
  refine hval.trans ?_
  have : (programLength (Nat.bits t) : ENat) + (c : ENat)
      = (((Nat.bits t).length + c : ℕ) : ENat) := by
    push_cast
    rfl
  exact le_of_eq this

end Kolmogorov
