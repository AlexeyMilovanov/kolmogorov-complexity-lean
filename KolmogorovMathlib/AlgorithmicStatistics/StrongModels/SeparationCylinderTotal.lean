import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.CylinderRealization
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalReduction
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseEnumeration

/-!
# Cylinder codes and their prefixes carry the same total information

VS40 §7 uses repeatedly that the canonical code of a cylinder
`cylinder n y = {z : |z| = n, y ⊑ z}` and its defining prefix `y` are
`O(log n)`-equivalent for total conditional complexity:

* from `y` (with the suffix length as advice) one computes the canonical
  prefix-cube code of `cylinder n y`;
* from that code (with `|y|` as advice) one reads off any listed member and
  truncates it to its first `|y|` bits, recovering `y`.

Both programs are total on every context, so the two directions combine into
`TotalEquivalentWithin T (codedUniformOn (cylinder n y) _).code y (logSlack C n)`
with a constant `C` depending only on the optimal total machine `T`
(`separationCylinder_totalEquivalent_prefix`).
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### From the prefix to the cylinder code -/

/-- Read the program as the binary code of a suffix length `s` and return the
canonical code of the cylinder with prefix the context and suffix length `s`.
This is total for every program and every context. -/
noncomputable def cylinderOfPrefixCode (input : BitString × BitString) : BitString :=
  prefixCubeCode (pairCode input.2 (natCode (decodeBits input.1)))

theorem cylinderOfPrefixCode_computable : Computable cylinderOfPrefixCode := by
  unfold cylinderOfPrefixCode
  exact prefixCubeCode_computable.comp
    ((pairCode_primrec.comp Primrec.snd
      (natCode_primrec.comp (primrecDecodeBits.comp Primrec.fst))).to_comp)

/-- The decompressor computing a cylinder code from its prefix. -/
noncomputable def cylinderOfPrefixDecompressor : Map :=
  fun input => Part.some (cylinderOfPrefixCode input)

theorem cylinderOfPrefixDecompressor_partrec :
    isDecompressor cylinderOfPrefixDecompressor :=
  Computable.partrec cylinderOfPrefixCode_computable

theorem cylinderOfPrefixDecompressor_total (p : BitString) :
    IsTotalProgram cylinderOfPrefixDecompressor p := by
  intro y
  trivial

/-- The canonical prefix-cube encoder produces the canonical uniform code of the
cylinder it names. -/
theorem prefixCubeCode_pairCode_cylinder
    (n : Nat) (u : BitString) (hu : u.length ≤ n)
    (hne : (cylinder n u).Nonempty) :
    prefixCubeCode (pairCode u (natCode (n - u.length))) =
      (codedUniformOn (cylinder n u) hne).code := by
  have hset : prefixCubeSet u (n - u.length) = cylinder n u := by
    rw [prefixCubeSet_eq_cylinder, Nat.add_sub_of_le hu]
  unfold prefixCubeCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeNatCode_natCode]
  rw [hset]
  exact canonicalUniformCodeOfList_canonicalFinsetList (cylinder n u) hne

theorem cylinderOfPrefixDecompressor_produces
    (n : Nat) (u : BitString) (hu : u.length ≤ n)
    (hne : (cylinder n u).Nonempty) :
    produces cylinderOfPrefixDecompressor (Nat.bits (n - u.length)) u
      (codedUniformOn (cylinder n u) hne).code := by
  unfold produces cylinderOfPrefixDecompressor cylinderOfPrefixCode
  simp only [decodeBits_natBits]
  rw [prefixCubeCode_pairCode_cylinder n u hu hne]
  exact Part.mem_some _

/-! ### From the cylinder code back to the prefix -/

/-- Read the program as the binary code of a prefix length `l`, decode the
support of the coded distribution in the context, and return the first `l` bits
of its first listed point.  This is total for every program and every context. -/
def prefixOfCylinderCode (input : BitString × BitString) : BitString :=
  ((codeSupportList input.2).headI).take (decodeBits input.1)

theorem prefixOfCylinderCode_primrec : Primrec prefixOfCylinderCode := by
  unfold prefixOfCylinderCode
  exact Primrec.list_take.comp
    (Primrec.list_headI.comp (codeSupportList_primrec.comp Primrec.snd))
    (primrecDecodeBits.comp Primrec.fst)

/-- The decompressor recovering a cylinder's prefix from its canonical code. -/
noncomputable def prefixOfCylinderDecompressor : Map :=
  fun input => Part.some (prefixOfCylinderCode input)

theorem prefixOfCylinderDecompressor_partrec :
    isDecompressor prefixOfCylinderDecompressor :=
  Computable.partrec prefixOfCylinderCode_primrec.to_comp

theorem prefixOfCylinderDecompressor_total (p : BitString) :
    IsTotalProgram prefixOfCylinderDecompressor p := by
  intro y
  trivial

/-- The lexicographically first listed member of a nonempty cylinder belongs to
that cylinder. -/
theorem headI_canonicalFinsetList_mem
    (S : Finset BitString) (hS : S.Nonempty) :
    (canonicalFinsetList S).headI ∈ S := by
  rcases hl : canonicalFinsetList S with _ | ⟨a, t⟩
  · exfalso
    have hcard : S.card = 0 := by
      rw [← length_canonicalFinsetList S, hl]
      rfl
    exact absurd (Finset.card_pos.mpr hS) (by omega)
  · have hmem : a ∈ canonicalFinsetList S := by
      rw [hl]
      exact List.mem_cons_self ..
    simpa [hl] using mem_canonicalFinsetList.mp hmem

theorem prefixOfCylinderDecompressor_produces
    (n : Nat) (u : BitString)
    (hne : (cylinder n u).Nonempty) :
    produces prefixOfCylinderDecompressor (Nat.bits u.length)
      (codedUniformOn (cylinder n u) hne).code u := by
  unfold produces prefixOfCylinderDecompressor prefixOfCylinderCode
  simp only [decodeBits_natBits, codeSupportList_codedUniformOn]
  have hmem : (canonicalFinsetList (cylinder n u)).headI ∈ cylinder n u :=
    headI_canonicalFinsetList_mem (cylinder n u) hne
  obtain ⟨-, hpre⟩ := (mem_cylinder n u _).mp hmem
  have htake : (canonicalFinsetList (cylinder n u)).headI.take u.length = u :=
    (List.prefix_iff_eq_take.mp hpre).symm
  rw [htake]
  exact Part.mem_some _

/-! ### The two directions combined -/

/-- **A cylinder code and its defining prefix are `O(log n)`-total-equivalent.**

For every optimal total conditional machine `T` there is a constant `C` such
that, for every prefix `y` and every length `n ≥ |y|`, the canonical uniform
code of `cylinder n y` and the string `y` are `logSlack C n`-equivalent for
total conditional complexity. -/
theorem separationCylinder_totalEquivalent_prefix
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ C, ∀ y n (h : y.length ≤ n),
      let A := cylinder n y
      TotalEquivalentWithin T
        (codedUniformOn A
          (cylinderFamilyMem_nonempty ⟨n, y, h, rfl⟩)).code
        y
        (logSlack C n) := by
  obtain ⟨cFwd, hFwd⟩ :=
    hT.2 cylinderOfPrefixDecompressor cylinderOfPrefixDecompressor_partrec
  obtain ⟨cBwd, hBwd⟩ :=
    hT.2 prefixOfCylinderDecompressor prefixOfCylinderDecompressor_partrec
  refine ⟨cFwd + cBwd + 1, ?_⟩
  intro y n h A
  have hne : A.Nonempty := cylinderFamilyMem_nonempty ⟨n, y, h, rfl⟩
  have hbitsY : (Nat.bits y.length).length ≤ (Nat.bits n).length :=
    length_natBits_mono h
  have hbitsS : (Nat.bits (n - y.length)).length ≤ (Nat.bits n).length :=
    length_natBits_mono (Nat.sub_le _ _)
  constructor
  · calc
      totalCondK T (codedUniformOn A hne).code y
          ≤ totalCondK cylinderOfPrefixDecompressor
              (codedUniformOn A hne).code y + (cFwd : ENat) := hFwd _ _
      _ ≤ ((Nat.bits (n - y.length)).length : ENat) + (cFwd : ENat) := by
          gcongr
          exact totalCondK_le_programLength
            (cylinderOfPrefixDecompressor_total (Nat.bits (n - y.length)))
            (cylinderOfPrefixDecompressor_produces n y h hne)
      _ ≤ (logSlack (cFwd + cBwd + 1) n : ENat) := by
          exact_mod_cast (show
            (Nat.bits (n - y.length)).length + cFwd ≤
              logSlack (cFwd + cBwd + 1) n by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)])
  · calc
      totalCondK T y (codedUniformOn A hne).code
          ≤ totalCondK prefixOfCylinderDecompressor
              y (codedUniformOn A hne).code + (cBwd : ENat) := hBwd _ _
      _ ≤ ((Nat.bits y.length).length : ENat) + (cBwd : ENat) := by
          gcongr
          exact totalCondK_le_programLength
            (prefixOfCylinderDecompressor_total (Nat.bits y.length))
            (prefixOfCylinderDecompressor_produces n y hne)
      _ ≤ (logSlack (cFwd + cBwd + 1) n : ENat) := by
          exact_mod_cast (show
            (Nat.bits y.length).length + cBwd ≤
              logSlack (cFwd + cBwd + 1) n by
            unfold logSlack
            nlinarith [Nat.zero_le ((Nat.bits n).length)])

end Kolmogorov
