import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.Restricted.Examples.Cylinders

namespace Kolmogorov

open CodedFiniteDistribution

/-- Input to the existing canonical prefix-cube encoder. -/
def cylinderModelInput
    (input : BitString × BitString) : BitString :=
  let r := decodeBits input.1
  pairCode (input.2.take r) (natCode (input.2.length - r))

theorem cylinderModelInput_primrec :
    Primrec cylinderModelInput := by
  unfold cylinderModelInput
  exact pairCode_primrec.comp
    (Primrec.list_take.comp Primrec.snd
      (primrecDecodeBits.comp Primrec.fst))
    (natCode_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.list_length.comp Primrec.snd)
        (primrecDecodeBits.comp Primrec.fst)))

/-- Uniform cylinder-code constructor.  The program encodes only the desired
prefix length; on a varying condition `y`, it returns the canonical code of the
cylinder determined by `y.take r` inside the length-`y.length` cube. -/
noncomputable def cylinderModelCode
    (input : BitString × BitString) : BitString :=
  prefixCubeCode (cylinderModelInput input)

theorem cylinderModelCode_computable :
    Computable cylinderModelCode :=
  prefixCubeCode_computable.comp cylinderModelInput_primrec.to_comp

/-- The total decompressor interpreting its program as a binary prefix length. -/
noncomputable def cylinderModelDecompressor : Map :=
  fun input => Part.some (cylinderModelCode input)

theorem cylinderModelDecompressor_partrec :
    isDecompressor cylinderModelDecompressor :=
  Computable.partrec cylinderModelCode_computable

theorem cylinderModelDecompressor_total (p : BitString) :
    IsTotalProgram cylinderModelDecompressor p := by
  intro y
  trivial

theorem cylinderModelCode_eq
    (n : Nat) (u x : BitString) (hu : u.length ≤ n)
    (hx : x ∈ cylinder n u) :
    cylinderModelCode (Nat.bits u.length, x) =
      (codedUniformOn (cylinder n u) ⟨x, hx⟩).code := by
  obtain ⟨hxLength, hux⟩ := (mem_cylinder n u x).mp hx
  have htake : x.take u.length = u :=
    (List.prefix_iff_eq_take.mp hux).symm
  have hcube :
      prefixCubeSet u (n - u.length) = cylinder n u := by
    rw [prefixCubeSet_eq_cylinder, Nat.add_sub_of_le hu]
  unfold cylinderModelCode cylinderModelInput prefixCubeCode
  simp only [decodeBits_natBits, decodeFirst_pairCode,
    decodeSecond_pairCode, decodeNatCode_natCode]
  rw [htake, hxLength, hcube]
  exact canonicalUniformCodeOfList_canonicalFinsetList
    (cylinder n u) ⟨x, hx⟩

theorem cylinderModelDecompressor_produces
    (n : Nat) (u x : BitString) (hu : u.length ≤ n)
    (hx : x ∈ cylinder n u) :
    produces cylinderModelDecompressor (Nat.bits u.length) x
      (codedUniformOn (cylinder n u) ⟨x, hx⟩).code := by
  unfold produces cylinderModelDecompressor
  rw [cylinderModelCode_eq n u x hu hx]
  exact ⟨trivial, rfl⟩

theorem cylinder_isStrongSetModel
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ n u x (_hu : u.length ≤ n)
      (hx : x ∈ cylinder n u),
      IsStrongSetModel T x (cylinder n u) ⟨x, hx⟩
        (logSlack c n) := by
  obtain ⟨c, hc⟩ :=
    hT.2 cylinderModelDecompressor
      cylinderModelDecompressor_partrec
  refine ⟨c + 1, ?_⟩
  intro n u x hu hx
  have hbits :
      (Nat.bits u.length).length ≤ (Nat.bits n).length :=
    length_natBits_mono hu
  unfold IsStrongSetModel
  calc
    totalCondK T (codedUniformOn (cylinder n u) ⟨x, hx⟩).code x
        ≤ totalCondK cylinderModelDecompressor
            (codedUniformOn (cylinder n u) ⟨x, hx⟩).code x +
              (c : ENat) :=
      hc _ _
    _ ≤ ((Nat.bits u.length).length : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength
        (cylinderModelDecompressor_total (Nat.bits u.length))
        (cylinderModelDecompressor_produces n u x hu hx)
    _ ≤ (logSlack (c + 1) n : ENat) := by
      exact_mod_cast (show
        (Nat.bits u.length).length + c ≤ logSlack (c + 1) n by
          unfold logSlack
          nlinarith [Nat.zero_le ((Nat.bits n).length)])

noncomputable def plainCylinderDecompressor : Map :=
  fun input =>
    let u := decodePlainAdviceProgram input.1
    let n := decodeBits (decodePlainAdviceData input.1)
    Part.some (prefixCubeCode (pairCode u (natCode (n - u.length))))

theorem plainCylinderDecompressor_partrec :
    isDecompressor plainCylinderDecompressor := by
  have hu : Computable (fun input : BitString × BitString =>
      decodePlainAdviceProgram input.1) :=
    decodePlainAdviceProgram_computable.comp Computable.fst
  have hn : Computable (fun input : BitString × BitString =>
      decodeBits (decodePlainAdviceData input.1)) :=
    primrecDecodeBits.to_comp.comp
      (decodePlainAdviceData_computable.comp Computable.fst)
  have hu_len : Computable (fun input : BitString × BitString =>
      (decodePlainAdviceProgram input.1).length) :=
    Primrec.list_length.to_comp.comp hu
  have hn_sub_u : Computable (fun input : BitString × BitString =>
      decodeBits (decodePlainAdviceData input.1) - (decodePlainAdviceProgram input.1).length) :=
    Primrec.nat_sub.to_comp.comp hn hu_len
  have hp : Computable (fun input : BitString × BitString =>
      pairCode (decodePlainAdviceProgram input.1)
        (natCode (decodeBits (decodePlainAdviceData input.1) -
          (decodePlainAdviceProgram input.1).length))) :=
    pairCode_primrec.to_comp.comp hu (natCode_primrec.to_comp.comp hn_sub_u)
  exact Computable.partrec (prefixCubeCode_computable.comp hp)

theorem plainCylinderDecompressor_produces
    (n : Nat) (u x : BitString) (hu : u.length ≤ n)
    (hx : x ∈ cylinder n u) :
    produces plainCylinderDecompressor (plainAdviceCode u (Nat.bits n)) []
      (codedUniformOn (cylinder n u) ⟨x, hx⟩).code := by
  unfold produces plainCylinderDecompressor
  simp only [decodePlainAdviceProgram_code,
    decodePlainAdviceData_code, decodeBits_natBits]
  have h_eq : prefixCubeCode (pairCode u (natCode (n - u.length))) =
      cylinderModelCode (Nat.bits u.length, x) := by
    unfold cylinderModelCode cylinderModelInput
    simp only [decodeBits_natBits]
    have hxLength := ((mem_cylinder n u x).mp hx).1
    have htake := (List.prefix_iff_eq_take.mp ((mem_cylinder n u x).mp hx).2).symm
    rw [hxLength, htake]
  rw [h_eq, cylinderModelCode_eq n u x hu hx]
  exact ⟨trivial, rfl⟩

theorem plainSetComplexity_cylinder_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c, ∀ n u x (_hu : u.length ≤ n)
      (hx : x ∈ cylinder n u),
      plainSetComplexity V (cylinder n u) ⟨x, hx⟩ ≤
        (u.length + logSlack c n : ENat) := by
  obtain ⟨cInv, hInv⟩ :=
    hV.2 plainCylinderDecompressor plainCylinderDecompressor_partrec
  refine ⟨cInv + 4, ?_⟩
  intro n u x hu hx
  have hprod := plainCylinderDecompressor_produces n u x hu hx
  unfold plainSetComplexity
  calc
    plainK V (codedUniformOn (cylinder n u) ⟨x, hx⟩).code
        ≤ condK plainCylinderDecompressor
            (codedUniformOn (cylinder n u) ⟨x, hx⟩).code [] +
            (cInv : ENat) :=
      hInv _ _
    _ ≤ ((plainAdviceCode u (Nat.bits n)).length : ENat) +
          (cInv : ENat) := by
      gcongr
      exact sInf_le ⟨plainAdviceCode u (Nat.bits n), hprod, rfl⟩
    _ ≤ (u.length + logSlack (cInv + 4) n : ENat) := by
      apply Nat.cast_le.mpr
      rw [length_plainAdviceCode]
      have hsmall :
          (Nat.bits (Nat.bits n).length).length ≤
            (Nat.bits n).length :=
        length_natBits_le_self (Nat.bits n).length
      unfold logSlack
      calc
        u.length + (Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + 1 + cInv
            ≤ u.length + (Nat.bits n).length + 2 * (Nat.bits n).length + 1 + cInv := by omega
        _ = u.length + 3 * (Nat.bits n).length + 1 + cInv := by omega
        _ ≤ u.length + ((cInv + 4) * (Nat.bits n).length + (cInv + 4)) := by
          have hmul : 3 * (Nat.bits n).length ≤ (cInv + 4) * (Nat.bits n).length := by
            exact Nat.mul_le_mul_right (Nat.bits n).length (by omega)
          omega

theorem cylinderProfile_to_strongProfile
    (V U T : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (hT : IsOptimalTotalConditional T) :
    ∃ c, ∀ x i j,
      InDescriptionProfileIn cylinderFamily U x i j →
      InStrongDescriptionProfile V T x
        (logSlack c x.length) (i + c) j := by
  obtain ⟨cStrong, hStrong⟩ :=
    cylinder_isStrongSetModel T hT
  obtain ⟨cPlain, hPlain⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  refine ⟨cStrong + cPlain, ?_⟩
  intro x i j hprofile
  obtain ⟨S, hS, hFamily, hdesc⟩ := hprofile
  obtain ⟨n, u, hu, hS_eq⟩ := hFamily
  subst S
  have hx : x ∈ cylinder n u := hdesc.1
  have hxLength : x.length = n :=
    ((mem_cylinder n u x).mp hx).1
  refine ⟨cylinder n u, hS, ?_, ?_⟩
  · refine ⟨hx, ?_, hdesc.2.2⟩
    unfold plainSetComplexity
    calc
      plainK V (codedUniformOn (cylinder n u) hS).code
          ≤ KPPlain U (codedUniformOn (cylinder n u) hS).code +
              (cPlain : ENat) :=
        hPlain _
      _ ≤ (i : ENat) + (cPlain : ENat) := by
        gcongr
        simpa [setComplexity] using hdesc.2.1
      _ ≤ ((i + (cStrong + cPlain) : Nat) : ENat) := by
        exact_mod_cast (show i + cPlain ≤ i + (cStrong + cPlain) by
          omega)
  · refine (hStrong n u x hu hx).mono ?_
    rw [hxLength]
    exact logSlack_mono_left (Nat.le_add_right cStrong cPlain) n

end Kolmogorov
