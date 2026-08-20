import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongSufficientStatistic
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions

/-!
# Support lemmas for VS40 Lemma 4

Generic ingredients used by the assembly of `lemma_4`:

* `totalCondK_headI_le_totalCondK_code`: a total program for the canonical code
  of a finite set yields, at the same length up to an additive constant, a total
  program for the lexicographically first element of that set.
* `plainK_mem_le_of_plainSetComplexity_le`: every element of a finite set is
  described by the set plus its ordinal, i.e.
  `C(z) ≤ C(D) + log #D + 2 log C(D) + O(1)`.
* `exists_minimal_boundedOutputStage_cover`: a finite set of strings of
  complexity at most `m` has a least enumeration stage covering it.
* `bits_length_le_of_le_add_mul`: an arithmetic bound saying that a quantity
  which is at most `n` plus a logarithmic term has logarithm `log n + O(1)`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### From a set code to its canonical element, totally -/

/-- The decompressor that runs `T` and then returns the lexicographically first
point of the decoded finite distribution. -/
noncomputable def canonicalHeadOfTotal (T : Map) : Map := fun pr =>
  (T pr).bind fun w =>
    Part.some ((decodeDistributionData w).map CodedDistributionEntry.point).headI

theorem canonicalHeadOfTotal_partrec {T : Map} (hT : isDecompressor T) :
    isDecompressor (canonicalHeadOfTotal T) := by
  have H : Computable (fun p : (BitString × BitString) × BitString =>
      ((decodeDistributionData p.2).map CodedDistributionEntry.point).headI) :=
    (Primrec.list_headI.comp
      (Primrec.list_map (decodeDistributionData_primrec.comp Primrec.snd)
        (entry_point_primrec.comp Primrec.snd).to₂)).to_comp
  exact Partrec.bind hT H.to₂.partrec₂

/-- A total program for the canonical code of a nonempty finite set is, up to an
additive constant, also a total program for the set's lexicographically first
element. -/
theorem totalCondK_headI_le_totalCondK_code
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ (S : Finset BitString) (hS : S.Nonempty) (y : BitString),
      totalCondK T (canonicalFinsetList S).headI y ≤
        totalCondK T (codedUniformOn S hS).code y + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (canonicalHeadOfTotal T) (canonicalHeadOfTotal_partrec hT.1)
  refine ⟨c, fun S hS y => ?_⟩
  rcases eq_or_ne (totalCondK T (codedUniformOn S hS).code y) ⊤ with htop | htop
  · rw [htop]; simp
  · obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp htop
    have hle : totalCondK T (codedUniformOn S hS).code y ≤ (N : ENat) :=
      le_of_eq hN.symm
    obtain ⟨p, hptot, hplen, hpprod⟩ :=
      (totalCondK_le_iff T _ y N).mp hle
    have hEtot : IsTotalProgram (canonicalHeadOfTotal T) p := by
      intro y'
      have hdom := hptot y'
      simp [canonicalHeadOfTotal, Part.bind_dom, hdom]
    have hEprod :
        produces (canonicalHeadOfTotal T) p y (canonicalFinsetList S).headI := by
      have hpoints := dataPoints_codedUniformOn S hS
      refine Part.mem_bind_iff.mpr ⟨(codedUniformOn S hS).code, hpprod, ?_⟩
      rw [hpoints]
      exact Part.mem_some _
    have h1 : totalCondK (canonicalHeadOfTotal T)
        (canonicalFinsetList S).headI y ≤ (N : ENat) :=
      (totalCondK_le_iff _ _ _ N).mpr ⟨p, hEtot, hplen, hEprod⟩
    calc totalCondK T (canonicalFinsetList S).headI y
        ≤ totalCondK (canonicalHeadOfTotal T)
            (canonicalFinsetList S).headI y + (c : ENat) := hc _ _
      _ ≤ (N : ENat) + (c : ENat) := by gcongr
      _ = totalCondK T (codedUniformOn S hS).code y + (c : ENat) := by rw [hN]

/-! ### Elements of a finite set are cheap given the set -/

/-- Ordinary plain complexity of a member of a finite set, in terms of the plain
complexity of the set's canonical code and the set's log-cardinality. -/
theorem plainK_mem_le_of_plainSetComplexity_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (D : Finset BitString) (hD : D.Nonempty) (z : BitString)
        (a : Nat),
      z ∈ D →
      plainSetComplexity V D hD ≤ (a : ENat) →
      plainK V z ≤
        ((a + finiteSetLogCard D + 2 * (Nat.bits a).length + c : Nat) : ENat) := by
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  obtain ⟨cElem, hElem⟩ := condK_element_via_model V hV
  have hIdDecomp :
      isDecompressor (fun pr : BitString × BitString => Part.some pr.2) :=
    Computable.snd.partrec
  obtain ⟨cSelf, hSelf⟩ := hV.2 _ hIdDecomp
  have hself : ∀ w : BitString, condK V w w ≤ (cSelf : ENat) := by
    intro w
    have h0 : condK (fun pr : BitString × BitString => Part.some pr.2) w w ≤
        (0 : ENat) := by
      refine sInf_le ⟨[], Part.mem_some w, ?_⟩
      simp [programLength]
    calc condK V w w
        ≤ condK (fun pr : BitString × BitString => Part.some pr.2) w w +
            (cSelf : ENat) := hSelf w w
      _ ≤ 0 + (cSelf : ENat) := by gcongr
      _ = (cSelf : ENat) := by simp
  refine ⟨cSelf + 2 * (Nat.bits cSelf).length + cElem + cTwo, ?_⟩
  intro D hD z a hz ha
  have hcond : condK V z (codedUniformOn D hD).code ≤
      ((cSelf + finiteSetLogCard D + 2 * (Nat.bits cSelf).length + cElem :
        Nat) : ENat) :=
    hElem D D hD hD z cSelf hz (hself _)
  have hmain := hTwo z (codedUniformOn D hD).code a
      (cSelf + finiteSetLogCard D + 2 * (Nat.bits cSelf).length + cElem)
      ha hcond
  refine hmain.trans ?_
  exact_mod_cast Nat.le_of_eq (by ring)

/-! ### The least covering stage -/

/-- If every element of `D` has complexity at most `m`, there is a least
enumeration stage at which all of `D` has been printed. -/
theorem exists_minimal_boundedOutputStage_cover
    (q : Nat.Partrec.Code) (m : Nat) (D : Finset BitString)
    (hsub : ∀ z ∈ D, z ∈ completedBoundedOutput q m) :
    ∃ t, (∀ z ∈ D, z ∈ boundedOutputStage q m t) ∧
      ∀ t' < t, ¬ (∀ z ∈ D, z ∈ boundedOutputStage q m t') := by
  classical
  have hex : ∃ t, ∀ z ∈ D, z ∈ boundedOutputStage q m t :=
    ⟨maxHaltingStage q m, hsub⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun t' ht' => Nat.find_min hex ht'⟩

/-! ### An arithmetic bound on binary lengths -/

/-- A quantity bounded by `n` plus a logarithmic correction has binary length
`log n + O(1)`. -/
theorem bits_length_le_of_le_add_mul (C n a : Nat)
    (h : a ≤ n + C * (Nat.bits n).length + C) :
    (Nat.bits a).length ≤ (Nat.bits n).length + (Nat.bits (C + 2)).length + 2 := by
  have hbits : ∀ x : Nat, (Nat.bits x).length = Nat.size x := by
    intro x; rw [Nat.size_eq_bits_len]
  rw [hbits, hbits, hbits] at *
  set s := Nat.size n with hs
  set sC := Nat.size (C + 2) with hsC
  have hn : n < 2 ^ s := Nat.lt_size_self n
  have hC : C + 2 < 2 ^ sC := Nat.lt_size_self (C + 2)
  have hslt : s < 2 ^ s := Nat.lt_two_pow_self
  have hXpos : 0 < 2 ^ s := Nat.two_pow_pos _
  have hYpos : 0 < 2 ^ sC := Nat.two_pow_pos _
  have hkey : a < 2 ^ (s + sC + 2) := by
    have hpow : 2 ^ (s + sC + 2) = 4 * (2 ^ s * 2 ^ sC) := by
      rw [pow_add, pow_add]; ring
    rw [hpow]
    nlinarith [hn, hC, hslt, hXpos, hYpos]
  exact Nat.size_le.mpr hkey

/-- Incrementing a natural number costs at most one extra binary digit. -/
theorem length_natBits_succ_le (k : ℕ) :
    (Nat.bits (k + 1)).length ≤ (Nat.bits k).length + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  refine Nat.size_le.mpr ?_
  have h : k < 2 ^ Nat.size k := Nat.lt_size_self k
  have hpos : 0 < 2 ^ Nat.size k := Nat.two_pow_pos _
  calc k + 1 ≤ 2 ^ Nat.size k := h
    _ < 2 ^ Nat.size k * 2 := by omega
    _ = 2 ^ (Nat.size k + 1) := (pow_succ 2 _).symm

/-! ### Uniform primitive recursion for the bounded-output enumeration

The bounded-output API exposes primitive recursion for a *fixed* machine code.
The Lemma 4 decoders receive that code through a shortest description of
`standardEnumeratorCode q`, so their searches must be uniform in the decoded
code. -/

theorem snapshotCodes_primrec_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Nat) × Nat =>
      snapshotCodes p.1.1 p.1.2 p.2) := by
  apply Primrec.listFilterMap
    (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst))
  apply Primrec.option_bind
  · exact (Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.encode.comp
          (Primrec.pair Primrec.snd (Primrec.const []))))).of_eq
        (fun _ => rfl)
  · exact Primrec.decode.comp Primrec.snd

theorem boundedOutputStage_primrec_uniform :
    Primrec (fun p : (Nat.Partrec.Code × Nat) × Nat =>
      boundedOutputStage p.1.1 p.1.2 p.2) := by
  have hbase : Primrec (fun p : (Nat.Partrec.Code × Nat) × Nat =>
      (snapshotCodes p.1.1 p.1.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (snapshotCodes_primrec_uniform.comp
        (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂
      (fun (p : (Nat.Partrec.Code × Nat) × Nat)
        (z : Nat × List BitString) =>
          (z.2 ++ snapshotCodes p.1.1 p.1.2 (z.1 + 1)).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp
        (Primrec.snd.comp Primrec.snd)
        (snapshotCodes_primrec_uniform.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨q, m⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [boundedOutputStage]
      rw [← ih]

end Kolmogorov
