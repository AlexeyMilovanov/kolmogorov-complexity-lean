import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.Restricted.EffectiveSelection.Part02
import KolmogorovMathlib.Restricted.EffectiveSelection

/-!
# Improving descriptions inside a restricted family

This module adapts the marked-description argument to a decidable pre-description family.
`descriptionsWithComplexityLeAndSizeLeIn` and `ManyIJDescriptionsIn` express the available
models and their multiplicity, with monotonicity and visibility lemmas relating them to stages.

The marked code stream covers every sufficiently numerous collection of candidate descriptions.
Its duplicate-free rank gives a short address, encoded by `familyMarkedInput` and decoded by
`selN`, `selI`, `selJ`, `selK`, and `selR`; these selectors are primitive recursive and
the address length is bounded.

The resulting data feed the uniform selection machine and the final restricted improvement.
-/



namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Restricted `(i,j)` descriptions available for multiplicity counting. -/
noncomputable def descriptionsWithComplexityLeAndSizeLeIn
    (𝒜 : PreDescriptionFamily) (U : Map) (i j : ℕ) : Finset (Finset BitString) := by
  classical
  exact (descriptionsWithComplexityLeAndSizeLe U i j).filter (fun S => 𝒜.mem S)

/-- Restricted multiplicity of `(i,j)` descriptions, counted by distinct
canonical finite sets as in the unrestricted `ManyIJDescriptions`. -/
noncomputable def ManyIJDescriptionsIn
    (𝒜 : PreDescriptionFamily) (U : Map) (x : BitString) (i j k : ℕ) : Prop :=
  2 ^ k ≤ ((descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter
    (fun S => x ∈ S)).card

/-- Having `2 ^ k` restricted `(i, j)`-descriptions implies having `2 ^ k'` of them for `k' ≤ k`. -/
theorem ManyIJDescriptionsIn.mono_k {𝒜 : PreDescriptionFamily} {U : Map} {x : BitString}
    {i j k k' : ℕ}
    (h : ManyIJDescriptionsIn 𝒜 U x i j k) (hk : k' ≤ k) : ManyIJDescriptionsIn 𝒜 U x i j k' := by
  unfold ManyIJDescriptionsIn at *
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk) h

/-- Restricted description multiplicity is monotone in the size bound `j`. -/
theorem ManyIJDescriptionsIn.mono_j {𝒜 : PreDescriptionFamily} {U : Map} {x : BitString}
    {i j j' k : ℕ}
    (h : ManyIJDescriptionsIn 𝒜 U x i j k) (hj : j ≤ j') : ManyIJDescriptionsIn 𝒜 U x i j' k := by
  classical
  unfold ManyIJDescriptionsIn at *
  refine h.trans (Finset.card_le_card ?_)
  refine Finset.filter_subset_filter _ ?_
  intro S hS
  unfold descriptionsWithComplexityLeAndSizeLeIn at hS ⊢
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨descriptionsWithComplexityLeAndSizeLe_subset_of_le_right U i hj hS.1, hS.2⟩

/-- One description already witnesses multiplicity `2 ^ 0`: a set of the family containing `x`,
of complexity at most `i` and size at most `2 ^ j`, gives `ManyIJDescriptionsIn … 0`. -/
theorem manyIJDescriptionsIn_zero_of_mem {𝒜 : PreDescriptionFamily} {U : Map} {x : BitString}
    {i j : ℕ} {A : Finset BitString}
    (hA : A.Nonempty) (hx : x ∈ A) (hmem : 𝒜.mem A) (hcomp : setComplexity U A hA ≤ (i : ENat))
        (hsize : A.card ≤ 2 ^ j) :
    ManyIJDescriptionsIn 𝒜 U x i j 0 := by
  classical
  unfold ManyIJDescriptionsIn
  rw [pow_zero]
  refine Finset.card_pos.mpr ?_
  refine ⟨A, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hx⟩
  unfold descriptionsWithComplexityLeAndSizeLeIn
  rw [Finset.mem_filter]
  refine ⟨?_, hmem⟩
  unfold descriptionsWithComplexityLeAndSizeLe
  rw [Finset.mem_filter]
  exact ⟨mem_descriptionsWithComplexityLe_of_complexity hA hcomp, hsize⟩

/-- Every set in the finite description universe is nonempty: it is the (nonempty)
support of a canonical uniform code. -/
theorem nonempty_of_mem_descriptionsWithComplexityLe {U : Map} {i : ℕ}
    {S : Finset BitString} (hS : S ∈ descriptionsWithComplexityLe U i) : S.Nonempty := by
  unfold descriptionsWithComplexityLe at hS
  rw [Finset.mem_biUnion] at hS
  obtain ⟨c, _, hc⟩ := hS
  by_cases hcanon : isCanonicalUniformCode c
  · rw [if_pos hcanon, Finset.mem_singleton] at hc
    obtain ⟨hne, _⟩ := hcanon
    rw [hc]; exact hne
  · rw [if_neg hcanon] at hc; simp at hc

/-- The code of the uniform distribution on a finite set determines the set. -/
theorem codedUniformOn_code_injective {S T : Finset BitString}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hcode : (codedUniformOn S hS).code = (codedUniformOn T hT).code) :
    S = T := by
  have hdist : codedUniformOn S hS = codedUniformOn T hT :=
    CodedFiniteDistribution.code_injective hcode
  have hsupp := congrArg CodedFiniteDistribution.support hdist
  simpa [codedUniformOn_support] using hsupp

/-- A set of complexity at most `i` has the code of its uniform distribution appear in some
finite snapshot of the enumeration of codes of complexity at most `i`. -/
theorem codedUniformOn_code_mem_snapshot_of_description
    {U : Map} {c : Code} (hc : IsCodeFor c U) {i : ℕ}
    {S : Finset BitString} (hS : S.Nonempty)
    (hmem : S ∈ descriptionsWithComplexityLe U i) :
    ∃ t : ℕ, (codedUniformOn S hS).code ∈ snapshotCodes c i t := by
  obtain ⟨t₀, hmax⟩ := exists_max_countHalts c i
  have hSnap : S ∈ snapshotDescriptions c i t₀ := by
    rw [snapshotDescriptions_eq_descriptionsWithComplexityLe hc i t₀ hmax]
    exact hmem
  unfold snapshotDescriptions at hSnap
  rw [Finset.mem_image] at hSnap
  rcases hSnap with ⟨w, hw, hwS⟩
  rw [List.mem_toFinset, List.mem_filter] at hw
  rcases hw with ⟨hwSnap, hwCanon⟩
  obtain ⟨hW, hwCode⟩ := eq_codedUniformOn_of_isCanonicalUniformCodeBool hwCanon
  have hwCodeS : w = (codedUniformOn S hS).code := by
    rw [hwCode]
    exact codedUniformOn_code_congr hW hS hwS
  exact ⟨t₀, by simpa [hwCodeS] using hwSnap⟩

/-- For `fullFamily` the restricted description universe is the unrestricted one, since
`fullFamily.mem = Nonempty` and every description is nonempty. -/
theorem descriptionsWithComplexityLeAndSizeLeIn_fullFamily (U : Map) (i j : ℕ) :
    descriptionsWithComplexityLeAndSizeLeIn fullFamily U i j
      = descriptionsWithComplexityLeAndSizeLe U i j := by
  classical
  unfold descriptionsWithComplexityLeAndSizeLeIn
  ext S
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact nonempty_of_mem_descriptionsWithComplexityLe (Finset.mem_filter.mp h).1

/-- For `fullFamily` the restricted multiplicity predicate collapses to the unrestricted
`ManyIJDescriptions`. -/
theorem manyIJDescriptionsIn_fullFamily_iff (U : Map) (x : BitString) (i j k : ℕ) :
    ManyIJDescriptionsIn fullFamily U x i j k ↔ ManyIJDescriptions U x i j k := by
  unfold ManyIJDescriptionsIn ManyIJDescriptions
  rw [descriptionsWithComplexityLeAndSizeLeIn_fullFamily]

/-- Restricted Improving Descriptions (size half). -/
theorem inDescriptionProfileIn_improving_size (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      InDescriptionProfileIn 𝒜 U x i j →
      k ≤ j →
      InDescriptionProfileIn 𝒜 U x
        (i + k + logSlack c (n + k + 𝒜.overhead n))
        (j - k) := by
  obtain ⟨c, hc⟩ := inDescriptionProfileIn_cover_shift U hU 𝒜
  exact ⟨c, fun x n i j k hx hprof hk => hc x n i j k hx hk hprof⟩

/-- A visibility lemma: `ManyIJDescriptionsIn` means there is some stage `t` where the required
multiplicity is visible in `familyStageDescriptionCodes`. -/
theorem manyIJDescriptionsIn_visible_stage {U : Map} {c : Code} (hc : IsCodeFor c U)
    (𝒜 : PreDescriptionFamily) (x : BitString) (n i j k : ℕ) :
    x.length = n →
    ManyIJDescriptionsIn 𝒜 U x i j k →
    ∃ t : ℕ, 2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card := by
  intro _hn hmany
  classical
  let F := (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter (fun S => x ∈ S)
  let codeOf : Finset BitString → BitString := fun S =>
    if hS : S.Nonempty then (codedUniformOn S hS).code else []
  have hF_eq : F =
      (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter (fun S => x ∈ S) := rfl
  have enum_prefix_of_le :
      ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ →
        𝒜.enumeration.enum t₁ <+: 𝒜.enumeration.enum t₂ := by
    intro t₁ t₂ hle
    induction hle with
    | refl => exact List.prefix_refl _
    | step _ ih => exact List.IsPrefix.trans ih (𝒜.enumeration.mono _)
  have stage_mono :
      ∀ {t₁ t₂ : ℕ} {w : BitString}, t₁ ≤ t₂ →
        w ∈ familyStageDescriptionCodes c i 𝒜 j t₁ x →
        w ∈ familyStageDescriptionCodes c i 𝒜 j t₂ x := by
    intro t₁ t₂ w hle hw
    rw [mem_familyStageDescriptionCodes, Finset.mem_inter] at hw ⊢
    rcases hw with ⟨⟨hwEnum, hwSnap⟩, hwDesc⟩
    refine ⟨⟨?_, ?_⟩, hwDesc⟩
    · rw [List.mem_toFinset] at hwEnum
      exact List.mem_toFinset.mpr ((enum_prefix_of_le hle).subset hwEnum)
    · rw [List.mem_toFinset] at hwSnap
      exact List.mem_toFinset.mpr (snapshotCodes_mem_of_le hle hwSnap)
  have each_visible :
      ∀ S ∈ F, ∃ t : ℕ, codeOf S ∈ familyStageDescriptionCodes c i 𝒜 j t x := by
    intro S hSF
    have hSF' : S ∈ (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter
        (fun S => x ∈ S) := by simpa [F] using hSF
    rw [Finset.mem_filter] at hSF'
    have hbaseA := Finset.mem_filter.mp hSF'.1
    have hbase := Finset.mem_filter.mp hbaseA.1
    have hS : S.Nonempty := 𝒜.nonempty_of_mem hbaseA.2
    have hcodeOf : codeOf S = (codedUniformOn S hS).code := by
      simp [codeOf, hS]
    obtain ⟨tEnum, htEnum⟩ := 𝒜.enumeration.complete S hS hbaseA.2
    obtain ⟨tSnap, htSnap⟩ :=
      codedUniformOn_code_mem_snapshot_of_description hc hS hbase.1
    refine ⟨max tEnum tSnap, ?_⟩
    rw [hcodeOf, mem_familyStageDescriptionCodes, Finset.mem_inter]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact List.mem_toFinset.mpr
        ((enum_prefix_of_le (le_max_left tEnum tSnap)).subset htEnum)
    · exact List.mem_toFinset.mpr
        (snapshotCodes_mem_of_le (le_max_right tEnum tSnap) htSnap)
    · exact ⟨S, hS, hbaseA.2, rfl, hbase.2, hSF'.2⟩
  let stageOf : Finset BitString → ℕ := fun S =>
    if h : S ∈ F then Classical.choose (each_visible S h) else 0
  let T := Finset.sup F stageOf
  have code_mem_T : ∀ S ∈ F, codeOf S ∈ familyStageDescriptionCodes c i 𝒜 j T x := by
    intro S hSF
    have hchosen := Classical.choose_spec (each_visible S hSF)
    have hle : stageOf S ≤ T := by
      exact Finset.le_sup (f := stageOf) hSF
    have hstage : stageOf S = Classical.choose (each_visible S hSF) := by
      simp [stageOf, hSF]
    exact stage_mono hle (by simpa [hstage] using hchosen)
  have code_inj : (F : Set (Finset BitString)).InjOn codeOf := by
    intro S hSFSet T' hTFSet hcode
    have hSF : S ∈ F := by simpa using hSFSet
    have hTF : T' ∈ F := by simpa using hTFSet
    have hSF' : S ∈ (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter
        (fun S => x ∈ S) := by simpa [F] using hSF
    have hTF' : T' ∈ (descriptionsWithComplexityLeAndSizeLeIn 𝒜 U i j).filter
        (fun S => x ∈ S) := by simpa [F] using hTF
    rw [Finset.mem_filter] at hSF' hTF'
    have hSA := Finset.mem_filter.mp hSF'.1
    have hTA := Finset.mem_filter.mp hTF'.1
    have hS : S.Nonempty := 𝒜.nonempty_of_mem hSA.2
    have hT : T'.Nonempty := 𝒜.nonempty_of_mem hTA.2
    have hcodeS : codeOf S = (codedUniformOn S hS).code := by
      simp [codeOf, hS]
    have hcodeT : codeOf T' = (codedUniformOn T' hT).code := by
      simp [codeOf, hT]
    exact codedUniformOn_code_injective hS hT (by simpa [hcodeS, hcodeT] using hcode)
  have hcard : F.card ≤ (familyStageDescriptionCodes c i 𝒜 j T x).card :=
    Finset.card_le_card_of_injOn codeOf code_mem_T code_inj
  refine ⟨T, ?_⟩
  exact hmany.trans (by simpa [F] using hcard)

/-- Every `n`-bit string with `2^k` visible restricted descriptions is covered
by a selected family description in the stream. -/
theorem familyMarkedCodeStream_covers_many (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) (x : BitString) :
    x.length = n →
    2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
    ∃ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyDescriptionCode 𝒜 j x w := by
  intro hxlen hmany
  exact familyMarkedCodeStream_covers c i 𝒜 n j k t x hxlen hmany

/-- Removing duplicates does not lengthen a list of strings. -/
theorem eraseDups_bitString_length_le (L : List BitString) :
    L.eraseDups.length ≤ L.length := by
  have hfin : L.eraseDups.toFinset = L.toFinset := by
    ext w
    simp
  calc L.eraseDups.length
      = L.eraseDups.toFinset.card :=
        (List.toFinset_card_of_nodup (nodup_eraseDups_bitString L)).symm
    _ = L.toFinset.card := by rw [hfin]
    _ ≤ L.length := List.toFinset_card_le _

/-- Every member of a list occupies a position in its duplicate-free version. -/
theorem exists_rank_getD_eraseDups (L : List BitString) {w : BitString}
    (hw : w ∈ L) :
    ∃ r, r < L.eraseDups.length ∧ L.eraseDups.getD r [] = w := by
  have hw' : w ∈ L.eraseDups := mem_eraseDups_bitString.mpr hw
  rw [List.mem_iff_getElem] at hw'
  rcases hw' with ⟨r, hr, hget⟩
  refine ⟨r, hr, ?_⟩
  simp [List.getD_eq_getElem?_getD, hr, hget]

/-- The address space `2 (i + 2)(i + 1)(n + 1)` of the marked stream needs at most
`3 |bits (n + i + j)| + 10` bits, so naming a stream position costs `O(log)`. -/
theorem markedStream_poly_bits_bound (n i j : ℕ) :
    (Nat.bits (2 * ((i + 2) * (i + 1) * (n + 1)))).length ≤
      3 * (Nat.bits (n + i + j)).length + 10 := by
  set M := n + i + j
  set W := (Nat.bits M).length
  set L := (Nat.bits (M + 2)).length
  have hMpow : M + 2 < 2 ^ L := by
    simpa [L] using lt_two_pow_length_natBits (M + 2)
  have hi2 : i + 2 < 2 ^ L := by
    have : i + 2 ≤ M + 2 := by omega
    exact lt_of_le_of_lt this hMpow
  have hi1 : i + 1 < 2 ^ L := by
    have : i + 1 ≤ M + 2 := by omega
    exact lt_of_le_of_lt this hMpow
  have hn1 : n + 1 < 2 ^ L := by
    have : n + 1 ≤ M + 2 := by omega
    exact lt_of_le_of_lt this hMpow
  have hprod :
      2 * ((i + 2) * (i + 1) * (n + 1)) < 2 ^ (3 * L + 1) := by
    have h12 : (i + 2) * (i + 1) < (2 ^ L) * (2 ^ L) :=
      Nat.mul_lt_mul'' hi2 hi1
    have h123 :
        ((i + 2) * (i + 1)) * (n + 1) <
          ((2 ^ L) * (2 ^ L)) * (2 ^ L) :=
      Nat.mul_lt_mul'' h12 hn1
    have hpow : 2 ^ (3 * L + 1) =
        2 * (((2 ^ L) * (2 ^ L)) * (2 ^ L)) := by
      rw [show 3 * L = L * 3 by ring, pow_add, pow_mul]
      ring
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left h123 (by decide : 0 < 2)
  have hq :
      (Nat.bits (2 * ((i + 2) * (i + 1) * (n + 1)))).length ≤
        3 * L + 1 :=
    length_natBits_lt_pow hprod
  have hL : L ≤ W + 3 := by
    have h := length_natBits_add_le M 2
    have htwo : (Nat.bits 2).length = 2 := by decide
    simpa [L, W, htwo, Nat.add_assoc] using h
  omega

/-- Every rank below `(i + 2)(i + 1)(n + 1) 2 ^ (i + 1 - k)` has a self-delimiting address of
length at most `i - k` plus a logarithmic slack term. -/
theorem markedStream_rank_address_slack (c_idx : ℕ) :
    ∃ c_slack : ℕ, ∀ (n i j k r : ℕ),
      k ≤ i →
      r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) →
      ∃ z : BitString,
        bitsToNat z = r ∧
        z.length + 2 * (Nat.bits z.length).length + c_idx ≤
          i - k + logSlack c_slack (n + i + j) := by
  obtain ⟨c_bits, hc_bits⟩ := logSlack_linear_bound 2 4 10
  refine ⟨13 + c_bits + c_idx, fun n i j k r hk hr => ?_⟩
  let M := n + i + j
  let P := 2 * ((i + 2) * (i + 1) * (n + 1))
  let q := (Nat.bits P).length
  let s := i - k + q
  have hpowP : P < 2 ^ q := by
    simpa [P, q] using lt_two_pow_length_natBits P
  have hexp : i + 1 - k = i - k + 1 := by omega
  have hbound_eq :
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) =
        P * 2 ^ (i - k) := by
    simp [P, hexp, pow_succ]
    ring
  have hr_pow : r < 2 ^ s := by
    have hlt : r < P * 2 ^ (i - k) := by
      simpa [hbound_eq] using hr
    have hmul : P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpowP)
    have hpow : 2 ^ q * 2 ^ (i - k) = 2 ^ s := by
      rw [show s = q + (i - k) by omega, pow_add]
    exact lt_of_lt_of_le hlt (by simpa [hpow] using hmul)
  refine ⟨chunkAddress r s, bitsToNat_chunkAddress r s, ?_⟩
  have hzlen : (chunkAddress r s).length = s := chunkAddress_length r s hr_pow
  rw [hzlen]
  have hq : q ≤ 3 * (Nat.bits M).length + 10 := by
    simpa [M, P, q] using markedStream_poly_bits_bound n i j
  have hs_linear : s ≤ 4 * M + 10 := by
    have hbits_le : (Nat.bits M).length ≤ M := length_natBits_le M
    omega
  have hs_bits : 2 * (Nat.bits s).length ≤ logSlack c_bits M := by
    have hmono : (Nat.bits s).length ≤ (Nat.bits (4 * M + 10)).length :=
      length_natBits_mono hs_linear
    have hraw : 2 * (Nat.bits s).length ≤ logSlack 2 (4 * M + 10) := by
      unfold logSlack
      omega
    exact hraw.trans (hc_bits M)
  have hq_slack : q ≤ logSlack 13 M := by
    unfold logSlack
    omega
  have hc_slack : c_idx ≤ logSlack c_idx M := by
    unfold logSlack
    omega
  have hsum :
      q + 2 * (Nat.bits s).length + c_idx ≤
        logSlack 13 M + logSlack c_bits M + logSlack c_idx M := by
    omega
  have hadd :
      logSlack 13 M + logSlack c_bits M + logSlack c_idx M =
        logSlack (13 + c_bits + c_idx) M := by
    rw [logSlack_add_const, logSlack_add_const]
  have hsum' :
      q + 2 * (Nat.bits s).length + c_idx ≤
        logSlack (13 + c_bits + c_idx) M := by
    exact hsum.trans (le_of_eq hadd)
  have hs_expand :
      s + 2 * (Nat.bits s).length + c_idx =
        i - k + (q + 2 * (Nat.bits s).length + c_idx) := by
    simp [s]
    omega
  rw [hs_expand]
  exact Nat.add_le_add_left (by simpa [M] using hsum') (i - k)

/-- Any selected code has a bounded ordinal in the duplicate-free marked stream.
This is the exact rank fact consumed by
`selected_family_code_setComplexity_bound`. -/
theorem exists_markedStream_rank (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) {w : BitString}
    (hw : w ∈ familyMarkedCodeStream c i 𝒜 n j k t) :
    ∃ r : ℕ,
      r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) ∧
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.getD r [] = w := by
  obtain ⟨r, hr, hget⟩ :=
    exists_rank_getD_eraseDups (familyMarkedCodeStream c i 𝒜 n j k t) hw
  refine ⟨r, ?_, hget⟩
  exact lt_of_lt_of_le hr
    (le_trans (eraseDups_bitString_length_le _)
      (familyMarkedCodeStream_length_bound c i 𝒜 n j k t))

/-- The duplicate-free marked stream at an earlier stage is a prefix of the one at a later stage,
so ranks in the stream are stable. -/
theorem familyMarkedCodeStream_eraseDups_prefix_of_le (c : Code) (i : ℕ)
    (𝒜 : PreDescriptionFamily) (n j k : ℕ) {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) :
    (familyMarkedCodeStream c i 𝒜 n j k t₁).eraseDups <+:
      (familyMarkedCodeStream c i 𝒜 n j k t₂).eraseDups := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hstep0 := familyMarkedCodeStream_mono c i 𝒜 n j k (t₁ + d)
      obtain ⟨tail, htail⟩ := hstep0
      have hstep : (familyMarkedCodeStream c i 𝒜 n j k (t₁ + d)).eraseDups <+:
          (familyMarkedCodeStream c i 𝒜 n j k (t₁ + (d + 1))).eraseDups := by
        rw [show t₁ + (d + 1) = t₁ + d + 1 by omega, ← htail, List.eraseDups_append]
        exact List.prefix_append _ _
      exact List.IsPrefix.trans (ih (by omega)) hstep

/-- The first packed component: `n`. -/
def selN (s : BitString) : ℕ := bitsToNat (decodeFirst s)
/-- The second packed component: `i`. -/
def selI (s : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond s))
/-- The third packed component: `j`. -/
def selJ (s : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond (decodeSecond s)))
/-- The fourth packed component: `k`. -/
def selK (s : BitString) : ℕ :=
    bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond s))))
/-- The fifth packed component: `r`. -/
def selR (s : BitString) : ℕ :=
    bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond s))))

/-- The five parameters `n, i, j, k, r` packed into a single self-delimiting string. -/
def familyMarkedInput (n i j k r : ℕ) : BitString :=
  pairCode (Nat.bits n)
      (pairCode (Nat.bits i) (pairCode (Nat.bits j) (pairCode (Nat.bits k) (Nat.bits r))))

/-- The first component read off a packed input is `n`. -/
@[simp] theorem selN_familyMarkedInput (n i j k r : ℕ) : selN (familyMarkedInput n i j k r) = n :=
    by
  simp [selN, familyMarkedInput, decodeFirst_pairCode, bitsToNat_bits]

/-- The second component read off a packed input is `i`. -/
@[simp] theorem selI_familyMarkedInput (n i j k r : ℕ) : selI (familyMarkedInput n i j k r) = i :=
    by
  simp [selI, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The third component read off a packed input is `j`. -/
@[simp] theorem selJ_familyMarkedInput (n i j k r : ℕ) : selJ (familyMarkedInput n i j k r) = j :=
    by
  simp [selJ, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The fourth component read off a packed input is `k`. -/
@[simp] theorem selK_familyMarkedInput (n i j k r : ℕ) : selK (familyMarkedInput n i j k r) = k :=
    by
  simp [selK, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The fifth component read off a packed input is the rank `r`. -/
@[simp] theorem selR_familyMarkedInput (n i j k r : ℕ) : selR (familyMarkedInput n i j k r) = r :=
    by
  simp [selR, familyMarkedInput, decodeSecond_pairCode, bitsToNat_bits]

/-- Reading `n` off a packed input is computable. -/
theorem selN_computable : Computable selN := bitsToNat_computable.comp decodeFirst_computable
/-- Reading `i` off a packed input is computable. -/
theorem selI_computable : Computable selI :=
    bitsToNat_computable.comp (decodeFirst_computable.comp decodeSecond_computable)
/-- Reading `j` off a packed input is computable. -/
theorem selJ_computable : Computable selJ :=
    bitsToNat_computable.comp
        (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
/-- Reading `k` off a packed input is computable. -/
theorem selK_computable : Computable selK :=
    bitsToNat_computable.comp
        (decodeFirst_computable.comp (decodeSecond_computable.comp (decodeSecond_computable.comp
                                                                     decodeSecond_computable)))
/-- Reading the rank `r` off a packed input is computable. -/
theorem selR_computable : Computable selR :=
    bitsToNat_computable.comp
        (decodeSecond_computable.comp (decodeSecond_computable.comp (decodeSecond_computable.comp
                                                                      decodeSecond_computable)))

/-- Reading `n` off a packed input is primitive recursive. -/
theorem selN_primrec : Primrec selN := bitsToNat_primrec.comp decodeFirst_primrec
/-- Reading `i` off a packed input is primitive recursive. -/
theorem selI_primrec : Primrec selI :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
/-- Reading `j` off a packed input is primitive recursive. -/
theorem selJ_primrec : Primrec selJ :=
    bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))
/-- Reading `k` off a packed input is primitive recursive. -/
theorem selK_primrec : Primrec selK :=
    bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp
                                                               decodeSecond_primrec)))
/-- Reading the rank `r` off a packed input is primitive recursive. -/
theorem selR_primrec : Primrec selR :=
    bitsToNat_primrec.comp
        (decodeSecond_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp
                                                                decodeSecond_primrec)))

/-! ### Uniform computability of the marked-code stream

The fixed-parameter computability lemmas in `EffectiveSelection.lean`
(`familyMarkedCodeStream_computable` etc.) all hold with `i, n, j, k` fixed.
For the selector we need joint (uniform) computability in *all* the numeric
parameters and the stage `t`.  We rebuild the stream's computability with the
parameters bundled into a tuple. -/

/-- `selectionThreshold` is primitive recursive jointly in `(i, k)`. -/
theorem selectionThreshold_primrec :
    Primrec (fun p : ℕ × ℕ => selectionThreshold p.1 p.2) := by
  unfold selectionThreshold
  exact Primrec.nat_div.comp
    (Primrec.nat_add.comp (primrec_two_pow_aux.comp Primrec.snd) Primrec.fst)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))

end Kolmogorov
