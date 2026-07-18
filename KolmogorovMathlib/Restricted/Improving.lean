import KolmogorovMathlib.Restricted.Selection
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions

/-!
# M4: Restricted Improving Descriptions

Plan reference: `PLAN_RESTRICTED_TYPE.md`, milestone M4.

This file assembles the improving descriptions theorem (P-IMP) in the restricted
case. It proves both the size half (using `BasicProfile.lean`'s cover shift) and
the complexity half (using `Selection.lean`'s strategy).
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

theorem ManyIJDescriptionsIn.mono_k {𝒜 : PreDescriptionFamily} {U : Map} {x : BitString}
    {i j k k' : ℕ}
    (h : ManyIJDescriptionsIn 𝒜 U x i j k) (hk : k' ≤ k) : ManyIJDescriptionsIn 𝒜 U x i j k' := by
  unfold ManyIJDescriptionsIn at *
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk) h

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

theorem codedUniformOn_code_injective {S T : Finset BitString}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hcode : (codedUniformOn S hS).code = (codedUniformOn T hT).code) :
    S = T := by
  have hdist : codedUniformOn S hS = codedUniformOn T hT :=
    CodedFiniteDistribution.code_injective hcode
  have hsupp := congrArg CodedFiniteDistribution.support hdist
  simpa [codedUniformOn_support] using hsupp

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

/-- Stress test on `fullFamily`: the restricted description universe is the full
one, since `fullFamily.mem = Nonempty` and every description is nonempty. -/
theorem descriptionsWithComplexityLeAndSizeLeIn_fullFamily (U : Map) (i j : ℕ) :
    descriptionsWithComplexityLeAndSizeLeIn fullFamily U i j
      = descriptionsWithComplexityLeAndSizeLe U i j := by
  classical
  unfold descriptionsWithComplexityLeAndSizeLeIn
  ext S
  rw [Finset.mem_filter]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact nonempty_of_mem_descriptionsWithComplexityLe (Finset.mem_filter.mp h).1

/-- Stress test on `fullFamily`: the restricted multiplicity predicate collapses
to the unrestricted `ManyIJDescriptions` (mirrors M1's
`inDescriptionProfileIn_fullFamily_iff`). -/
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

/-- The total number of marked sets in the stream is bounded by the same
polynomial factor as the unrestricted selection. -/
theorem selected_family_code_index_bound (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) :
    (familyMarkedCodeStream c i 𝒜 n j k t).length ≤ (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k)
        := by
  exact familyMarkedCodeStream_length_bound c i 𝒜 n j k t

/-- Every `n`-bit string with `2^k` visible restricted descriptions is covered
by a selected family description in the stream. -/
theorem familyMarkedCodeStream_covers_many (c : Code) (i : ℕ) (𝒜 : PreDescriptionFamily)
    (n j k t : ℕ) (x : BitString) :
    x.length = n →
    2 ^ k ≤ (familyStageDescriptionCodes c i 𝒜 j t x).card →
    ∃ w ∈ familyMarkedCodeStream c i 𝒜 n j k t, IsFamilyDescriptionCode 𝒜 j x w := by
  intro hxlen hmany
  exact familyMarkedCodeStream_covers c i 𝒜 n j k t x hxlen hmany

theorem eraseDups_bitString_length_le (L : List BitString) :
    L.eraseDups.length ≤ L.length := by
  have hfin : L.eraseDups.toFinset = L.toFinset := by
    ext w
    simp [mem_eraseDups_bitString]
  calc L.eraseDups.length
      = L.eraseDups.toFinset.card :=
        (List.toFinset_card_of_nodup (nodup_eraseDups_bitString L)).symm
    _ = L.toFinset.card := by rw [hfin]
    _ ≤ L.length := List.toFinset_card_le _

theorem exists_rank_getD_eraseDups (L : List BitString) {w : BitString}
    (hw : w ∈ L) :
    ∃ r, r < L.eraseDups.length ∧ L.eraseDups.getD r [] = w := by
  have hw' : w ∈ L.eraseDups := mem_eraseDups_bitString.mpr hw
  rw [List.mem_iff_getElem] at hw'
  rcases hw' with ⟨r, hr, hget⟩
  refine ⟨r, hr, ?_⟩
  simp [List.getD_eq_getElem?_getD, hr, hget]

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
    have hbits_le : (Nat.bits M).length ≤ M := length_natBits_le_self M
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
This is the exact rank fact consumed by the remaining coding leaf. -/
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
      (selected_family_code_index_bound c i 𝒜 n j k t))

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

def familyMarkedInput (n i j k r : ℕ) : BitString :=
  pairCode (Nat.bits n)
      (pairCode (Nat.bits i) (pairCode (Nat.bits j) (pairCode (Nat.bits k) (Nat.bits r))))

@[simp] theorem selN_familyMarkedInput (n i j k r : ℕ) : selN (familyMarkedInput n i j k r) = n :=
    by
  simp [selN, familyMarkedInput, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem selI_familyMarkedInput (n i j k r : ℕ) : selI (familyMarkedInput n i j k r) = i :=
    by
  simp [selI, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem selJ_familyMarkedInput (n i j k r : ℕ) : selJ (familyMarkedInput n i j k r) = j :=
    by
  simp [selJ, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem selK_familyMarkedInput (n i j k r : ℕ) : selK (familyMarkedInput n i j k r) = k :=
    by
  simp [selK, familyMarkedInput, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem selR_familyMarkedInput (n i j k r : ℕ) : selR (familyMarkedInput n i j k r) = r :=
    by
  simp [selR, familyMarkedInput, decodeSecond_pairCode, bitsToNat_bits]

theorem selN_computable : Computable selN := bitsToNat_computable.comp decodeFirst_computable
theorem selI_computable : Computable selI :=
    bitsToNat_computable.comp (decodeFirst_computable.comp decodeSecond_computable)
theorem selJ_computable : Computable selJ :=
    bitsToNat_computable.comp
        (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
theorem selK_computable : Computable selK :=
    bitsToNat_computable.comp
        (decodeFirst_computable.comp (decodeSecond_computable.comp (decodeSecond_computable.comp
                                                                     decodeSecond_computable)))
theorem selR_computable : Computable selR :=
    bitsToNat_computable.comp
        (decodeSecond_computable.comp (decodeSecond_computable.comp (decodeSecond_computable.comp
                                                                      decodeSecond_computable)))

theorem selN_primrec : Primrec selN := bitsToNat_primrec.comp decodeFirst_primrec
theorem selI_primrec : Primrec selI :=
    bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
theorem selJ_primrec : Primrec selJ :=
    bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))
theorem selK_primrec : Primrec selK :=
    bitsToNat_primrec.comp
        (decodeFirst_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp
                                                               decodeSecond_primrec)))
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
    (Primrec.nat_add.comp (primrec_two_pow.comp Primrec.snd) Primrec.fst)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))

/-- `isFamilyModelCodeBool` is primitive recursive jointly in the code `w` and
the parameter `j`. -/
theorem isFamilyModelCodeBool_primrec_uniform :
    Primrec (fun p : BitString × ℕ => isFamilyModelCodeBool p.2 p.1) := by
  unfold isFamilyModelCodeBool
  refine Primrec.and.comp ?_ ?_
  · exact isCanonicalUniformCodeBool_primrec.comp Primrec.fst
  · have h_card : Primrec (fun p : BitString × ℕ =>
        (canonicalFinsetList (((decodeDistributionData p.1).map
          CodedDistributionEntry.point).toFinset)).length) := by
      refine Primrec.list_length.comp
        (Kolmogorov.canonicalFinsetList_toFinset_primrec.comp ?_)
      exact (Primrec.list_map (decodeDistributionData_primrec.comp Primrec.fst)
        (entry_point_primrec.comp Primrec.snd))
    have h2 : Primrec (fun p : BitString × ℕ => 2 ^ p.2) := primrec_two_pow.comp Primrec.snd
    convert Primrec.nat_le.comp h_card h2 using 1
    simp +decide [PrimrecPred]

/-- Uniform version of `blockSelection_primrec`: primitive recursive jointly in
`(n, i, j, k, s)` and the block `B`. -/
theorem blockSelection_primrec_uniform :
    Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString =>
      blockSelection q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2) := by
  have hn : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hB : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString => q.2) := Primrec.snd
  have hm : Primrec (fun q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString =>
      selectionThreshold q.1.2.1 q.1.2.2.2.1) :=
    Primrec₂.comp selectionThreshold_primrec hi hk
  have hpT : Primrec₂ (fun (q : (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) (x : BitString) =>
      decide (selectionThreshold q.1.2.1 q.1.2.2.2.1 ≤
        (q.2.filter (fun b => decide (x ∈ canonicalFinsetList
          (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_le.comp (hm.comp Primrec.fst)
      (coverFilterCount_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hT := list_filter_primrec (allStrings_primrec.comp hn) hpT
  have hTa := hT.comp (Primrec.fst (β := List BitString)
    (α := (ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString))
  have hAllPred : Primrec₂ (fun (a : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) × List BitString)
      (x : BitString) =>
      decide (0 < (a.2.filter (fun b => decide (x ∈ canonicalFinsetList
        (((decodeDistributionData b).map CodedDistributionEntry.point).toFinset)))).length)) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0)
      (coverFilterCount_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hAll := list_all_primrec hTa hAllPred
  have hBound : Primrec (fun a : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List BitString) × List BitString =>
      decide (a.2.length ≤ a.1.2.length * (a.1.1.1 + 1) /
        selectionThreshold a.1.1.2.1 a.1.1.2.2.2.1)) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.nat_div.comp
        (Primrec.nat_mul.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.const 1)))
        (hm.comp Primrec.fst)))
  have hP := (Primrec.and.comp hAll hBound).to₂
  have hg := Primrec.option_getD.comp
    (list_find?_primrec (primrec_sublists_gen hB) hP) (Primrec.const [])
  apply hg.of_eq
  intro q
  unfold blockSelection
  rw [computableGreedyCover_eq]
  congr!

/-- Uniform version of `selectionStrategyOnline_primrec`: primitive recursive
jointly in `(n, i, j, k)` and the list `S`. -/
theorem selectionStrategyOnline_primrec_uniform :
    Primrec (fun q : (ℕ × ℕ × ℕ × ℕ) × List BitString =>
      selectionStrategyOnline q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  unfold selectionStrategyOnline
  refine Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
  refine Primrec.list_flatMap ?_ ?_
  · refine list_filter_primrec
      (Primrec.list_range.comp (Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 2))) ?_
    exact (Primrec.beq.comp
      (Primrec.nat_mod.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
        (primrec_two_pow.comp Primrec.snd)) (Primrec.const 0)).to₂
  · have hn : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hi : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hj : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.2.1) :=
      Primrec.fst.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    have hk : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.1.2.2.2) :=
      Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    have hS : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hm : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hs : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ => r.2) := Primrec.snd
    have hwin : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ =>
        (r.1.1.2.take (r.1.2 + 1)).drop ((r.1.2 + 1) - 2 ^ r.2)) :=
      Primrec.list_drop.comp (Primrec.list_take.comp hS (Primrec.succ.comp hm))
        (Primrec.nat_sub.comp (Primrec.succ.comp hm) (primrec_two_pow.comp hs))
    have htuple : Primrec (fun r : (((ℕ × ℕ × ℕ × ℕ) × List BitString) × ℕ) × ℕ =>
        ((r.1.1.1.1, r.1.1.1.2.1, r.1.1.1.2.2.1, r.1.1.1.2.2.2, r.2),
          (r.1.1.2.take (r.1.2 + 1)).drop ((r.1.2 + 1) - 2 ^ r.2))) :=
      Primrec.pair (Primrec.pair hn (Primrec.pair hi (Primrec.pair hj (Primrec.pair hk hs)))) hwin
    exact (blockSelection_primrec_uniform.comp htuple).to₂

/-- Uniform version of `familyCandidateModelCodesList_computable`: computable
jointly in `(i, j, t)`. -/
theorem familyCandidateModelCodesList_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ =>
      familyCandidateModelCodesList c q.1 𝒜 q.2.1 q.2.2) := by
  unfold familyCandidateModelCodesList
  have hi : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hj : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hw : Primrec (fun r : (List BitString × (ℕ × ℕ × ℕ)) × BitString => r.2) := Primrec.snd
  have h1 := (decide_mem_primrec (β := BitString)).comp
      ((snapshotCodes_primrec c).comp (Primrec.pair hi ht)) hw
  have h2 := isFamilyModelCodeBool_primrec_uniform.comp (Primrec.pair hw hj)
  have hb := Primrec.and.comp h1 h2
  have h_filter := list_filter_primrec
    (f := fun a : List BitString × (ℕ × ℕ × ℕ) => a.1) Primrec.fst hb.to₂
  have hcomp := h_filter.to_comp.comp
    (Computable.pair
      ((𝒜.enumeration.computable).comp (Computable.snd.comp Computable.snd))
      Computable.id)
  refine hcomp.of_eq (fun q => ?_)
  simp only [id_eq]
  apply List.filter_congr
  intro w _
  refine congrArg₂ (· && ·) ?_ rfl
  exact congrArg _ (Subsingleton.elim _ _)

section StageUniform
-- `familyCandidateModelCodesList` is a reducible `def`; unfolding it during the
-- `Computable.comp` unifications below leads to a `whnf` heartbeat blow-up, so we
-- treat it as irreducible and raise the heartbeat budget for this one assembly.
attribute [local irreducible] familyCandidateModelCodesList

set_option maxHeartbeats 1000000 in
-- Uniform version of `familyStageModelCodesList_computable`: computable jointly
-- in `(i, j, t)`.
-- The `Computable.nat_rec` assembly over the accumulated stage lists is
-- elaboration-heavy (but terminating); the default heartbeat budget is too low.
theorem familyStageModelCodesList_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ =>
      familyStageModelCodesList c q.1 𝒜 q.2.1 q.2.2) := by
  have hg : Computable (fun q : ℕ × ℕ × ℕ =>
      (familyCandidateModelCodesList c q.1 𝒜 q.2.1 0).eraseDups) :=
    eraseDups_bitstring_primrec.to_comp.comp
      ((familyCandidateModelCodesList_computable_uniform c 𝒜).comp
        (Computable.pair Computable.fst
          (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const 0))))
  have hh : Computable₂ (fun (q : ℕ × ℕ × ℕ) (p : ℕ × List BitString) =>
      (p.2 ++ familyCandidateModelCodesList c q.1 𝒜 q.2.1 (p.1 + 1)).eraseDups) := by
    have happ : Computable (fun r : (ℕ × ℕ × ℕ) × (ℕ × List BitString) =>
        r.2.2 ++ familyCandidateModelCodesList c r.1.1 𝒜 r.1.2.1 (r.2.1 + 1)) := by
      refine (Primrec.list_append (α := BitString)).to_comp.comp
        (Computable.snd.comp Computable.snd) ?_
      exact (familyCandidateModelCodesList_computable_uniform c 𝒜).comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
            (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    exact (eraseDups_bitstring_primrec.to_comp.comp happ).to₂
  refine (Computable.nat_rec (Computable.snd.comp Computable.snd) hg hh).of_eq (fun q => ?_)
  obtain ⟨i, j, t⟩ := q
  induction t with
  | zero => rfl
  | succ n ih => simp [familyStageModelCodesList, ih]

end StageUniform

section MarkedStreamUniform
-- `selectionStrategyOnline` is a reducible `def`; keeping it irreducible prevents a
-- `whnf` blow-up when the final `of_eq` reconciles the composed function with
-- the unfolded `familyMarkedCodeStream`.
attribute [local irreducible] selectionStrategyOnline

/-- Uniform version of `familyMarkedCodeStream_computable`: computable jointly in
`(i, n, j, k, t)`. -/
theorem familyMarkedCodeStream_computable_uniform
    (c : Code) (𝒜 : PreDescriptionFamily) :
    Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ =>
      familyMarkedCodeStream c q.1 𝒜 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hi : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.1) := Computable.fst
  have hn : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.1) := Computable.fst.comp Computable.snd
  have hjj : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hkk : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have htt : Computable (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hstage := (familyStageModelCodesList_computable_uniform c 𝒜).comp
    (Computable.pair hi (Computable.pair hjj htt))
  have htuple := Computable.pair
    (Computable.pair hn (Computable.pair hi (Computable.pair hjj hkk))) hstage
  unfold familyMarkedCodeStream
  exact (selectionStrategyOnline_primrec_uniform.to_comp.comp htuple).of_eq (fun q => rfl)

end MarkedStreamUniform

noncomputable def familyMarkedCodeSelectorFn (c : Code) (𝒜 : PreDescriptionFamily) : BitString →.
    BitString :=
  fun s =>
    let n := selN s
    let i := selI s
    let j := selJ s
    let k := selK s
    let r := selR s
    (Nat.rfind (fun t => Part.some (decide (r < (familyMarkedCodeStream c i 𝒜 n j k
                                                  t).eraseDups.length)))).bind
      (fun t =>
        let stream := (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups
        Part.some (stream.getD r []))

section SelectorPartrec
attribute [local irreducible] familyMarkedCodeStream selN selI selJ selK selR

theorem familyMarkedCodeSelectorFn_partrec (c : Code) (𝒜 : PreDescriptionFamily) : Partrec
    (familyMarkedCodeSelectorFn c 𝒜) := by
  have h_stream : Computable (fun st : BitString × ℕ =>
      (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
        st.2).eraseDups) :=
    eraseDups_bitstring_primrec.to_comp.comp
      ((familyMarkedCodeStream_computable_uniform c 𝒜).comp
        ((selI_computable.comp Computable.fst).pair
          ((selN_computable.comp Computable.fst).pair
            ((selJ_computable.comp Computable.fst).pair
              ((selK_computable.comp Computable.fst).pair Computable.snd)))))
  have h_lt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have h_check : Computable (fun st : BitString × ℕ =>
      decide (selR st.1 <
        (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
          st.2).eraseDups.length)) :=
    h_lt.comp ((selR_computable.comp Computable.fst).pair
      (Computable.list_length.comp h_stream))
  have h_post : Computable (fun st : BitString × ℕ =>
      (familyMarkedCodeStream c (selI st.1) 𝒜 (selN st.1) (selJ st.1) (selK st.1)
        st.2).eraseDups.getD (selR st.1) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp h_stream
      (selR_computable.comp Computable.fst)
  exact (Partrec.bind (Partrec.rfind h_check.to₂.partrec₂) h_post.to₂.partrec₂).of_eq
    (fun s => rfl)

end SelectorPartrec

theorem familyMarkedCodeSelectorFn_eq_of_rank (c : Code) (𝒜 : PreDescriptionFamily)
    (n i j k r t : ℕ)
    (h_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.length)
    (h_first : ∀ t' < t, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length)) :
    familyMarkedCodeSelectorFn c 𝒜 (familyMarkedInput n i j k r) = Part.some
        ((familyMarkedCodeStream c i 𝒜 n j k t).eraseDups.getD r []) := by
  unfold familyMarkedCodeSelectorFn
  simp only [selN_familyMarkedInput, selI_familyMarkedInput, selJ_familyMarkedInput,
    selK_familyMarkedInput, selR_familyMarkedInput]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨t, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    constructor
    · simp [h_lt]
    · intro m hm
      simp [h_first m hm]
  · simp

theorem familyMarkedInput_KPPlain_le_addr (U : Map) (hU : IsOptimalPrefixConditional U)
    (c_partrec : ℕ) :
    ∃ c_slack : ℕ, ∀ (n i j k r m : ℕ), r < 2 ^ (m + 1) →
      KPPlain U (familyMarkedInput n i j k r) + (c_partrec : ENat) ≤ ((m : ENat) + 1) + logSlack
          c_slack (n + i + j + k + m) := by
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_bits, hc_bits⟩ := logSlack_linear_bound 2 9 5
  refine ⟨(12 + c_len + c_partrec) + c_bits, fun n i j k r m hr => ?_⟩
  let M := n + i + j + k + m
  let W := (Nat.bits M).length
  let w := familyMarkedInput n i j k r
  have hnW : (Nat.bits n).length ≤ W := by exact length_natBits_mono (by omega : n ≤ M)
  have hiW : (Nat.bits i).length ≤ W := by exact length_natBits_mono (by omega : i ≤ M)
  have hjW : (Nat.bits j).length ≤ W := by exact length_natBits_mono (by omega : j ≤ M)
  have hkW : (Nat.bits k).length ≤ W := by exact length_natBits_mono (by omega : k ≤ M)
  have hrm : (Nat.bits r).length ≤ m + 1 := by
    exact length_natBits_lt_pow hr
  have hWle : W ≤ M := by
    simpa [W] using length_natBits_le_self M
  have hw_len : w.length ≤ (m + 1) + (8 * W + 4) := by
    simp [w, familyMarkedInput]
    omega
  have hw_linear : w.length ≤ 9 * M + 5 := by
    calc w.length ≤ (m + 1) + (8 * W + 4) := hw_len
      _ ≤ (m + 1) + (8 * M + 4) := by omega
      _ ≤ 9 * M + 5 := by omega
  have hbits : 2 * (Nat.bits w.length).length ≤ logSlack c_bits M := by
    have hmono : (Nat.bits w.length).length ≤ (Nat.bits (9 * M + 5)).length :=
      length_natBits_mono hw_linear
    have hraw : 2 * (Nat.bits w.length).length ≤ logSlack 2 (9 * M + 5) := by
      unfold logSlack
      omega
    exact hraw.trans (hc_bits M)
  have hdirect : 8 * W + 4 + c_len + c_partrec ≤ logSlack (12 + c_len + c_partrec) M := by
    unfold logSlack
    simp [W]
    nlinarith [Nat.zero_le (c_len * (Nat.bits M).length),
      Nat.zero_le (c_partrec * (Nat.bits M).length),
      Nat.zero_le (4 * (Nat.bits M).length)]
  have hslack : (8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length ≤
      logSlack ((12 + c_len + c_partrec) + c_bits) M := by
    have hsum : (8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length ≤
        logSlack (12 + c_len + c_partrec) M + logSlack c_bits M := by
      omega
    have hadd : logSlack (12 + c_len + c_partrec) M + logSlack c_bits M =
        logSlack ((12 + c_len + c_partrec) + c_bits) M := by
      rw [logSlack_add_const]
    exact hsum.trans (le_of_eq hadd)
  have hnat : w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec ≤
      (m + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M := by
    have hlen' : w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec ≤
        (m + 1) + ((8 * W + 4 + c_len + c_partrec) + 2 * (Nat.bits w.length).length) := by
      omega
    omega
  calc KPPlain U w + (c_partrec : ENat)
      ≤ (w.length + 2 * (Nat.bits w.length).length + (c_len : ENat)) + (c_partrec : ENat) := by
        exact add_le_add (hc_len w) le_rfl
    _ = ((w.length + 2 * (Nat.bits w.length).length + c_len + c_partrec : ℕ) : ENat) := by
        push_cast
        ring
    _ ≤ (((m + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M : ℕ) : ENat) := by
        exact_mod_cast hnat
    _ = ((m : ENat) + 1) + logSlack ((12 + c_len + c_partrec) + c_bits) M := by
        push_cast
        ring

/-- Hard coding leaf for selected marked-code streams.  A code selected by the
effective marked stream has set complexity bounded by its rank in that stream;
`exists_markedStream_rank` and `markedStream_rank_address_slack` provide the
rank-length arithmetic, while the remaining work is the packed computable
decoder for `familyMarkedCodeStream`. -/
theorem selected_family_code_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) :
    ∃ c_slack : ℕ, ∀ (n i j k t : ℕ) (w : BitString)
      (S : Finset BitString) (hS : S.Nonempty),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i 𝒜 n j k t →
      w = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) := by
  have _hc_used : IsCodeFor c U := hc
  obtain ⟨c_map, hc_map⟩ := KPPlain_partrec_map_le U hU (familyMarkedCodeSelectorFn c 𝒜)
    (familyMarkedCodeSelectorFn_partrec c 𝒜)
  obtain ⟨c_input, hc_input⟩ := familyMarkedInput_KPPlain_le_addr U hU c_map
  obtain ⟨c_fold, hc_fold⟩ := logSlack_linear_bound c_input 5 10
  refine ⟨c_fold + 20, fun n i j k t w S hS hk hw_stream hcode => ?_⟩
  obtain ⟨r, hr_stage, hget_t⟩ :=
    exists_rank_getD_eraseDups (familyMarkedCodeStream c i 𝒜 n j k t) hw_stream
  have hr_bound : r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
    exact lt_of_lt_of_le hr_stage
      (le_trans (eraseDups_bitString_length_le _)
        (selected_family_code_index_bound c i 𝒜 n j k t))
  let M := n + i + j
  let P := 2 * ((i + 2) * (i + 1) * (n + 1))
  let q := (Nat.bits P).length
  let m := i - k + q
  have hpowP : P < 2 ^ q := by
    simpa [P, q] using lt_two_pow_length_natBits P
  have hexp : i + 1 - k = i - k + 1 := by omega
  have hbound_eq :
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) =
        P * 2 ^ (i - k) := by
    simp [P, hexp, pow_succ]
    ring
  have hr_pow_m : r < 2 ^ (m + 1) := by
    have hlt : r < P * 2 ^ (i - k) := by
      simpa [hbound_eq] using hr_bound
    have hmul : P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpowP)
    have hpow : 2 ^ q * 2 ^ (i - k) = 2 ^ m := by
      rw [show m = q + (i - k) by omega, pow_add]
    exact lt_of_lt_of_le hlt (by
      calc P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) := hmul
        _ = 2 ^ m := hpow
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ m))
  let h_exists : ∃ u, r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length := ⟨t, hr_stage⟩
  let t0 := Nat.find h_exists
  have ht0_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.length :=
    Nat.find_spec h_exists
  have ht0_le_t : t0 ≤ t :=
    Nat.find_le (p := fun u => r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length) hr_stage
  have hfirst : ∀ t' < t0, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length) := by
    intro t' ht'
    exact Nat.find_min h_exists ht'
  have hpre : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups <+:
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups :=
    familyMarkedCodeStream_eraseDups_prefix_of_le c i 𝒜 n j k ht0_le_t
  have hget_t0 : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.getD r [] = w := by
    have hget := StagedEnumeration.getD_eq_of_prefix
      (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups hpre r [] ht0_lt
    rw [← hget_t]
    exact hget.symm
  have hsel_eq := familyMarkedCodeSelectorFn_eq_of_rank c 𝒜 n i j k r t0 ht0_lt hfirst
  rw [hget_t0] at hsel_eq
  have hw_sel : w ∈ familyMarkedCodeSelectorFn c 𝒜 (familyMarkedInput n i j k r) :=
    Part.eq_some_iff.mp hsel_eq
  have hcomp1 : KPPlain U w ≤ KPPlain U (familyMarkedInput n i j k r) + (c_map : ENat) :=
    hc_map (familyMarkedInput n i j k r) w hw_sel
  have hcomp2 : KPPlain U (familyMarkedInput n i j k r) + (c_map : ENat) ≤
      ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) :=
    hc_input n i j k r m hr_pow_m
  have hq : q ≤ 3 * (Nat.bits M).length + 10 := by
    simpa [M, P, q] using markedStream_poly_bits_bound n i j
  have hm_le : m + 1 ≤ (i - k) + (3 * (Nat.bits M).length + 11) := by
    simp [m]
    omega
  have hbudget : n + i + j + k + m ≤ 5 * M + 10 := by
    have hWle : (Nat.bits M).length ≤ M := length_natBits_le_self M
    simp [M, m]
    omega
  have hfold : logSlack c_input (n + i + j + k + m) ≤ logSlack c_fold M := by
    exact (logSlack_mono (c := c_input) hbudget).trans (hc_fold M)
  have hqslack : 3 * (Nat.bits M).length + 11 + logSlack c_fold M ≤
      logSlack (c_fold + 20) M := by
    unfold logSlack
    nlinarith [Nat.zero_le (17 * (Nat.bits M).length)]
  have htotal : ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) ≤
      (i - k : ENat) + logSlack (c_fold + 20) M := by
    have hnat : m + 1 + logSlack c_input (n + i + j + k + m) ≤
        (i - k) + logSlack (c_fold + 20) M := by
      have hnat1 : m + 1 + logSlack c_input (n + i + j + k + m) ≤
          (i - k) + (3 * (Nat.bits M).length + 11 + logSlack c_fold M) := by
        omega
      omega
    exact_mod_cast hnat
  unfold setComplexity
  rw [← hcode]
  exact (hcomp1.trans hcomp2).trans htotal

/-- The complexity bound for elements extracted from the marked stream.  The
nontrivial coding work is isolated in `selected_family_code_setComplexity_bound`;
this wrapper just decodes `IsFamilyDescriptionCode`, carrying forward family
membership, membership of `x`, and the `2^j` size bound. -/
theorem selected_family_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c U) (𝒜 : PreDescriptionFamily) :
    ∃ c_slack : ℕ, ∀ (x : BitString) (n i j k t : ℕ) (w : BitString),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i 𝒜 n j k t →
      IsFamilyDescriptionCode 𝒜 j x w →
      ∃ (S : Finset BitString) (hS : S.Nonempty), 𝒜.mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) ∧
        S.card ≤ 2 ^ j := by
  obtain ⟨c_slack, hcode⟩ := selected_family_code_setComplexity_bound U hU c hc 𝒜
  refine ⟨c_slack, fun x n i j k t w hk hw_stream hw_desc => ?_⟩
  rcases hw_desc with ⟨S, hS, hmem, hcode_eq, hcard, hxS⟩
  exact ⟨S, hS, hmem, hxS, hcode n i j k t w S hS hk hw_stream hcode_eq, hcard⟩

/-- **Selector obligation for the restricted complexity half (M4 core leaf).**

The concrete set-existence content of the restricted Improving Descriptions
theorem (complexity half), phrased exactly as the *proved* unrestricted
`setComplexity_halfRichComplexityPortion_le` /
`exists_halfRichComplexityRefinedSet_logSlack` (`DescriptionSnapshot.lean`): an
effective selection over the family enumeration produces, for every length-`n`
string `x` with `2^k` restricted `(i,j)`-descriptions, a family member `S ∋ x`
of complexity `≤ (i-k) + O(log(n+i+j))` and log-size `≤ j + O(log(n+i+j))`.

This is the single remaining M4 computability leaf.  Intended construction
(matches the unrestricted `emittedHalfRichChunks` proof and plan M4):
* make the finite-stage greedy selection of `Selection.lean` *effective* — an
  explicit computable marked-code stream over the family enumeration
  (`𝒜.enumeration.computable`), instead of the current `Classical.choose`-based
  `selectionStrategy`; coverage is `selectionStrategy_covers`, the count bound is
  `selectionStrategy_length_bound` (`≤ (i+1)²(n+1)2^(i+1-k)`, i.e. `2^(i-k)` up
  to the visible `poly(n)` factor);
* the marked set containing `x` is then recovered by its ordinal index in the
  marked stream, of length `≤ (i-k) + O(log n)`, via the M0 fixed-length index
  bound `StagedEnumeration.KP_le_fixed_length_index_of_cond_enumeration`.
Family membership `𝒜.mem S` is automatic from the enumeration soundness
(condition (1)); the complexity half uses only condition (1). -/
theorem exists_familyComplexityRefinedSet (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : PreDescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜 U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), 𝒜.mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c_code, hc_code⟩ : ∃ c_code : Code, IsCodeFor c_code U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_slack, hc_slack⟩ := selected_family_setComplexity_bound U hU c_code hc_code 𝒜
  refine ⟨c_slack, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨t, ht⟩ := manyIJDescriptionsIn_visible_stage hc_code 𝒜 x n i j k hn hmany
  obtain ⟨w, hw_stream, hw_desc⟩ := familyMarkedCodeStream_covers_many c_code i 𝒜 n j k t x hn ht
  obtain ⟨S, hS, hmem, hxS, hcomp, hcard⟩ := hc_slack x n i j k t w hk hw_stream hw_desc
  refine ⟨S, hS, hmem, hxS, ?_, ?_⟩
  · exact hcomp
  · refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))

/-- Restricted Improving Descriptions (complexity half).  Proved from the
concrete selector obligation `exists_familyComplexityRefinedSet` by the standard
profile assembly (the same trivial glue as the proved unrestricted
`exists_description_smaller_complexity_of_many_logSlack`): the selected family
member `S ∋ x` is exactly an `𝒜`-description witnessing the shifted profile
point. -/
theorem inDescriptionProfileIn_improving_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsIn 𝒜 U x i j k →
      k ≤ i →
      InDescriptionProfileIn 𝒜 U x
        (i - k + logSlack c (n + i + j))
        (j + logSlack c (n + i + j)) := by
  obtain ⟨c, hc⟩ := exists_familyComplexityRefinedSet U hU 𝒜
  refine ⟨c, fun x n i j k hn hmany hk => ?_⟩
  obtain ⟨S, hS, hmem, hxS, hcomp, hcard⟩ := hc x n i j k hn hmany hk
  exact ⟨S, hS, hmem, hxS, hcomp, hcard⟩

end Kolmogorov
