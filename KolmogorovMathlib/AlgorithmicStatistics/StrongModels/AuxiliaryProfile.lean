import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.NormalPair
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.ProfileCardinality
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.T3Boundary

/-!
# The auxiliary profile of VS40 Theorem `card`

This file collects the auxiliary-profile machinery used by the lower bound on
profile cardinality: the vertical-shift re-encoding of a boundary curve, the
auxiliary profile `P̃`, its boundary, the exact add-noise transform identity,
the continuity of that transform, and the supply of conditionally random
tails.  The capstone `thm_card` itself lives in `ProfileCardinalityLower`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The auxiliary profile `P̃` used to bound the cardinality from below. -/
def auxiliaryProfile (P : Set (Nat × Nat)) (mp kp : Nat) : Set (Nat × Nat) :=
  {q | (q.1 ≤ mp ∧ (q.1, q.2 + (kp - mp)) ∈ P) ∨ mp ≤ q.1}

/-- Re-encode the boundary obtained by subtracting a fixed vertical offset
from a decoded curve and truncating it at the supplied new endpoint.  The
input is `pairCode oldCode (pairCode (natCode newK) (natCode offset))`. -/
noncomputable def auxiliaryCurveCode (w : BitString) : BitString :=
  let oldCode := decodeFirst w
  let params := decodeSecond w
  let newK := decodeNatCode (decodeFirst params)
  let offset := decodeNatCode (decodeSecond params)
  curveEncode (fun i => decodeCurve oldCode i - offset) newK

/-- Re-encoding a curve after subtracting an offset and truncating is computable. -/
theorem auxiliaryCurveCode_computable : Computable auxiliaryCurveCode := by
  unfold auxiliaryCurveCode curveEncode
  have hcode : Primrec (fun w : BitString => decodeFirst w) :=
    decodeFirst_primrec
  have hnewK : Primrec (fun w : BitString =>
      decodeNatCode (decodeFirst (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
  have hoffset : Primrec (fun w : BitString =>
      decodeNatCode (decodeSecond (decodeSecond w))) :=
    decodeNatCode_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec)
  have hrange : Primrec (fun w : BitString =>
      List.range (decodeNatCode (decodeFirst (decodeSecond w)) + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp hnewK)
  have hvalue : Primrec₂ (fun (w : BitString) (i : ℕ) =>
      decodeCurve (decodeFirst w) i -
        decodeNatCode (decodeSecond (decodeSecond w))) :=
    Primrec.nat_sub.comp
      (decodeCurve_primrec.comp (hcode.comp Primrec.fst) Primrec.snd)
      (hoffset.comp Primrec.fst)
  have hmap : Primrec (fun w : BitString =>
      (List.range (decodeNatCode (decodeFirst (decodeSecond w)) + 1)).map
        (fun i => decodeCurve (decodeFirst w) i -
          decodeNatCode (decodeSecond (decodeSecond w)))) :=
    Primrec.list_map hrange hvalue
  have hfinal : Primrec (fun w : BitString =>
      ((List.range (decodeNatCode (decodeFirst (decodeSecond w)) + 1)).map
        (fun i => decodeCurve (decodeFirst w) i -
          decodeNatCode (decodeSecond (decodeSecond w)))).flatMap
            (fun v => List.replicate v true ++ [false])) := by
    apply Primrec.list_flatMap hmap
    have hnat : Primrec₂ (fun (_ : BitString) (v : ℕ) => natCode v) :=
      primrec_natCode.comp Primrec.snd
    simpa [natCode] using hnat
  exact hfinal.to_comp

/-- On the input packing an old curve code with a new endpoint and an offset, the encoder returns
the curve obtained by lowering the old curve by the offset and cutting it at the new endpoint. -/
theorem auxiliaryCurveCode_input (oldCode : BitString) (newK offset : ℕ) :
    auxiliaryCurveCode
        (pairCode oldCode (pairCode (natCode newK) (natCode offset))) =
      curveEncode (fun i => decodeCurve oldCode i - offset) newK := by
  simp [auxiliaryCurveCode, decodeFirst_pairCode, decodeSecond_pairCode,
    decodeNatCode_natCode]

/-- The canonical code of the vertically shifted boundary costs at most a
linear multiple of the old boundary complexity plus logarithmic endpoint
advice. -/
lemma auxiliaryCurveCode_complexity
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (b : ProfileBoundary V) (newK offset n : ℕ),
      newK ≤ n → offset ≤ n →
      (plainK V (curveEncode (fun i => b.height i - offset) newK)).toNat ≤
        C * b.KP + logSlack C n := by
  obtain ⟨cMap, hMap⟩ :=
    plainK_map_le V hV auxiliaryCurveCode auxiliaryCurveCode_computable
  obtain ⟨cPlainPair, hPlainPair⟩ :=
    plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨cPrefixPair, hPrefixPair⟩ :=
    KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨cNat, hNat⟩ := KPPlain_natCode_le_log U hU
  obtain ⟨cExact, hExact⟩ :=
    KP_le_condK_given_plain_program_length V U hV hU
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cLength, hLength⟩ := KPPlain_le_two_mul_length U hU
  let C := cExact + cRemove + cLength + 2 * cNat + cPrefixPair +
    cPlainPair + cMap + 7
  refine ⟨C, ?_⟩
  intro b newK offset n hnewK hoffset
  have hbFinite : plainK V b.code ≠ ⊤ :=
    condK_ne_top_of_optimal V hV b.code []
  have hbValue : plainK V b.code = (b.KP : ENat) := by
    rw [b.h_KP]
    exact (ENat.coe_toNat hbFinite).symm
  have hbExact : KP U b.code (pairCode [] (Nat.bits b.KP)) ≤
      ((b.KP + cExact : ℕ) : ENat) := by
    exact_mod_cast hExact b.code [] b.KP hbValue
  have hbBits : KPPlain U (Nat.bits b.KP) ≤
      ((2 * (Nat.bits b.KP).length + cLength : ℕ) : ENat) :=
    hLength (Nat.bits b.KP)
  have hbPrefix : KPPlain U b.code ≤
      ((b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove : ℕ) :
        ENat) := by
    calc
      KPPlain U b.code
          ≤ KP U b.code (pairCode [] (Nat.bits b.KP)) +
              KPPlain U (Nat.bits b.KP) + (cRemove : ENat) :=
        hRemove b.code [] (Nat.bits b.KP)
      _ ≤ ((b.KP + cExact : ℕ) : ENat) +
          ((2 * (Nat.bits b.KP).length + cLength : ℕ) : ENat) +
            (cRemove : ENat) := by gcongr
      _ = _ := by push_cast; ring
  let params := pairCode (natCode newK) (natCode offset)
  let input := pairCode b.code params
  have hparams : KPPlain U params ≤
      ((2 * (Nat.bits newK).length + cNat +
        (2 * (Nat.bits offset).length + cNat) + cPrefixPair : ℕ) : ENat) := by
    change KPPair U (natCode newK) (natCode offset) ≤ _
    calc
      KPPair U (natCode newK) (natCode offset)
          ≤ KPPlain U (natCode newK) + KPPlain U (natCode offset) +
              (cPrefixPair : ENat) := hPrefixPair _ _
      _ ≤ ((2 * (Nat.bits newK).length + cNat : ℕ) : ENat) +
            ((2 * (Nat.bits offset).length + cNat : ℕ) : ENat) +
              (cPrefixPair : ENat) := by
            gcongr
            · exact hNat newK
            · exact hNat offset
      _ = _ := by push_cast; ring
  have hinput : plainK V input ≤
      ((b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove +
        (2 * (Nat.bits newK).length + cNat +
          (2 * (Nat.bits offset).length + cNat) + cPrefixPair) +
        cPlainPair : ℕ) : ENat) := by
    calc
      plainK V input ≤
          KPPlain U b.code + KPPlain U params + (cPlainPair : ENat) :=
        hPlainPair _ _
      _ ≤ ((b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove : ℕ) : ENat) +
          ((2 * (Nat.bits newK).length + cNat +
            (2 * (Nat.bits offset).length + cNat) + cPrefixPair : ℕ) : ENat) +
            (cPlainPair : ENat) := by gcongr
      _ = _ := by push_cast; ring
  have hnewKBits : (Nat.bits newK).length ≤ (Nat.bits n).length :=
    length_natBits_mono hnewK
  have hoffsetBits : (Nat.bits offset).length ≤ (Nat.bits n).length :=
    length_natBits_mono hoffset
  have hbBits : (Nat.bits b.KP).length ≤ b.KP :=
    length_natBits_le b.KP
  have hbudget :
      b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove +
          (2 * (Nat.bits newK).length + cNat +
            (2 * (Nat.bits offset).length + cNat) + cPrefixPair) +
          cPlainPair + cMap ≤
        C * b.KP + logSlack C n := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length)]
  have hcode : auxiliaryCurveCode input =
      curveEncode (fun i => b.height i - offset) newK := by
    rw [show input = pairCode b.code
        (pairCode (natCode newK) (natCode offset)) from rfl,
      auxiliaryCurveCode_input]
    congr 2
    funext i
    rw [b.decodeCurve_code]
  have hbound :
      plainK V (curveEncode (fun i => b.height i - offset) newK) ≤
        ((C * b.KP + logSlack C n : ℕ) : ENat) := by
    rw [← hcode]
    calc
      plainK V (auxiliaryCurveCode input)
          ≤ plainK V input + (cMap : ENat) := hMap input
      _ ≤ ((b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove +
          (2 * (Nat.bits newK).length + cNat +
            (2 * (Nat.bits offset).length + cNat) + cPrefixPair) +
          cPlainPair : ℕ) : ENat) + (cMap : ENat) := by gcongr
      _ = ((b.KP + cExact + 2 * (Nat.bits b.KP).length + cLength + cRemove +
          (2 * (Nat.bits newK).length + cNat +
            (2 * (Nat.bits offset).length + cNat) + cPrefixPair) +
          cPlainPair + cMap : ℕ) : ENat) := by push_cast; ring
      _ ≤ ((C * b.KP + logSlack C n : ℕ) : ENat) := by
        exact_mod_cast hbudget
  have hnewFinite :
      plainK V (curveEncode (fun i => b.height i - offset) newK) ≠ ⊤ :=
    condK_ne_top_of_optimal V hV _ []
  rw [← ENat.coe_toNat hnewFinite] at hbound
  exact_mod_cast hbound

/-- The auxiliary profile of an admissible profile set is again admissible. -/
lemma auxiliaryProfile_isAdmissible (P : Set (Nat × Nat)) (kp mp : ℕ)
    (hadm : IsAdmissibleProfileSet P) (_hkP : kP P = (kp : ENat)) (hmP : mP P kp = (mp : ENat)) :
    IsAdmissibleProfileSet (auxiliaryProfile P mp kp) := by
  have hmp_mem : (mp, kp - mp) ∈ P := m_P_mem_of_eq P kp mp hmP
  have hUp : IsUpperSet P := hadm.isUpperSet
  have hstep := hadm.step
  refine ⟨⟨(mp, 0), ?_⟩, ?_, ?_⟩
  · simp [auxiliaryProfile]
  · intro ⟨a1, b1⟩ ⟨a2, b2⟩ hle hmem
    rcases Prod.mk_le_mk.mp hle with ⟨ha, _⟩
    simp only [auxiliaryProfile, Set.mem_setOf_eq] at hmem ⊢
    rcases hmem with ⟨_, hP⟩ | hmp_le
    · rcases Nat.lt_or_ge mp a2 with _ | _
      · right; omega
      · left
        refine ⟨by omega, ?_⟩
        apply hUp (Prod.mk_le_mk.mpr ⟨ha, by omega⟩) hP
    · right; omega
  · intro a b c habc
    simp only [auxiliaryProfile, Set.mem_setOf_eq] at habc ⊢
    rcases habc with ⟨_, hP⟩ | hmp_le
    · rcases Nat.lt_or_ge mp (a + b) with _ | _
      · right; omega
      · left
        refine ⟨by omega, ?_⟩
        have hP' : (a, b + (c + (kp - mp))) ∈ P := by
          have heq : b + c + (kp - mp) = b + (c + (kp - mp)) := by omega
          rwa [← heq]
        exact hstep a b (c + (kp - mp)) hP'
    · right; omega

/-- The auxiliary profile of a boundary-presented profile set is again cut out by a boundary, with
horizontal intercept `mp`, vertical intercept `np - (kp - mp)` and complexity linear in the
original one plus a logarithmic term. -/
lemma auxiliaryProfile_boundary (V U : Map)
    (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
  ∃ C : ℕ, ∀ (P : Set (Nat × Nat)) (kp mp np : ℕ) (b : ProfileBoundary V),
    IsAdmissibleProfileSet P →
    profileSet V b = P →
    kP P = (kp : ENat) →
    mP P kp = (mp : ENat) →
    nP P = (np : ENat) →
    ∃ b_tilde : ProfileBoundary V,
      b_tilde.kP = mp ∧
      b_tilde.nP = np - (kp - mp) ∧
      profileSet V b_tilde = auxiliaryProfile P mp kp ∧
      b_tilde.KP ≤ C * b.KP + logSlack C np := by
  obtain ⟨C, hcomplexity⟩ := auxiliaryCurveCode_complexity V U hV hU
  refine ⟨C, ?_⟩
  intro P kp mp np b hadm hbP hkP hmP hnP
  have hbKP : kP P = (b.kP : ENat) := by
    rw [← hbP]
    exact b.k_P_profileSet
  have hbNP : nP P = (b.nP : ENat) := by
    rw [← hbP]
    exact b.n_P_profileSet
  have hbk : b.kP = kp := by
    exact_mod_cast hbKP.symm.trans hkP
  have hbn : b.nP = np := by
    exact_mod_cast hbNP.symm.trans hnP
  have hmpkp : mp ≤ kp := by
    have h := m_P_le_k_P_of_eq P kp hkP
    rw [hmP, hkP] at h
    exact_mod_cast h
  have hkpnp : kp ≤ np := by
    have h := k_P_le_n_P_of_admissible hadm
    rw [hkP, hnP] at h
    exact_mod_cast h
  let d := kp - mp
  have hdnp : d ≤ np := by
    dsimp [d]
    omega
  have hmpnp : mp ≤ np := hmpkp.trans hkpnp
  have hmpHeight : b.height mp ≤ d := by
    have hmem : (mp, d) ∈ P := by
      dsimp [d]
      exact m_P_mem_of_eq P kp mp hmP
    rw [← hbP] at hmem
    exact hmem
  have hzeroAfter : ∀ i, mp ≤ i → b.height i - d = 0 := by
    intro i hi
    have hle := b.antitone hi
    omega
  have hpositiveBefore : ∀ i, i < mp → 0 < b.height i - d := by
    intro i hi
    by_contra hnot
    have hheight : b.height i ≤ d := by omega
    have hdiagB : (i, kp - i) ∈ profileSet V b := by
      change b.height i ≤ kp - i
      dsimp [d] at hheight
      omega
    have hdiag : (i, kp - i) ∈ P := by
      rw [← hbP]
      exact hdiagB
    have hle : mP P kp ≤ (i : ENat) := by
      unfold mP
      apply sInf_le
      exact ⟨i, rfl, hdiag⟩
    rw [hmP] at hle
    have : mp ≤ i := by exact_mod_cast hle
    omega
  let b_tilde : ProfileBoundary V := {
    height := fun i => b.height i - d
    kP := mp
    nP := np - d
    height_zero_of_ge := hzeroAfter
    height_pos_of_lt := hpositiveBefore
    height_zero := by rw [b.height_zero, hbn]
    antitone := by
      intro i j hij
      exact Nat.sub_le_sub_right (b.antitone hij) d
    slope := by
      intro i
      by_cases hle : b.height i ≤ d
      · exact Or.inl (by omega)
      · right
        have hpos : 0 < b.height i := by omega
        rcases b.slope i with hzero | hlt
        · omega
        · omega
    code := curveEncode (fun i => b.height i - d) mp
    h_code := rfl
    KP := (plainK V (curveEncode (fun i => b.height i - d) mp)).toNat
    h_KP := rfl }
  refine ⟨b_tilde, rfl, rfl, ?_, ?_⟩
  · ext ⟨i, j⟩
    change b.height i - d ≤ j ↔
      (i ≤ mp ∧ (i, j + (kp - mp)) ∈ P) ∨ mp ≤ i
    constructor
    · intro hij
      rcases Nat.lt_or_ge i mp with himp | hmpi
      · left
        refine ⟨himp.le, ?_⟩
        rw [← hbP]
        change b.height i ≤ j + (kp - mp)
        dsimp [d] at hij
        omega
      · exact Or.inr hmpi
    · rintro (⟨_hi, hmem⟩ | hmpi)
      · rw [← hbP] at hmem
        change b.height i ≤ j + (kp - mp) at hmem
        dsimp [d]
        omega
      · exact hzeroAfter i hmpi ▸ Nat.zero_le j
  · exact hcomplexity b mp d np hmpnp hdnp

/-- The noise transform is continuous in its arguments: profile sets and parameters that agree up to
`eps` are sent to profile sets that agree up to `C * eps`. -/
lemma addNoiseProfileTransform_continuity :
  ∃ C : ℕ, ∀ (P' P'' : Set (Nat×Nat)) (kx kx' kxy kxy' l l' eps : ℕ),
    ProfileSetsWithinNeighborhood P' P'' eps →
    kx ≤ kx' + eps → kx' ≤ kx + eps →
    kxy ≤ kxy' + eps → kxy' ≤ kxy + eps →
    l ≤ l' + eps → l' ≤ l + eps →
    (∀ q ∈ P', kxy ≤ q.1 + q.2 + l + eps) →
    (∀ q ∈ P'', kxy' ≤ q.1 + q.2 + l' + eps) →
    ProfileSetsWithinNeighborhood (AddNoiseProfileTransform P' kx kxy l)
      (AddNoiseProfileTransform P'' kx' kxy' l') (C * eps) := by
  refine ⟨3, ?_⟩
  intro P' P'' kx kx' kxy kxy' l l' eps hnear
    hkx hkx' hkxy hkxy' hl hl' hsuff hsuff'
  have transport :
      ∀ (A B : Set (Nat × Nat)) (ka kb kpa kpb la lb : ℕ),
        ProfileSetsWithinNeighborhood A B eps →
        ka ≤ kb + eps → kb ≤ ka + eps →
        kpa ≤ kpb + eps → kpb ≤ kpa + eps →
        la ≤ lb + eps → lb ≤ la + eps →
        (∀ q ∈ B, kpb ≤ q.1 + q.2 + lb + eps) →
        ∀ q ∈ AddNoiseProfileTransform A ka kpa la,
          ∃ q' ∈ AddNoiseProfileTransform B kb kpb lb,
            natPairLInfDistance q q' ≤ 3 * eps := by
    intro A B ka kb kpa kpb la lb hAB hka hkb hkpa hkpb hla hlb hBsuff
    rintro ⟨a, b⟩ hab
    rcases hab with hbase | hhigh
    · rcases hbase with ⟨i, j, hi, hij, hq⟩
      have ha : a = i := congrArg Prod.fst hq
      have hb : b = j + la := congrArg Prod.snd hq
      subst a
      subst b
      obtain ⟨⟨u, v⟩, huv, hdist⟩ := hAB.1 (i, j) hij
      unfold natPairLInfDistance at hdist
      by_cases hukb : u ≤ kb
      · refine ⟨(u, v + lb), Or.inl ⟨u, v, hukb, huv, rfl⟩, ?_⟩
        unfold natPairLInfDistance
        apply max_le <;> omega
      · refine ⟨(u, v + lb + eps), Or.inr ⟨Nat.lt_of_not_ge hukb, ?_⟩, ?_⟩
        · have hs := hBsuff (u, v) huv
          omega
        · unfold natPairLInfDistance
          apply max_le <;> omega
    · rcases hhigh with ⟨hka_lt, hkpa_sum⟩
      by_cases hkb_lt : kb < a
      · refine ⟨(a, b + eps), Or.inr ⟨hkb_lt, ?_⟩, ?_⟩
        · omega
        · unfold natPairLInfDistance
          apply max_le <;> omega
      · have hakb : a ≤ kb := Nat.le_of_not_gt hkb_lt
        refine ⟨(kb + 1, b + eps), Or.inr ⟨by omega, ?_⟩, ?_⟩
        · omega
        · unfold natPairLInfDistance
          apply max_le <;> omega
  constructor
  · exact transport P' P'' kx kx' kxy kxy' l l' hnear
      hkx hkx' hkxy hkxy' hl hl' hsuff'
  · exact transport P'' P' kx' kx kxy' kxy l' l hnear.symm
      hkx' hkx hkxy' hkxy hl' hl hsuff

/-- For every `y` and every `d` there are at least about `2 ^ d` strings of length `d` that are
random given `y` up to a fixed additive constant. -/
lemma exists_many_conditionally_random_tails {V : Map} :
  ∃ C : ℕ, ∀ (y : BitString) (d : ℕ),
    ∃ R : Finset BitString,
      R.Nonempty ∧
      (∀ z ∈ R,
        z.length = d ∧
        (d : ENat) ≤ condK V z y + (C : ENat)) ∧
      (d : ENat) ≤ finiteSetLogCard R + (C : ENat) := by
  classical
  refine ⟨2, fun y d => ?_⟩
  rcases Nat.lt_or_ge d 3 with hd | hd
  · -- Small `d`: the whole length-`d` cube works, everything is `≤ 2`.
    refine ⟨stringsOfLength d, ?_, ?_, ?_⟩
    · exact Finset.card_pos.mp (by rw [card_stringsOfLength]; positivity)
    · intro z hz
      refine ⟨(mem_stringsOfLength d z).mp hz, ?_⟩
      calc (d : ENat) ≤ ((2 : ℕ) : ENat) := by exact_mod_cast (show d ≤ 2 by omega)
        _ ≤ condK V z y + ((2 : ℕ) : ENat) := le_add_self
    · calc (d : ENat) ≤ ((2 : ℕ) : ENat) := by exact_mod_cast (show d ≤ 2 by omega)
        _ ≤ (finiteSetLogCard (stringsOfLength d) : ENat) + ((2 : ℕ) : ENat) := le_add_self
  · -- `d ≥ 3`: direct incompressibility counting.
    set R := (stringsOfLength d).filter
      (fun z => ¬ (condK V z y ≤ ((d - 2 : ℕ) : ENat))) with hR
    set Bad := (stringsOfLength d).filter
      (fun z => condK V z y ≤ ((d - 2 : ℕ) : ENat)) with hBad
    -- The `≤ d-2` slice lands in the compressible words of budget `d-2`.
    have hBad_sub : Bad ⊆ compressibleWords V y (d - 2) := by
      intro z hz
      rw [hBad, Finset.mem_filter] at hz
      have hlt : condK V z y < ((d - 1 : ℕ) : ENat) :=
        lt_of_le_of_lt hz.2 (by exact_mod_cast (show d - 2 < d - 1 by omega))
      have hmem := mem_compressibleWords_of_condK_lt V z y (d - 1) (by omega) hlt
      have heq : (d - 1) - 1 = d - 2 := by omega
      rwa [heq] at hmem
    have hBad_lt : Bad.card < 2 ^ (d - 1) := by
      calc Bad.card ≤ (compressibleWords V y (d - 2)).card := Finset.card_le_card hBad_sub
        _ < 2 ^ ((d - 2) + 1) := card_compressibleWordsLt V y (d - 2)
        _ = 2 ^ (d - 1) := by congr 1; omega
    -- The two filters partition the length-`d` cube.
    have hsum : Bad.card + R.card = 2 ^ d := by
      have h := Finset.card_filter_add_card_filter_not
        (s := stringsOfLength d) (fun z => condK V z y ≤ ((d - 2 : ℕ) : ENat))
      rw [card_stringsOfLength] at h
      exact h
    have hpow : (2 : ℕ) ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
      have h1 : (d - 1) + 1 = d := by omega
      calc (2 : ℕ) ^ d = 2 ^ ((d - 1) + 1) := by rw [h1]
        _ = 2 ^ (d - 1) * 2 := pow_succ 2 (d - 1)
        _ = 2 ^ (d - 1) + 2 ^ (d - 1) := by ring
    have hR_card : 2 ^ (d - 1) < R.card := by omega
    have hlog : d ≤ finiteSetLogCard R := by
      have hnot : ¬ (R.card ≤ 2 ^ (d - 1)) := by omega
      have hnot' : ¬ (finiteSetLogCard R ≤ d - 1) := by
        rw [finiteSetLogCard_le_iff]; exact hnot
      omega
    refine ⟨R, ?_, ?_, ?_⟩
    · rw [← Finset.card_pos]; omega
    · intro z hz
      rw [hR, Finset.mem_filter] at hz
      refine ⟨(mem_stringsOfLength d z).mp hz.1, ?_⟩
      have hlt : ((d - 2 : ℕ) : ENat) < condK V z y := not_le.mp hz.2
      have hle2 : ((d - 2 : ℕ) : ENat) ≤ condK V z y := le_of_lt hlt
      have hd2 : (d : ENat) = ((d - 2 : ℕ) : ENat) + ((2 : ℕ) : ENat) := by
        rw [← Nat.cast_add]; congr 1; omega
      calc (d : ENat) = ((d - 2 : ℕ) : ENat) + ((2 : ℕ) : ENat) := hd2
        _ ≤ condK V z y + ((2 : ℕ) : ENat) := by gcongr
    · calc (d : ENat) ≤ (finiteSetLogCard R : ENat) := by exact_mod_cast hlog
        _ ≤ (finiteSetLogCard R : ENat) + ((2 : ℕ) : ENat) := le_self_add

/-- Adding `kp - mp` noise bits to the auxiliary profile of `P` recovers `P` itself. -/
lemma addNoiseProfileTransform_auxiliaryProfile :
  ∀ (P : Set (Nat × Nat)) (kp mp : ℕ),
    IsAdmissibleProfileSet P →
    kP P = (kp : ENat) →
    mP P kp = (mp : ENat) →
    AddNoiseProfileTransform (auxiliaryProfile P mp kp) mp kp (kp - mp) = P := by
  intro P kp mp hadm hkP hmP
  have hkp_mem : (kp, 0) ∈ P := k_P_mem_of_eq P kp hkP
  have hmp_mem : (mp, kp - mp) ∈ P := m_P_mem_of_eq P kp mp hmP
  have hUp : IsUpperSet P := hadm.isUpperSet
  have hstep := hadm.step
  have hmp_le_kp : mp ≤ kp := by
    have h := m_P_le_k_P_of_eq P kp hkP
    rw [hmP, hkP] at h
    exact_mod_cast h
  -- The crux: the step condition (with `c = 0`) forces `kp ≤ a + b` for every `(a,b) ∈ P`.
  have hsuff : ∀ a b : ℕ, (a, b) ∈ P → kp ≤ a + b := by
    intro a b hab
    have hstep' : (a + b, 0) ∈ P := by simpa using hstep a b 0 (by simpa using hab)
    have hle : kP P ≤ ((a + b : ℕ) : ENat) := sInf_le ⟨a + b, rfl, hstep'⟩
    rw [hkP] at hle; exact_mod_cast hle
  ext ⟨a, b⟩
  simp only [AddNoiseProfileTransform, auxiliaryProfile, Set.mem_setOf_eq, Prod.mk.injEq]
  constructor
  · rintro (⟨i, j, hi, hij, ha, hb⟩ | ⟨hmpa, hkab⟩)
    · subst ha
      rcases hij with ⟨_, hijP⟩ | hi'
      · rw [hb]; exact hijP
      · have hie : a = mp := le_antisymm hi hi'
        rw [hb, hie]
        exact hUp (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_add_left _ _⟩) hmp_mem
    · rcases Nat.lt_or_ge a kp with hak | hak
      · have hpre : (mp, (a - mp) + (kp - a)) ∈ P := by
          have hmp_eq : (a - mp) + (kp - a) = kp - mp := by omega
          rw [hmp_eq]; exact hmp_mem
        have hdiag : (a, kp - a) ∈ P := by
          have h := hstep mp (a - mp) (kp - a) hpre
          have hmpa' : mp + (a - mp) = a := by omega
          rwa [hmpa'] at h
        exact hUp (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) hdiag
      · exact hUp (Prod.mk_le_mk.mpr ⟨hak, by omega⟩) hkp_mem
  · intro hab
    rcases Nat.lt_or_ge mp a with ham | ham
    · exact Or.inr ⟨ham, hsuff a b hab⟩
    · have hkab := hsuff a b hab
      refine Or.inl ⟨a, b - (kp - mp), ham, Or.inl ⟨ham, ?_⟩, rfl, ?_⟩
      · have hbe : (b - (kp - mp)) + (kp - mp) = b := by omega
        rw [hbe]; exact hab
      · omega
end Kolmogorov
