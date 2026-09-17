import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.Position
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.TailProfile.Part01

/-!
# The tail characterisation of the description profile

`tail_characterization`: on the range `i + j ≤ n` the ordinary description profile of a
length-`n` string and its suffix position in the completed enumeration agree, up to
logarithmic slack.  `tail_characterization_forward` is the half proved here — a string whose
profile contains `(i, j)` has at least `2 ^ j` strings after it — and the other half comes
from `TailProfile/Part01`.

`OmegaSelectorBounds` names the two constants the budget estimate depends on (how much the
tail selector and the dyadic-block decoder raise plain complexity), `omega_count_budget_le`
bounds the budget `m` in terms of them, and `logSlack_dominates_constants`,
`tail_payload_length_le`, `nat_le_two_pow` and `le_two_pow_add_ten` are the size estimates
that absorb the constants into the slack.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- Every natural number `k` is bounded by `2 ^ k`. -/
private theorem nat_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ q hq =>
    rw [pow_succ']
    linarith [Nat.one_le_pow q 2 zero_lt_two]

/-- Every natural number `K` satisfies `K ≤ 2 ^ (K + 10)`. -/
private theorem le_two_pow_add_ten (K : ℕ) : K ≤ 2 ^ (K + 10) := by
  have hK := nat_le_two_pow K
  have hpow : 2 ^ K ≤ 2 ^ (K + 10) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right K 10)
  exact hK.trans hpow

/-- Monotonicity of `completedBoundedOutput` with respect to budget. -/
private theorem completedBoundedOutput_le (V : Map) (c : Code) (hc : IsCodeFor c V)
    {m1 m2 : ℕ} (hm : m1 ≤ m2) {y : BitString}
    (hy : y ∈ completedBoundedOutput c m1) : y ∈ completedBoundedOutput c m2 := by
  have hyK : plainK V y ≤ (m1 : ENat) :=
    (mem_completedBoundedOutput_iff_plainK_le hc _ y).mp hy
  exact (mem_completedBoundedOutput_iff_plainK_le hc m2 y).mpr
    (hyK.trans (by exact_mod_cast hm))

/-- Upper bound on the bit-length of the tail payload encoding. -/
private theorem tail_payload_length_le (n i j C count : ℕ) (hij : i + j ≤ n)
    (hcountBits : (Nat.bits count).length ≤ j) :
    (pairCode (Nat.bits (i + j + logSlack C n)) (Nat.bits count)).length ≤
      j + 4 * (Nat.bits n).length + 2 * (Nat.bits C).length + 5 := by
  let L := (Nat.bits n).length
  let LC := (Nat.bits C).length
  have hijBits : (Nat.bits (i + j)).length ≤ L := length_natBits_mono hij
  have hslackBits : (Nat.bits (logSlack C n)).length ≤ L + LC + 1 :=
    length_natBits_logSlack_le C n
  have hmBits : (Nat.bits (i + j + logSlack C n)).length ≤ 2 * L + LC + 2 := by
    calc
      (Nat.bits (i + j + logSlack C n)).length
          ≤ (Nat.bits (i + j)).length + (Nat.bits (logSlack C n)).length + 1 :=
        length_natBits_add_le (i + j) (logSlack C n)
      _ ≤ 2 * L + LC + 2 := by omega
  rw [length_pairCode]
  omega

/-- The two constant bounds the omega budget estimate rests on: the tail omega selector raises
the plain complexity of its input by at most `C_map`, and a pair costs at most `C_pair` over the
prefix complexities of its two components. -/
private def OmegaSelectorBounds (V U : Map) (c : Code) (C_map C_pair : ℕ) : Prop :=
  (∀ x y, y ∈ descriptionTailOmegaSelector c x → plainK V y ≤ plainK V x + C_map) ∧
    ∀ x y, plainK V (pairCode x y) ≤ KPPlain U x + KPPlain U y + C_pair

/-- Bounding budget `m` by combining complexity upper bounds for the tail omega selector. -/
private theorem omega_count_budget_le (V U : Map) (c : Code)
    (C_omega C_map C_pair C_len i m : ℕ) (S_code payload : BitString)
    (hC_omega : (m : ENat) ≤ plainKNat V (omegaCount c m) + (C_omega : ENat))
    (hselector : Nat.bits (omegaCount c m) ∈
      descriptionTailOmegaSelector c (pairCode S_code payload))
    (hbounds : OmegaSelectorBounds V U c C_map C_pair)
    (hcode : KPPlain U S_code ≤ (i : ENat))
    (hpayload : KPPlain U payload ≤
      ((payload.length + 2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat)) :
    m ≤ i + payload.length + 2 * (Nat.bits payload.length).length +
      C_len + C_pair + C_map + C_omega := by
  obtain ⟨hC_map, hC_pair⟩ := hbounds
  have hmENat : (m : ENat) ≤ ((i + payload.length +
      2 * (Nat.bits payload.length).length +
      C_len + C_pair + C_map + C_omega : ℕ) : ENat) := by
    calc
      (m : ENat) ≤ plainKNat V (omegaCount c m) + (C_omega : ENat) := hC_omega
      _ ≤ (plainK V (pairCode S_code payload) + (C_map : ENat)) +
          (C_omega : ENat) := by
        gcongr; exact hC_map _ _ hselector
      _ ≤ ((KPPlain U S_code + KPPlain U payload + (C_pair : ENat)) +
          (C_map : ENat)) + (C_omega : ENat) := by
        gcongr; exact hC_pair S_code payload
      _ ≤ (((i : ENat) + ((payload.length +
          2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat) +
          (C_pair : ENat)) + (C_map : ENat)) + (C_omega : ENat) := by
        gcongr
      _ = ((i + payload.length + 2 * (Nat.bits payload.length).length +
          C_len + C_pair + C_map + C_omega : ℕ) : ENat) := by
        push_cast; ring
  exact_mod_cast hmENat

/-- Logarithmic slack dominates constant and bit-length terms for large `C`. -/
private theorem logSlack_dominates_constants (n C_mem C_omega C_map C_pair C_len : ℕ) :
    let K := C_mem + C_omega + C_map + C_pair + C_len + 64
    let C := 2 ^ (K + 10)
    let L := (Nat.bits n).length
    let LC := (Nat.bits C).length
    6 * L + 4 * LC + 17 + C_len + C_pair + C_map + C_omega < logSlack C n := by
  intro K C L LC
  have hCbits : LC ≤ K + 11 := by
    apply length_natBits_lt_pow
    dsimp [LC, C]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)
  have hCseven : 7 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : 7 ≤ 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 10 K))
  have hCconstant : 5 * K + 61 < C := by
    dsimp [C]
    rw [pow_add]
    have hsmall : 5 * K + 61 ≤ 66 * 2 ^ K := by
      have hKpow := nat_le_two_pow K
      omega
    calc
      5 * K + 61 ≤ 66 * 2 ^ K := hsmall
      _ < 2 ^ K * 2 ^ 10 := by
        rw [show 66 * 2 ^ K = 2 ^ K * 66 by ring]
        exact Nat.mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  have hmul : 7 * L ≤ C * L := Nat.mul_le_mul_right L hCseven
  have hconst : 4 * LC + 17 + C_len + C_pair + C_map + C_omega ≤ 5 * K + 61 := by
    dsimp [K] at *; omega
  dsimp [logSlack, L]
  dsimp [L] at hmul
  omega

/-- A string of length `n` whose description profile contains `(i, j)` has at least `2 ^ j`
strings in the suffix coordinate at level `i + j + logSlack C n`: the forward half of the
characterisation of profiles by tail counts. -/
theorem tail_characterization_forward
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j : ℕ),
      x.length = n →
      i + j ≤ n →
      InDescriptionProfile U x i j →
      2 ^ j ≤ suffixCoordinate c (i + j + logSlack C n) x := by
  obtain ⟨C_mem, hC_mem⟩ := mem_completed_of_isIJDescription V U hV hU c hc
  obtain ⟨C_omega, hC_omega⟩ := plainKNat_omegaCount_lower V hV c hc
  obtain ⟨C_map, hC_map⟩ := plainK_partrec_map_le V hV
    (descriptionTailOmegaSelector c)
    (descriptionTailOmegaSelector_partrec c)
  obtain ⟨C_pair, hC_pair⟩ := plainK_pair_le_KPPlain_add_KPPlain V U hV hU
  obtain ⟨C_len, hC_len⟩ := KPPlain_le_length_add_log U hU
  let K := C_mem + C_omega + C_map + C_pair + C_len + 64
  let C := 2 ^ (K + 10)
  refine ⟨C, fun x n i j _hn hij hprof => ?_⟩
  obtain ⟨S, hS, hdesc⟩ := hprof
  let S_code := (codedUniformOn S hS).code
  let S_list := canonicalFinsetList S
  let m := i + j + logSlack C n
  have hCmemC : C_mem ≤ C := by
    have hCK : C_mem ≤ K := by dsimp [K]; omega
    exact hCK.trans (le_two_pow_add_ten K)
  have hjn : j ≤ n := by omega
  have hmemBudget : i + j + logSlack C_mem j ≤ m := by
    dsimp [m]
    have hslack : logSlack C_mem j ≤ logSlack C n :=
      (logSlack_mono_left hCmemC j).trans (logSlack_mono_right C hjn)
    omega
  have hSsubset : ∀ y ∈ S_list, y ∈ completedBoundedOutput c m := by
    intro y hy
    exact completedBoundedOutput_le V c hc hmemBudget
      (hC_mem x y i j S hS hdesc (mem_canonicalFinsetList.mp hy))
  have hcover : ∃ t, S_list.all (fun y => (boundedOutputStage c m t).elem y) = true := by
    obtain ⟨t, ht⟩ := exists_stage_covering_finset c m S (fun y hy =>
      hSsubset y (mem_canonicalFinsetList.mpr hy))
    refine ⟨t, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    rw [List.elem_eq_mem]
    exact decide_eq_true (ht y (mem_canonicalFinsetList.mp hy))
  by_contra htail
  push Not at htail
  let t₀ := Nat.find hcover
  have ht₀spec : S_list.all (fun y => (boundedOutputStage c m t₀).elem y) = true :=
    Nat.find_spec hcover
  have ht₀mem : t₀ ∈ Nat.rfind (fun t => Part.some
      (S_list.all (fun y => (boundedOutputStage c m t).elem y))) := by
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · exact Part.mem_some_iff.mpr ht₀spec.symm
    · intro t ht
      have hnot := Nat.find_min hcover ht
      exact Part.mem_some_iff.mpr (Bool.eq_false_iff.mpr hnot).symm
  have hxList : x ∈ S_list := mem_canonicalFinsetList.mpr hdesc.1
  have hxStage : x ∈ boundedOutputStage c m t₀ := by
    rw [List.all_eq_true] at ht₀spec
    have hxElem := ht₀spec x hxList
    simpa [List.elem_eq_mem] using hxElem
  have hprefix : boundedOutputStage c m t₀ <+: completedBoundedOutput c m :=
    boundedOutputStage_prefix_completed c m t₀
  obtain ⟨R, hR, hRtail⟩ := prefix_remainder_length_le_tailAfter hprefix hxStage
  let count := omegaCount c m - (boundedOutputStage c m t₀).length
  have hcountR : count = R.length := by
    dsimp [count, omegaCount]
    rw [hR, List.length_append]
    omega
  have hcountLt : count < 2 ^ j := by
    have htailLe : tailAfter (completedBoundedOutput c m) x < suffixCoordinate c m x := by
      have hxCompleted : x ∈ completedBoundedOutput c m :=
        List.IsPrefix.subset hprefix hxStage
      unfold suffixCoordinate
      rw [suffixCountIncluding_eq_tailAfter_add_one hxCompleted]
      omega
    rw [hcountR]
    exact lt_of_le_of_lt hRtail (htailLe.trans htail)
  have hrecover : descriptionTailOmegaSelector c (descriptionTailOmegaInput S_code m count) =
      Part.some (Nat.bits (omegaCount c m)) := by
    apply descriptionTailOmegaSelector_recovers c m S_code S_list
    · exact (dataPoints_codedUniformOn S hS).symm
    · exact hSsubset
    · exact ⟨t₀, (Part.eq_some_iff.mpr ht₀mem).symm, rfl⟩
  have hselector : Nat.bits (omegaCount c m) ∈
      descriptionTailOmegaSelector c (descriptionTailOmegaInput S_code m count) :=
    Part.eq_some_iff.mp hrecover
  let payload := pairCode (Nat.bits m) (Nat.bits count)
  let input := descriptionTailOmegaInput S_code m count
  have hinput : input = pairCode S_code payload := rfl
  have hcountBits : (Nat.bits count).length ≤ j := length_natBits_lt_pow hcountLt
  let L := (Nat.bits n).length
  let LC := (Nat.bits C).length
  have hpayloadLinear : payload.length ≤ j + 4 * L + 2 * LC + 5 :=
    tail_payload_length_le n i j C count hij hcountBits
  have hnPow : n < 2 ^ L := by
    have hlt := lt_two_pow_length_natBits n
    dsimp [L]
    exact hlt
  have hpayloadBits : (Nat.bits payload.length).length ≤ L + LC + 6 := by
    have hpayloadPow : payload.length < 2 ^ (L + LC + 6) := by
      rw [show L + LC + 6 = L + LC + 6 by rfl, pow_add, pow_add]
      have hjPow : j < 2 ^ L := lt_of_le_of_lt hjn hnPow
      let P := 2 ^ L * 2 ^ LC
      have hPpos : 0 < P := by positivity
      have h2L : 2 ^ L ≤ P := by
        calc 2 ^ L = 2 ^ L * 1 := (mul_one _).symm
        _ ≤ 2 ^ L * 2 ^ LC := Nat.mul_le_mul_left (2 ^ L) (Nat.one_le_pow LC 2 zero_lt_two)
      have hLP : L ≤ P := (nat_le_two_pow L).trans h2L
      have h2LC : 2 ^ LC ≤ P := by
        calc 2 ^ LC = 1 * 2 ^ LC := (one_mul _).symm
        _ ≤ 2 ^ L * 2 ^ LC := Nat.mul_le_mul_right (2 ^ LC) (Nat.one_le_pow L 2 zero_lt_two)
      have hLCP : LC ≤ P := (nat_le_two_pow LC).trans h2LC
      have hjP : j < P := hjPow.trans_le h2L
      have hOneP : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr hPpos.ne'
      calc
        payload.length ≤ j + 4 * L + 2 * LC + 5 := hpayloadLinear
        _ < 12 * P := by omega
        _ < P * 2 ^ 6 := by
          rw [show 12 * P = P * 12 by ring]
          exact Nat.mul_lt_mul_of_pos_left (by norm_num) hPpos
        _ = 2 ^ L * 2 ^ LC * 2 ^ 6 := rfl
    exact length_natBits_lt_pow hpayloadPow
  have hcodeComplexity : KPPlain U S_code ≤ (i : ENat) := by
    have hcomp := hdesc.2.1
    dsimp [S_code, setComplexity]
    exact hcomp
  have hpayloadComplexity : KPPlain U payload ≤
      ((payload.length + 2 * (Nat.bits payload.length).length + C_len : ℕ) : ENat) :=
    hC_len payload
  have hmNat : m ≤ i + payload.length + 2 * (Nat.bits payload.length).length +
      C_len + C_pair + C_map + C_omega :=
    omega_count_budget_le V U c C_omega C_map C_pair C_len i m S_code payload
      (hC_omega m) hselector ⟨hC_map, hC_pair⟩ hcodeComplexity hpayloadComplexity
  have hraw : m ≤ i + j + 6 * L + 4 * LC + 17 + C_len + C_pair + C_map + C_omega := by
    omega
  have hlarge : 6 * L + 4 * LC + 17 + C_len + C_pair + C_map + C_omega < logSlack C n :=
    logSlack_dominates_constants n C_mem C_omega C_map C_pair C_len
  dsimp [m] at hraw
  omega

/-- On the source-relevant range `i+j ≤ n`, the ordinary description profile and the suffix
position in the plain bounded-complexity list determine one another up to uniform logarithmic
coordinate shifts (`thm:tail-characterization`).

The two constants are fixed before all strings and parameters.  They are kept
separate because the forward direction changes the plain-list budget, whereas
the reverse direction changes the prefix-profile complexity coordinate; taking
a post-hoc maximum would require a false monotonicity claim about enumeration
positions. -/
theorem tail_characterization
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C_forward C_reverse : ℕ,
      ∀ (x : BitString) (n i j : ℕ),
        x.length = n →
        i + j ≤ n →
        (InDescriptionProfile U x i j →
          2 ^ j ≤
            suffixCoordinate c
              (i + j + logSlack C_forward n) x) ∧
        (2 ^ j ≤
            tailAfter (completedBoundedOutput c (i + j)) x →
          InDescriptionProfile U x
            (i + logSlack C_reverse n) j) := by
  obtain ⟨C_forward, hforward⟩ :=
    tail_characterization_forward V U hV hU c hc
  obtain ⟨C_reverse, hreverse⟩ :=
    tail_characterization_reverse V U hV hU c hc
  exact ⟨C_forward, C_reverse, fun x n i j hn hij =>
    ⟨hforward x n i j hn hij, hreverse x n i j hn hij⟩⟩

end Kolmogorov
