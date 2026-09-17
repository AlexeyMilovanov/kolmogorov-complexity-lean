import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.ComputableCover.PaddedCover

namespace Kolmogorov
open MeasureTheory Set
open scoped ENNReal
variable {E : ℕ → ℕ → Option BitString}

/-! ### The hypotheses on the enumeration -/

section Cover

variable {E : ℕ → ℕ → Option BitString}

/-- Each totalised interval is at least as heavy as the corresponding enumerated one, up to the
junk term. -/
lemma inv_two_pow_length_coverStr_le (d s : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (coverStr E d s).length
      ≤ (E d s).elim 0 (cantorMass uniformMeasure) + (2 : ℝ≥0∞)⁻¹ ^ (d + s + 1) := by
  cases h : E d s with
  | none => simp [coverStr, h]
  | some x =>
      simp only [coverStr, h, Option.getD_some, Option.elim_some, cantorMass_uniformMeasure]
      exact le_self_add

variable (hsum : ∀ d : ℕ, (∑' s : ℕ, (E d s).elim 0 (cantorMass uniformMeasure))
  ≤ (2 : ℝ≥0∞)⁻¹ ^ d)

include hsum

/-- The masses of the totalised level-`d` intervals sum to at most `2·2^(-d)`. -/
lemma tsum_inv_two_pow_length_coverStr_le (d : ℕ) :
    (∑' s : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (coverStr E d s).length) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ d := by
  calc (∑' s : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (coverStr E d s).length)
      ≤ ∑' s : ℕ, ((E d s).elim 0 (cantorMass uniformMeasure) + (2 : ℝ≥0∞)⁻¹ ^ (d + s + 1)) :=
        ENNReal.tsum_le_tsum fun s => inv_two_pow_length_coverStr_le d s
    _ = (∑' s : ℕ, (E d s).elim 0 (cantorMass uniformMeasure))
          + ∑' s : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (d + s + 1) := ENNReal.tsum_add
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ d + (2 : ℝ≥0∞)⁻¹ ^ d := by
        rw [tsum_inv_two_pow_shift d]
        exact add_le_add (hsum d) (le_refl _)
    _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ d := (two_mul _).symm

/-- Every interval of the level-`d` cover has length at least `d`. -/
lemma le_length_coverStr (d s : ℕ) : d ≤ (coverStr E d s).length := by
  cases h : E d s with
  | none =>
      have : coverStr E d s = coverJunk d s := by simp [coverStr, h]
      rw [this, length_coverJunk]
      omega
  | some x =>
      have hle : (2 : ℝ≥0∞)⁻¹ ^ x.length ≤ (2 : ℝ≥0∞)⁻¹ ^ d := by
        calc (2 : ℝ≥0∞)⁻¹ ^ x.length = (E d s).elim 0 (cantorMass uniformMeasure) := by
              rw [h]
              simp [cantorMass_uniformMeasure]
          _ ≤ ∑' t : ℕ, (E d t).elim 0 (cantorMass uniformMeasure) := ENNReal.le_tsum s
          _ ≤ (2 : ℝ≥0∞)⁻¹ ^ d := hsum d
      have hx : coverStr E d s = x := by simp [coverStr, h]
      rw [hx]
      exact inv_two_pow_exponent_le hle

/-! ### The series `∑ₙ 2^(-f(n))` converges -/

omit hsum

/-- The majorant `2 ^ (2 * c) * 2⁻¹ ^ (length of the stage string)` of the `c`-th candidate term at
level `n`, taken over the stage of the level-`3 * c` cover padded to `n`, and `0` when there is
no such stage. -/
noncomputable def coverTerm (E : ℕ → ℕ → Option BitString) (c n : ℕ) : ℝ≥0∞ :=
  ((coverIdx E (3 * c) n).map fun s =>
    (2 : ℝ≥0∞) ^ (2 * c) * (2 : ℝ≥0∞)⁻¹ ^ (coverStr E (3 * c) s).length).getD 0

/-- The weight of a candidate is at most `2 ^ -(n + c)` plus the majorant term of that level. -/
lemma inv_two_pow_coverCand_le (n c : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ coverCand E n c ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n := by
  cases h : coverIdx E (3 * c) n with
  | none => simp [coverCand, coverTerm, h]
  | some s =>
      simp only [coverCand, coverTerm, h, Option.map_some, Option.getD_some]
      exact le_trans (inv_two_pow_sub_le _ _) le_add_self

include hsum

/-- The majorant terms of level `c` sum to at most `2 * 2 ^ -c`, which is what makes the series
of the exponent converge. -/
lemma tsum_coverTerm_le (c : ℕ) : (∑' n : ℕ, coverTerm E c n) ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ c := by
  have hinj : Function.Injective (coverLen E (3 * c)) := coverLen_injective _
  have hsupp : Function.support (coverTerm E c) ⊆ Set.range (coverLen E (3 * c)) := by
    intro n hn
    cases h : coverIdx E (3 * c) n with
    | none =>
        exact absurd (show coverTerm E c n = 0 by simp [coverTerm, h]) hn
    | some s => exact ⟨s, coverIdx_eq_some _ _ _ h⟩
  have hval : ∀ s : ℕ, coverTerm E c (coverLen E (3 * c) s)
      = (2 : ℝ≥0∞) ^ (2 * c) * (2 : ℝ≥0∞)⁻¹ ^ (coverStr E (3 * c) s).length := by
    intro s
    simp [coverTerm, coverIdx_of_coverLen]
  have hfinal : (2 : ℝ≥0∞) ^ (2 * c) * (2 * (2 : ℝ≥0∞)⁻¹ ^ (3 * c)) = 2 * (2 : ℝ≥0∞)⁻¹ ^ c := by
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (3 * c) = (2 : ℝ≥0∞)⁻¹ ^ (2 * c) * (2 : ℝ≥0∞)⁻¹ ^ c := by
      rw [← pow_add]
      congr 1
      omega
    have hcancel : (2 : ℝ≥0∞) ^ (2 * c) * (2 : ℝ≥0∞)⁻¹ ^ (2 * c) = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    calc (2 : ℝ≥0∞) ^ (2 * c) * (2 * (2 : ℝ≥0∞)⁻¹ ^ (3 * c))
        = 2 * ((2 : ℝ≥0∞) ^ (2 * c) * (2 : ℝ≥0∞)⁻¹ ^ (2 * c)) * (2 : ℝ≥0∞)⁻¹ ^ c := by
          rw [hsplit]; ring
      _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ c := by rw [hcancel, mul_one]
  rw [← hinj.tsum_eq hsupp, tsum_congr hval, ENNReal.tsum_mul_left, ← hfinal]
  gcongr
  exact tsum_inv_two_pow_length_coverStr_le hsum (3 * c)

/-- **The series of SUV Theorem 96 converges.** -/
theorem tsum_inv_two_pow_coverExponent_ne_top :
    (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ coverExponent E n) ≠ ⊤ := by
  have hstep : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ coverExponent E n
      ≤ ∑' c : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n) := by
    intro n
    obtain ⟨c, hc⟩ := exists_coverExponent_eq (E := E) n
    calc (2 : ℝ≥0∞)⁻¹ ^ coverExponent E n = (2 : ℝ≥0∞)⁻¹ ^ coverCand E n c := by rw [hc]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n := inv_two_pow_coverCand_le n c
      _ ≤ ∑' c : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n) := ENNReal.le_tsum c
  have hbound : (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ coverExponent E n) ≤ 8 := by
    calc (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ coverExponent E n)
        ≤ ∑' n : ℕ, ∑' c : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n) :=
          ENNReal.tsum_le_tsum hstep
      _ = ∑' c : ℕ, ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ (n + c) + coverTerm E c n) := ENNReal.tsum_comm
      _ = ∑' c : ℕ, ((∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + c)) + ∑' n : ℕ, coverTerm E c n) :=
          tsum_congr fun c => ENNReal.tsum_add
      _ ≤ ∑' c : ℕ, (2 * (2 : ℝ≥0∞)⁻¹ ^ c + 2 * (2 : ℝ≥0∞)⁻¹ ^ c) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          exact add_le_add (le_of_eq (tsum_inv_two_pow_add_right c)) (tsum_coverTerm_le hsum c)
      _ = 4 * ∑' c : ℕ, (2 : ℝ≥0∞)⁻¹ ^ c := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun c => ?_
          rw [← two_mul, ← mul_assoc]
          norm_num
      _ = 8 := by rw [tsum_inv_two_pow_self]; norm_num
  exact ne_top_of_le_ne_top (by norm_num) hbound

omit hsum

/-! ### The decompressor -/

/-- The string of the padded level-`d` cover whose ordinal number is `m`. -/
def coverPick (E : ℕ → ℕ → Option BitString) (d m : ℕ) : BitString :=
  coverStr E d (coverFind E d m) ++
    (bitStringsOfLength (coverLen E d (coverFind E d m) -
      (coverStr E d (coverFind E d m)).length)).getD (m - coverBase E d (coverFind E d m)) []

/-- **The decompressor of SUV Theorems 96 and 97** (pp. 153-154): the program `1^c 0 u`
describes the string of the padded level-`3c` cover whose ordinal number is coded by `u`. -/
def coverOutput (E : ℕ → ℕ → Option BitString) (p : BitString) : BitString :=
  coverPick E (3 * (unaryParse p).1) (bitStringToNat (unaryParse p).2)

/-- The decompressor of SUV Theorems 96 and 97 as a `Map`: the total map sending a program `q` to
`coverOutput E q.1`. -/
def coverMachine (E : ℕ → ℕ → Option BitString) : Map := fun q => Part.some (coverOutput E q.1)

/-- An index inside the block of a stage is found at that stage. -/
lemma coverFind_eq {d s m : ℕ} (h1 : coverBase E d s ≤ m) (h2 : m < coverBase E d (s + 1)) :
    coverFind E d m = s := by
  have ht1 : coverBase E d (coverFind E d m) ≤ m := coverBase_coverFind_le d m
  have ht2 : m < coverBase E d (coverFind E d m + 1) := lt_coverBase_coverFind_succ d m
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono : coverBase E d (coverFind E d m + 1) ≤ coverBase E d s :=
      (coverBase_strictMono (E := E) d).monotone (by omega)
    omega
  · have hmono : coverBase E d (s + 1) ≤ coverBase E d (coverFind E d m) :=
      (coverBase_strictMono (E := E) d).monotone (by omega)
    omega

/-- The string of ordinal number `coverBase + j` is the `j`-th extension of the stage's interval
to its padding level. -/
lemma coverPick_eq (d s j : ℕ) (hj : j < 2 ^ (coverLen E d s - (coverStr E d s).length)) :
    coverPick E d (coverBase E d s + j) =
      coverStr E d s ++
        (bitStringsOfLength (coverLen E d s - (coverStr E d s).length)).getD j [] := by
  have hfind : coverFind E d (coverBase E d s + j) = s :=
    coverFind_eq (Nat.le_add_right _ _) (by rw [coverBase_succ]; omega)
  rw [coverPick, hfind, Nat.add_sub_cancel_left]

/-- A number below `2^k` has a code of at most `k` bits. -/
lemma length_natToBitString_le {m k : ℕ} (h : m < 2 ^ k) : (natToBitString m).length ≤ k := by
  have hpow : (2 : ℕ) ^ k < 2 ^ (k + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have hsize : Nat.size (m + 1) ≤ k + 1 := Nat.size_le.mpr (by omega)
  have hbits : (Nat.bits (m + 1)).length = Nat.size (m + 1) := Nat.size_eq_bits_len (m + 1)
  have hlen : (natToBitString m).length = Nat.size (m + 1) - 1 := by
    rw [natToBitString, List.length_dropLast, hbits]
  omega

section Machine

variable (hE : Computable₂ E)

include hE

/-- Reading the string of a given ordinal number in the padded cover is computable. -/
lemma computable_coverPick : Computable₂ (coverPick E) := by
  have hfind : Computable fun p : ℕ × ℕ => coverFind E p.1 p.2 := computable_coverFind hE
  have hstr : Computable fun p : ℕ × ℕ => coverStr E p.1 (coverFind E p.1 p.2) :=
    (computable_coverStr hE).comp Computable.fst hfind
  have hlen : Computable fun p : ℕ × ℕ => coverLen E p.1 (coverFind E p.1 p.2) :=
    (computable_coverLen hE).comp Computable.fst hfind
  have hbase : Computable fun p : ℕ × ℕ => coverBase E p.1 (coverFind E p.1 p.2) :=
    (computable_coverBase hE).comp Computable.fst hfind
  have hk : Computable fun p : ℕ × ℕ =>
      coverLen E p.1 (coverFind E p.1 p.2) - (coverStr E p.1 (coverFind E p.1 p.2)).length :=
    Primrec.nat_sub.to_comp.comp hlen (Computable.list_length.comp hstr)
  have hj : Computable fun p : ℕ × ℕ => p.2 - coverBase E p.1 (coverFind E p.1 p.2) :=
    Primrec.nat_sub.to_comp.comp Computable.snd hbase
  have htail : Computable fun p : ℕ × ℕ =>
      (bitStringsOfLength (coverLen E p.1 (coverFind E p.1 p.2) -
        (coverStr E p.1 (coverFind E p.1 p.2)).length)).getD
          (p.2 - coverBase E p.1 (coverFind E p.1 p.2)) [] :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp
      (computable_bitStringsOfLength.comp hk) hj
  exact Primrec.list_append.to_comp.comp hstr htail

/-- The output of the cover decompressor is computable in the program. -/
lemma computable_coverOutput : Computable (coverOutput E) := by
  have hc : Computable fun p : BitString => 3 * (unaryParse p).1 :=
    Primrec.nat_mul.to_comp.comp (Computable.const 3)
      (Computable.fst.comp computable_unaryParse)
  have hm : Computable fun p : BitString => bitStringToNat (unaryParse p).2 :=
    computable_bitStringToNat.comp (Computable.snd.comp computable_unaryParse)
  exact (computable_coverPick hE).comp hc hm

/-- The cover machine is a decompressor. -/
lemma isDecompressor_coverMachine : isDecompressor (coverMachine E) := by
  exact (computable_coverOutput hE).comp Computable.fst

end Machine

/-- The cover machine describes its output within the length of the program. -/
lemma plainK_coverMachine_le (p : BitString) :
    plainK (coverMachine E) (coverOutput E p) ≤ (p.length : ℕ∞) :=
  sInf_le ⟨p, Part.mem_some _, rfl⟩

/-- The universal machine describes `coverOutput E p` with `|p| + O(1)` bits. -/
lemma exists_const_plainK_coverOutput_le {V : Map} (hV : isOptimalConditional V)
    (hE : Computable₂ E) :
    ∃ K : ℕ, ∀ p : BitString, plainK V (coverOutput E p) ≤ (p.length : ℕ∞) + (K : ℕ∞) := by
  obtain ⟨K, hK⟩ := hV.2 (coverMachine E) (isDecompressor_coverMachine hE)
  refine ⟨K, fun p => ?_⟩
  calc plainK V (coverOutput E p) ≤ plainK (coverMachine E) (coverOutput E p) + (K : ℕ∞) :=
        hK _ _
    _ ≤ (p.length : ℕ∞) + (K : ℕ∞) := add_le_add (plainK_coverMachine_le p) (le_refl _)

/-- The padded string of stage `s` with tail index `j` is described by `c + k + 2 + K` bits. -/
lemma plainK_coverPick_le {V : Map}
    (K : ℕ) (hK : ∀ p : BitString, plainK V (coverOutput E p) ≤ (p.length : ℕ∞) + (K : ℕ∞))
    (c s j k : ℕ) (y : BitString)
    (hk : coverLen E (3 * c) s - (coverStr E (3 * c) s).length = k)
    (hj : j < 2 ^ k) (hy : (bitStringsOfLength k).getD j [] = y) :
    plainK V (coverStr E (3 * c) s ++ y) ≤ ((c + k + 2 + K : ℕ) : ℕ∞) := by
  subst hk
  subst hy
  have hbaselt : coverBase E (3 * c) s
      < 2 ^ (coverLen E (3 * c) s - (coverStr E (3 * c) s).length) := coverBase_lt_two_pow _ _
  have hsplit : (2 : ℕ) ^ (coverLen E (3 * c) s - (coverStr E (3 * c) s).length + 1)
      = 2 ^ (coverLen E (3 * c) s - (coverStr E (3 * c) s).length)
        + 2 ^ (coverLen E (3 * c) s - (coverStr E (3 * c) s).length) := by
    rw [pow_succ]
    omega
  have hmlt : coverBase E (3 * c) s + j
      < 2 ^ (coverLen E (3 * c) s - (coverStr E (3 * c) s).length + 1) := by omega
  have hdec : coverOutput E (List.replicate c true ++ false ::
      natToBitString (coverBase E (3 * c) s + j))
      = coverStr E (3 * c) s ++
        (bitStringsOfLength (coverLen E (3 * c) s -
          (coverStr E (3 * c) s).length)).getD j [] := by
    simp only [coverOutput, unaryParse_code, bitStringToNat_natToBitString]
    exact coverPick_eq (3 * c) s j hj
  have hplen : (List.replicate c true ++ false ::
      natToBitString (coverBase E (3 * c) s + j)).length
      ≤ c + (coverLen E (3 * c) s - (coverStr E (3 * c) s).length) + 2 := by
    rw [length_unaryCode]
    have hu := length_natToBitString_le hmlt
    omega
  calc plainK V (coverStr E (3 * c) s ++
        (bitStringsOfLength (coverLen E (3 * c) s -
          (coverStr E (3 * c) s).length)).getD j [])
      = plainK V (coverOutput E (List.replicate c true ++ false ::
          natToBitString (coverBase E (3 * c) s + j))) := by rw [hdec]
    _ ≤ ((List.replicate c true ++ false ::
          natToBitString (coverBase E (3 * c) s + j)).length : ℕ∞) + (K : ℕ∞) := hK _
    _ ≤ ((c + (coverLen E (3 * c) s - (coverStr E (3 * c) s).length) + 2 : ℕ) : ℕ∞)
          + (K : ℕ∞) := by
        exact add_le_add (by exact_mod_cast hplen) (le_refl _)
    _ = ((c + (coverLen E (3 * c) s - (coverStr E (3 * c) s).length) + 2 + K : ℕ) : ℕ∞) := by
        push_cast
        ring

/-- **The key step of SUV Theorems 96 and 97** (pp. 153-154): a sequence that is not Martin-Löf
random has, for every `c₀`, a prefix of length `n` with `C((ω)ₙ) + f(n) + c₀ < n`. -/
theorem exists_plainK_add_coverExponent_lt {V : Map} (hV : isOptimalConditional V)
    (hE : Computable₂ E)
    (hmass : ∀ d : ℕ, (∑' s : ℕ, (E d s).elim 0 (cantorMass uniformMeasure)) ≤ (2 : ℝ≥0∞)⁻¹ ^ d)
    (hcov : ∀ (d : ℕ) (v : CantorSeq), ¬ IsMartinLofRandom uniformMeasure v →
      ∃ s : ℕ, v ∈ coverSet (E d) s)
    {w : CantorSeq} (hw : ¬ IsMartinLofRandom uniformMeasure w) (c₀ : ℕ) :
    ∃ n : ℕ, plainK V (cantorPrefix w n) + (coverExponent E n : ℕ∞) + (c₀ : ℕ∞) < (n : ℕ∞) := by
  classical
  obtain ⟨K, hK⟩ := exists_const_plainK_coverOutput_le hV hE
  obtain ⟨s, hs⟩ := hcov (3 * (K + c₀ + 3)) w hw
  obtain ⟨x, hx⟩ : ∃ x : BitString, E (3 * (K + c₀ + 3)) s = some x := by
    cases h : E (3 * (K + c₀ + 3)) s with
    | none =>
        rw [coverSet, h] at hs
        exact absurd hs (Set.notMem_empty w)
    | some x => exact ⟨x, rfl⟩
  simp only [coverSet, hx, Option.elim_some] at hs
  have hxstr : coverStr E (3 * (K + c₀ + 3)) s = x := by simp [coverStr, hx]
  have hxlen : (coverStr E (3 * (K + c₀ + 3)) s).length = x.length := by rw [hxstr]
  have hlL : x.length ≤ coverLen E (3 * (K + c₀ + 3)) s := by
    rw [← hxlen]
    exact length_coverStr_le_coverLen _ _
  have h3c : 3 * (K + c₀ + 3) ≤ x.length := by
    rw [← hxlen]
    exact le_length_coverStr hmass _ _
  have hpre : cantorPrefix w x.length = x := (isCantorPrefix_iff_cantorPrefix_eq x w).1 hs
  have hlent : ((cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s)).drop x.length).length
      = coverLen E (3 * (K + c₀ + 3)) s - x.length := by simp
  have hcat : x ++ (cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s)).drop x.length
      = cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s) := by
    conv_rhs =>
      rw [← List.take_append_drop x.length (cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s))]
    rw [cantorPrefix_take w x.length _ hlL, hpre]
  have htmem : (cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s)).drop x.length
      ∈ bitStringsOfLength (coverLen E (3 * (K + c₀ + 3)) s - x.length) :=
    mem_bitStringsOfLength_iff.mpr hlent
  obtain ⟨j, hjlt, hjt⟩ := List.getElem_of_mem htmem
  have hjlt' : j < 2 ^ (coverLen E (3 * (K + c₀ + 3)) s - x.length) := by
    rwa [length_bitStringsOfLength] at hjlt
  have hgetD : (bitStringsOfLength (coverLen E (3 * (K + c₀ + 3)) s - x.length)).getD j []
      = (cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s)).drop x.length := by
    rw [List.getD_eq_getElem _ _ hjlt, hjt]
  have hdesc := plainK_coverPick_le K hK (K + c₀ + 3) s j
    (coverLen E (3 * (K + c₀ + 3)) s - x.length)
    ((cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s)).drop x.length) (by rw [hxlen]) hjlt' hgetD
  rw [hxstr, hcat] at hdesc
  have hcL : K + c₀ + 3 ≤ coverLen E (3 * (K + c₀ + 3)) s := by omega
  have hexp : coverExponent E (coverLen E (3 * (K + c₀ + 3)) s) ≤ x.length - 2 * (K + c₀ + 3) := by
    have h1 : coverExponent E (coverLen E (3 * (K + c₀ + 3)) s)
        ≤ coverCand E (coverLen E (3 * (K + c₀ + 3)) s) (K + c₀ + 3) :=
      coverExponent_le _ _ hcL
    have h2 : coverCand E (coverLen E (3 * (K + c₀ + 3)) s) (K + c₀ + 3)
        = x.length - 2 * (K + c₀ + 3) := by
      rw [coverCand, coverIdx_of_coverLen]
      simp [hxlen]
    omega
  refine ⟨coverLen E (3 * (K + c₀ + 3)) s, ?_⟩
  have hnat : ((K + c₀ + 3) + (coverLen E (3 * (K + c₀ + 3)) s - x.length) + 2 + K)
      + (x.length - 2 * (K + c₀ + 3)) + c₀ < coverLen E (3 * (K + c₀ + 3)) s := by omega
  calc plainK V (cantorPrefix w (coverLen E (3 * (K + c₀ + 3)) s))
        + (coverExponent E (coverLen E (3 * (K + c₀ + 3)) s) : ℕ∞) + (c₀ : ℕ∞)
      ≤ (((K + c₀ + 3) + (coverLen E (3 * (K + c₀ + 3)) s - x.length) + 2 + K : ℕ) : ℕ∞)
          + ((x.length - 2 * (K + c₀ + 3) : ℕ) : ℕ∞) + (c₀ : ℕ∞) := by
        gcongr
    _ = ((((K + c₀ + 3) + (coverLen E (3 * (K + c₀ + 3)) s - x.length) + 2 + K)
          + (x.length - 2 * (K + c₀ + 3)) + c₀ : ℕ) : ℕ∞) := by push_cast; ring
    _ < ((coverLen E (3 * (K + c₀ + 3)) s : ℕ) : ℕ∞) := by exact_mod_cast hnat

end Cover

/-! ### The enumeration supplied by the universal Martin-Löf test -/

/-- The disjointified enumeration of the universal Martin-Löf test for the uniform measure:
its level-`d` intervals are pairwise disjoint, so their masses **sum** to at most `2^(-d)`, and
every non-random sequence lies in one of them. -/
theorem exists_coverEnum : ∃ E : ℕ → ℕ → Option BitString, Computable₂ E ∧
    (∀ d : ℕ, (∑' s : ℕ, (E d s).elim 0 (cantorMass uniformMeasure)) ≤ (2 : ℝ≥0∞)⁻¹ ^ d) ∧
    (∀ (d : ℕ) (w : CantorSeq), ¬ IsMartinLofRandom uniformMeasure w →
      ∃ s : ℕ, w ∈ coverSet (E d) s) := by
  obtain ⟨T, hT⟩ := exists_universal_martinLof_test isComputableMeasure_uniform
  obtain ⟨g, hg, hgT⟩ := hT.1.1
  have hcs : ∀ f : ℕ → Option BitString,
      (⋃ i, (f i).elim ∅ cantorCylinder) = ⋃ i, coverSet f i := fun _ => rfl
  refine ⟨fun d => disjEnum (g d), computable_disjEnum hg, ?_, ?_⟩
  · intro d
    rw [tsum_measure_disjEnum, ← hcs (g d), ← hgT d]
    have hb := hT.1.2 d
    rwa [dyadicValue_one_eq_inv_two_pow'] at hb
  · intro d w hw
    have hmem : w ∈ ⋂ n, T n := (not_isMartinLofRandom_iff_mem_universal_test hT w).1 hw
    have hwd : w ∈ T d := Set.mem_iInter.1 hmem d
    rw [hgT d, hcs (g d), ← coverSet_disjEnum_iUnion] at hwd
    exact Set.mem_iUnion.1 hwd

/-! ### The two criteria -/

/-- **SUV Theorem 96** (Section 5.6, p. 152): there is a total computable `f : ℕ → ℕ` with
`∑ 2^(-f(n)) < ∞` such that any sequence obeying `C((ω)ₙ | n) ≥ n − f(n) − c` for some `c` and
all `n` is Martin-Löf random with respect to the uniform measure. -/
theorem exists_computable_summable_condK_criterion' {V : Map} (hV : isOptimalConditional V) :
    ∃ f : ℕ → ℕ, Computable f ∧ (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ ∧
      ∀ w : CantorSeq,
        (∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ condK V (cantorPrefix w n) (natToBitString n) + f n + c) →
          IsMartinLofRandom uniformMeasure w := by
  obtain ⟨E, hE, hmass, hcov⟩ := exists_coverEnum
  refine ⟨coverExponent E, computable_coverExponent hE,
    tsum_inv_two_pow_coverExponent_ne_top hmass, ?_⟩
  intro w hwhyp
  by_contra hw
  obtain ⟨c₁, hc₁⟩ := hwhyp
  obtain ⟨c₂, hc₂⟩ := exists_const_condK_le_plainK hV
  obtain ⟨n, hn⟩ := exists_plainK_add_coverExponent_lt hV hE hmass hcov hw (c₁ + c₂)
  have hle : (n : ℕ∞)
      ≤ plainK V (cantorPrefix w n) + (coverExponent E n : ℕ∞) + ((c₁ + c₂ : ℕ) : ℕ∞) := by
    calc (n : ℕ∞)
        ≤ condK V (cantorPrefix w n) (natToBitString n) + (coverExponent E n : ℕ∞)
            + (c₁ : ℕ∞) := hc₁ n
      _ ≤ plainK V (cantorPrefix w n) + (c₂ : ℕ∞) + (coverExponent E n : ℕ∞)
            + (c₁ : ℕ∞) := by gcongr; exact hc₂ _ _
      _ = plainK V (cantorPrefix w n) + (coverExponent E n : ℕ∞) + ((c₁ + c₂ : ℕ) : ℕ∞) := by
          push_cast
          ring
  exact absurd hle (not_le.mpr hn)

/-- **SUV Theorem 97 ⇐** (Section 5.6, p. 154): if `C((ω)ₙ) ≥ n − f(n) − O(1)` for every total
computable `f` with a convergent series `∑ 2^(-f(n))`, then `ω` is Martin-Löf random with
respect to the uniform measure. -/
theorem isMartinLofRandom_uniform_of_forall_computable_summable_le_plainK' {V : Map}
    (hV : isOptimalConditional V) {w : CantorSeq}
    (hw : ∀ f : ℕ → ℕ, Computable f → (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ f n) ≠ ⊤ →
      ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ plainK V (cantorPrefix w n) + f n + c) :
    IsMartinLofRandom uniformMeasure w := by
  obtain ⟨E, hE, hmass, hcov⟩ := exists_coverEnum
  by_contra hnr
  obtain ⟨c₀, hc₀⟩ := hw (coverExponent E) (computable_coverExponent hE)
    (tsum_inv_two_pow_coverExponent_ne_top hmass)
  obtain ⟨n, hn⟩ := exists_plainK_add_coverExponent_lt hV hE hmass hcov hnr c₀
  exact absurd (hc₀ n) (not_le.mpr hn)

end Kolmogorov


