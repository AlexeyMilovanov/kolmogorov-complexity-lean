/-
Copyright (c) 2026. All rights reserved.
-/
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Basic
import KolmogorovMathlib.Complexity.Incompressibility

/-!
# Section 5.6: the plain-complexity criteria of Theorems 95-98

SUV proves Theorem 95 (p. 151) by a counting argument: for a total computable `f` with
`∑ 2^(-f(n)) < ∞` the set

`D_c = {x : C(x | l(x)) + f(l(x)) + c < l(x)}`

has fewer than `2^(n - f(n) - c)` elements of each length `n`, hence uniform measure at most
`2^(-c) · ∑ₙ 2^(-f(n))`; it is enumerable because `C` is upper semicomputable, so the sets
`D_{c+d}` form a Martin-Löf test and a random sequence avoids one of them.

Only the counting/measure step is left as a leaf here.  The remark after Theorem 95 (p. 152)
-- that upper semicomputability of `f` already suffices, so `f(n) = K(n)` is allowed -- is
built into the statement: `f` takes values in `ℕ∞` and is only assumed to have an r.e. strict
upper graph.
-/

namespace Kolmogorov

open MeasureTheory
open scoped ENNReal

/-! ### Upper semicomputability of conditional plain complexity -/

/-- The strict upper graph of conditional plain complexity is r.e.: `C_V(x | y) < n` holds
exactly when some program shorter than `n` produces `x` from `y`, and the graph of the
partial recursive `V` is r.e. -/
theorem isRE_condK_lt {V : Map} (hV : isDecompressor V) :
    IsRE fun q : BitString × BitString × ℕ => condK V q.1 q.2.1 < (q.2.2 : ℕ∞) := by
  classical
  have hgraph : IsRE fun t : (BitString × BitString × ℕ) × BitString =>
      t.1.1 ∈ V (t.2, t.1.2.1) := by
    have hmap : Computable fun t : (BitString × BitString × ℕ) × BitString =>
        ((t.2, t.1.2.1), t.1.1) :=
      Computable.pair
        (Computable.pair Computable.snd
          (Computable.fst.comp (Computable.snd.comp Computable.fst)))
        (Computable.fst.comp Computable.fst)
    exact (Partrec.graphIsRe V hV).comp_computable hmap
  have hbool : Computable fun t : (BitString × BitString × ℕ) × BitString =>
      decide (t.2.length < t.1.2.2) := by
    refine Primrec.to_comp (PrimrecPred.decide ?_)
    exact Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  refine (IsRE.exists_encodable (R := fun (q : BitString × BitString × ℕ) (p : BitString) =>
    decide (p.length < q.2.2) = true ∧ q.1 ∈ V (p, q.2.1))
    (hgraph.and_computable hbool)).of_iff fun q => ?_
  rw [condK, sInf_lt_iff]
  constructor
  · rintro ⟨p, hlen, hprod⟩
    exact ⟨((p.length : ℕ) : ℕ∞), ⟨p, hprod, rfl⟩, by exact_mod_cast of_decide_eq_true hlen⟩
  · rintro ⟨m, ⟨p, hprod, rfl⟩, hlt⟩
    exact ⟨p, decide_eq_true (by exact_mod_cast hlt), hprod⟩

/-! ### The deficiency set of Theorem 95 -/

/-- SUV p. 151 (proof of Theorem 95): the strings whose conditional plain complexity given
their own length falls below `l(x) - f(l(x)) - c`.  `f` is `ℕ∞`-valued so that the remark
after Theorem 95 (`f(n) = K(n)`) is an instance. -/
def condKDeficiencySet (V : Map) (f : ℕ → ℕ∞) (c : ℕ) : Set BitString :=
  {x | condK V x (natToBitString x.length) + f x.length + c < (x.length : ℕ∞)}

/-- Membership in the deficiency set is the `Σ₁` condition "some pair of strict upper bounds
for the two complexities already fits under the length". -/
lemma mem_condKDeficiencySet_iff (V : Map) (f : ℕ → ℕ∞) (c : ℕ) (x : BitString) :
    x ∈ condKDeficiencySet V f c ↔
      ∃ ab : ℕ × ℕ, condK V x (natToBitString x.length) < ((ab.1 + 1 : ℕ) : ℕ∞)
        ∧ f x.length < ((ab.2 + 1 : ℕ) : ℕ∞) ∧ ab.1 + ab.2 + c < x.length := by
  constructor
  · intro h
    have h' : condK V x (natToBitString x.length) + f x.length + (c : ℕ∞)
        < (x.length : ℕ∞) := h
    have hK : condK V x (natToBitString x.length) ≠ ⊤ := by
      intro htop
      rw [htop] at h'
      simp at h'
    have hF : f x.length ≠ ⊤ := by
      intro htop
      rw [htop] at h'
      simp at h'
    refine ⟨((condK V x (natToBitString x.length)).toNat, (f x.length).toNat), ?_, ?_, ?_⟩
    · conv_lhs => rw [← ENat.coe_toNat hK]
      exact_mod_cast Nat.lt_succ_self _
    · conv_lhs => rw [← ENat.coe_toNat hF]
      exact_mod_cast Nat.lt_succ_self _
    · rw [← ENat.coe_toNat hK, ← ENat.coe_toNat hF] at h'
      exact_mod_cast h'
  · rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    have hKne : condK V x (natToBitString x.length) ≠ ⊤ := ne_top_of_lt ha
    have hFne : f x.length ≠ ⊤ := ne_top_of_lt hb
    have ha' : condK V x (natToBitString x.length) ≤ (a : ℕ∞) := by
      have hlt : (condK V x (natToBitString x.length)).toNat < a + 1 := by
        rw [← ENat.coe_toNat hKne] at ha
        exact_mod_cast ha
      conv_lhs => rw [← ENat.coe_toNat hKne]
      exact_mod_cast Nat.lt_succ_iff.1 hlt
    have hb' : f x.length ≤ (b : ℕ∞) := by
      have hlt : (f x.length).toNat < b + 1 := by
        rw [← ENat.coe_toNat hFne] at hb
        exact_mod_cast hb
      conv_lhs => rw [← ENat.coe_toNat hFne]
      exact_mod_cast Nat.lt_succ_iff.1 hlt
    change condK V x (natToBitString x.length) + f x.length + (c : ℕ∞) < (x.length : ℕ∞)
    calc condK V x (natToBitString x.length) + f x.length + (c : ℕ∞)
        ≤ (a : ℕ∞) + (b : ℕ∞) + (c : ℕ∞) := by gcongr
      _ = ((a + b + c : ℕ) : ℕ∞) := by push_cast; ring
      _ < (x.length : ℕ∞) := by exact_mod_cast hab

/-- SUV p. 151: the deficiency sets are uniformly enumerable, because `C` is upper
semicomputable and `f` is assumed to be as well. -/
theorem isRE_condKDeficiencySet {V : Map} (hV : isDecompressor V) {f : ℕ → ℕ∞}
    (hf : IsRE fun q : ℕ × ℕ => f q.1 < (q.2 : ℕ∞)) :
    IsRE fun q : ℕ × BitString => q.2 ∈ condKDeficiencySet V f q.1 := by
  classical
  have hcode : Computable fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      (p.1.2, natToBitString p.1.2.length, p.2.1 + 1) := by
    refine Computable.pair (Computable.snd.comp Computable.fst) (Computable.pair ?_ ?_)
    · exact computable_natToBitString.comp
        ((Primrec.to_comp Primrec.list_length).comp (Computable.snd.comp Computable.fst))
    · exact Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
  have h1 : IsRE fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      condK V p.1.2 (natToBitString p.1.2.length) < ((p.2.1 + 1 : ℕ) : ℕ∞) :=
    (isRE_condK_lt hV).comp_computable hcode
  have hlen : Computable fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      (p.1.2.length, p.2.2 + 1) :=
    Computable.pair
      ((Primrec.to_comp (Primrec.list_length)).comp (Computable.snd.comp Computable.fst))
      (Primrec.succ.to_comp.comp (Computable.snd.comp Computable.snd))
  have h2 : IsRE fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      f p.1.2.length < ((p.2.2 + 1 : ℕ) : ℕ∞) := hf.comp_computable hlen
  have hbool : Computable fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      decide (p.2.1 + p.2.2 + p.1.1 < p.1.2.length) := by
    refine Primrec.to_comp (PrimrecPred.decide ?_)
    exact Primrec.nat_lt.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
  have hall : IsRE fun p : (ℕ × BitString) × (ℕ × ℕ) =>
      decide (p.2.1 + p.2.2 + p.1.1 < p.1.2.length) = true ∧
        (condK V p.1.2 (natToBitString p.1.2.length) < ((p.2.1 + 1 : ℕ) : ℕ∞)
          ∧ f p.1.2.length < ((p.2.2 + 1 : ℕ) : ℕ∞)) := (h1.and h2).and_computable hbool
  refine (IsRE.exists_encodable (R := fun (q : ℕ × BitString) (ab : ℕ × ℕ) =>
    decide (ab.1 + ab.2 + q.1 < q.2.length) = true ∧
      (condK V q.2 (natToBitString q.2.length) < ((ab.1 + 1 : ℕ) : ℕ∞)
        ∧ f q.2.length < ((ab.2 + 1 : ℕ) : ℕ∞))) hall).of_iff fun q => ?_
  rw [mem_condKDeficiencySet_iff]
  constructor
  · rintro ⟨ab, hlt, hA, hB⟩
    exact ⟨ab, hA, hB, of_decide_eq_true hlt⟩
  · rintro ⟨ab, hA, hB, hlt⟩
    exact ⟨ab, decide_eq_true hlt, hA, hB⟩

open scoped Classical in
/-- The length-`n` slice of the deficiency set. -/
noncomputable def condKDeficiencySlice (V : Map) (f : ℕ → ℕ∞) (c n : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun x => x ∈ condKDeficiencySet V f c)

open scoped Classical in
/-- SUV p. 151: at length `n` the deficiency set has fewer than `2^(n - f(n) - c)` members,
because each of them is produced from the code of `n` by a program shorter than
`n - f(n) - c` and distinct strings need distinct programs. -/
lemma sum_uniformMeasure_condKDeficiencySlice_le (V : Map) (f : ℕ → ℕ∞) (c n : ℕ) :
    ∑ x ∈ condKDeficiencySlice V f c n, uniformMeasure (cantorCylinder x)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (f n) := by
  rcases Finset.eq_empty_or_nonempty (condKDeficiencySlice V f c n) with hemp | ⟨x₀, hx₀⟩
  · simp [hemp]
  -- read off `f n ≠ ⊤` and the length budget from a single member
  rw [condKDeficiencySlice, Finset.mem_filter, mem_stringsOfLength] at hx₀
  obtain ⟨hlen₀, hmem₀⟩ := hx₀
  have hdef₀ : condK V x₀ (natToBitString x₀.length) + f x₀.length + (c : ℕ∞)
      < (x₀.length : ℕ∞) := hmem₀
  rw [hlen₀] at hdef₀
  have hfne : f n ≠ ⊤ := by
    intro htop
    rw [htop] at hdef₀
    simp at hdef₀
  set k : ℕ := (f n).toNat with hk
  have hfk : f n = (k : ℕ∞) := (ENat.coe_toNat hfne).symm
  rw [hfk] at hdef₀
  have hbudget : k + c < n := by
    have hle : (k : ℕ∞) ≤ condK V x₀ (natToBitString n) + (k : ℕ∞) := le_add_self
    have h1 : (k : ℕ∞) + (c : ℕ∞)
        ≤ condK V x₀ (natToBitString n) + (k : ℕ∞) + (c : ℕ∞) := add_le_add hle le_rfl
    have h2 : ((k + c : ℕ) : ℕ∞) < (n : ℕ∞) := by
      push_cast
      exact lt_of_le_of_lt h1 hdef₀
    exact_mod_cast h2
  set m : ℕ := n - k - c - 1 with hm
  have hm1 : m + 1 = n - k - c := by omega
  -- every member of the slice is compressible with budget `m`
  have hsub : condKDeficiencySlice V f c n ⊆ compressibleWords V (natToBitString n) m := by
    intro x hx
    rw [condKDeficiencySlice, Finset.mem_filter, mem_stringsOfLength] at hx
    obtain ⟨hlen, hmem⟩ := hx
    have hdef : condK V x (natToBitString x.length) + f x.length + (c : ℕ∞)
        < (x.length : ℕ∞) := hmem
    rw [hlen, hfk] at hdef
    have hKne : condK V x (natToBitString n) ≠ ⊤ := by
      intro htop
      rw [htop] at hdef
      simp at hdef
    have hnat : (condK V x (natToBitString n)).toNat + k + c < n := by
      rw [← ENat.coe_toNat hKne] at hdef
      exact_mod_cast hdef
    have hlt : condK V x (natToBitString n) < ((m + 1 : ℕ) : ℕ∞) := by
      rw [← ENat.coe_toNat hKne]
      exact_mod_cast (by omega : (condK V x (natToBitString n)).toNat < m + 1)
    rw [compressibleWords, Finset.mem_filter]
    obtain ⟨lenE, hmemLen, hvalLt⟩ := (sInf_lt_iff).mp hlt
    obtain ⟨p, hp_prod, rfl⟩ := hmemLen
    have hple : programLength p ≤ m := Nat.lt_succ_iff.mp (ENat.coe_lt_coe.mp hvalLt)
    refine ⟨?_, ?_⟩
    · rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨p, mem_programsLe m p hple, progToOut_eq_some.mpr hp_prod⟩
    · exact le_trans (sInf_le ⟨p, hp_prod, rfl⟩) (by exact_mod_cast hple)
  have hcard : (condKDeficiencySlice V f c n).card ≤ 2 ^ (m + 1) :=
    le_of_lt (lt_of_le_of_lt (Finset.card_le_card hsub) (card_compressibleWordsLt _ _ _))
  -- each member has uniform mass exactly `2^(-n)`
  have hmass : ∀ x ∈ condKDeficiencySlice V f c n,
      uniformMeasure (cantorCylinder x) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro x hx
    rw [condKDeficiencySlice, Finset.mem_filter, mem_stringsOfLength] at hx
    rw [uniformMeasure_cantorCylinder, hx.1]
  have hsum : ∑ x ∈ condKDeficiencySlice V f c n, uniformMeasure (cantorCylinder x)
      = ((condKDeficiencySlice V f c n).card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [Finset.sum_congr rfl hmass, Finset.sum_const, nsmul_eq_mul]
  have hsplit : (2 : ℝ≥0∞)⁻¹ ^ n = (2 : ℝ≥0∞)⁻¹ ^ (m + 1) * (2 : ℝ≥0∞)⁻¹ ^ (k + c) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel : ((2 : ℝ≥0∞) ^ (m + 1)) * (2 : ℝ≥0∞)⁻¹ ^ (m + 1) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hcardE : ((condKDeficiencySlice V f c n).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (m + 1) := by
    calc ((condKDeficiencySlice V f c n).card : ℝ≥0∞) ≤ ((2 ^ (m + 1) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hcard
      _ = (2 : ℝ≥0∞) ^ (m + 1) := by push_cast; ring
  rw [hsum, hsplit, hfk, complexityWeight_coe]
  calc ((condKDeficiencySlice V f c n).card : ℝ≥0∞)
        * ((2 : ℝ≥0∞)⁻¹ ^ (m + 1) * (2 : ℝ≥0∞)⁻¹ ^ (k + c))
      ≤ (2 : ℝ≥0∞) ^ (m + 1) * ((2 : ℝ≥0∞)⁻¹ ^ (m + 1) * (2 : ℝ≥0∞)⁻¹ ^ (k + c)) := by
        gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (k + c) := by rw [← mul_assoc, hcancel, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞)⁻¹ ^ k := by rw [← pow_add]; congr 1; omega

open scoped Classical in
/-- **The counting step of SUV Theorem 95 (p. 151).**  The set of sequences with a prefix `x`
satisfying `C(x | l(x)) + f(l(x)) + c < l(x)` has uniform measure at most
`2^(-c) · ∑ₙ 2^(-f(n))`. -/
theorem uniformMeasure_prefixHitSet_condKDeficiencySet_le (V : Map) (f : ℕ → ℕ∞) (c : ℕ) :
    uniformMeasure (prefixHitSet (condKDeficiencySet V f c))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c * ∑' n : ℕ, complexityWeight (f n) := by
  have hunion : prefixHitSet (condKDeficiencySet V f c)
      = ⋃ n : ℕ, ⋃ x ∈ condKDeficiencySlice V f c n, cantorCylinder x := by
    rw [prefixHitSet_eq_iUnion_cantorCylinder]
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun x hx => ?_
      refine Set.subset_iUnion_of_subset x.length ?_
      refine Set.subset_iUnion₂_of_subset x ?_ (le_refl _)
      rw [condKDeficiencySlice, Finset.mem_filter, mem_stringsOfLength]
      exact ⟨rfl, hx⟩
    · refine Set.iUnion_subset fun n => Set.iUnion₂_subset fun x hx => ?_
      rw [condKDeficiencySlice, Finset.mem_filter] at hx
      exact Set.subset_iUnion₂ (s := fun x (_ : x ∈ condKDeficiencySet V f c) =>
        cantorCylinder x) x hx.2
  calc uniformMeasure (prefixHitSet (condKDeficiencySet V f c))
      = uniformMeasure (⋃ n : ℕ, ⋃ x ∈ condKDeficiencySlice V f c n, cantorCylinder x) := by
        rw [hunion]
    _ ≤ ∑' n : ℕ, uniformMeasure (⋃ x ∈ condKDeficiencySlice V f c n, cantorCylinder x) :=
        measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ∑ x ∈ condKDeficiencySlice V f c n, uniformMeasure (cantorCylinder x) :=
        ENNReal.tsum_le_tsum fun n => measure_biUnion_finset_le _ _
    _ ≤ ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ c * complexityWeight (f n) :=
        ENNReal.tsum_le_tsum (sum_uniformMeasure_condKDeficiencySlice_le V f c)
    _ = (2 : ℝ≥0∞)⁻¹ ^ c * ∑' n : ℕ, complexityWeight (f n) := ENNReal.tsum_mul_left

/-- **SUV Theorem 95 and its remark (Section 5.6, pp. 151-152), general form.**  If the
`ℕ∞`-valued `f` has an r.e. strict upper graph (in particular if it is total computable, and
also for `f = K`) and `∑ₙ 2^(-f(n))` converges, then every Martin-Löf random sequence
satisfies `C((w)_n | n) ≥ n - f(n) - c` for one constant `c` and all `n`. -/
theorem le_condK_cantorPrefix_add_of_isMartinLofRandom_uniform_general {V : Map}
    (hV : isDecompressor V) {f : ℕ → ℕ∞} (hf : IsRE fun q : ℕ × ℕ => f q.1 < (q.2 : ℕ∞))
    (hconv : (∑' n : ℕ, complexityWeight (f n)) ≠ ⊤) {w : CantorSeq}
    (hw : IsMartinLofRandom uniformMeasure w) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ condK V (cantorPrefix w n) (natToBitString n) + f n + c := by
  classical
  -- a dyadic bound for the convergent series
  obtain ⟨d, hd⟩ := ENNReal.exists_nat_gt hconv
  have hdle : (∑' n : ℕ, complexityWeight (f n)) ≤ (2 : ℝ≥0∞) ^ d := by
    refine le_trans hd.le ?_
    have hn2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc (d : ℝ≥0∞) ≤ ((2 ^ d : ℕ) : ℝ≥0∞) := by exact_mod_cast hn2.le
      _ = (2 : ℝ≥0∞) ^ d := by push_cast; ring
  have hinvd : ((2 : ℝ≥0∞)⁻¹) ^ d * (2 : ℝ≥0∞) ^ d = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  -- the shifted deficiency sets form a Martin-Löf test
  have hshift : Computable fun q : ℕ × BitString => (q.1 + d, q.2) :=
    Computable.pair (Primrec.to_comp (Primrec.nat_add.comp Primrec.fst (Primrec.const d)))
      Computable.snd
  have hRE : IsRE fun q : ℕ × BitString => q.2 ∈ condKDeficiencySet V f (q.1 + d) :=
    (isRE_condKDeficiencySet hV hf).comp_computable hshift
  have hmass : ∀ k : ℕ,
      uniformMeasure (prefixHitSet (condKDeficiencySet V f (k + d))) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    refine le_trans (uniformMeasure_prefixHitSet_condKDeficiencySet_le V f (k + d)) ?_
    calc (2 : ℝ≥0∞)⁻¹ ^ (k + d) * ∑' n : ℕ, complexityWeight (f n)
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + d) * (2 : ℝ≥0∞) ^ d := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ k * (((2 : ℝ≥0∞)⁻¹) ^ d * (2 : ℝ≥0∞) ^ d) := by
          rw [pow_add]; ring
      _ = (2 : ℝ≥0∞)⁻¹ ^ k := by rw [hinvd, mul_one]
  have htest := isMartinLofTest_prefixHitSet (μ := uniformMeasure)
    (S := fun k => condKDeficiencySet V f (k + d)) hRE hmass
  -- a random sequence avoids some level of the test
  by_contra hcon
  push_neg at hcon
  refine hw _ htest (Set.mem_iInter.2 fun k => ?_)
  obtain ⟨n, hn⟩ := hcon (k + d)
  refine ⟨n, ?_⟩
  change condK V (cantorPrefix w n) (natToBitString (cantorPrefix w n).length)
      + f (cantorPrefix w n).length + ((k + d : ℕ) : ℕ∞) < ((cantorPrefix w n).length : ℕ∞)
  rw [cantorPrefix_length]
  exact hn

end Kolmogorov
