import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaCount
import KolmogorovMathlib.Entropy.Coding
import KolmogorovMathlib.Entropy.Complexity.Frequencies
import KolmogorovMathlib.Entropy.Inequalities
import KolmogorovMathlib.InformationInequalities.UniformSets

/-!
# The easy direction: complexity inequalities imply entropy inequalities

SUV Section 10.1, pp. 314–315.

A linear inequality `∑_I λ_I C(x_I) ≤ O(log N)` for the complexities of all tuples of strings of
length at most `N` forces the inequality `∑_I λ_I H(ξ_I) ≤ 0` for entropies
(`holdsForEntropies_of_holdsForComplexitiesLen`).  The argument takes `N` independent copies of
the column `⟨ξ_1, …, ξ_n⟩`, reads the resulting `n × N` matrix as a tuple of rows and uses
Theorem 147 of Chapter 7: the expected complexity of the `I`-rows is `N · H(ξ_I) + O(log N)`;
dividing by `N` and letting `N → ∞` kills the error term (`nonpos_of_mul_le_logSlack`).
-/

namespace Kolmogorov

open Finset

variable {n : ℕ}

/-! ### The easy direction: complexities ⇒ entropies -/

/- The rows of the i.i.d. sample matrix, using one fixed-width block for every value of each
random variable.  The width is deliberately shared by all coordinates, so all row lengths are
linear in the number of sampled columns. -/
private def iidRowWidth {Ω : Type} [Fintype Ω] (X : Fin n → Ω → ℕ) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun ω => (Nat.bits (X i ω)).length

private def iidRows {Ω : Type} [Fintype Ω] (X : Fin n → Ω → ℕ)
    (N : ℕ) (w : Fin N → Ω) (i : Fin n) : BitString :=
  (List.ofFn fun j => natBitsFixed (iidRowWidth X) (X i (w j))).flatten

/- Each row in the encoded sample matrix has exactly `N` fixed-width blocks. -/
private lemma iidRows_tupleMaxLength_le {Ω : Type} [Fintype Ω]
    (X : Fin n → Ω → ℕ) (N : ℕ) (w : Fin N → Ω) :
    tupleMaxLength (iidRows X N w) ≤ iidRowWidth X * N + iidRowWidth X := by
  have hlen : ∀ i : Fin n, (iidRows X N w i).length = N * iidRowWidth X := by
    intro i
    simp [iidRows, List.length_flatten, List.sum_ofFn]
  unfold tupleMaxLength
  refine Finset.sup_le fun i _ => ?_
  rw [hlen i, Nat.mul_comm]
  omega

private lemma flatten_injective_of_length {α : Type} {k : ℕ}
    {l l' : List (List α)} (hcard : l.length = l'.length)
    (hl : ∀ x ∈ l, x.length = k) (hl' : ∀ x ∈ l', x.length = k)
    (hflat : l.flatten = l'.flatten) : l = l' := by
  induction l generalizing l' with
  | nil => simpa using hcard.symm
  | cons x xs ih =>
      cases l' with
      | nil => simp at hcard
      | cons y ys =>
          have hcard' : xs.length = ys.length := by simpa using hcard
          have hx : x.length = k := hl x (by simp)
          have hy : y.length = k := hl' y (by simp)
          have hxy : x = y := by
            have h := congrArg (List.take k) hflat
            simpa [hx, hy] using h
          subst y
          congr 1
          apply ih hcard'
          · intro z hz
            exact hl z (by simp [hz])
          · intro z hz
            exact hl' z (by simp [hz])
          · have h := congrArg (List.drop k) hflat
            simpa [hx] using h

private lemma power_dist_map_eq_prod_dist {Ω A : Type} [Fintype Ω]
    [DecidableEq A] (μ : FiniteProbSpace Ω) (Y : Ω → A) (N : ℕ)
    (v : Fin N → A) :
    (μ.power N).dist (fun w j => Y (w j)) v = ∏ j, μ.dist Y (v j) := by
  classical
  unfold FiniteProbSpace.dist FiniteProbSpace.probOf
  rw [Finset.sum_filter]
  have hw : ∀ w : Fin N → Ω,
      (if (fun j => Y (w j)) = v then ∏ j, μ.prob (w j) else 0) =
        ∏ j, if Y (w j) = v j then μ.prob (w j) else 0 := by
    intro w
    by_cases h : (fun j => Y (w j)) = v
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [ite_eq_left (congrFun h j)]
    · rw [ite_eq_right h]
      have hj : ∃ j, Y (w j) ≠ v j := by
        simpa only [not_forall] using (not_congr funext_iff).mp h
      obtain ⟨j, hj⟩ := hj
      rw [Finset.prod_eq_zero (Finset.mem_univ j)]
      simp [hj]
  simp_rw [FiniteProbSpace.power, hw]
  rw [← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset Finset.univ
      (fun j ω => if Y ω = v j then μ.prob ω else 0)]
  congr 1
  funext j
  rw [Finset.sum_filter]

private lemma entropy_power_map_eq_mul_finite {Ω A : Type} [Fintype Ω] [Finite A]
    [DecidableEq A] (μ : FiniteProbSpace Ω) (Y : Ω → A) (N : ℕ) :
    entropy (μ.power N) (fun w j => Y (w j)) = (N : ℝ) * entropy μ Y := by
  let _ := Fintype.ofFinite A
  rw [entropy_eq_entropyDist, entropy_eq_entropyDist,
    show (μ.power N).dist (fun w j => Y (w j)) =
      fun v => ∏ j, μ.dist Y (v j) from
        funext (power_dist_map_eq_prod_dist μ Y N),
    entropyDist_prod_eq (μ.dist_nonneg Y) (by
      rw [← μ.sum_dist_eq_one Y]
      exact (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => by
        rw [μ.dist_eq_zero_of_not_mem_range ha]).symm) N]

private lemma entropy_power_map_eq_mul {Ω A : Type} [Fintype Ω] [DecidableEq A]
    (μ : FiniteProbSpace Ω) (Y : Ω → A) (N : ℕ) :
    entropy (μ.power N) (fun w j => Y (w j)) = (N : ℝ) * entropy μ Y := by
  classical
  let Y' : Ω → rangeFinset Y := fun ω => ⟨Y ω, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
  let f : (Fin N → rangeFinset Y) → (Fin N → A) := fun v j => (v j).val
  have hf : Function.Injective f := by
    intro v v' h
    funext j
    exact Subtype.ext (congrFun h j)
  have hword : (fun (w : Fin N → Ω) j => Y (w j)) =
      f ∘ (fun w j => Y' (w j)) := by
    funext w j
    rfl
  have hY : entropy μ Y' = entropy μ Y := by
    have h := entropy_comp_of_injective μ Y' Subtype.val_injective
    exact h.symm
  rw [hword, entropy_comp_of_injective (μ.power N) _ hf,
    entropy_power_map_eq_mul_finite μ Y' N, hY]

private lemma entropy_iidRows_subtuple_eq {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) (I : Finset (Fin n)) (N : ℕ) :
    entropy (μ.power N) (fun w => subtupleCode (iidRows X N w) I) =
      (N : ℝ) * entropySub μ X I := by
  classical
  let Y : Ω → (I → ℕ) := subtuple X I
  let W : (Fin N → Ω) → (Fin N → (I → ℕ)) := fun w j => Y (w j)
  let e : (Fin N → (I → ℕ)) → BitString := fun v =>
    listCode ((I.sort (· ≤ ·)).map fun i =>
      (List.ofFn fun j => natBitsFixed (iidRowWidth X)
        (if hi : i ∈ I then v j ⟨i, hi⟩ else 0)).flatten)
  have hcomp : (fun w => subtupleCode (iidRows X N w) I) = e ∘ W := by
    funext w
    simp only [subtupleCode, e, Function.comp_apply]
    apply congrArg listCode
    rw [List.map_eq_map_iff]
    intro i hi
    have hiI : i ∈ I := (Finset.mem_sort _).1 hi
    simp [iidRows, W, Y, subtuple, hiI]
  have hactual : ∀ w w' : Fin N → Ω, e (W w) = e (W w') → W w = W w' := by
    intro w w' he
    apply funext
    intro j
    apply funext
    intro i
    have hmaps := listCode_injective he
    have hrow : iidRows X N w i = iidRows X N w' i := by
      have h := List.map_eq_map_iff.mp hmaps i.val ((Finset.mem_sort _).2 i.2)
      simp only [W, Y, subtuple, i.2, dite_eq_left] at h
      exact h.trans (by rfl)
    have hchunks :
        (List.ofFn fun j => natBitsFixed (iidRowWidth X) (X i.val (w j))) =
          List.ofFn fun j => natBitsFixed (iidRowWidth X) (X i.val (w' j)) := by
      apply flatten_injective_of_length (k := iidRowWidth X) (by simp)
      · simp
      · simp
      · exact hrow
    have hbits := congrFun (List.ofFn_injective hchunks) j
    have hlen : (Nat.bits (X i.val (w j))).length ≤ iidRowWidth X := by
      exact (Finset.le_sup (f := fun ω => (Nat.bits (X i.val ω)).length)
        (Finset.mem_univ (w j))).trans
          (Finset.le_sup (f := fun i => Finset.univ.sup fun ω =>
            (Nat.bits (X i ω)).length) (Finset.mem_univ i.val))
    have hlen' : (Nat.bits (X i.val (w' j))).length ≤ iidRowWidth X := by
      exact (Finset.le_sup (f := fun ω => (Nat.bits (X i.val ω)).length)
        (Finset.mem_univ (w' j))).trans
          (Finset.le_sup (f := fun i => Finset.univ.sup fun ω =>
            (Nat.bits (X i ω)).length) (Finset.mem_univ i.val))
    apply natBitsFixed_inj
        (lt_of_lt_of_le (lt_two_pow_length_natBits _) (Nat.pow_le_pow_right (by omega) hlen))
        (lt_of_lt_of_le (lt_two_pow_length_natBits _) (Nat.pow_le_pow_right (by omega) hlen'))
        hbits
  have hinj : Set.InjOn e {v | 0 < (μ.power N).dist W v} := by
    intro v hv v' hv' he
    obtain ⟨w, hw, _⟩ := ((μ.power N).dist_pos_iff W v).1 hv
    obtain ⟨w', hw', _⟩ := ((μ.power N).dist_pos_iff W v').1 hv'
    rw [← hw, ← hw'] at he ⊢
    exact hactual w w' he
  rw [hcomp]
  change entropy (μ.power N) (fun w => e (W w)) = _
  rw [(entropy_comp_eq_iff (μ.power N) W e).2 hinj,
    entropy_power_map_eq_mul μ Y N]
  rfl

private lemma entropy_le_expect_plainK_add_logSlack (D : Map)
    {Ω : Type} [Fintype Ω] (ν : FiniteProbSpace Ω) (Z : Ω → BitString) (c L : ℕ)
    (hK : ∀ z, plainK D z ≤ (z.length : ℕ∞) + (c : ℕ∞))
    (hL : ∀ ω, (Z ω).length ≤ L) :
    entropy ν Z ≤ ν.expect (fun ω => ((plainK D (Z ω)).toNat : ℝ)) +
      (logSlack 1 (L + c + 1) : ℝ) := by
  classical
  let R := rangeFinset Z
  have hfinite : ∀ z : ↥R, plainK D z.val ≠ ⊤ := fun z =>
    ne_top_of_le_natCast_add (hK z.val)
  let p : Code R := fun z => Classical.choose
    (exists_program_of_KP_ne_top (M := D) (x := z.val) (y := []) (by
      rw [KP_eq_condK]
      exact hfinite z))
  have hp : ∀ z : ↥R, produces D (p z) [] z.val := fun z =>
    (Classical.choose_spec
      (exists_program_of_KP_ne_top (M := D) (x := z.val) (y := []) (by
        rw [KP_eq_condK]
        exact hfinite z))).1
  have hplen : ∀ z : ↥R, (p z).length = (plainK D z.val).toNat := fun z => by
    have h := congrArg ENat.toNat
      (Classical.choose_spec
        (exists_program_of_KP_ne_top (M := D) (x := z.val) (y := []) (by
          rw [KP_eq_condK]
          exact hfinite z))).2
    exact h.trans (by rfl)
  have hpinj : Function.Injective p := by
    intro z z' h
    apply Subtype.ext
    exact Part.mem_unique (h ▸ hp z) (hp z')
  have hpbound : ∀ z : ↥R, (p z).length < L + c + 1 := by
    intro z
    rw [hplen]
    obtain ⟨ω, hω⟩ := mem_rangeFinset.1 z.property
    have hk' : plainK D z.val ≤ ((z.val.length + c : ℕ) : ℕ∞) := by
      simpa using hK z.val
    have hk := ENat.toNat_le_of_le_natCast hk'
    have hzlen : z.val.length ≤ L := by simpa [hω] using hL ω
    exact lt_of_le_of_lt (hk.trans (Nat.add_le_add_right hzlen c)) (by omega)
  let q : R → ℝ := fun z => ν.dist Z z.val
  have hqnonneg : ∀ z, 0 ≤ q z := fun z => ν.dist_nonneg Z z.val
  have hqsum : ∑ z, q z = 1 := by
    change ∑ z : ↥(rangeFinset Z), ν.dist Z z.val = 1
    rw [Finset.sum_coe_sort, ν.sum_dist_eq_one]
  have havg : p.avgLength q =
      ν.expect (fun ω => ((plainK D (Z ω)).toNat : ℝ)) := by
    unfold Code.avgLength FiniteProbSpace.expect
    simp only [q, hplen]
    change (∑ z : ↥(rangeFinset Z),
      ν.dist Z z.val * ((plainK D z.val).toNat : ℝ)) = _
    have hcoe : (∑ z : ↥(rangeFinset Z),
        ν.dist Z z.val * ((plainK D z.val).toNat : ℝ)) =
        ∑ z ∈ rangeFinset Z, ν.dist Z z * ((plainK D z).toNat : ℝ) := by
      exact Finset.sum_coe_sort (rangeFinset Z)
        (fun z => ν.dist Z z * ((plainK D z).toNat : ℝ))
    rw [hcoe]
    have hfiber := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset Ω)) (t := rangeFinset Z) (g := Z)
      (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) => mem_rangeFinset.2 ⟨ω, rfl⟩)
      (fun ω => ν.prob ω * ((plainK D (Z ω)).toNat : ℝ))
    rw [← hfiber]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold FiniteProbSpace.dist FiniteProbSpace.probOf
    rw [mul_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [(Finset.mem_filter.1 hω).2]
    ring
  have hent : entropy ν Z = entropyDist q := by
    unfold entropy entropyDist
    change (∑ a ∈ rangeFinset Z, negMulLog2 (ν.dist Z a)) =
      ∑ z : ↥(rangeFinset Z), negMulLog2 (ν.dist Z z.val)
    exact (Finset.sum_coe_sort (rangeFinset Z)
      (fun z => negMulLog2 (ν.dist Z z))).symm
  have hcode := entropyDist_sub_logb_le_avgLength_of_injective
    hqnonneg hqsum hpinj hpbound
  rw [← hent, havg] at hcode
  have hpow : ((L + c + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((Nat.bits (L + c + 1)).length : ℕ) : ℝ) := by
    exact_mod_cast (lt_two_pow_length_natBits (L + c + 1)).le
  have hlog : Real.logb 2 ((L + c + 1 : ℕ) : ℝ) ≤
      ((Nat.bits (L + c + 1)).length : ℝ) :=
    (Real.logb_le_iff_le_rpow one_lt_two (by positivity)).2 hpow
  have hslack : ((Nat.bits (L + c + 1)).length : ℝ) ≤
      (logSlack 1 (L + c + 1) : ℝ) := by
    simp [logSlack]
  calc
    entropy ν Z ≤ ν.expect (fun ω => ((plainK D (Z ω)).toNat : ℝ)) +
        Real.logb 2 ((L + c + 1 : ℕ) : ℝ) := by linarith
    _ ≤ ν.expect (fun ω => ((plainK D (Z ω)).toNat : ℝ)) +
        (logSlack 1 (L + c + 1) : ℝ) := by
      gcongr
      exact hlog.trans hslack

private lemma length_listCode_eq_sum (l : List BitString) :
    (listCode l).length = (l.map fun x => 2 * x.length + 1).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [length_listCode_cons, ih]
      simp

private lemma iidRows_subtupleCode_length_le {Ω : Type} [Fintype Ω]
    (X : Fin n → Ω → ℕ) (I : Finset (Fin n)) (N : ℕ) (w : Fin N → Ω) :
    (subtupleCode (iidRows X N w) I).length ≤
      (2 * n * iidRowWidth X) * N + n := by
  rw [subtupleCode, length_listCode_eq_sum]
  have hrow : ∀ i : Fin n, (iidRows X N w i).length = N * iidRowWidth X := by
    intro i
    simp [iidRows, List.length_flatten, List.sum_ofFn]
  rw [List.map_map]
  change ((I.sort (· ≤ ·)).map
    (fun i => 2 * (iidRows X N w i).length + 1)).sum ≤ _
  simp_rw [hrow]
  simp only [List.map_const', Finset.length_sort, List.sum_replicate, smul_eq_mul]
  have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
  calc
    I.card * (2 * (N * iidRowWidth X) + 1) ≤
        n * (2 * (N * iidRowWidth X) + 1) := Nat.mul_le_mul_right _ hcard
    _ = (2 * n * iidRowWidth X) * N + n := by ring

/- The prefix-code lower bound from Theorem 147, transferred to the plain complexity of every
subtuple of the encoded rows.  The transfer costs only `O(log N)`, uniformly over the finitely
many subtuples. -/
private lemma exists_iidRows_expected_plainK_lower_bound
    (D : Map) (hD : isOptimalConditional D) {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) :
    ∃ c : ℕ, ∀ (I : Finset (Fin n)) (N : ℕ),
      (N : ℝ) * entropySub μ X I ≤
        (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) +
            (logSlack c N : ℝ) := by
  obtain ⟨cK, hK⟩ := plainK_le_length D hD
  let a := 2 * n * iidRowWidth X
  obtain ⟨c, hc⟩ := logSlack_linear_bound 1 a (n + cK + 1)
  refine ⟨c, fun I N => ?_⟩
  let Z : (Fin N → Ω) → BitString := fun w => subtupleCode (iidRows X N w) I
  have hlen : ∀ w, (Z w).length ≤ a * N + n := fun w => by
    exact iidRows_subtupleCode_length_le X I N w
  have hmain := entropy_le_expect_plainK_add_logSlack D (μ.power N) Z cK
    (a * N + n) hK hlen
  rw [show entropy (μ.power N) Z = (N : ℝ) * entropySub μ X I by
    exact entropy_iidRows_subtuple_eq μ X I N] at hmain
  calc
    (N : ℝ) * entropySub μ X I ≤
        (μ.power N).expect (fun w => ((plainK D (Z w)).toNat : ℝ)) +
          (logSlack 1 (a * N + n + cK + 1) : ℝ) := hmain
    _ = (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) +
          (logSlack 1 (a * N + (n + cK + 1)) : ℝ) := by
      simp only [Z, tuplePlainK, Nat.add_assoc]
    _ ≤ (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) +
          (logSlack c N : ℝ) := by
      gcongr
      exact_mod_cast hc N

/- A fixed-width block of a number below `2 ^ w` reads back as that number. -/
private lemma bitsToNat_natBitsFixed (w : ℕ) :
    ∀ k, k < 2 ^ w → bitsToNat (natBitsFixed w k) = k := by
  induction w with
  | zero => intro k hk; obtain rfl : k = 0 := (by simpa using hk); rfl
  | succ w ih =>
    intro k hk
    have hk2 : k / 2 < 2 ^ w := by rw [pow_succ] at hk; omega
    have hsplit : natBitsFixed (w + 1) k = Nat.testBit k 0 :: natBitsFixed w (k / 2) := by
      simp [natBitsFixed, List.ofFn_succ, Nat.testBit_succ]
    rw [hsplit]
    simp only [bitsToNat, List.foldr_cons]
    change 2 * bitsToNat (natBitsFixed w (k / 2)) + _ = k
    rw [ih _ hk2]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.testBit_zero, h] <;> omega

/- Cutting a concatenation of blocks of a common positive width `b` into consecutive pieces of
length `b` recovers the blocks. -/
private lemma blocks_flatten {b : ℕ} (hb : 0 < b) : ∀ cs : List BitString,
    (∀ c ∈ cs, c.length = b) →
    (List.range (cs.flatten.length / b)).map
      (fun i => (List.range b).map fun k => cs.flatten.getD (i * b + k) false) = cs := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons c cs ih =>
    intro hc
    have hcb : c.length = b := hc c (by simp)
    have hcs : ∀ d ∈ cs, d.length = b := fun d hd => hc d (by simp [hd])
    have hlen : (c :: cs).flatten.length / b = cs.flatten.length / b + 1 := by
      rw [List.flatten_cons, List.length_append, hcb]
      rw [Nat.add_comm, Nat.add_div_right _ hb]
    rw [hlen, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · apply List.ext_getElem (by simp [hcb])
      intro k hk _
      simp only [List.getElem_map, List.getElem_range, List.flatten_cons, zero_mul, zero_add]
      simp at hk
      rw [List.getD_append _ _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < c.length)]
    · conv_rhs => rw [← ih hcs]
      apply List.map_congr_left
      intro i _
      apply List.map_congr_left
      intro k hk
      simp only [List.flatten_cons]
      simp at hk
      rw [List.getD_append_right _ _ _ _ (by rw [hcb]; nlinarith)]
      congr 1
      rw [hcb, Nat.succ_mul]
      omega

/-- The block code of a word over a finite alphabet is decoded, letter by letter, into the ranks
of its letters by a primitive recursive function. -/
lemma exists_primrec_wordBits_decoder (A : Type*) [Fintype A] [Encodable A] :
    ∃ dec : BitString → List ℕ, Primrec dec ∧
      ∀ l : List A, dec (wordBits A l) = l.map (alphabetIndex A) := by
  set b := alphabetWidth A
  refine ⟨fun x => ((List.range (x.length / b)).map fun i =>
      (List.range b).map fun k => x.getD (i * b + k) false).map bitsToNat, ?_, ?_⟩
  · have hg : Primrec₂ (fun (x : BitString) (i : ℕ) =>
        (List.range b).map fun k => x.getD (i * b + k) false) := by
      refine Primrec.list_map (Primrec.const _) ?_
      exact ((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.const b)) Primrec.snd)).to₂
    have hc : Primrec (fun x : BitString => (List.range (x.length / b)).map fun i =>
        (List.range b).map fun k => x.getD (i * b + k) false) :=
      Primrec.list_map (Primrec.list_range.comp
        (Primrec.nat_div.comp Primrec.list_length (Primrec.const b))) hg
    exact Primrec.list_map hc (bitsToNat_primrec.comp Primrec.snd).to₂
  · intro l
    have hb : 0 < b := Nat.succ_pos _
    have hw : wordBits A l = (l.map (alphabetCode A)).flatten := rfl
    simp only [hw]
    rw [blocks_flatten hb _ (by simp [b]), List.map_map]
    apply List.map_congr_left
    intro a _
    exact bitsToNat_natBitsFixed _ _ (alphabetIndex_lt_two_pow a)

/- Recoding: a word over a finite alphabet, each letter of which carries a fixed list of
strings, is computably turned into the `listCode` of its rows, the `t`-th row being the
concatenation of the `t`-th strings of its letters. -/
private lemma exists_computable_rows_of_wordBits (A : Type*) [Fintype A] [Encodable A]
    (codes : A → List BitString) (k : ℕ) :
    ∃ f : BitString → BitString, Computable f ∧ ∀ l : List A,
      f (wordBits A l) = listCode ((List.range k).map fun t =>
        l.flatMap fun a => (codes a).getD t []) := by
  classical
  obtain ⟨dec, hdec, hdecw⟩ := exists_primrec_wordBits_decoder A
  let T : List (List BitString) := (List.range (Fintype.card A)).map fun m =>
    if h : ∃ a : A, alphabetIndex A a = m then codes (Classical.choose h) else []
  have hT : ∀ a : A, T.getD (alphabetIndex A a) [] = codes a := by
    intro a
    have hlt := alphabetIndex_lt_card a
    have hex : ∃ b : A, alphabetIndex A b = alphabetIndex A a := ⟨a, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    simp only [Option.map_some, Option.getD_some, dite_eq_left hex]
    rw [alphabetIndex_injective (Classical.choose_spec hex)]
  have hL : Primrec listCode := by
    have h := Primrec.list_foldr (f := fun l : List BitString => l)
      (g := fun _ => ([] : BitString))
      (h := fun _ p => pairCode p.1 p.2) Primrec.id (Primrec.const [])
      (CodedFiniteDistribution.pairCode_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
    exact h.of_eq fun l => rfl
  refine ⟨fun x => listCode ((List.range k).map fun t =>
      (dec x).flatMap fun m => (T.getD m []).getD t []), ?_, ?_⟩
  · refine (hL.comp (Primrec.list_map (Primrec.const _) ?_)).to_comp
    exact (Primrec.list_flatMap (hdec.comp Primrec.fst)
      ((Primrec.list_getD []).comp ((Primrec.list_getD []).comp (Primrec.const T) Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).to₂).to₂
  · intro l
    simp only [hdecw, List.flatMap_map, hT]

/- The expected number of occurrences of a value among `N` independent copies is `N` times its
probability. -/
private lemma power_expect_freq_eq {Ω A : Type} [Fintype Ω] [DecidableEq A]
    (μ : FiniteProbSpace Ω) (Y : Ω → A) (N : ℕ) (a : A) :
    ∑ w : Fin N → Ω, (μ.power N).prob w * (freq (fun j => Y (w j)) a : ℝ) =
      (N : ℝ) * μ.dist Y a := by
  classical
  have hcoord : ∀ j : Fin N, ∑ w : Fin N → Ω, (μ.power N).prob w *
      (if Y (w j) = a then (1 : ℝ) else 0) = μ.dist Y a := by
    intro j
    let h : Fin N → Ω → ℝ := fun k ω => if k = j then (if Y ω = a then 1 else 0) else 1
    have hprod : ∑ w : Fin N → Ω, (μ.power N).prob w * ∏ k, h k (w k) =
        ∏ k, ∑ ω, μ.prob ω * h k ω := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      simp [FiniteProbSpace.power, Finset.prod_mul_distrib]
    have hl : ∀ w : Fin N → Ω, ∏ k, h k (w k) = if Y (w j) = a then 1 else 0 := by
      intro w
      simp [h]
    have hr : ∏ k, ∑ ω, μ.prob ω * h k ω = ∑ ω, μ.prob ω * (if Y ω = a then 1 else 0) := by
      have : ∀ k, ∑ ω, μ.prob ω * h k ω =
          if k = j then ∑ ω, μ.prob ω * (if Y ω = a then 1 else 0) else 1 := by
        intro k
        by_cases hk : k = j
        · simp [h, hk]
        · simp [h, hk, μ.sum_prob]
      simp [this]
    simp only [hl] at hprod
    rw [hprod, hr]
    unfold FiniteProbSpace.dist FiniteProbSpace.probOf
    rw [Finset.sum_filter]
    simp [mul_ite]
  have hfreq : ∀ w : Fin N → Ω, (freq (fun j => Y (w j)) a : ℝ) =
      ∑ j, if Y (w j) = a then (1 : ℝ) else 0 := by
    intro w
    rw [freq, Finset.natCast_card_filter]
  simp_rw [hfreq, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hcoord j]
  simp

/- Concavity of entropy: the expected entropy of the empirical frequencies of `N` independent
copies is at most the entropy of one copy. -/
private lemma expect_mul_entropyDist_freq_le {Ω A : Type} [Fintype Ω] [Fintype A]
    [DecidableEq A] (μ : FiniteProbSpace Ω) (Y : Ω → A) (N : ℕ) :
    (μ.power N).expect (fun w => (N : ℝ) *
        entropyDist fun a => (freq (fun j => Y (w j)) a : ℝ) / N) ≤
      (N : ℝ) * entropy μ Y := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [FiniteProbSpace.expect]
  rw [entropy_eq_entropyDist]
  unfold FiniteProbSpace.expect entropyDist
  have hswap : ∑ w, (μ.power N).prob w * ((N : ℝ) *
      ∑ a, negMulLog2 ((freq (fun j => Y (w j)) a : ℝ) / N)) =
      (N : ℝ) * ∑ a, ∑ w, (μ.power N).prob w *
        negMulLog2 ((freq (fun j => Y (w j)) a : ℝ) / N) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ => by ring
  rw [hswap]
  gcongr with a
  refine (sum_mul_negMulLog2_le Finset.univ _ _ (fun w _ => (μ.power N).prob_nonneg w)
    (μ.power N).sum_prob (fun w _ => by positivity)).trans (le_of_eq ?_)
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by positivity
  simp_rw [mul_div_assoc', ← Finset.sum_div, power_expect_freq_eq]
  field_simp

/- The upper bound for one fixed subtuple: the `I`-rows are computable from the word of
`I`-columns, whose complexity is at most `N` times the entropy of its letter frequencies plus
`O(log N)` (Theorem 146), and these entropies average to at most `H(ξ_I)`. -/
private lemma exists_iidRows_expected_plainK_upper_bound_sub
    (D : Map) (hD : isOptimalConditional D) {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) (I : Finset (Fin n)) :
    ∃ c : ℕ, ∀ N : ℕ,
      (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) ≤
        (N : ℝ) * entropySub μ X I + (logSlack c N : ℝ) := by
  classical
  set s := I.sort (· ≤ ·) with hs
  let Y : Ω → List ℕ := fun ω => s.map fun i => X i ω
  let A := ↥(rangeFinset Y)
  let Yl : Ω → A := fun ω => ⟨Y ω, mem_rangeFinset.2 ⟨ω, rfl⟩⟩
  have hent : entropy μ Yl = entropySub μ X I := by
    have h1 : entropy μ Yl = entropy μ Y :=
      (entropy_comp_of_injective μ Yl Subtype.val_injective).symm
    let g : (I → ℕ) → List ℕ := fun F => s.map fun i => if h : i ∈ I then F ⟨i, h⟩ else 0
    have hg : Function.Injective g := by
      intro F F' hFF
      funext i
      have h := List.map_inj_left.1 hFF i.val ((Finset.mem_sort _).2 i.2)
      simpa [i.2] using h
    have hY : Y = g ∘ subtuple X I := by
      funext ω
      refine List.map_congr_left fun i hi => ?_
      have hiI : i ∈ I := (Finset.mem_sort _).1 hi
      simp [hiI, subtuple]
    rw [h1, hY, entropy_comp_of_injective μ _ hg]
    rfl
  obtain ⟨cA, hcA⟩ := exists_plainK_word_le_entropy_freq A D hD
  obtain ⟨f, hf, hfw⟩ := exists_computable_rows_of_wordBits A
    (fun a => a.val.map (natBitsFixed (iidRowWidth X))) s.length
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD f hf
  obtain ⟨cK, hcK⟩ := plainK_le_length D hD
  have hrow : ∀ (N : ℕ) (w : Fin N → Ω),
      f (finWordBits A fun j => Yl (w j)) = subtupleCode (iidRows X N w) I := by
    intro N w
    rw [finWordBits, hfw, subtupleCode, ← hs]
    congr 1
    refine List.ext_getElem (by simp) fun t ht _ => ?_
    have ht' : t < s.length := by simpa using ht
    simp only [List.getElem_map, List.getElem_range, iidRows, List.flatMap, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun j => ?_)
    simp [Yl, Y, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  refine ⟨cA + c1, fun N => ?_⟩
  set L : ℝ := (logSlack cA N : ℝ) + c1 with hL
  have hpt : ∀ w : Fin N → Ω, ((tuplePlainK D (iidRows X N w) I).toNat : ℝ) ≤
      (N : ℝ) * (entropyDist fun a => (freq (fun j => Yl (w j)) a : ℝ) / N) + L := by
    intro w
    have h146 := hcA N fun j => Yl (w j)
    set x := finWordBits A fun j => Yl (w j)
    have hfin : plainK D x ≠ ⊤ := ne_top_of_le_natCast_add (hcK x)
    have hle : plainK D (f x) ≤ (((plainK D x).toNat + c1 : ℕ) : ℕ∞) := by
      have := hc1 x
      rw [← ENat.natCast_toNat hfin] at this
      exact_mod_cast this
    have hnat := ENat.toNat_le_of_le_natCast hle
    rw [hrow] at hnat
    have hr : ((tuplePlainK D (iidRows X N w) I).toNat : ℝ) ≤
        ((plainK D x).toNat : ℝ) + c1 := by
      exact_mod_cast hnat
    rw [hL]
    linarith
  have hexp_le : (μ.power N).expect (fun w =>
      ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) ≤
      (μ.power N).expect (fun w => (N : ℝ) *
        (entropyDist fun a => (freq (fun j => Yl (w j)) a : ℝ) / N)) + L := by
    unfold FiniteProbSpace.expect
    calc ∑ w, (μ.power N).prob w * ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)
        ≤ ∑ w, (μ.power N).prob w * ((N : ℝ) *
            (entropyDist fun a => (freq (fun j => Yl (w j)) a : ℝ) / N) + L) :=
          Finset.sum_le_sum fun w _ =>
            mul_le_mul_of_nonneg_left (hpt w) ((μ.power N).prob_nonneg w)
      _ = _ := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (μ.power N).sum_prob,
            one_mul]
  have hjensen := expect_mul_entropyDist_freq_le μ Yl N
  rw [hent] at hjensen
  have hslack : L ≤ (logSlack (cA + c1) N : ℝ) := by
    rw [hL]
    simp only [logSlack]
    push_cast
    nlinarith [(Nat.cast_nonneg (Nat.bits N).length : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg c1 : (0 : ℝ) ≤ c1)]
  linarith

/- Type-class coding gives the matching upper bound for every subtuple.  This version does not
assume that the probabilities are computable: a word is described by its empirical frequencies
and its rank in the corresponding type class. -/
private lemma exists_iidRows_expected_plainK_upper_bound
    (D : Map) (hD : isOptimalConditional D) {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) :
    ∃ c : ℕ, ∀ (I : Finset (Fin n)) (N : ℕ),
      (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) ≤
        (N : ℝ) * entropySub μ X I + (logSlack c N : ℝ) := by
  choose cI hcI using fun I => exists_iidRows_expected_plainK_upper_bound_sub D hD μ X I
  refine ⟨∑ J, cI J, fun I N => (hcI I N).trans ?_⟩
  have hle : cI I ≤ ∑ J, cI J :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
  have hmono : logSlack (cI I) N ≤ logSlack (∑ J, cI J) N :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hle) hle
  have hmono' : (logSlack (cI I) N : ℝ) ≤ logSlack (∑ J, cI J) N := by exact_mod_cast hmono
  linarith

/- A finite linear form preserves the coordinatewise `O(log N)` approximation.  Positive
coefficients use the lower complexity bound and negative coefficients use the upper one. -/
private lemma exists_evalEntropy_le_expected_evalComplexity
    (f : LinearForm n) (D : Map) {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) (c₁ c₂ : ℕ)
    (hlower : ∀ (I : Finset (Fin n)) (N : ℕ),
      (N : ℝ) * entropySub μ X I ≤
        (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) +
            (logSlack c₁ N : ℝ))
    (hupper : ∀ (I : Finset (Fin n)) (N : ℕ),
      (μ.power N).expect (fun w =>
          ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)) ≤
        (N : ℝ) * entropySub μ X I + (logSlack c₂ N : ℝ)) :
    ∃ c : ℕ, ∀ N : ℕ,
      (N : ℝ) * f.evalEntropy μ X ≤
        (μ.power N).expect (fun w => f.evalComplexity D (iidRows X N w)) +
          (logSlack c N : ℝ) := by
  let s : ℝ := ∑ I ∈ nonemptyParts n, |f I|
  let k : ℕ := ⌈s⌉₊
  refine ⟨k * (c₁ + c₂), fun N => ?_⟩
  let e : Finset (Fin n) → ℝ := fun I =>
    (μ.power N).expect fun w =>
      ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)
  have hsk : s ≤ (k : ℝ) := by simpa [k] using Nat.le_ceil s
  have hslack₁ : 0 ≤ (logSlack c₁ N : ℝ) := by positivity
  have hslack₂ : 0 ≤ (logSlack c₂ N : ℝ) := by positivity
  have hterm : ∀ I : Finset (Fin n),
      f I * ((N : ℝ) * entropySub μ X I) ≤
        f I * e I + |f I| *
          ((logSlack c₁ N : ℝ) + (logSlack c₂ N : ℝ)) := by
    intro I
    by_cases hf : 0 ≤ f I
    · rw [abs_of_nonneg hf]
      have h := mul_le_mul_of_nonneg_left (hlower I N) hf
      change f I * ((N : ℝ) * entropySub μ X I) ≤
        f I * (e I + (logSlack c₁ N : ℝ)) at h
      nlinarith
    · have hf' : f I < 0 := lt_of_not_ge hf
      rw [abs_of_neg hf']
      have h := mul_le_mul_of_nonpos_left (hupper I N) hf'.le
      change f I * ((N : ℝ) * entropySub μ X I + (logSlack c₂ N : ℝ)) ≤
        f I * e I at h
      nlinarith
  have hexpect :
      (μ.power N).expect (fun w => f.evalComplexity D (iidRows X N w)) =
        ∑ I ∈ nonemptyParts n, f I * e I := by
    unfold FiniteProbSpace.expect LinearForm.evalComplexity
    rw [Finset.sum_congr rfl fun w _ => Finset.mul_sum .., Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    change (∑ w, (μ.power N).prob w *
        (f I * ((tuplePlainK D (iidRows X N w) I).toNat : ℝ))) =
      f I * ∑ w, (μ.power N).prob w *
        ((tuplePlainK D (iidRows X N w) I).toNat : ℝ)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hexpect]
  calc
    (N : ℝ) * f.evalEntropy μ X =
        ∑ I ∈ nonemptyParts n, f I * ((N : ℝ) * entropySub μ X I) := by
      unfold LinearForm.evalEntropy
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      ring
    _ ≤ ∑ I ∈ nonemptyParts n,
        (f I * e I + |f I| *
          ((logSlack c₁ N : ℝ) + (logSlack c₂ N : ℝ))) := by
      exact Finset.sum_le_sum fun I _ => hterm I
    _ = (∑ I ∈ nonemptyParts n, f I * e I) +
        s * ((logSlack c₁ N : ℝ) + (logSlack c₂ N : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ I ∈ nonemptyParts n, f I * e I) +
        (k : ℝ) * ((logSlack c₁ N : ℝ) + (logSlack c₂ N : ℝ)) := by
      gcongr
    _ = (∑ I ∈ nonemptyParts n, f I * e I) +
        (logSlack (k * (c₁ + c₂)) N : ℝ) := by
      simp only [logSlack]
      push_cast
      ring

private lemma exists_iid_rows_with_expected_complexity_lower_bound
    (f : LinearForm n) (D : Map) (hD : isOptimalConditional D)
    {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) :
    ∃ (rows : (N : ℕ) → (Fin N → Ω) → Fin n → BitString) (a c : ℕ),
      ∀ N : ℕ,
        (∀ w, tupleMaxLength (rows N w) ≤ a * N + a) ∧
          (N : ℝ) * f.evalEntropy μ X ≤
            (μ.power N).expect (fun w => f.evalComplexity D (rows N w)) +
              (logSlack c N : ℝ) := by
  obtain ⟨c₁, hc₁⟩ := exists_iidRows_expected_plainK_lower_bound D hD μ X
  obtain ⟨c₂, hc₂⟩ := exists_iidRows_expected_plainK_upper_bound D hD μ X
  obtain ⟨c, hc⟩ :=
    exists_evalEntropy_le_expected_evalComplexity f D μ X c₁ c₂ hc₁ hc₂
  exact ⟨iidRows X, iidRowWidth X, c, fun N =>
    ⟨iidRows_tupleMaxLength_le X N, hc N⟩⟩

private lemma exists_expected_complexity_bound_for_iid_rows
    (f : LinearForm n) (D : Map) (h : HoldsForComplexitiesLen f D)
    {Ω : Type} [Fintype Ω] (μ : FiniteProbSpace Ω)
    (rows : (N : ℕ) → (Fin N → Ω) → Fin n → BitString) (a : ℕ)
    (hlen : ∀ (N : ℕ) (w : Fin N → Ω), tupleMaxLength (rows N w) ≤ a * N + a) :
    ∃ c : ℕ, ∀ N : ℕ,
      (μ.power N).expect (fun w => f.evalComplexity D (rows N w)) ≤
        (logSlack c N : ℝ) := by
  obtain ⟨c₀, hc₀⟩ := h
  obtain ⟨c, hc⟩ := logSlack_linear_bound c₀ a a
  refine ⟨c, fun N => ?_⟩
  calc
    (μ.power N).expect (fun w => f.evalComplexity D (rows N w)) ≤
        (logSlack c₀ (a * N + a) : ℝ) := by
      unfold FiniteProbSpace.expect
      calc
        ∑ w, (μ.power N).prob w * f.evalComplexity D (rows N w) ≤
            ∑ w, (μ.power N).prob w * (logSlack c₀ (a * N + a) : ℝ) := by
          refine Finset.sum_le_sum fun w _ => ?_
          exact mul_le_mul_of_nonneg_left
            (hc₀ (a * N + a) (rows N w) (hlen N w)) ((μ.power N).prob_nonneg w)
        _ = (logSlack c₀ (a * N + a) : ℝ) := by
          rw [← Finset.sum_mul, (μ.power N).sum_prob, one_mul]
    _ ≤ (logSlack c N : ℝ) := by
      exact_mod_cast hc N

private lemma exists_mul_evalEntropy_le_logSlack_of_holdsForComplexitiesLen
    (f : LinearForm n) (D : Map) (hD : isOptimalConditional D)
    (h : HoldsForComplexitiesLen f D) {Ω : Type} [Fintype Ω]
    (μ : FiniteProbSpace Ω) (X : Fin n → Ω → ℕ) :
    ∃ c : ℕ, ∀ N : ℕ,
      (N : ℝ) * f.evalEntropy μ X ≤ (logSlack c N : ℝ) := by
  obtain ⟨rows, a, c₁, hrows⟩ :=
    exists_iid_rows_with_expected_complexity_lower_bound f D hD μ X
  obtain ⟨c₂, hc₂⟩ :=
    exists_expected_complexity_bound_for_iid_rows f D h μ rows a
      (fun N w => (hrows N).1 w)
  refine ⟨c₁ + c₂, fun N => ?_⟩
  calc
    (N : ℝ) * f.evalEntropy μ X ≤
        (μ.power N).expect (fun w => f.evalComplexity D (rows N w)) +
          (logSlack c₁ N : ℝ) := (hrows N).2
    _ ≤ (logSlack c₂ N : ℝ) + (logSlack c₁ N : ℝ) := by
      gcongr
      exact hc₂ N
    _ = (logSlack (c₁ + c₂) N : ℝ) := by
      rw [add_comm]
      exact_mod_cast (logSlack_add_constants c₁ c₂ N).symm

/-- A real number `a` with `N a ≤ c log N + c` for every `N` is non-positive: a positive `a`
makes the left-hand side grow linearly. -/
lemma nonpos_of_mul_le_logSlack (a : ℝ) (c : ℕ)
    (h : ∀ N : ℕ, (N : ℝ) * a ≤ (logSlack c N : ℝ)) : a ≤ 0 := by
  by_contra ha
  have ha_pos : 0 < a := lt_of_not_ge ha
  obtain ⟨k, hk⟩ := exists_nat_gt ((4 * c : ℝ) / a + 1)
  have hk_pos : 0 < k := by
    have hdiv : (0 : ℝ) ≤ (4 * c : ℝ) / a := div_nonneg (by positivity) ha_pos.le
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hk_a : (4 * c : ℝ) < k * a := by
    have hdiv : (4 * c : ℝ) / a < k := lt_trans (lt_add_one _) hk
    exact (div_lt_iff₀ ha_pos).mp hdiv
  have hbits : (Nat.bits (k * k)).length ≤ k + 2 := by
    simpa using bits_length_le_sqrt_add_two (k * k)
  have hlog : (logSlack c (k * k) : ℝ) ≤ (c : ℝ) * (k + 2) + c := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left c hbits) c
  have hmain := h (k * k)
  have hc : (0 : ℝ) ≤ c := by positivity
  have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk_pos
  push_cast at hmain hlog hk_a hk_one
  nlinarith

/-- **The easy half of Romashchenko's equivalence.**  If a linear form is valid for the plain
complexities of all tuples of strings of length at most `N`, with `O(log N)` precision, then it
is valid for the entropies of all tuples of random variables.  The proof applies the
complexity inequality to the rows of a matrix of `N` independent copies of the tuple and uses
Theorem 147 of Chapter 7 (`E C = N · H + O(log N)`); the error term disappears in the limit
`N → ∞`.  SUV Section 10.1, pp. 314–315 (unnumbered). -/
theorem holdsForEntropies_of_holdsForComplexitiesLen (f : LinearForm n) (D : Map)
    (hD : isOptimalConditional D) (h : HoldsForComplexitiesLen f D) :
    HoldsForEntropies f := by
  intro Ω _ μ X
  obtain ⟨c, hc⟩ :=
    exists_mul_evalEntropy_le_logSlack_of_holdsForComplexitiesLen f D hD h μ X
  exact nonpos_of_mul_le_logSlack (f.evalEntropy μ X) c hc

end Kolmogorov
