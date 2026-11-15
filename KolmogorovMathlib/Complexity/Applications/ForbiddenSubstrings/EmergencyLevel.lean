/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Complexity.Applications.ForbiddenSubstrings.BiinfiniteSequences

/-!
# Emergency Level

Miller's emergency levels, used in the proof that a set of forbidden substrings of small enough
weight can be avoided by an infinite sequence (Shen–Uspensky–Vereshchagin, p. 243 ff.).

For a set `F` of finite binary strings, a parameter `c` and a string `x`, the emergency level
`emergency c F x` sums `c ^ k` over all possible occurrences of a string `z ∈ F` that overlap the
end of `x` and miss `k` bits.  The main declarations are:

* `emergency`: the emergency level;
* `emergency_nil`, `one_le_emergency_of_suffix`: the level of the empty string is `0`, and it is at
  least `1` as soon as a forbidden string is a suffix;
* `emergency_append_add`, `exists_bit_emergency_lt_one`: how the level changes when one bit is
  appended, and the existence of a bit keeping the level below `1`;
* `exists_avoiding_of_tsum_lt`, `exists_avoidsLong`: if the weight of `F` is small, there is a
  sequence avoiding `F`.
-/

namespace Kolmogorov.Applications
open scoped ENNReal

/-! ### Miller's emergency levels -/

open Classical in
/-- **SUV p. 243.**  The *emergency level* `w_c(x)`: the sum, over all `z ∈ F` and over all possible
occurrences of `z` in an extension of `x` with non-zero overlap, of `c^k`, where `k` is the number
of bits of `z` missing in `x`.  A possible occurrence with overlap `j` is one where the first `j`
bits of `z` are the last `j` bits of `x`. -/
noncomputable def emergency (c : ℝ≥0∞) (F : Set (List Bool)) (x : List Bool) : ℝ≥0∞ :=
  ∑' z : F, ∑ j ∈ Finset.Icc 1 (min x.length z.1.length),
    if z.1.take j = x.drop (x.length - j) then c ^ (z.1.length - j) else 0

/-- **SUV p. 244.**  Initially the emergency level is `0`. -/
theorem emergency_nil (c : ℝ≥0∞) (F : Set (List Bool)) : emergency c F [] = 0 := by
  simp [emergency]

/-- **SUV p. 244.**  If a non-empty forbidden string is a suffix of `x`, the emergency level of `x`
is at least `1`.  The book says "if `x` contains a forbidden string"; only the suffix case is used,
since the first forbidden substring to appear in a growing string is a suffix, and an occurrence
strictly inside `x` is not counted by the definition. -/
theorem one_le_emergency_of_suffix (c : ℝ≥0∞) {F : Set (List Bool)} {x z : List Bool} (hz : z ∈ F)
    (hne : z ≠ []) (hsuf : z <:+ x) : 1 ≤ emergency c F x := by
  classical
  have hlen : z.length ≤ x.length := hsuf.length_le
  have hpos : 1 ≤ z.length := List.length_pos_iff.mpr hne
  have hmem : z.length ∈ Finset.Icc 1 (min x.length z.length) :=
    Finset.mem_Icc.mpr ⟨hpos, le_min hlen le_rfl⟩
  have hdrop : z.take z.length = x.drop (x.length - z.length) := by
    obtain ⟨t, rfl⟩ := hsuf
    simp
  calc (1 : ℝ≥0∞) = if z.take z.length = x.drop (x.length - z.length)
          then c ^ (z.length - z.length) else 0 := by rw [ite_eq_left hdrop]; simp
    _ ≤ ∑ j ∈ Finset.Icc 1 (min x.length z.length),
          if z.take j = x.drop (x.length - j) then c ^ (z.length - j) else 0 :=
        Finset.single_le_sum (f := fun j => if z.take j = x.drop (x.length - j)
          then c ^ (z.length - j) else 0) (fun _ _ => zero_le) hmem
    _ ≤ emergency c F x := by
        unfold emergency
        exact ENNReal.le_tsum (f := fun z : F => ∑ j ∈ Finset.Icc 1 (min x.length z.1.length),
          if z.1.take j = x.drop (x.length - j) then c ^ (z.1.length - j) else 0) ⟨z, hz⟩

/-- The contribution of one string `z` to the emergency level, with overlap `i + 1`. -/
private noncomputable def emergencyTerm (c : ℝ≥0∞) (z x : List Bool) : ℝ≥0∞ := by
  classical
  exact ∑ i ∈ Finset.range (min x.length z.length),
    if z.take (i + 1) = x.drop (x.length - (i + 1)) then c ^ (z.length - (i + 1)) else 0

/-- The emergency level is the sum of the contributions of the strings of `F`. -/
private lemma emergency_eq_tsum (c : ℝ≥0∞) (F : Set (List Bool)) (x : List Bool) :
    emergency c F x = ∑' z : F, emergencyTerm c z.1 x := by
  refine tsum_congr fun z => ?_
  unfold emergencyTerm
  refine (Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    have h1 := Finset.mem_Icc.mp ha
    have h2 := Finset.mem_Icc.mp hb
    omega
  · intro i hi
    have := Finset.mem_range.mp hi
    exact ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro j hj
    have h1 := (Finset.mem_Icc.mp hj).1
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp

open Classical in
/-- The overlap condition for `x ++ [b]`: the overlap `i + 1` of `z` with `x ++ [b]` is possible
exactly when the overlap `i` with `x` is, and the next bit of `z` is `b`. -/
private lemma overlap_snoc (z x : List Bool) (b : Bool) {i : ℕ} (hil : i < z.length)
    (hia : i ≤ x.length) :
    z.take (i + 1) = (x ++ [b]).drop ((x ++ [b]).length - (i + 1)) ↔
      z.take i = x.drop (x.length - i) ∧ z[i] = b := by
  have hlen : (x ++ [b]).length - (i + 1) = x.length - i := by simp
  rw [hlen, List.drop_append_of_le_length (by omega), List.take_add_one,
    List.getElem?_eq_getElem hil]
  simp only [Option.toList_some]
  constructor
  · intro h
    have hl : (z.take i).length = (x.drop (x.length - i)).length := by
      simp only [List.length_take, List.length_drop]
      omega
    have hsplit := List.append_inj h hl
    exact ⟨hsplit.1, by simpa using hsplit.2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

open Classical in
/-- **The identity for one string `z`.** -/
private lemma emergencyTerm_append_add (c : ℝ≥0∞) {x z : List Bool} (hz : z ≠ [])
    (hsuf : ¬ z <:+ x) :
    c * emergencyTerm c z (x ++ [false]) + c * emergencyTerm c z (x ++ [true]) =
      emergencyTerm c z x + c ^ z.length := by
  have hlpos : 0 < z.length := List.length_pos_iff.mpr hz
  set G : ℕ → ℝ≥0∞ := fun i =>
    if z.take i = x.drop (x.length - i) then c ^ (z.length - i) else 0 with hG
  -- The sum over the two bits, multiplied by `c`, is a sum of `G`.
  have hbits : c * emergencyTerm c z (x ++ [false]) + c * emergencyTerm c z (x ++ [true]) =
      ∑ i ∈ Finset.range (min (x.length + 1) z.length), G i := by
    have hlenx : ∀ b : Bool, (x ++ [b]).length = x.length + 1 := fun b => by simp
    unfold emergencyTerm
    simp only [hlenx]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hil : i < z.length := by omega
    have hia : i ≤ x.length := by omega
    have hpow : c * c ^ (z.length - (i + 1)) = c ^ (z.length - i) := by
      rw [← pow_succ']
      congr 1
      omega
    simp only [hG]
    have hf := overlap_snoc z x false hil hia
    have ht := overlap_snoc z x true hil hia
    rw [hlenx false] at hf
    rw [hlenx true] at ht
    by_cases hm : z.take i = x.drop (x.length - i)
    · cases hbit : z[i] with
      | false =>
        rw [ite_eq_left (hf.mpr ⟨hm, hbit⟩),
          ite_eq_right (fun h => by simpa [hbit] using (ht.mp h).2), ite_eq_left hm, mul_zero,
          add_zero, hpow]
      | true =>
        rw [ite_eq_right (fun h => by simpa [hbit] using (hf.mp h).2),
          ite_eq_left (ht.mpr ⟨hm, hbit⟩), ite_eq_left hm, mul_zero, zero_add, hpow]
    · rw [ite_eq_right (fun h => hm (hf.mp h).1), ite_eq_right (fun h => hm (ht.mp h).1),
        ite_eq_right hm, mul_zero, add_zero]
  -- The term for overlap `0` is `c ^ |z|`.
  have hG0 : G 0 = c ^ z.length := by simp [hG]
  -- The terms for positive overlap are those of `x`.
  have hxterm : emergencyTerm c z x =
      ∑ i ∈ Finset.range (min (x.length + 1) z.length - 1), G (i + 1) := by
    unfold emergencyTerm
    simp only [hG]
    by_cases hal : x.length < z.length
    · have h1 : min x.length z.length = min (x.length + 1) z.length - 1 := by omega
      rw [h1]
    · have hla : z.length ≤ x.length := not_lt.mp hal
      have h1 : min x.length z.length = (min (x.length + 1) z.length - 1) + 1 := by omega
      rw [h1, Finset.sum_range_succ]
      have hlast : min (x.length + 1) z.length - 1 + 1 = z.length := by omega
      have hnot : ¬ z.take (min (x.length + 1) z.length - 1 + 1) =
          x.drop (x.length - (min (x.length + 1) z.length - 1 + 1)) := by
        rw [hlast, List.take_length]
        intro h
        exact hsuf ⟨x.take (x.length - z.length), by
          conv_rhs => rw [← List.take_append_drop (x.length - z.length) x]
          rw [← h]⟩
      rw [ite_eq_right hnot, add_zero]
  have hsplit : min (x.length + 1) z.length = (min (x.length + 1) z.length - 1) + 1 := by omega
  rw [hbits, hxterm, hsplit, Finset.sum_range_succ', Nat.add_sub_cancel, hG0]

/-- **SUV p. 244.**  The identity `w_c(x) = c w_c(x0) + c w_c(x1) - ∑_{z∈F} c^{l(z)}`, in the form
without subtraction, assuming that no forbidden string is a suffix of `x` and the empty string is
not forbidden. -/
theorem emergency_append_add (c : ℝ≥0∞) {F : Set (List Bool)} {x : List Bool} (hnil : [] ∉ F)
    (hx : ∀ z ∈ F, ¬ z <:+ x) :
    c * emergency c F (x ++ [false]) + c * emergency c F (x ++ [true]) =
      emergency c F x + ∑' z : F, c ^ z.1.length := by
  simp only [emergency_eq_tsum]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine tsum_congr fun z => ?_
  exact emergencyTerm_append_add c (fun h => hnil (h ▸ z.2)) (hx z.1 z.2)

/-- **SUV p. 244.**  The invariant `w_c(x) < 1` can be kept when a bit is added, if
`1 + ∑_{z∈F} c^{l(z)} < 2c`. -/
theorem exists_bit_emergency_lt_one {c : ℝ≥0∞} {F : Set (List Bool)} {x : List Bool} (hnil : [] ∉ F)
    (hsum : 1 + ∑' z : F, c ^ z.1.length < 2 * c) (hx : emergency c F x < 1)
    (hsuf : ∀ z ∈ F, ¬ z <:+ x) : ∃ b, emergency c F (x ++ [b]) < 1 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon false
  have h1 := hcon true
  have hid := emergency_append_add c (x := x) hnil hsuf
  have hle : 2 * c ≤ c * emergency c F (x ++ [false]) + c * emergency c F (x ++ [true]) := by
    calc 2 * c = c * 1 + c * 1 := by rw [mul_one, two_mul]
      _ ≤ _ := by gcongr
  rw [hid] at hle
  have hlt : emergency c F x + ∑' z : F, c ^ z.1.length < 1 + ∑' z : F, c ^ z.1.length := by
    have hfin : ∑' z : F, c ^ z.1.length ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hsum
      exact not_top_lt hsum
    exact ENNReal.add_lt_add_right hfin hx
  exact absurd (hle.trans_lt (hlt.trans hsum)) (lt_irrefl _)

/-! ### Miller's proof of Theorem 157 -/

/-- **SUV p. 244.**  If `1 + ∑_{z∈F} c^{l(z)} < 2c`, there is a sequence with no substring in `F`:
it is built bit by bit keeping the invariant `w_c(x) < 1`. -/
theorem exists_avoiding_of_tsum_lt {c : ℝ≥0∞} {F : Set (List Bool)} (hnil : [] ∉ F)
    (hsum : 1 + ∑' z : F, c ^ z.1.length < 2 * c) : ∃ w, ∀ u ∈ F, ¬ OccursIn u w := by
  have hsuf : ∀ x, emergency c F x < 1 → ∀ z ∈ F, ¬ z <:+ x := fun x hx z hz hzx =>
    absurd (one_le_emergency_of_suffix c hz (fun h => hnil (h ▸ hz)) hzx) (not_le.mpr hx)
  have hnext : ∀ x : {x // emergency c F x < 1}, ∃ b, emergency c F (x.1 ++ [b]) < 1 :=
    fun x => exists_bit_emergency_lt_one hnil hsum x.2 (hsuf _ x.2)
  choose b hb using hnext
  let hist : ℕ → {x // emergency c F x < 1} := fun n =>
    Nat.rec ⟨[], by rw [emergency_nil]; exact zero_lt_one⟩ (fun _ x => ⟨x.1 ++ [b x], hb x⟩) n
  let w : ℕ → Bool := fun n => b (hist n)
  have hprefix : ∀ n, (hist n).1 = seqFactor w 0 n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [seqFactor_succ, ← ih, Nat.zero_add]
  refine ⟨w, fun u hu ⟨i, hi⟩ => ?_⟩
  have hs : u <:+ (hist (i + u.length)).1 := by
    rw [hprefix, seqFactor_add w 0 i u.length, Nat.zero_add, hi]
    exact List.suffix_append _ _
  exact hsuf _ (hist _).2 u hu hs

/-- The sum of `c^{l(z)}` over the long forbidden strings is bounded by a tail of a geometric
series. -/
private lemma tsum_pow_length_le {α : ℝ} {F : Set (List Bool)} (hF : IsAtMostForbidden α F) {r : ℝ}
    (hr : 0 ≤ r) (L : ℕ) :
    ∑' z : ({z ∈ F | L ≤ z.length} : Set (List Bool)), ENNReal.ofReal r ^ z.1.length ≤
      ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ α * r) ^ (k + L)) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  let g : ({z ∈ F | L ≤ z.length} : Set (List Bool)) → ℕ := fun z => z.1.length - L
  have hbound : ∀ k, ∑ z ∈ s with g z = k, ENNReal.ofReal r ^ z.1.length ≤
      ENNReal.ofReal (((2 : ℝ) ^ α * r) ^ (k + L)) := by
    intro k
    have hlen : ∀ z ∈ s.filter (fun z => g z = k), z.1.length = k + L := by
      intro z hz
      have h1 := (Finset.mem_filter.mp hz).2
      have h2 := z.2.2
      simp only [g] at h1
      omega
    have hcard : (((s.filter fun z => g z = k).card : ℕ) : ℝ) ≤ (2 : ℝ) ^ (α * (k + L : ℕ)) := by
      refine le_trans ?_ (hF (k + L))
      have hinj : Set.InjOn (Subtype.val : ({z ∈ F | L ≤ z.length} : Set (List Bool)) → List Bool)
          (s.filter fun z => g z = k : Finset _) := Subtype.val_injective.injOn
      rw [← Finset.card_image_of_injOn hinj]
      have hsub : (((s.filter fun z => g z = k).image Subtype.val : Finset (List Bool)) :
          Set (List Bool)) ⊆ {x ∈ F | x.length = k + L} := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact ⟨z.2.1, hlen z hz⟩
      have hfin : ({x ∈ F | x.length = k + L} : Set (List Bool)).Finite :=
        (finite_length_eq (k + L)).subset fun x hx => hx.2
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    calc ∑ z ∈ s with g z = k, ENNReal.ofReal r ^ z.1.length
        = ∑ z ∈ s with g z = k, ENNReal.ofReal r ^ (k + L) :=
          Finset.sum_congr rfl fun z hz => by rw [hlen z hz]
      _ = ((s.filter fun z => g z = k).card : ℝ≥0∞) * ENNReal.ofReal r ^ (k + L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((s.filter fun z => g z = k).card : ℝ) * r ^ (k + L)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_pow hr]
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ α * r) ^ (k + L)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpow : ((2 : ℝ) ^ α * r) ^ (k + L) = (2 : ℝ) ^ (α * (k + L : ℕ)) * r ^ (k + L) := by
            rw [mul_pow, Real.rpow_mul (by norm_num), Real.rpow_natCast]
          rw [hpow]
          exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hr _)
  calc ∑ z ∈ s, ENNReal.ofReal r ^ z.1.length
      = ∑ k ∈ s.image g, ∑ z ∈ s with g z = k, ENNReal.ofReal r ^ z.1.length :=
        (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem g hz) _).symm
    _ ≤ ∑ k ∈ s.image g, ENNReal.ofReal (((2 : ℝ) ^ α * r) ^ (k + L)) :=
        Finset.sum_le_sum fun k _ => hbound k
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ α * r) ^ (k + L)) := ENNReal.sum_le_tsum _

/-- **SUV Theorem 157, p. 241.**  Let `0 < α < 1`, with at most `2^{αn}` forbidden strings of each
length `n`.  Then there are `c` and an infinite sequence with no forbidden substring of length `c`
or more.  The proof is Miller's, of pp. 243-244: `c` between `1/2` and `2^{-α}` makes the series
finite, and deleting the short strings makes it small. -/
theorem exists_avoidsLong {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) {F : Set (List Bool)}
    (hF : IsAtMostForbidden α F) : ∃ c w, AvoidsLong F c w := by
  set r : ℝ := (2 : ℝ) ^ (-(1 + α) / 2) with hr
  have hr0 : 0 < r := by positivity
  have hrhalf : 1 / 2 < r := by
    have h : (1 : ℝ) / 2 = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
    rw [h, hr]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  set ρ : ℝ := (2 : ℝ) ^ α * r with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    have h : ρ = (2 : ℝ) ^ (α + -(1 + α) / 2) := by
      rw [hρ, hr, Real.rpow_add (by norm_num)]
    rw [h]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (ρ ^ k)
  have hf : ∑' k, f k ≠ ⊤ := (summable_geometric_of_lt_one hρ0 hρ1).tsum_ofReal_ne_top
  have htail := ENNReal.tendsto_sum_nat_add f hf
  have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (2 * r - 1) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨L, hL, hL1⟩ := ((htail.eventually (gt_mem_nhds hε)).and
    (Filter.eventually_ge_atTop 1)).exists
  let F' : Set (List Bool) := {z ∈ F | L ≤ z.length}
  have hnil : [] ∉ F' := fun h => by
    have : L ≤ 0 := h.2
    omega
  have hsum : 1 + ∑' z : F', ENNReal.ofReal r ^ z.1.length < 2 * ENNReal.ofReal r := by
    have hle := tsum_pow_length_le hF hr0.le L
    have hlt : ∑' z : F', ENNReal.ofReal r ^ z.1.length < ENNReal.ofReal (2 * r - 1) :=
      hle.trans_lt hL
    calc 1 + ∑' z : F', ENNReal.ofReal r ^ z.1.length
        < 1 + ENNReal.ofReal (2 * r - 1) := ENNReal.add_lt_add_left ENNReal.one_ne_top hlt
      _ = 2 * ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
          rw [show (1 : ℝ) + (2 * r - 1) = 2 * r by ring, ENNReal.ofReal_mul (by norm_num)]
          norm_num
  obtain ⟨w, hw⟩ := exists_avoiding_of_tsum_lt hnil hsum
  exact ⟨L, w, fun u hu hlen => hw u ⟨hu, hlen⟩⟩

end Kolmogorov.Applications
