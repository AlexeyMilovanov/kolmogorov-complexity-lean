import KolmogorovMathlib.MonotoneComplexity.Stream
import KolmogorovMathlib.MonotoneComplexity.StreamTopology

/-!
# Recovering a stream from its set of finite approximations

`IsStreamPrefixSet T` says that `T` is nonempty, prefix-closed and linearly ordered by the
prefix relation — exactly the shape of the set of finite approximations of a stream.
`BitStream.ofPrefixSet` reconstructs the stream: the longest member when the lengths are bounded
(`exists_greatest_of_bddAbove_length`), the sequence determined by the members otherwise
(`mem_of_isCantorPrefix`, `isCantorPrefix_of_mem`). The reconstruction is exact:
`BitStream.finite_le_ofPrefixSet_iff` says the finite approximations of the resulting stream are
precisely the members of `T`. This is what lets a monotone machine's output set be read as a
single stream.
-/

open Set

namespace Kolmogorov

/-- A nonempty, prefix-closed and linearly ordered set of bit strings: the set of finite
approximations of a single stream. -/
def IsStreamPrefixSet (T : Set BitString) : Prop :=
  [] ∈ T ∧
  (∀ {x y}, x <+: y → y ∈ T → x ∈ T) ∧
  (∀ {x y}, x ∈ T → y ∈ T → x <+: y ∨ y <+: x)

/-- Two members of a stream prefix set of the same length are equal. -/
lemma chain_eq_of_length_eq {T : Set BitString} (hT : IsStreamPrefixSet T) {x y : BitString}
    (hx : x ∈ T) (hy : y ∈ T) (h : x.length = y.length) : x = y := by
  rcases hT.2.2 hx hy with hxy | hyx
  · exact hxy.eq_of_length h
  · exact (hyx.eq_of_length h.symm).symm

/-- A stream prefix set of bounded length has a longest member, of which every member is a prefix.
-/
lemma exists_greatest_of_bddAbove_length {T : Set BitString} (hT : IsStreamPrefixSet T)
    (h_bdd : ∃ M, ∀ x ∈ T, x.length ≤ M) : ∃ m ∈ T, ∀ y ∈ T, y <+: m := by
  obtain ⟨M, hM⟩ := h_bdd
  let P (n : ℕ) := ∃ x ∈ T, x.length = n
  have : DecidablePred P := Classical.decPred P
  have hP0 : P 0 := ⟨[], hT.1, rfl⟩
  set n := Nat.findGreatest P M
  have hPn : P n := Nat.findGreatest_spec (m := 0) (hmb := by omega) (hm := hP0)
  obtain ⟨m, hm_in, hm_len⟩ := hPn
  use m, hm_in
  intro y hy
  rcases hT.2.2 hy hm_in with hym | hmy
  · exact hym
  · have hy_len_M : y.length ≤ M := hM y hy
    have hy_len_n : y.length ≤ n := Nat.le_findGreatest (hmb := hy_len_M) (hm := ⟨y, hy, rfl⟩)
    have heq : m = y := hmy.eq_of_length (by have := hmy.length_le; omega)
    rw [heq]

-- Unbounded case:
/-- A set of strings of unbounded length has members longer than any given bound. -/
lemma exists_mem_length_gt {T : Set BitString} (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M)
    (n : ℕ) : ∃ y ∈ T, n < y.length := by
  by_contra h
  push Not at h
  exact h_unbdd ⟨n, h⟩

open Classical in
/-- The stream whose finite approximations are exactly the members of `T`: the longest member if `T`
is bounded, and the sequence they determine otherwise. -/
noncomputable def BitStream.ofPrefixSet (T : Set BitString) (hT : IsStreamPrefixSet T) :
    BitStream :=
  if h_bdd : ∃ M, ∀ x ∈ T, x.length ≤ M then
    .finite (choose (exists_greatest_of_bddAbove_length hT h_bdd))
  else
    .infinite fun i =>
      (choose (exists_mem_length_gt h_bdd i)).get
        ⟨i, (choose_spec (exists_mem_length_gt h_bdd i)).2⟩

/-- A string and an extension of it agree at every position of the shorter one. -/
lemma isPrefix_get_eq {x y : BitString} (hxy : x <+: y) {i : ℕ}
    (hi : i < x.length) (hi2 : i < y.length) : x[i] = y[i] := by
  rcases hxy with ⟨t, rfl⟩
  exact (List.getElem_append_left hi).symm

/-- A shorter string agreeing with a longer one at every one of its positions is a prefix of it. -/
lemma isPrefix_of_getElem_eq {x y : BitString} (h_len : x.length ≤ y.length)
    (h_eq : ∀ i (hi : i < x.length), x[i] = y[i]) : x <+: y := by
  have H : x = y.take x.length := by
    apply List.ext_get
    · rw [List.length_take]
      exact (Nat.min_eq_left h_len).symm
    · intro i hi1 hi2
      have h3 : i < y.length := by omega
      have h4 : (y.take x.length)[i] = y[i] := List.getElem_take (h := hi2)
      have h5 : x[i] = y[i] := h_eq i hi1
      have h6 : x.get ⟨i, hi1⟩ = x[i] := rfl
      have h7 : (y.take x.length).get ⟨i, hi2⟩ = (y.take x.length)[i] := rfl
      rw [h6, h7, h4, ← h5]
  use y.drop x.length
  nth_rw 1 [H]
  exact List.take_append_drop x.length y

open Classical in
/-- For an unbounded stream prefix set, every prefix of the determined sequence belongs to the set.
-/
lemma mem_of_isCantorPrefix {T : Set BitString} (hT : IsStreamPrefixSet T)
    (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) (x : BitString)
    (h : IsCantorPrefix x (fun i => (choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (choose_spec (exists_mem_length_gt h_unbdd i)).2⟩)) :
    x ∈ T := by
  set y := choose (exists_mem_length_gt h_unbdd x.length)
  have hy := choose_spec (exists_mem_length_gt h_unbdd x.length)
  have hy_in : y ∈ T := hy.1
  have hy_len : x.length < y.length := hy.2
  have hxy : x <+: y := by
    apply isPrefix_of_getElem_eq (by omega)
    intro i hi
    have h_w : (choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (choose_spec (exists_mem_length_gt h_unbdd i)).2⟩ = x[i] := h i hi
    set y_i := choose (exists_mem_length_gt h_unbdd i)
    have hy_i := choose_spec (exists_mem_length_gt h_unbdd i)
    have hy_i_in : y_i ∈ T := hy_i.1
    have hy_i_len : i < y_i.length := hy_i.2
    have H_w : y_i.get ⟨i, hy_i_len⟩ = x[i] := h_w
    rcases hT.2.2 hy_i_in hy_in with h1 | h2
    · have : y_i.get ⟨i, hy_i_len⟩ = y_i[i] := rfl
      rw [this] at H_w
      have : y_i[i] = y[i] := isPrefix_get_eq h1 hy_i_len (by omega)
      rw [← H_w, this]
    · have : y_i.get ⟨i, hy_i_len⟩ = y_i[i] := rfl
      rw [this] at H_w
      have : y_i[i] = y[i] := (isPrefix_get_eq h2 (by omega) hy_i_len).symm
      rw [← H_w, this]
  exact hT.2.1 hxy hy_in

open Classical in
/-- For an unbounded stream prefix set, every member is a prefix of the determined sequence. -/
lemma isCantorPrefix_of_mem {T : Set BitString} (hT : IsStreamPrefixSet T)
    (h_unbdd : ¬ ∃ M, ∀ x ∈ T, x.length ≤ M) (x : BitString) (hx : x ∈ T) :
    IsCantorPrefix x (fun i => (choose (exists_mem_length_gt h_unbdd i)).get
      ⟨i, (choose_spec (exists_mem_length_gt h_unbdd i)).2⟩) := by
  intro i hi
  set y_i := choose (exists_mem_length_gt h_unbdd i)
  have hy_i := choose_spec (exists_mem_length_gt h_unbdd i)
  have hy_i_in : y_i ∈ T := hy_i.1
  have hy_i_len : i < y_i.length := hy_i.2
  change y_i.get ⟨i, hy_i_len⟩ = x[i]
  rcases hT.2.2 hx hy_i_in with h1 | h2
  · have : y_i.get ⟨i, hy_i_len⟩ = y_i[i] := rfl
    rw [this]
    have : x[i] = y_i[i] := isPrefix_get_eq h1 hi hy_i_len
    rw [this]
  · have : y_i.get ⟨i, hy_i_len⟩ = y_i[i] := rfl
    rw [this]
    have : x[i] = y_i[i] := (isPrefix_get_eq h2 hy_i_len hi).symm
    rw [this]

open Classical in
/-- The stream built from `T` approximates exactly the members of `T`. -/
theorem BitStream.finite_le_ofPrefixSet_iff {T} (hT : IsStreamPrefixSet T) (x : BitString) :
    BitStream.finite x ≤ BitStream.ofPrefixSet T hT ↔ x ∈ T := by
  rw [BitStream.ofPrefixSet]
  split_ifs with h_bdd
  · set m := choose (exists_greatest_of_bddAbove_length hT h_bdd)
    have hm := choose_spec (exists_greatest_of_bddAbove_length hT h_bdd)
    have hm_in : m ∈ T := hm.1
    have hm_max : ∀ y ∈ T, y <+: m := hm.2
    constructor
    · intro h
      exact hT.2.1 h hm_in
    · intro hx
      exact hm_max x hx
  · constructor
    · intro h
      exact mem_of_isCantorPrefix hT h_bdd x h
    · intro hx
      exact isCantorPrefix_of_mem hT h_bdd x hx

end Kolmogorov
