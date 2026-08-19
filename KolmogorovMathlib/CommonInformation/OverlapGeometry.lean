import KolmogorovMathlib.CommonInformation.Definitions

/-!
# Common Information: overlap geometry and length arithmetic

Chapter-local, complexity-free infrastructure for the Exercise 307 overlap
representation.  Everything here is a statement about lists of booleans and
natural numbers, kernel-checked independently of Kolmogorov complexity.

The picture is the SUV overlap diagram: a shared string `u` of length `kxy`
whose length-`lx` prefix represents `x` and whose length-`ly` suffix represents
`y`.  When `kxy ≤ lx + ly` the prefix and suffix overlap in a block of length
`lx + ly - kxy` (the "common part" `z`); when `lx + ly ≤ kxy` there is instead
a private gap of length `kxy - (lx + ly)`.

The two pure operations are:

* `literalOverlap u lx ly` — the literal intersection block of the length-`lx`
  prefix and length-`ly` suffix of `u`;
* `resizeToLength w n` — truncate-or-zero-pad `w` to the exact length `n`.

Both come with exact length theorems, and `literalOverlap` comes with the
explicit left/overlap/right factorization of `u`.  The pure-`Nat` lemmas
`overlap_gap_lengths`, `normalized_overlap_gap_lengths`, and
`sharedDescriptionLengths_close` isolate the arithmetic used later to normalize
a raw shared description to an exact-length overlap witness.

None of these lemmas assume truncation is harmless: every `take`/`drop` length
is proved from explicit bounds so that no requested block is silently shortened.
-/

namespace Kolmogorov

/-! ### The overlap block -/

/-- The literal intersection of the length-`lx` prefix and the length-`ly`
suffix of `u`.  When `u.length ≤ lx + ly` this is the shared block occupying
positions `[u.length - ly, lx)`. -/
def literalOverlap (u : BitString) (lx ly : Nat) : BitString :=
  (u.drop (u.length - ly)).take (lx + ly - u.length)

/-- In the overlap case (`kxy ≤ lx + ly`, with both block lengths bounded by the
outer length `kxy = u.length`), the overlap block has the exact length
`lx + ly - kxy`. -/
theorem literalOverlap_length {u : BitString} {lx ly kxy : Nat}
    (hu : u.length = kxy)
    (hlx : lx ≤ kxy) (hly : ly ≤ kxy)
    (hov : kxy ≤ lx + ly) :
    (literalOverlap u lx ly).length = lx + ly - kxy := by
  unfold literalOverlap
  rw [List.length_take, List.length_drop, hu]
  omega

/-- Exact left/overlap/right factorization of `u` in the overlap case.  The
left-private block has length `kxy - ly`, the overlap block has length
`lx + ly - kxy` (from `literalOverlap_length`), and the right-private block has
length `kxy - lx`. -/
theorem literalOverlap_factorization {u : BitString} {lx ly kxy : Nat}
    (hu : u.length = kxy)
    (_hlx : lx ≤ kxy) (hly : ly ≤ kxy)
    (hov : kxy ≤ lx + ly) :
    ∃ left right,
      u = left ++ literalOverlap u lx ly ++ right ∧
      left.length = kxy - ly ∧
      right.length = kxy - lx := by
  refine ⟨u.take (u.length - ly), u.drop lx, ?_, ?_, ?_⟩
  · have hsplit : (u.length - ly) + (lx + ly - u.length) = lx := by rw [hu]; omega
    calc
      u = u.take lx ++ u.drop lx := (List.take_append_drop lx u).symm
      _ = u.take ((u.length - ly) + (lx + ly - u.length)) ++ u.drop lx := by rw [hsplit]
      _ = (u.take (u.length - ly)
            ++ (u.drop (u.length - ly)).take (lx + ly - u.length)) ++ u.drop lx := by
            rw [List.take_add]
      _ = u.take (u.length - ly) ++ literalOverlap u lx ly ++ u.drop lx := by
            unfold literalOverlap; rfl
  · rw [List.length_take, hu]; omega
  · rw [List.length_drop, hu]

/-! ### Exact resizing -/

/-- Truncate-or-zero-pad `w` to the exact length `n`. -/
def resizeToLength (w : BitString) (n : Nat) : BitString :=
  w.take n ++ List.replicate (n - w.length) false

/-- Resizing to `n` produces a string of length exactly `n`. -/
@[simp] theorem resizeToLength_length (w : BitString) (n : Nat) :
    (resizeToLength w n).length = n := by
  unfold resizeToLength
  rw [List.length_append, List.length_take, List.length_replicate]
  omega

/-- Resizing to the current length is the identity. -/
theorem resizeToLength_self (w : BitString) :
    resizeToLength w w.length = w := by
  simp [resizeToLength]

/-- Resizing is reversible from the resized word, the original length, and
the suffix discarded by truncation.  In the padding case the suffix is empty
and taking the original length removes the padding. -/
theorem resizeToLength_take_original_append_drop
    (w : BitString) (n : Nat) :
    (resizeToLength w n).take w.length ++ w.drop n = w := by
  by_cases hn : n ≤ w.length
  · unfold resizeToLength
    rw [Nat.sub_eq_zero_of_le hn]
    simp only [List.replicate_zero, List.append_nil, List.take_take]
    rw [Nat.min_eq_right hn, List.take_append_drop]
  · have hwn : w.length ≤ n := Nat.le_of_not_ge hn
    unfold resizeToLength
    rw [(List.take_eq_self_iff w).mpr hwn, List.drop_eq_nil_of_le hwn]
    simp

/-! ### Pure `Nat` overlap/gap arithmetic -/

/-- The core overlap/gap component identities for any two block lengths bounded
by the outer length.  With `shared := lx + ly - kxy`, `gap := kxy - (lx + ly)`,
`left := lx - shared`, and `right := ly - shared`, exactly one of `shared`/`gap`
is nonzero and the four components tile the outer length `kxy`. -/
theorem overlap_gap_lengths {lx ly kxy : Nat} (hlx : lx ≤ kxy) (hly : ly ≤ kxy) :
    (lx - (lx + ly - kxy)) + (lx + ly - kxy) = lx ∧
    (lx + ly - kxy) + (ly - (lx + ly - kxy)) = ly ∧
    (lx - (lx + ly - kxy)) + (lx + ly - kxy)
      + (kxy - (lx + ly)) + (ly - (lx + ly - kxy)) = kxy :=
  ⟨by omega, by omega, by omega⟩

/-- The normalized form used by Exercise 307: with the visible target lengths
`lx = min kx kxy`, `ly = min ky kxy`, the left/shared/gap/right components tile
`kxy`, and the left-plus-shared and shared-plus-right blocks recover `lx`, `ly`
respectively. -/
theorem normalized_overlap_gap_lengths (kx ky kxy : Nat) :
    let lx := min kx kxy
    let ly := min ky kxy
    let shared := lx + ly - kxy
    let gap := kxy - (lx + ly)
    let left := lx - shared
    let right := ly - shared
    left + shared + gap + right = kxy ∧
    left + shared = lx ∧
    shared + right = ly := by
  intro lx ly shared gap left right
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [left, right, shared, gap, lx, ly]; omega

/-- Raw block lengths determine the three normalized component lengths up to
three times the input error.  This is the quantitative arithmetic needed before
resizing the private-left, shared, and private-right programs in Exercise 307.
The use of `min` makes the statement valid even when a machine-dependent
constant puts `kx` or `ky` slightly above `kxy`. -/
theorem normalizedSharedComponentLengths_close
    {na np nb kx ky kxy d : Nat}
    (hx : NatCloseWithin (na + np) kx d)
    (hy : NatCloseWithin (np + nb) ky d)
    (hxy : NatCloseWithin (na + np + nb) kxy d) :
    let lx := min kx kxy
    let ly := min ky kxy
    let shared := lx + ly - kxy
    let left := lx - shared
    let right := ly - shared
    NatCloseWithin na left (3 * d) ∧
      NatCloseWithin np shared (3 * d) ∧
      NatCloseWithin nb right (3 * d) := by
  dsimp
  unfold NatCloseWithin at *
  omega

/-- The visible prefix and suffix target lengths used by normalization stay
within `2*d` of the requested complexity values.  The same hypotheses also
bound the visible parameters of the two resized decoders by one fixed linear
expression in `kxy` and `d`, allowing their logarithmic costs to be folded back
to `logSlack _ (kxy + 1)`. -/
theorem normalizedSharedTargetLengths_close
    {na np nb kx ky kxy d : Nat}
    (hx : NatCloseWithin (na + np) kx d)
    (hy : NatCloseWithin (np + nb) ky d)
    (hxy : NatCloseWithin (na + np + nb) kxy d) :
    let lx := min kx kxy
    let ly := min ky kxy
    NatCloseWithin lx kx (2 * d) ∧
      NatCloseWithin ly ky (2 * d) ∧
      na + np + lx + 1 ≤ 3 * (kxy + d + 1) ∧
      np + nb + ly + 1 ≤ 3 * (kxy + d + 1) := by
  dsimp
  unfold NatCloseWithin at *
  omega

/-- Nat-only length cancellation for a shared description.  Given two-sided
closeness of the block sums `C(x|z)+C(z)` to `C(x)` and `C(z)+C(y|z)` to `C(y)`
(error `e`), of `C(z)` to the mutual information `m` (error `d`), and of
`C(x,y)+m` to `C(x)+C(y)` (error `d`), the total raw length `C(x|z)+C(z)+C(y|z)`
is within `2e + 2d` of `C(x,y)`. -/
theorem sharedDescriptionLengths_close
    {kx ky kxy kz kxz kyz m d e : Nat}
    (hx : NatCloseWithin (kxz + kz) kx e)
    (hy : NatCloseWithin (kz + kyz) ky e)
    (hz : NatCloseWithin kz m d)
    (hI : NatCloseWithin (kxy + m) (kx + ky) d) :
    NatCloseWithin (kxz + kz + kyz) kxy (2 * e + 2 * d) := by
  unfold NatCloseWithin at *
  omega

/-- Exact normalized string geometry: a shared description built from
exactly sized left, shared, and right components recovers the original length
and has the expected prefix and suffix. -/
theorem normalizedSharedDescription_shape
    (a p b : BitString) (kx ky kxy : Nat) :
    let lx := min kx kxy
    let ly := min ky kxy
    let shared := lx + ly - kxy
    let gap := kxy - (lx + ly)
    let left := lx - shared
    let right := ly - shared
    let u := resizeToLength a left ++ resizeToLength p shared ++
      List.replicate gap false ++ resizeToLength b right
    u.length = kxy ∧
    u.take lx = resizeToLength a left ++ resizeToLength p shared ∧
    u.drop (u.length - ly) =
      resizeToLength p shared ++ resizeToLength b right := by
  intro lx ly shared gap left right u
  have ⟨h_sum, h_lx, h_ly⟩ := normalized_overlap_gap_lengths kx ky kxy
  have h_left_shared : left + shared = lx := by exact h_lx
  have h_shared_right : shared + right = ly := by exact h_ly
  have h_sum' : left + shared + gap + right = kxy := by exact h_sum
  refine ⟨?_, ?_, ?_⟩
  · dsimp [u]
    simp [left, shared, gap, right, lx, ly]
    omega
  · dsimp [u]
    have h1 : (resizeToLength a left ++ resizeToLength p shared).length = lx := by
      rw [List.length_append, resizeToLength_length, resizeToLength_length, h_left_shared]
    have H :
        resizeToLength a left ++ resizeToLength p shared ++
            List.replicate gap false ++ resizeToLength b right =
          (resizeToLength a left ++ resizeToLength p shared) ++
            (List.replicate gap false ++ resizeToLength b right) := by
      rw [List.append_assoc]
    rw [H, ← h1, List.take_left]
  · dsimp [u]
    have hu_len : u.length = kxy := by
      dsimp [u]
      simp [left, shared, gap, right, lx, ly]
      omega
    rw [hu_len]
    by_cases hov : kxy ≤ lx + ly
    · have hgap : gap = 0 := by
        dsimp [gap]
        omega
      have hleft : left = kxy - ly := by
        dsimp [left, shared]
        omega
      have h1 : (resizeToLength a left).length = kxy - ly := by
        rw [resizeToLength_length, hleft]
      have H_u :
          resizeToLength a left ++ resizeToLength p shared ++
              List.replicate gap false ++ resizeToLength b right =
            resizeToLength a left ++
              (resizeToLength p shared ++ resizeToLength b right) := by
        rw [hgap]
        simp
      rw [H_u, ← h1, List.drop_left]
    · have hshared : shared = 0 := by
        dsimp [shared]
        omega
      have hp : resizeToLength p shared = [] := by
        rw [hshared, resizeToLength]
        simp
      have H_u :
          resizeToLength a left ++ resizeToLength p shared ++
              List.replicate gap false ++ resizeToLength b right =
            (resizeToLength a left ++ List.replicate gap false) ++
              resizeToLength b right := by
        rw [hp]
        simp
      have h2 :
          (resizeToLength a left ++ List.replicate gap false).length =
            kxy - ly := by
        rw [List.length_append, resizeToLength_length, List.length_replicate]
        dsimp [left, gap, shared] at *
        omega
      rw [H_u, ← h2, hp, List.drop_left]
      simp

end Kolmogorov
