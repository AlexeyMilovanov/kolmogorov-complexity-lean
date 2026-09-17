import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.GreedyCover
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Logic.Equiv.Fintype
import KolmogorovMathlib.Restricted.Examples.HammingBalls.Part01

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

/-!
### Sphere-wise Hamming cover

This is Proposition 26's actual proof architecture.  For `r > n / 2`, cover
the whole cube using `hamming_probabilistic_cover`.  Otherwise decompose
`hammingBall n z r` into the spheres of radii `a <= r`.  A sphere with
`a <= r_c` is covered by the single ball centered at `z`.  For
`r_c < a <= n / 2`, choose a distance `f` such that a polynomial fraction of
the radius-`r_c` sphere around a center at distance `f` from `z` lies in the
target radius-`a` sphere.  The choice of `f` is the random-order/prefix-flip
argument from the paper: for every set of `r_c` flipped coordinates, the path
obtained by toggling coordinates one at a time goes from weight `r_c` to
`n - r_c` and therefore hits weight `a`; pigeonhole over the `n + 1` times.

The sphere incidence graph is regular under coordinate permutations.  Apply
`greedy_cover_indexed` on the selected center sphere and then concatenate the
at most `n + 1` shell covers.  Ball/sphere cardinality differs by at most an
`n + 1` factor, so the public `(n + 1)^7` budget has ample slack.

In particular, centers are not required to belong to the original ball.
-/

/-- Flips the bits of `x` at the indices in `S`. -/
def flipPositions (n : ℕ) (x : BitString) (S : Finset ℕ) : BitString :=
  List.ofFn (fun (i : Fin n) => if i.val ∈ S then !x[i.val]! else x[i.val]!)

/-- Flipping a set of positions preserves the length `n`. -/
theorem flipPositions_length (n : ℕ) (x : BitString) (S : Finset ℕ) :
    (flipPositions n x S).length = n := by
  simp [flipPositions]

/-- Flipping the positions in `S`, all below `n`, moves a string to Hamming distance `#S`. -/
theorem hammingDist_flipPositions (n : ℕ) (x : BitString) (S : Finset ℕ) (hx : x.length = n)
    (hS : ∀ i ∈ S, i < n) :
    hammingDist x (flipPositions n x S) = S.card := by
  rw [hammingDist_eq_filter_card n x (flipPositions n x S) hx (flipPositions_length n x S)]
  congr 1
  ext i
  by_cases hi : i < n
  · by_cases hmem : i ∈ S
    · simp [flipPositions, hi, hmem]
    · simp [flipPositions, hi, hmem]
  · have hnotmem : i ∉ S := fun h => hi (hS i h)
    simp [hi, hnotmem]

/-- Flipping a fixed set of positions is injective on strings of length `n`. -/
theorem flipPositions_inj (n : ℕ) (S : Finset ℕ) :
    ∀ x y : BitString,
        x.length = n → y.length = n → flipPositions n x S = flipPositions n y S → x = y := by
  intro x y hx hy hflip
  apply List.ext_get (by rw [hx, hy])
  intro i hi_x hi_y
  have hi_n : i < n := by simpa [hx] using hi_x
  have hget := congrArg (fun l : BitString => l[i]!) hflip
  simp only [flipPositions, List.getElem!_eq_getElem?_getD, Bool.default_bool, List.length_ofFn,
      hi_n, getElem!_pos, List.getElem_ofFn, List.getElem?_eq_getElem hi_x, Option.getD_some,
      List.getElem?_eq_getElem hi_y] at hget
  by_cases hmem : i ∈ S
  · simp [hmem] at hget
    cases x[i] <;> cases y[i] <;> simp_all
  · simp only [hmem, ↓reduceIte] at hget
    exact hget

/-- Flipping the first `t` positions of `x` one at a time passes through distance exactly `a`
from `z`, for every `a` between `hammingDist z x` and `n / 2`. -/
lemma prefix_flip_path_hits (n : ℕ) (z x : BitString) (r_c a : ℕ)
    (hz : z.length = n) (hx : x.length = n)
    (hr : hammingDist z x = r_c) (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ t ≤ n, hammingDist z (flipPositions n x (Finset.range t)) = a := by
  classical
  let d : ℕ → ℕ := fun t => hammingDist z (flipPositions n x (Finset.range t))
  have hflip_zero : flipPositions n x (Finset.range 0) = x := by
    refine List.ext_get ?_ ?_
    · simp [flipPositions, hx]
    · intro i hi_flip hi_x
      have hi_n : i < n := by simpa [flipPositions] using hi_flip
      simp [flipPositions, List.getElem?_eq_getElem hi_x]
  have hd0 : d 0 = r_c := by
    change hammingDist z (flipPositions n x (Finset.range 0)) = r_c
    rw [hflip_zero, hr]
  have hflip_all : flipPositions n x (Finset.range n) = x.map (fun b => !b) := by
    refine List.ext_get ?_ ?_
    · simp [flipPositions, hx]
    · intro i hi_flip hi_map
      have hi_n : i < n := by simpa [flipPositions] using hi_flip
      have hi_x : i < x.length := by simpa using hi_map
      simp [flipPositions, List.getElem?_eq_getElem hi_x]
  have hdn : d n = n - r_c := by
    simp only [d, hflip_all]
    rw [hammingDist_comm z (x.map fun b => !b)]
    rw [hammingDist_map_not x z (by rw [hx, hz])]
    rw [hx, hammingDist_comm x z, hr]
  have ha_le_dn : a ≤ d n := by
    rw [hdn]
    have h2a : 2 * a ≤ n := by
      nlinarith [Nat.mul_le_mul_left 2 ha2, Nat.div_mul_le_self n 2]
    omega
  have hstep : ∀ t : ℕ, d (t + 1) ≤ d t + 1 := by
    intro t
    have hsucc :
        hammingDist (flipPositions n x (Finset.range t))
            (flipPositions n x (Finset.range (t + 1))) ≤ 1 := by
      rw [hammingDist_eq_filter_card n (flipPositions n x (Finset.range t))
        (flipPositions n x (Finset.range (t + 1)))
        (flipPositions_length n x (Finset.range t))
        (flipPositions_length n x (Finset.range (t + 1)))]
      have hsub :
          (Finset.filter (fun i =>
            (flipPositions n x (Finset.range t))[i]! ≠
              (flipPositions n x (Finset.range (t + 1)))[i]!) (Finset.range n)) ⊆
            ({t} : Finset ℕ) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        by_contra hit
        rw [Finset.mem_singleton] at hit
        have hin : i < n := Finset.mem_range.mp hi.1
        have hsame :
            (if i ∈ Finset.range t then !x[i]! else x[i]!) =
              (if i ∈ Finset.range (t + 1) then !x[i]! else x[i]!) := by
          by_cases hit' : i < t
          · have hi_t : i ∈ Finset.range t := Finset.mem_range.mpr hit'
            have hi_succ : i ∈ Finset.range (t + 1) :=
              Finset.mem_range.mpr (Nat.lt_trans hit' (Nat.lt_succ_self t))
            simp [hi_t, hi_succ]
          · have hi_t : i ∉ Finset.range t := by
              rw [Finset.mem_range]
              exact hit'
            have hi_succ : i ∉ Finset.range (t + 1) := by
              rw [Finset.mem_range]
              omega
            simp [hi_t, hi_succ]
        have hvals :
            (flipPositions n x (Finset.range t))[i]! =
              (flipPositions n x (Finset.range (t + 1)))[i]! := by
          simpa [flipPositions, hin] using hsame
        exact hi.2 hvals
      calc
        (Finset.filter (fun i =>
            (flipPositions n x (Finset.range t))[i]! ≠
              (flipPositions n x (Finset.range (t + 1)))[i]!) (Finset.range n)).card
            ≤ ({t} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 1 := by simp
    have htri := hammingDist_triangle_of_eq_length z
      (flipPositions n x (Finset.range t))
      (flipPositions n x (Finset.range (t + 1)))
      (by rw [hz, flipPositions_length])
      (by rw [flipPositions_length, flipPositions_length])
    dsimp [d]
    omega
  let P : ℕ → Prop := fun t => t ≤ n ∧ a ≤ d t
  have hex : ∃ t, P t := ⟨n, le_rfl, ha_le_dn⟩
  let t0 := Nat.find hex
  have ht0_spec : P t0 := Nat.find_spec hex
  have ht0_ne_zero : t0 ≠ 0 := by
    intro ht0_zero
    have : a ≤ r_c := by
      have h := ht0_spec.2
      rwa [ht0_zero, hd0] at h
    omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero ht0_ne_zero
  have ht0_eq : Nat.find hex = s + 1 := by
    simpa [t0] using hs
  have ht0_eq' : t0 = s + 1 := by
    simpa [t0] using ht0_eq
  have hnot_prev : ¬ P s := Nat.find_min hex (by
    rw [ht0_eq]
    exact Nat.lt_succ_self s)
  have ht0_le_n : s + 1 ≤ n := by
    simpa [ht0_eq'] using ht0_spec.1
  have ha_le_succ : a ≤ d (s + 1) := by
    simpa [ht0_eq'] using ht0_spec.2
  have hs_le_n : s ≤ n := by omega
  have hds_lt : d s < a := by
    have hnot : ¬ a ≤ d s := fun h => hnot_prev ⟨hs_le_n, h⟩
    omega
  have hdsucc_le : d (s + 1) ≤ a := by
    have := hstep s
    omega
  exact ⟨s + 1, ht0_le_n, le_antisymm hdsucc_le ha_le_succ⟩

/-- Flipping the same positions in both arguments preserves the Hamming distance. -/
lemma flipPositions_comm_dist (n : ℕ) (z x : BitString) (S : Finset ℕ)
    (hz : z.length = n) (hx : x.length = n) :
    hammingDist (flipPositions n z S) (flipPositions n x S) = hammingDist z x := by
  rw [hammingDist_eq_filter_card n (flipPositions n z S) (flipPositions n x S)
      (flipPositions_length n z S) (flipPositions_length n x S),
    hammingDist_eq_filter_card n z x hz hx]
  congr 1
  ext i
  by_cases hi : i < n
  · by_cases hmem : i ∈ S <;> simp [flipPositions, hi, hmem]
  · simp [hi]

/-- Some centre on a sphere around `z` covers, within radius `r_c`, at least a `1 / (n + 1)`
fraction of the sphere of radius `r_c` worth of points of the sphere of radius `a`. -/
theorem exists_dense_hamming_center_shell (n : ℕ) (z : BitString) (r_c a : ℕ)
    (hz : z.length = n) (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ f ≤ n, ∃ (c : BitString), c ∈ hammingSphere n z f ∧
      (hammingSphere n z r_c).card ≤
        (n + 1) * ((hammingSphere n c r_c).filter (fun y => y ∈ hammingSphere n z a)).card := by
  classical
  let R := hammingSphere n z r_c
  let center : ℕ → BitString := fun t => flipPositions n z (Finset.range t)
  let Y : ℕ → Finset BitString :=
    fun t => (hammingSphere n (center t) r_c).filter (fun y => y ∈ hammingSphere n z a)
  have hx_len : ∀ p : {x // x ∈ R}, (p : BitString).length = n := by
    intro p
    exact (mem_stringsOfLength n p.1).mp (Finset.mem_filter.mp p.2).1
  have hx_dist : ∀ p : {x // x ∈ R}, hammingDist z (p : BitString) = r_c := by
    intro p
    exact (Finset.mem_filter.mp p.2).2
  have hhit : ∀ p : {x // x ∈ R},
      ∃ t ≤ n, hammingDist z (flipPositions n (p : BitString) (Finset.range t)) = a := by
    intro p
    exact prefix_flip_path_hits n z p.1 r_c a hz (hx_len p) (hx_dist p) ha1 ha2
  let τ : {x // x ∈ R} → ℕ := fun p => Classical.choose (hhit p)
  have hτ_le : ∀ p : {x // x ∈ R}, τ p ≤ n := by
    intro p
    exact (Classical.choose_spec (hhit p)).1
  have hτ_hit : ∀ p : {x // x ∈ R},
      hammingDist z (flipPositions n (p : BitString) (Finset.range (τ p))) = a := by
    intro p
    exact (Classical.choose_spec (hhit p)).2
  let imagePoint : {x // x ∈ R} → BitString :=
    fun p => flipPositions n (p : BitString) (Finset.range (τ p))
  let embed : {x // x ∈ R} → Sigma (fun _ : ℕ => BitString) :=
    fun p => ⟨τ p, imagePoint p⟩
  have hmaps : Set.MapsTo embed (↑R.attach) (↑((Finset.range (n + 1)).sigma Y)) := by
    intro p _hp
    rw [Finset.mem_coe, Finset.mem_sigma]
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hτ_le p)), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hammingSphere, Finset.mem_filter]
      refine ⟨(mem_stringsOfLength n (imagePoint p)).mpr (flipPositions_length n p.1
          (Finset.range (τ p))), ?_⟩
      have hcomm := flipPositions_comm_dist n z p.1 (Finset.range (τ p)) hz (hx_len p)
      simpa [center, imagePoint, hx_dist p] using hcomm
    · rw [hammingSphere, Finset.mem_filter]
      exact ⟨(mem_stringsOfLength n (imagePoint p)).mpr (flipPositions_length n p.1
          (Finset.range (τ p))),
        hτ_hit p⟩
  have hinj : Set.InjOn embed (↑R.attach) := by
    intro p _hp q _hq heq
    have hpair := Sigma.mk.inj_iff.mp heq
    have ht : τ p = τ q := hpair.1
    have hy : imagePoint p = imagePoint q := eq_of_heq hpair.2
    have hflip :
        flipPositions n p.1 (Finset.range (τ p)) =
          flipPositions n q.1 (Finset.range (τ p)) := by
      simpa [imagePoint, ht] using hy
    exact Subtype.ext (flipPositions_inj n (Finset.range (τ p)) p.1 q.1
      (hx_len p) (hx_len q) hflip)
  have hR_le_sum : R.card ≤ ∑ t ∈ Finset.range (n + 1), (Y t).card := by
    calc
      R.card = R.attach.card := Finset.card_attach.symm
      _ ≤ ((Finset.range (n + 1)).sigma Y).card :=
          Finset.card_le_card_of_injOn embed hmaps hinj
      _ = ∑ t ∈ Finset.range (n + 1), (Y t).card := Finset.card_sigma _ _
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨t0, ht0_mem, ht0_max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) (fun t => (Y t).card) hne
  have hsum_le : (∑ t ∈ Finset.range (n + 1), (Y t).card) ≤
      (n + 1) * (Y t0).card := by
    calc
      (∑ t ∈ Finset.range (n + 1), (Y t).card)
          ≤ (Finset.range (n + 1)).card * (Y t0).card :=
            Finset.sum_le_card_nsmul _ _ _ (fun t ht => ht0_max t ht)
      _ = (n + 1) * (Y t0).card := by rw [Finset.card_range]
  refine ⟨t0, Nat.le_of_lt_succ (Finset.mem_range.mp ht0_mem), center t0, ?_, ?_⟩
  · rw [hammingSphere, Finset.mem_filter]
    refine ⟨(mem_stringsOfLength n (center t0)).mpr
      (flipPositions_length n z (Finset.range t0)), ?_⟩
    have hsupport : ∀ i ∈ Finset.range t0, i < n := by
      intro i hi
      have hit : i < t0 := Finset.mem_range.mp hi
      have ht0n : t0 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ht0_mem)
      omega
    rw [hammingDist_flipPositions n z (Finset.range t0) hz hsupport, Finset.card_range]
  · exact le_trans hR_le_sum hsum_le

/-- Encode a string by the coordinates on which it differs from a fixed base string. -/
def differenceMask (n : ℕ) (z y : BitString) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z[i.val]! ≠ y[i.val]!)

/-- Reconstruct the string with the prescribed difference mask from a base string. -/
def stringOfDifferenceMask (n : ℕ) (z : BitString) (S : Finset (Fin n)) : BitString :=
  List.ofFn (fun i => if i ∈ S then !z[i.val]! else z[i.val]!)

/-- The difference mask of the string built from a mask is that mask. -/
lemma differenceMask_stringOfDifferenceMask (n : ℕ) (z : BitString)
    (S : Finset (Fin n)) :
    differenceMask n z (stringOfDifferenceMask n z S) = S := by
      ext i; simp [differenceMask, stringOfDifferenceMask]

/-- Rebuilding a string of length `n` from its difference mask relative to `z` returns it. -/
lemma stringOfDifferenceMask_differenceMask (n : ℕ) (z y : BitString)
    (hz : z.length = n) (hy : y.length = n) :
    stringOfDifferenceMask n z (differenceMask n z y) = y := by
      refine List.ext_get ?_ ?_ <;> simp_all [ stringOfDifferenceMask, differenceMask ];
      grind

/-- The Hamming distance of two strings given by masks is the size of the symmetric difference of
the masks. -/
lemma hammingDist_stringOfDifferenceMask (n : ℕ) (z : BitString)
    (S T : Finset (Fin n)) :
    hammingDist (stringOfDifferenceMask n z S) (stringOfDifferenceMask n z T) =
      (S \ T).card + (T \ S).card := by
        -- By definition of `stringOfDifferenceMask`, the difference mask of `stringOfDifferenceMask
        -- n z S` and `stringOfDifferenceMask n z T` is `S \ T ∪ T \ S`.
        have h_diff_mask : differenceMask n (stringOfDifferenceMask n z S)
            (stringOfDifferenceMask n z T) = S \ T ∪ T \ S := by
          ext i; simp [differenceMask, stringOfDifferenceMask];
          grind;
        convert congr_arg Finset.card h_diff_mask using 1;
        · convert hammingDist_eq_filter_card n _ _ _ _ using 2;
          · refine Finset.card_bij ( fun i hi =>
              i ) ?_ ?_ ?_ <;> try simp only [List.getElem!_eq_getElem?_getD,
                Bool.default_bool, ne_eq,
                  Finset.mem_filter, Finset.mem_range, exists_prop, and_imp];
            · unfold differenceMask; aesop;
            · exact fun a₁ ha₁ a₂ ha₂ h => Fin.ext h;
            · intro b hb h; use ⟨ b, hb ⟩ ; simp [ *, differenceMask ] ;
          · unfold stringOfDifferenceMask; aesop;
          · unfold stringOfDifferenceMask; aesop;
        · rw [ Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hxS hxT =>
            by aesop ) ]

/-- A permutation of the ground set preserves the size of a symmetric difference. -/
lemma finset_symmetricDifference_card_map_perm {α : Type} [DecidableEq α]
    (σ : Equiv.Perm α) (S T : Finset α) :
    ((Finset.map σ.toEmbedding S) \ (Finset.map σ.toEmbedding T)).card +
        ((Finset.map σ.toEmbedding T) \ (Finset.map σ.toEmbedding S)).card =
      (S \ T).card + (T \ S).card := by
        rw [ show ( Finset.map ( Equiv.toEmbedding σ ) S \ Finset.map ( Equiv.toEmbedding σ )
            T ) = Finset.map ( Equiv.toEmbedding σ ) ( S \ T ) from ?_,
          show ( Finset.map ( Equiv.toEmbedding σ ) T \ Finset.map ( Equiv.toEmbedding σ ) S ) =
            Finset.map ( Equiv.toEmbedding σ ) ( T \ S ) from ?_ ];
        · rw [ Finset.card_map, Finset.card_map ];
        · ext; simp [Finset.mem_sdiff];
        · ext; simp [Finset.mem_sdiff]

/-- The difference mask of `y` relative to `z` has `hammingDist z y` elements. -/
lemma differenceMask_card_eq_hammingDist (n : ℕ) (z y : BitString)
    (hz : z.length = n) (hy : y.length = n) :
    (differenceMask n z y).card = hammingDist z y := by
      rw [hammingDist_eq_filter_card n z y hz hy]
      unfold differenceMask
      rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]

/-- The number of `a`-element masks at symmetric-difference distance `r_c` from a given mask
depends only on the size of that mask. -/
lemma mask_incidence_regular (n r_c f a : ℕ) :
    ∀ D1 : Finset (Fin n), D1.card = f →
    ∀ D2 : Finset (Fin n), D2.card = f →
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ (D1 \ Y).card + (Y \ D1).card = r_c)).card =
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ (D2 \ Y).card + (Y \ D2).card = r_c)).card := by
          intros D1 hD1 D2 hD2
          obtain ⟨σ, hσ⟩ : ∃ σ : Fin n ≃ Fin n, Finset.map σ.toEmbedding D1 = D2 := by
            obtain ⟨σ, hσ⟩ : ∃ σ : {x // x ∈ D1} ≃ {x // x ∈ D2}, True := by
              exact ⟨ Fintype.equivOfCardEq <| by aesop, trivial ⟩;
            refine ⟨ Equiv.extendSubtype σ, ?_ ⟩;
            ext x; simp [Equiv.extendSubtype];
            by_cases hx : x ∈ D2 <;> simp [ hx, Equiv.subtypeCongr ];
            grind +qlia;
          rw [ Finset.card_filter, Finset.card_filter ];
          apply Finset.sum_bij (fun Y _ => Finset.map σ.toEmbedding Y);
          · simp;
          · exact fun a₁ _ a₂ _ h => Finset.map_injective σ.toEmbedding h;
          · exact fun b _ => ⟨ Finset.map σ.symm.toEmbedding b, Finset.mem_univ _, by aesop ⟩;
          · simp [ ← hσ, finset_symmetricDifference_card_map_perm ]

/-- The number of points of the sphere of radius `a` around `z` within distance `r_c` of `c` is a
count of masks at prescribed symmetric-difference distance. -/
lemma filtered_hammingSphere_card_eq_mask_count
    (n r_c a : ℕ) (z c : BitString) (hz : z.length = n) (hc : c.length = n) :
    ((hammingSphere n c r_c).filter (fun y => y ∈ hammingSphere n z a)).card =
      (Finset.univ.filter (fun Y : Finset (Fin n) =>
        Y.card = a ∧ ((differenceMask n z c) \ Y).card +
          (Y \ (differenceMask n z c)).card = r_c)).card := by
            refine Finset.card_bij ( fun y hy => differenceMask n z y ) ?_ ?_ ?_;
            · simp only [hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and, and_imp];
              intro y hy₁ hy₂ hy₃ hy₄;
              rw [ ← hy₂, ← hy₄, ← hammingDist_stringOfDifferenceMask ];
              exact ⟨ differenceMask_card_eq_hammingDist n z y hz
                  ( by simpa [ stringsOfLength ] using mem_stringsOfLength n y |>.1 hy₃ ),
                by rw [ stringOfDifferenceMask_differenceMask n z c hz hc,
                  stringOfDifferenceMask_differenceMask n z y hz
                    ( by simpa [ stringsOfLength ] using mem_stringsOfLength n y |>.1 hy₃ ) ] ⟩;
            · intro y₁ hy₁ y₂ hy₂ h; have :=
                stringOfDifferenceMask_differenceMask n z y₁
              have := stringOfDifferenceMask_differenceMask n z y₂
              simp_all [ Finset.ext_iff ] ;
              simp_all [differenceMask];
              simp_all [ hammingSphere ];
              simp_all [ mem_stringsOfLength ];
            · intro Y hy; use stringOfDifferenceMask n z Y; simp_all only [Finset.mem_filter,
                Finset.mem_univ, true_and, hammingSphere, exists_prop];
              have h_dist : hammingDist c (stringOfDifferenceMask n z Y) = (differenceMask n z
                  c \ Y).card + (Y \ differenceMask n z c).card := by
                convert hammingDist_stringOfDifferenceMask n z ( differenceMask n z c ) Y using 1;
                rw [ stringOfDifferenceMask_differenceMask n z c hz hc ];
              have h_dist_z : hammingDist z (stringOfDifferenceMask n z Y) = Y.card := by
                convert hammingDist_stringOfDifferenceMask n z ∅ Y using 1;
                · unfold stringOfDifferenceMask; aesop;
                · simp;
              simp_all only [stringsOfLength, List.mem_toFinset, mem_allStrings, and_true,
                and_self];
              exact ⟨ by rw [ stringOfDifferenceMask ] ; simp [ hz ],
                  differenceMask_stringOfDifferenceMask n z Y ⟩

/-- Two centres on the same sphere around `z` cover equally many points of the sphere of
radius `a`. -/
theorem hammingSphere_incidence_regular (n r_c f a : ℕ) (z : BitString) (hz : z.length = n) :
    ∀ c1 ∈ hammingSphere n z f, ∀ c2 ∈ hammingSphere n z f,
      ((hammingSphere n c1 r_c).filter (fun y => y ∈ hammingSphere n z a)).card =
      ((hammingSphere n c2 r_c).filter (fun y => y ∈ hammingSphere n z a)).card := by
        intros c1 hc1 c2 hc2;
        rw [filtered_hammingSphere_card_eq_mask_count n r_c a z c1,
          filtered_hammingSphere_card_eq_mask_count n r_c a z c2]
        · convert mask_incidence_regular n r_c f a ( differenceMask n z c1 ) ( by
          rw [differenceMask_card_eq_hammingDist];
          · exact Finset.mem_filter.mp hc1 |>.2;
          · exact hz;
          · exact Finset.mem_filter.mp hc1 |>.1 |> fun h =>
              by simpa [ hz ] using mem_stringsOfLength n c1 |>.1 h; )
                ( differenceMask n z c2 ) ( by
          convert differenceMask_card_eq_hammingDist n z c2 hz _ |> Eq.trans
              <| Finset.mem_filter.mp hc2 |>.2;
          exact Finset.mem_filter.mp hc2 |>.1 |> fun h =>
              by simpa using mem_stringsOfLength n c2 |>.1 h; ) using 1
        · grind +splitImp
        · exact Finset.mem_filter.mp hc2 |>.1 |> fun h =>
            by simpa using mem_stringsOfLength n c2 |>.1 h;
        · exact hz;
        · exact Finset.mem_filter.mp hc1 |>.1 |> fun h =>
            by simpa [hz] using mem_stringsOfLength n c1 |>.1 h

/-- A sphere of radius `a ≤ n / 2` around `z` is covered by balls of radius `r_c` whose number
times the sphere volume of radius `r_c` is at most `(n + 1) ^ 2` times the sphere volume. -/
theorem hammingSphere_cover_centers (n : ℕ) (z : BitString) (r_c a : ℕ) (hz : z.length = n)
    (ha1 : r_c < a) (ha2 : a ≤ n / 2) :
    ∃ 𝒞_centers : Finset BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingSphere n z a, ∃ x ∈ 𝒞_centers, hammingDist x y ≤ r_c) ∧
      𝒞_centers.card * (hammingSphere n z r_c).card ≤ (n + 1) * (n + 1) * (hammingSphere n z
          a).card := by
  classical
  obtain ⟨f, _hfn, c0, hc0S, hdense0⟩ :=
    exists_dense_hamming_center_shell n z r_c a hz ha1 ha2
  let S := hammingSphere n z f
  let T := hammingSphere n z a
  let R := hammingSphere n z r_c
  let cover : BitString → Finset BitString :=
    fun x => T.filter (fun y => hammingDist x y = r_c)
  let m := (cover c0).card
  have hc0_len : c0.length = n :=
    (mem_stringsOfLength n c0).mp (Finset.mem_filter.mp hc0S).1
  have hcover_eq : ∀ x, cover x = (hammingSphere n x r_c).filter (fun y => y ∈ T) := by
    intro x
    ext y
    simp [cover, T, hammingSphere]
    tauto
  have hdense_m : R.card ≤ (n + 1) * m := by
    simpa [R, m, hcover_eq c0] using hdense0
  have hRpos : 0 < R.card := by
    have hrcn : r_c ≤ n := by omega
    dsimp [R]
    rw [hammingSphere_card n z r_c hz]
    exact Nat.choose_pos hrcn
  have hm_pos : 0 < m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    have : R.card ≤ 0 := by simpa [hm0] using hdense_m
    omega
  have hTpos : 0 < T.card := by
    have han : a ≤ n := by omega
    dsimp [T]
    rw [hammingSphere_card n z a hz]
    exact Nat.choose_pos han
  obtain ⟨y0, hy0T⟩ := Finset.card_pos.mp hTpos
  let q := ((hammingSphere n y0 r_c).filter (fun x => x ∈ S)).card
  have hrow : ∀ x ∈ S, (cover x).card = m := by
    intro x hxS
    have hreg := hammingSphere_incidence_regular n r_c f a z hz x hxS c0 hc0S
    change (cover x).card = (cover c0).card
    rw [hcover_eq x, hcover_eq c0]
    exact hreg
  have hcol : ∀ y ∈ T, ((hammingSphere n y r_c).filter (fun x => x ∈ S)).card = q := by
    intro y hyT
    have hreg := hammingSphere_incidence_regular n r_c a f z hz y hyT y0 hy0T
    simpa [q, S, hammingDist_comm] using hreg
  have hinc_filter : ∀ y ∈ T, (S.filter (fun x => y ∈ cover x)).card = q := by
    intro y hyT
    calc
      (S.filter (fun x => y ∈ cover x)).card
          = ((hammingSphere n y r_c).filter (fun x => x ∈ S)).card := by
              congr 1
              ext x
              constructor
              · intro hx
                rw [Finset.mem_filter] at hx ⊢
                rcases hx with ⟨hxS, hycov⟩
                have hx_len : x.length = n :=
                  (mem_stringsOfLength n x).mp (Finset.mem_filter.mp hxS).1
                refine ⟨?_, hxS⟩
                rw [hammingSphere, Finset.mem_filter]
                exact ⟨(mem_stringsOfLength n x).mpr hx_len,
                  by simpa [cover, hammingDist_comm] using (Finset.mem_filter.mp hycov).2⟩
              · intro hx
                rw [Finset.mem_filter] at hx ⊢
                rcases hx with ⟨hysphere, hxS⟩
                refine ⟨hxS, ?_⟩
                change y ∈ T.filter (fun y => hammingDist x y = r_c)
                rw [Finset.mem_filter]
                exact ⟨hyT, by simpa [hammingDist_comm] using (Finset.mem_filter.mp hysphere).2⟩
      _ = q := hcol y hyT
  have hq_pos : 0 < q := by
    obtain ⟨y1, hy1cover⟩ := Finset.card_pos.mp hm_pos
    have hy1T : y1 ∈ T := (Finset.mem_filter.mp hy1cover).1
    have hc0_y1 : c0 ∈ (hammingSphere n y1 r_c).filter (fun x => x ∈ S) := by
      rw [Finset.mem_filter]
      refine ⟨?_, hc0S⟩
      rw [hammingSphere, Finset.mem_filter]
      have hdist : hammingDist c0 y1 = r_c := (Finset.mem_filter.mp hy1cover).2
      exact ⟨(mem_stringsOfLength n c0).mpr hc0_len,
        by simpa [hammingDist_comm] using hdist⟩
    have hcol_y1 : ((hammingSphere n y1 r_c).filter (fun x => x ∈ S)).card = q :=
      hcol y1 hy1T
    rw [← hcol_y1]
    exact Finset.card_pos.mpr ⟨c0, hc0_y1⟩
  obtain ⟨C, hCS, hCcov, hCbound⟩ :=
    greedy_cover_indexed T S cover q hq_pos (fun y hy => by rw [hinc_filter y hy])
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x hxC
    exact (mem_stringsOfLength n x).mp (Finset.mem_filter.mp (hCS hxC)).1
  · intro y hyT
    have hycov := hCcov hyT
    rw [Finset.mem_biUnion] at hycov
    obtain ⟨x, hxC, hycover⟩ := hycov
    refine ⟨x, hxC, ?_⟩
    exact le_of_eq (Finset.mem_filter.mp hycover).2
  · have hdouble : S.card * m = T.card * q := by
      calc
        S.card * m = ∑ x ∈ S, m := by rw [Finset.sum_const, smul_eq_mul]
        _ = ∑ x ∈ S, (cover x).card := by
              apply Finset.sum_congr rfl
              intro x hxS
              rw [hrow x hxS]
        _ = ∑ x ∈ S, ∑ y ∈ T, (if hammingDist x y = r_c then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro x _hxS
              rw [show cover x = T.filter (fun y => hammingDist x y = r_c) from rfl]
              rw [Finset.card_filter]
        _ = ∑ y ∈ T, ∑ x ∈ S, (if hammingDist x y = r_c then 1 else 0) := by
              rw [Finset.sum_comm]
        _ = ∑ y ∈ T, (S.filter (fun x => y ∈ cover x)).card := by
              apply Finset.sum_congr rfl
              intro y hyT
              rw [Finset.card_filter]
              apply Finset.sum_congr rfl
              intro x _hxS
              by_cases hxy : hammingDist x y = r_c
              · simp [cover, hyT, hxy]
              · simp [cover, hyT, hammingDist_comm]
        _ = ∑ y ∈ T, q := by
              apply Finset.sum_congr rfl
              intro y hyT
              rw [hinc_filter y hyT]
        _ = T.card * q := by rw [Finset.sum_const, smul_eq_mul]
    have hlog : Nat.log2 T.card ≤ n := log2_card_hammingSphere_le n z a hz
    have hCq : C.card * q ≤ S.card * (n + 1) := by
      calc C.card * q ≤ S.card * (Nat.log2 T.card + 1) := hCbound
        _ ≤ S.card * (n + 1) := Nat.mul_le_mul_left _ (by omega)
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨c0, hc0S⟩
    have hCm : C.card * m ≤ T.card * (n + 1) := by
      exact Nat.le_of_mul_le_mul_left (c := S.card) (by
        calc S.card * (C.card * m) = C.card * (S.card * m) := by ring
          _ = C.card * (T.card * q) := by rw [hdouble]
          _ = T.card * (C.card * q) := by ring
          _ ≤ T.card * (S.card * (n + 1)) := Nat.mul_le_mul_left _ hCq
          _ = S.card * (T.card * (n + 1)) := by ring) hSpos
    calc
      C.card * R.card ≤ C.card * ((n + 1) * m) := Nat.mul_le_mul_left _ hdense_m
      _ = (n + 1) * (C.card * m) := by ring
      _ ≤ (n + 1) * (T.card * (n + 1)) := Nat.mul_le_mul_left _ hCm
      _ = (n + 1) * (n + 1) * T.card := by ring

/-- Below the middle the largest sphere carries at least a `1 / (n + 1)` fraction of the ball. -/
lemma hammingVol_le_mul_hammingSphere_card_of_le_half
    (n s : ℕ) (z : BitString) (hz : z.length = n) (hs : s ≤ n / 2) :
    hammingVol n s ≤ (n + 1) * (hammingSphere n z s).card := by
      -- By definition of `hammingVol`, we have `hammingVol n s = ∑ i ∈ Finset.range (s + 1),
      -- Nat.choose n i`.
      have h_hammingVol : hammingVol n s = ∑ i ∈ Finset.range (s + 1), Nat.choose n i := by
        rfl;
      rw [ h_hammingVol, hammingSphere_card n z s hz ];
      refine le_trans ( Finset.sum_le_sum fun i hi =>
          show Nat.choose n i ≤ Nat.choose n s from ?_ ) ?_;
      · have h_choose_mono : ∀ {i j : ℕ}, i ≤ j → j ≤ n / 2 → Nat.choose n i ≤ Nat.choose n j := by
          intros i j hij hjn; induction hij <;> simp_all only [Finset.mem_range,
              Order.lt_add_one_iff, le_refl, Nat.le_eq, Nat.succ_eq_add_one, Order.add_one_le_iff];
          exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] )
              ( Nat.choose_le_succ_of_lt_half_left ( by omega ) );
        exact h_choose_mono ( Finset.mem_range_succ_iff.mp hi ) hs;
      · simp +arith only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm];
        exact Nat.mul_le_mul_left _ ( by omega )

/-- A ball of radius above `n / 2` contains at least a `1 / (n + 1)` fraction of the cube. -/
lemma stringsOfLength_card_le_mul_hammingBall_card_of_half_lt
    (n r : ℕ) (z : BitString) (hz : z.length = n) (hr : n / 2 < r) :
    (stringsOfLength n).card ≤ (n + 1) * (hammingBall n z r).card := by
      have h_cube_card : (stringsOfLength n).card = ∑ i ∈ Finset.range (n + 1), Nat.choose n i := by
        rw [ card_stringsOfLength, Nat.sum_range_choose ];
      rw [ h_cube_card, mul_comm ];
      refine le_trans ?_ ( Nat.mul_le_mul_right (k :=
          n + 1) <| show ( hammingBall n z r |> Finset.card ) ≥ ( n.choose ( n / 2 ) ) from ?_ );
      · exact le_trans ( Finset.sum_le_sum fun _ _ =>
          Nat.choose_le_middle _ _ ) ( by simp [ mul_comm ] );
      · rw [ hammingBall_card ];
        · exact Finset.single_le_sum ( fun x _ =>
            Nat.zero_le ( Nat.choose n x ) ) ( Finset.mem_range.mpr ( by linarith ) );
        · exact hz

/-- A ball of radius `r ≤ n / 2` is covered by balls of radius `r_c` whose number times `c` is at
most `(n + 1) ^ 5` times the volume of the ball. -/
lemma hammingBall_cover_centers_of_le_half
    (n : ℕ) (z : BitString) (r c r_c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (hr : r ≤ n / 2) (hrc : r_c ≤ r)
    (h_r_bound : c ≤ hammingVol n r)
    (h_rc_bound : c ≤ (n + 1) * hammingVol n r_c) :
    ∃ 𝒞_centers : List BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingBall n z r, ∃ x ∈ 𝒞_centers,
        hammingDist x y ≤ r_c) ∧
      𝒞_centers.length * c ≤ (n + 1)^5 * (hammingBall n z r).card := by
  have hc_and_bound : 0 < c ∧ c ≤ hammingVol n r := ⟨hc, h_r_bound⟩
  by_cases h_cases : r_c < r
  · let I := Finset.Icc (r_c + 1) r
    have h_a_rc : ∀ a ∈ I, r_c < a := fun a ha => by
      rw [Finset.mem_Icc] at ha
      exact ha.1
    have h_a_n : ∀ a ∈ I, a ≤ n / 2 := fun a ha => by
      rw [Finset.mem_Icc] at ha
      exact le_trans ha.2 hr
    have hrc_half : r_c ≤ n / 2 := hrc.trans hr
    let f : ℕ → Finset BitString := fun a =>
      if ha : a ∈ I then
        Classical.choose (hammingSphere_cover_centers n z r_c a hz (h_a_rc a ha) (h_a_n a ha))
      else ∅
    have hf_spec : ∀ a ∈ I,
        (∀ x ∈ f a, x.length = n) ∧
        (∀ y ∈ hammingSphere n z a, ∃ x ∈ f a, hammingDist x y ≤ r_c) ∧
        (f a).card * (hammingSphere n z r_c).card ≤ (n + 1)^2 * (hammingSphere n z a).card := by
      intro a ha
      simp only [f, dif_pos ha]
      have :=
          Classical.choose_spec (hammingSphere_cover_centers n z r_c a hz
            (h_a_rc a ha) (h_a_n a ha))
      refine ⟨this.1, this.2.1, ?_⟩
      calc
        _ ≤ (n + 1) * (n + 1) * (hammingSphere n z a).card := this.2.2
        _ = (n + 1)^2 * (hammingSphere n z a).card := by ring
    have hf_card : ∀ a ∈ I, (f a).card * c ≤ (n + 1)^4 * (hammingSphere n z a).card := by
      intro a ha
      have h1 := (hf_spec a ha).2.2
      have h2 : hammingVol n r_c ≤ (n + 1) * (hammingSphere n z r_c).card :=
        hammingVol_le_mul_hammingSphere_card_of_le_half n r_c z hz hrc_half
      have h3 : c ≤ (n + 1)^2 * (hammingSphere n z r_c).card := by
        calc
          c ≤ (n + 1) * hammingVol n r_c := h_rc_bound
          _ ≤ (n + 1) * ((n + 1) * (hammingSphere n z r_c).card) := Nat.mul_le_mul_left _ h2
          _ = (n + 1)^2 * (hammingSphere n z r_c).card := by ring
      calc
        (f a).card * c ≤ (f a).card * ((n + 1)^2 * (hammingSphere n z r_c).card) :=
            Nat.mul_le_mul_left _ h3
        _ = (n + 1)^2 * ((f a).card * (hammingSphere n z r_c).card) := by ring
        _ ≤ (n + 1)^2 * ((n + 1)^2 * (hammingSphere n z a).card) := Nat.mul_le_mul_left _ h1
        _ = (n + 1)^4 * (hammingSphere n z a).card := by ring
    let 𝒞_centers := I.biUnion f
    have hC_len : ∀ x ∈ 𝒞_centers, x.length = n := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨a, ha, hxa⟩
      exact (hf_spec a ha).1 x hxa
    have hC_cov : ∀ y ∈ (stringsOfLength n).filter (fun y =>
        r_c < hammingDist z y ∧ hammingDist z y ≤ r), ∃ x ∈ 𝒞_centers, hammingDist x y ≤ r_c := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have hd := hy.2
      have ha : hammingDist z y ∈ I := by
        rw [Finset.mem_Icc]
        exact ⟨hd.1, hd.2⟩
      have hy_sphere : y ∈ hammingSphere n z (hammingDist z y) := by
        rw [hammingSphere, Finset.mem_filter]
        exact ⟨hy.1, rfl⟩
      obtain ⟨x, hx_f, hx_dist⟩ := (hf_spec (hammingDist z y) ha).2.1 y hy_sphere
      refine ⟨x, ?_, hx_dist⟩
      rw [Finset.mem_biUnion]
      exact ⟨hammingDist z y, ha, hx_f⟩
    have hC_card : 𝒞_centers.card * c ≤ (n + 1)^4 * (hammingBall n z r).card := by
      calc
        𝒞_centers.card * c ≤ (∑ a ∈ I, (f a).card) * c :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ a ∈ I, (f a).card * c := Finset.sum_mul _ _ _
        _ ≤ ∑ a ∈ I, (n + 1)^4 * (hammingSphere n z a).card :=
            Finset.sum_le_sum (fun a ha => hf_card a ha)
        _ = (n + 1)^4 * ∑ a ∈ I, (hammingSphere n z a).card := (Finset.mul_sum _ _ _).symm
        _ ≤ (n + 1)^4 * ∑ a ∈ Finset.range (r + 1), (hammingSphere n z a).card :=
            Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (fun a ha => by
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le ha.2))
        _ = (n + 1)^4 * (hammingBall n z r).card := by rw [sum_hammingSphere_card]
    refine ⟨𝒞_centers.toList ++ [z], ?_, ?_, ?_⟩
    · intro x hx
      rw [List.mem_append] at hx
      cases hx with
      | inl hx => exact hC_len x (Finset.mem_toList.mp hx)
      | inr hx =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [hx]
        exact hz
    · intro y hy
      by_cases hdist : hammingDist z y ≤ r_c
      · refine ⟨z, List.mem_append.mpr (Or.inr (List.mem_singleton_self z)), hdist⟩
      · rw [not_le] at hdist
        have hy_filter : y ∈ (stringsOfLength n).filter (fun y =>
            r_c < hammingDist z y ∧ hammingDist z y ≤ r) := by
          rw [Finset.mem_filter]
          rw [hammingBall, Finset.mem_filter] at hy
          exact ⟨hy.1, hdist, hy.2⟩
        obtain ⟨x, hxC, hx_dist⟩ := hC_cov y hy_filter
        have hxC' : x ∈ 𝒞_centers.toList := by exact Finset.mem_toList.mpr hxC
        exact ⟨x, List.mem_append.mpr (Or.inl hxC'), hx_dist⟩
    · calc
        (𝒞_centers.toList ++ [z]).length * c = (𝒞_centers.card + 1) * c := by simp
        _ = 𝒞_centers.card * c + c := by ring
        _ ≤ (n + 1)^4 * (hammingBall n z r).card + c := Nat.add_le_add_right hC_card c
        _ ≤ (n + 1)^4 * (hammingBall n z r).card + (n + 1)^4 * (hammingBall n z r).card := by
          refine Nat.add_le_add_left ?_ _
          calc
            c ≤ hammingVol n r := hc_and_bound.2
            _ = (hammingBall n z r).card := (hammingBall_card n z r hz).symm
            _ = 1 * (hammingBall n z r).card := (one_mul _).symm
            _ ≤ (n + 1)^4 * (hammingBall n z r).card := Nat.mul_le_mul_right _ (by
              have hpos : 1 ≤ n + 1 := by omega
              exact Nat.one_le_pow 4 (n + 1) hpos)
        _ = 2 * ((n + 1)^4 * (hammingBall n z r).card) := by ring
        _ ≤ (n + 1) * ((n + 1)^4 * (hammingBall n z r).card) := Nat.mul_le_mul_right _ (by
          have : 2 ≤ n + 1 := by omega
          exact this)
        _ = (n + 1)^5 * (hammingBall n z r).card := by ring
  · refine ⟨[z], ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
      exact hz
    · intro y hy
      refine ⟨z, by simp, ?_⟩
      rw [hammingBall, Finset.mem_filter] at hy
      linarith
    · calc
        [z].length * c = c := by simp
        _ ≤ hammingVol n r := hc_and_bound.2
        _ = (hammingBall n z r).card := (hammingBall_card n z r hz).symm
        _ = 1 * (hammingBall n z r).card := (one_mul _).symm
        _ ≤ (n + 1)^5 * (hammingBall n z r).card := Nat.mul_le_mul_right _ (by
          have hpos : 1 ≤ n + 1 := Nat.le_add_left 1 n
          exact Nat.one_le_pow 5 (n + 1) hpos)

/-- Cover a Hamming ball by Hamming balls of the largest radius whose volume
does not exceed `c`.  The public statement is unchanged; its proof must use
the sphere-wise construction above, not a lower bound on
`B(z,r) \cap B(y,r_c)` for every boundary point `y`. -/
theorem hammingBall_cover_centers (n : ℕ) (z : BitString) (r c r_c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (h_r_bound : c ≤ hammingVol n r)
    (h_rc_vol : hammingVol n r_c ≤ c) (h_rc_next : c ≤ hammingVol n (r_c + 1))
    (h_rc_bound : c ≤ (n + 1) * hammingVol n r_c) :
    ∃ 𝒞_centers : List BitString,
      (∀ x ∈ 𝒞_centers, x.length = n) ∧
      (∀ y ∈ hammingBall n z r, ∃ x ∈ 𝒞_centers, hammingDist x y ≤ r_c) ∧
      𝒞_centers.length * c ≤ (n + 1)^7 * (hammingBall n z r).card := by
  by_cases hn : n = 0
  · have hz0 : z = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst z
    subst n
    refine ⟨[[]], by simp, ?_, ?_⟩
    · intro y hy
      have hylen : y.length = 0 :=
        (mem_stringsOfLength 0 y).mp (Finset.mem_filter.mp hy).1
      have hy0 : y = [] := List.eq_nil_of_length_eq_zero hylen
      subst y
      simp [hammingDist]
    · have hvol : hammingVol 0 r = 1 := by
        have hle := hammingVol_le_two_pow 0 r
        have hpos := hammingVol_pos 0 r
        norm_num at hle ⊢
        omega
      have hc1 : c = 1 := by omega
      subst c
      have hmem : [] ∈ hammingBall 0 [] r := by
        simp [hammingBall, stringsOfLength, hammingDist]
      exact Finset.card_pos.mpr ⟨[], hmem⟩
  · by_cases hr : r ≤ n / 2
    · have hrn : r < n := by omega
      have hrc : r_c ≤ r :=
        hammingRadius_le_of_volume_le h_rc_vol h_r_bound hrn
      obtain ⟨C, hClen, hCcov, hCcard⟩ :=
        hammingBall_cover_centers_of_le_half n z r c r_c hz hc hr hrc
          h_r_bound h_rc_bound
      refine ⟨C, hClen, hCcov, hCcard.trans ?_⟩
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
    · have hrhalf : n / 2 < r := by omega
      obtain ⟨C, hClen, hCcov, hCcard⟩ :=
        hamming_probabilistic_cover n r_c (hammingVol n r_c)
          (hammingVol_pos n r_c) le_rfl
      refine ⟨C, hClen, ?_, ?_⟩
      · intro y hy
        exact hCcov y (Finset.mem_filter.mp hy).1
      · have hcube :=
          stringsOfLength_card_le_mul_hammingBall_card_of_half_lt n r z hz hrhalf
        calc
          C.length * c ≤ C.length * ((n + 1) * hammingVol n r_c) :=
            Nat.mul_le_mul_left _ h_rc_bound
          _ = (n + 1) * (C.length * hammingVol n r_c) := by ring
          _ ≤ (n + 1) * ((n + 1) * (stringsOfLength n).card) :=
            Nat.mul_le_mul_left _ hCcard
          _ ≤ (n + 1) * ((n + 1) * ((n + 1) *
              (hammingBall n z r).card)) := by
            gcongr
          _ = (n + 1)^3 * (hammingBall n z r).card := by ring
          _ ≤ (n + 1)^7 * (hammingBall n z r).card :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))

/-- Condition (3) covering theorem using the probabilistic covering lemma. -/
theorem hammingFamily_cover {A : Finset BitString} (hA : hammingFamilyMem A)
    (n c : ℕ) (hc : 0 < c) (hcA : c ≤ A.card) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, hammingFamilyMem B ∧ B.card ≤ c) ∧
      (∀ x ∈ A, x.length = n → ∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length * c ≤ hammingOverhead n * A.card := by
  by_cases hc_eq : A.card ≤ c
  · use [A]
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      simp only [List.mem_singleton] at hB
      subst hB
      exact ⟨hA, hc_eq⟩
    · intro x hxA _
      exact ⟨A, by simp, hxA⟩
    · have hc_eq_exact : c = A.card := le_antisymm hcA hc_eq
      have h_oh : 1 ≤ hammingOverhead n := hammingOverhead_pos n
      calc
        [A].length * c = 1 * A.card := by rw [List.length_singleton, hc_eq_exact]
        _ ≤ hammingOverhead n * A.card := Nat.mul_le_mul_right A.card h_oh
  · rcases hA with ⟨m, z, r, hzlen, hA_eq⟩
    by_cases hmn : m = n
    · have h_c_le : c ≤ 2^n := by
        refine le_trans hcA ?_
        rw [hmn] at hA_eq hzlen
        rw [hA_eq, hammingBall_card n z r hzlen]
        exact hammingVol_le_two_pow n r
      have hzlen' : z.length = n := by rw [← hmn]; exact hzlen
      obtain ⟨r_c, h_vol_le, h_vol_bound, h_vol_next⟩ :=
        exists_hamming_radius_for_volume n c hc h_c_le
      have hA_eq' : A = hammingBall n z r := by rw [← hmn, hA_eq]
      have h_r_bound : c < hammingVol n r := by
        have : c < A.card := lt_of_not_ge hc_eq
        rwa [hA_eq', hammingBall_card n z r hzlen'] at this
      obtain ⟨centers, h_centers_len, h_cover, h_count⟩ :=
        hammingBall_cover_centers n z r c r_c hzlen' hc
          (le_of_lt h_r_bound) h_vol_le h_vol_next h_vol_bound
      use centers.map (fun x => hammingBall n x r_c)
      refine ⟨?_, ?_, ?_⟩
      · intro B hB
        rw [List.mem_map] at hB
        rcases hB with ⟨x, hx_mem, rfl⟩
        refine ⟨⟨n, x, r_c, h_centers_len x hx_mem, rfl⟩, ?_⟩
        rw [hammingBall_card n x r_c (h_centers_len x hx_mem)]
        exact h_vol_le
      · intro x hxA hxlen
        rw [hA_eq'] at hxA
        obtain ⟨y, hy_mem, h_dist⟩ := h_cover x hxA
        refine ⟨hammingBall n y r_c, ?_, ?_⟩
        · rw [List.mem_map]
          exact ⟨y, hy_mem, rfl⟩
        · rw [hammingBall, Finset.mem_filter]
          refine ⟨(mem_stringsOfLength n x).mpr hxlen, h_dist⟩
      · rw [List.length_map]
        unfold hammingOverhead
        have : A.card = (hammingBall n z r).card := by rw [hA_eq']
        rw [this]
        exact h_count
    · use []
      refine ⟨by simp, ?_, by simp⟩
      intro x hxA hxlen
      rw [hA_eq, hammingBall, Finset.mem_filter] at hxA
      have hx_m : x.length = m := (mem_stringsOfLength m x).mp hxA.1
      omega

/-- The description family whose members are the Hamming balls. -/
noncomputable def hammingFamily : DescriptionFamily where
  mem := hammingFamilyMem
  nonempty_of_mem := @hammingFamilyMem_nonempty
  enumeration := {
    enum := hammingEnum
    computable := hammingEnum_computable
    mono := hammingEnum_mono
    sound := hammingEnum_sound
    complete := hammingEnum_complete
  }
  fullCube := hammingFamily_fullCube
  overhead := hammingOverhead
  overhead_pos := hammingOverhead_pos
  cover := @hammingFamily_cover

/-- The family of Hamming balls has polynomial covering overhead. -/
lemma hammingFamily_hasPolynomialOverhead : hammingFamily.HasPolynomialOverhead := by
  refine ⟨1, 7, by decide, ?_⟩
  intro n
  simp [hammingFamily, hammingOverhead]

end Kolmogorov


