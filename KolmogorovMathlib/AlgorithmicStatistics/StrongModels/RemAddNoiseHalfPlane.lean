import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.RemAddNoise
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation

/-!
# The forward inclusion of VS40 `rem:add-noise`

`AddNoiseProfileTransform` has two branches.  The uniform-extension branch is
already covered by `inPlainDescriptionProfile_pair_of_base`.  This file proves
the remaining *sufficiency half-plane* branch and assembles the full forward
inclusion: every point of the transformed profile lies within
`epsilon + O(log (|x| + |y|))` of the ordinary plain profile of the pair.

The half-plane branch is where the conditional randomness of the noise string
`y` given `x` is used: it enters only through the pair form of symmetry of
information (`plainK_pair_ge_plainK_add_length_of_random`), which turns
`|y| ≤ C(y | x) + epsilon` into `C(x) + |y| ≤ C(x, y) + epsilon + O(log)`.

The hypothesis really is needed: without it the half-plane branch is false, as
the profile of a non-stochastic string stays far above its sufficiency line.
-/

namespace Kolmogorov

/-- The singleton model places `(C(x) + O(1), 0)` in the ordinary plain profile
of `x`. -/
theorem inPlainDescriptionProfile_singleton
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x : BitString) (kx : Nat),
      plainK V x = (kx : ENat) →
      InPlainDescriptionProfile V x (kx + c) 0 := by
  obtain ⟨c, hc⟩ := plainSetComplexity_singleton_le_plainK V hV
  refine ⟨c, ?_⟩
  intro x kx hkx
  refine ⟨{x}, Finset.singleton_nonempty x, Finset.mem_singleton_self x, ?_, ?_⟩
  · calc
      plainSetComplexity V {x} (Finset.singleton_nonempty x)
          ≤ plainK V x + (c : ENat) := hc x
      _ = ((kx + c : Nat) : ENat) := by rw [hkx]; push_cast; ring
  · simp

/-- **Sufficiency half-plane branch of `rem:add-noise`.**  If the noise string
`y` is conditionally random given `x` up to loss `epsilon`, then every point
`(a, b)` with `C(x) < a` and `C(x, y) ≤ a + b` is, up to
`epsilon + O(log (|x| + |y|))` in the complexity coordinate, an ordinary plain
model of the canonical pair. -/
theorem inPlainDescriptionProfile_pair_of_halfPlane
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy a b : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      kx < a →
      kxy ≤ a + b →
      InPlainDescriptionProfile V (pairCode x y)
        (a + epsilon + logSlack c (x.length + y.length)) b := by
  let U : Map := Classical.choose exists_isOptimalPrefixConditional
  have hU : IsOptimalPrefixConditional U :=
    Classical.choose_spec exists_isOptimalPrefixConditional
  obtain ⟨cSing, hSing⟩ := inPlainDescriptionProfile_singleton V hV
  obtain ⟨cBase, hBase⟩ := inPlainDescriptionProfile_pair_of_base V hV
  obtain ⟨cShift, hShift⟩ := inPlainDescriptionProfile_shift V hV
  obtain ⟨cSoI, hSoI⟩ := plainK_pair_ge_plainK_add_length_of_random V U hV hU
  refine ⟨cSoI + cBase + cShift + cSing, ?_⟩
  intro x y epsilon kx kxy a b hkx hkxy hrandom hax hsuff
  set n := x.length + y.length with hn
  set s := y.length - b with hsdef
  -- The `{x} × {0,1}^{|y|}` model of the pair, sliced down to `2 ^ b` elements.
  have hbase :
      InPlainDescriptionProfile V (pairCode x y)
        (kx + cSing + logSlack cBase y.length) (0 + y.length) :=
    hBase x y (kx + cSing) 0 (hSing x kx hkx)
  have hsliced :
      InPlainDescriptionProfile V (pairCode x y)
        (kx + cSing + logSlack cBase y.length + s + logSlack cShift s)
        (0 + y.length - s) :=
    hShift (pairCode x y) (kx + cSing + logSlack cBase y.length)
      (0 + y.length) s hbase
  -- Symmetry of information converts conditional randomness into a lower bound
  -- on the complexity of the pair.
  have hsoi : kx + y.length ≤ kxy + epsilon + logSlack cSoI n :=
    hSoI x y epsilon kx kxy hkx hkxy hrandom
  have hslackBase : logSlack cBase y.length ≤ logSlack cBase n :=
    logSlack_mono_right cBase (by omega)
  have hslackShift : logSlack cShift s ≤ logSlack cShift n :=
    logSlack_mono_right cShift (by omega)
  have hslackSum :
      logSlack cSoI n + logSlack cBase n + logSlack cShift n + cSing
        ≤ logSlack (cSoI + cBase + cShift + cSing) n := by
    rw [logSlack_add_const, logSlack_add_const]
    exact logSlack_add_const_le (cSoI + cBase + cShift) cSing n
  have hkey :
      kx + cSing + logSlack cBase y.length + s + logSlack cShift s
        ≤ a + epsilon + logSlack (cSoI + cBase + cShift + cSing) n := by
    omega
  have hsize : 0 + y.length - s ≤ b := by omega
  exact ((hsliced.mono_i hkey).mono_j hsize)

/-- **Forward inclusion of VS40 `rem:add-noise`.**  Under conditional
randomness of `y` given `x` with loss `epsilon`, every point of the source's
displayed transformation of the ordinary plain profile of `x` lies within
`epsilon + O(log (|x| + |y|))` of the ordinary plain profile of the canonical
pair `pairCode x y`. -/
theorem addNoiseProfileTransform_to_pairProfile
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy : Nat) (q : Nat × Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      q ∈ AddNoiseProfileTransform
        (plainDescriptionProfileSet V x) kx kxy y.length →
      ∃ q' ∈ plainDescriptionProfileSet V (pairCode x y),
        natPairLInfDistance q q' ≤
          epsilon + logSlack c (x.length + y.length) := by
  obtain ⟨cBase, hBase⟩ := inPlainDescriptionProfile_pair_of_base V hV
  obtain ⟨cHalf, hHalf⟩ := inPlainDescriptionProfile_pair_of_halfPlane V hV
  refine ⟨cBase + cHalf, ?_⟩
  intro x y epsilon kx kxy q hkx hkxy hrandom hq
  set n := x.length + y.length with hn
  have hslackBase : logSlack cBase y.length ≤ logSlack cBase n :=
    logSlack_mono_right cBase (by omega)
  have hslackSum : logSlack cBase n + logSlack cHalf n
      ≤ logSlack (cBase + cHalf) n := by
    rw [logSlack_add_const]
  rcases hq with ⟨i, j, hi, hij, hqeq⟩ | ⟨hlow, hsuff⟩
  · -- Uniform-extension branch.
    refine ⟨(i + logSlack cBase y.length, j + y.length), hBase x y i j hij, ?_⟩
    subst hqeq
    unfold natPairLInfDistance
    omega
  · -- Sufficiency half-plane branch.
    refine ⟨(q.1 + epsilon + logSlack cHalf n, q.2), ?_, ?_⟩
    · exact hHalf x y epsilon kx kxy q.1 q.2 hkx hkxy hrandom hlow hsuff
    · unfold natPairLInfDistance
      omega

/-- The forward half of `RemAddNoiseStatement`, in the exact radius shape
`c * epsilon + logSlack c (|x| + |y|)` used by that interface.  Only the
reverse inclusion (profile of the pair back into the transformation) is still
missing from `RemAddNoiseStatement`. -/
theorem remAddNoise_forward_half
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x y : BitString) (epsilon kx kxy : Nat),
      plainK V x = (kx : ENat) →
      plainK V (pairCode x y) = (kxy : ENat) →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      ∀ q ∈ AddNoiseProfileTransform
          (plainDescriptionProfileSet V x) kx kxy y.length,
        ∃ q' ∈ plainDescriptionProfileSet V (pairCode x y),
          natPairLInfDistance q q' ≤
            c * epsilon + logSlack c (x.length + y.length) := by
  obtain ⟨c, hc⟩ := addNoiseProfileTransform_to_pairProfile V hV
  refine ⟨c + 1, ?_⟩
  intro x y epsilon kx kxy hkx hkxy hrandom q hq
  obtain ⟨q', hq', hdist⟩ := hc x y epsilon kx kxy q hkx hkxy hrandom hq
  refine ⟨q', hq', hdist.trans ?_⟩
  have hslack : logSlack c (x.length + y.length)
      ≤ logSlack (c + 1) (x.length + y.length) :=
    logSlack_mono_left (by omega) _
  have heps : epsilon ≤ (c + 1) * epsilon := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The full VS40 `rem:add-noise` profile stability theorem, assembled from
the direct truncation/multiplicity reverse inclusion and the proved forward
uniform-extension/half-plane inclusion. -/
theorem rem_add_noise
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    RemAddNoiseStatement V := by
  obtain ⟨cReverse, hReverse⟩ :=
    pairProfile_to_addNoiseProfileTransform V U hV hU
  obtain ⟨cForward, hForward⟩ := remAddNoise_forward_half V hV
  refine ⟨cReverse + cForward, ?_⟩
  intro x y epsilon kx kxy hkx hkxy hrandom
  constructor
  · intro q hq
    obtain ⟨q', hq', hdist⟩ :=
      hReverse x y epsilon kx kxy q hkx hkxy hrandom hq
    refine ⟨q', hq', hdist.trans ?_⟩
    have hslack : logSlack cReverse (x.length + y.length) ≤
        logSlack (cReverse + cForward) (x.length + y.length) :=
      logSlack_mono_left (by omega) _
    have hepsilon : cReverse * epsilon ≤
        (cReverse + cForward) * epsilon :=
      Nat.mul_le_mul_right epsilon (by omega)
    omega
  · intro q hq
    obtain ⟨q', hq', hdist⟩ :=
      hForward x y epsilon kx kxy hkx hkxy hrandom q hq
    refine ⟨q', hq', hdist.trans ?_⟩
    have hslack : logSlack cForward (x.length + y.length) ≤
        logSlack (cReverse + cForward) (x.length + y.length) :=
      logSlack_mono_left (by omega) _
    have hepsilon : cForward * epsilon ≤
        (cReverse + cForward) * epsilon :=
      Nat.mul_le_mul_right epsilon (by omega)
    omega

end Kolmogorov
