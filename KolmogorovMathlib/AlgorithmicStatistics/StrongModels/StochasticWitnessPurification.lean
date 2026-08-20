import KolmogorovMathlib.AlgorithmicStatistics.FiniteSetModel
import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.StandardDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Stochastic witness purification

This module proves an auxiliary normalization of stochasticity witnesses:
replacing an arbitrary witness for `x` by one that is *simple given `x`*.  It
does **not** replace the direct truncation/multiplicity proof required for
`prop:add-noise`, and it does **not** assume
`BudgetedRandomNoiseTransportStatement`, a purified witness, or the purification
conclusion itself.

* `KP_standardBlockCode_cond_self_le` (P1): the canonical code of a source
  standard block is `O(log)`-simple given any of its members.  This is the
  prefix-machine analogue of `standard_description_simple_given_x`, proved from
  the member-to-block selector.
* `exists_uniform_witness_of_isStochastic` (P2): an arbitrary stochasticity
  witness is matched by a *uniform finite-set* witness with the same parameters
  up to `O(log(n+alpha+beta))` slack (`n = l(x)`).  Derived from the proved §3
  bridge `exists_realizedGap_uniformSet_of_stochastic`.
* `stochastic_witness_purification` (P3): a standard-block witness satisfying
  the complexity, deficiency, and conditional-simplicity bounds together.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-- **P1.**  The canonical uniform code of a source standard block is
`O(log(m+j))`-simple given any of its members.  The block is recovered from the
member `x` and the two-number advice `(m, j)` by the member selector
`standardBlockFromMemberSelector`, so the prefix conditional complexity of the
code given `x` is bounded by the (self-delimiting) length of that advice.

This is the prefix-machine companion of `standard_description_simple_given_x`
(which is the plain conditional form), obtained by replacing
`condK_partrec_cond_map_le` with `KP_partrec_cond_first_map_le`. -/
theorem KP_standardBlockCode_cond_self_le
    (U V : Map) (hU : IsOptimalPrefixConditional U) (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m j x (hx : x ∈ standardBlock c m j x),
      KP U (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code x ≤
        (logSlack C (m + j) : ENat) := by
  have _hc := hc
  have hselectorSwapped :
      Partrec (fun q : BitString × BitString =>
        standardBlockFromMemberSelector c q.2 q.1) := by
    let swap : (BitString × BitString) → BitString × BitString := fun q => (q.2, q.1)
    have hswap : Computable swap := Computable.pair Computable.snd Computable.fst
    have hcomp := Partrec.comp (standardBlockFromMemberSelector_partrec c) hswap
    exact hcomp.of_eq (fun _ => rfl)
  obtain ⟨Cmap, hmap⟩ :=
    KP_partrec_cond_first_map_le U hU (standardBlockFromMemberSelector c) hselectorSwapped
  obtain ⟨Ccond, hcond⟩ := KP_le_KPPlain U hU
  obtain ⟨Clen, hlen⟩ := KPPlain_le_two_mul_length U hU
  let C := Cmap + Ccond + Clen + 6
  refine ⟨C, fun m j x hx => ?_⟩
  let z := standardBlockAdvice m j
  have hrec :
      (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code ∈
        standardBlockFromMemberSelector c x z := by
    simpa [z] using standardBlockFromMemberSelector_recovers c m j x hx
  have hadvice : KPPlain U z ≤ ((2 * z.length + Clen : ℕ) : ENat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hlen z
  calc
    KP U (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code x
        ≤ KP U z x + (Cmap : ENat) :=
      hmap z (codedUniformOn (standardBlock c m j x) ⟨x, hx⟩).code x hrec
    _ ≤ (KPPlain U z + (Ccond : ENat)) + (Cmap : ENat) := by
      gcongr
      exact hcond z x
    _ ≤ ((2 * z.length + Clen : ℕ) : ENat) + (Ccond : ENat) + (Cmap : ENat) := by
      gcongr
    _ ≤ (logSlack C (m + j) : ENat) := by
      exact_mod_cast (show
        2 * z.length + Clen + Ccond + Cmap ≤ logSlack C (m + j) by
        rw [show z.length =
            2 * (Nat.bits m).length + (Nat.bits j).length + 1 by
          simpa [z] using standardBlockAdvice_length m j]
        have hmb : (Nat.bits m).length ≤ (Nat.bits (m + j)).length :=
          length_natBits_mono (Nat.le_add_right m j)
        have hjb : (Nat.bits j).length ≤ (Nat.bits (m + j)).length :=
          length_natBits_mono (Nat.le_add_left j m)
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits (m + j)).length)])

/-- **P2 (honest slack).**  Every `(alpha, beta)`-stochasticity witness for `x`
(an arbitrary probability model) is matched by a *uniform finite-set* witness
`A ∋ x` whose set complexity is `alpha + O(log(n+alpha+beta))` and whose uniform
model has randomness deficiency `beta + O(log(n+alpha+beta))` at `x`, where
`n = l(x)`.

Slack note (corrected from the drafted `logSlack C (alpha+beta)`): the level of
`x` in its own witness is `~log(1/P.mass x)`, which can be as large as `l(x)`
even when `alpha, beta` are `O(log l(x))`.  So the level-set complexity/deficiency
overhead is genuinely `O(log l(x))`, matching the source's `O(log n)` and the
proved §3 bridge below.  A slack purely in `alpha+beta` is not achievable (take
`x` random of length `n`, `P` uniform on the length-`n` cube).

Derived directly from the proved §3 realized-gap bridge
`exists_realizedGap_uniformSet_of_stochastic`. -/
theorem exists_uniform_witness_of_isStochastic
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ x alpha beta, IsStochastic U x alpha beta →
      ∃ A : Finset BitString, ∃ hA : A.Nonempty, x ∈ A ∧
        setComplexity U A hA ≤ ((alpha + logSlack C (x.length + alpha + beta) : ℕ) : ENat) ∧
        DeficiencyLe U (codedUniformOn A hA) x (beta + logSlack C (x.length + alpha + beta)) := by
  obtain ⟨c, hc⟩ := exists_realizedGap_uniformSet_of_stochastic U hU
  refine ⟨c, fun x alpha beta hst => ?_⟩
  obtain ⟨A, hA, delta, i, j, kx, d, hgap, hdef, _hdd, hi, hd, _hlin⟩ :=
    hc x x.length alpha beta rfl hst
  refine ⟨A, hA, hgap.1, ?_, ?_⟩
  · rw [hgap.2.1]
    exact_mod_cast hi
  · exact DeficiencyLe.mono_beta hd hdef

/-- **P3 core.**  A uniform model with small *optimality* deficiency has
a single `prop_better_std` block which simultaneously preserves the complexity
budget, has small randomness deficiency, and is prefix-simple given `x`.

The optimality hypothesis is essential.  Randomness deficiency alone does not
bound optimality deficiency with logarithmic loss: the proved converse
`optimalityDeficiency_of_randomnessDeficiency` pays the model-complexity budget.
The final purification theorem first invokes
`stochasticity_to_optimal_set_thm`, which supplies exactly this stronger input.

All three conclusions below concern the same standard block.  This prevents a
vacuous proof using an unrelated low-deficiency block, which would not preserve
the source model's complexity budget and could not be used to prove P3. -/
theorem standardBlock_witness_of_setOptimalityDeficiency
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (alpha beta : ℕ)
      (A : Finset BitString) (hA : A.Nonempty),
      x ∈ A →
      setComplexity U A hA ≤ (alpha : ENat) →
      SetOptimalityDeficiencyLe U A hA x beta →
      ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
        setComplexity U (standardBlock c m r x) ⟨x, hxB⟩ ≤
            ((alpha + logSlack C (x.length + alpha + beta) : ℕ) : ENat) ∧
        DeficiencyLe U (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩) x
            (beta + logSlack C (x.length + alpha + beta)) ∧
        KP U (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩).code x ≤
          (logSlack C (x.length + alpha + beta) : ENat) := by
  obtain ⟨cBetter, hBetter⟩ := prop_better_std V U hV hU c hc
  obtain ⟨cSimple, hSimple⟩ := KP_standardBlockCode_cond_self_le U V hU c hc
  obtain ⟨cPlain, hPlain⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  let cExact := cPlain + cBits + 2
  have hExact : ∀ (z : BitString) (k N : ℕ),
      plainK V z = (k : ENat) → k ≤ N →
      KPPlain U z ≤ ((k + cExact * (Nat.bits N).length + cExact : ℕ) : ENat) := by
    intro z k N hk hkN
    have hkBits : (Nat.bits k).length ≤ (Nat.bits N).length :=
      length_natBits_mono hkN
    calc
      KPPlain U z ≤ (k : ENat) + KPPlain U (Nat.bits k) + (cPlain : ENat) :=
        hPlain z k hk
      _ ≤ (k : ENat) + ((2 * (Nat.bits k).length + cBits : ℕ) : ENat) +
          (cPlain : ENat) := by
        gcongr
        exact hBits (Nat.bits k)
      _ ≤ ((k + cExact * (Nat.bits N).length + cExact : ℕ) : ENat) := by
        exact_mod_cast (show
          k + (2 * (Nat.bits k).length + cBits) + cPlain ≤
            k + cExact * (Nat.bits N).length + cExact by
          dsimp [cExact]
          nlinarith [Nat.zero_le ((Nat.bits N).length)])
  obtain ⟨cRand, hRand⟩ := randomness_optimality U hU
  obtain ⟨cBetterFold, hBetterFold⟩ :=
    logSlack_linear_bound cBetter (cBetter + 1) cBetter
  obtain ⟨cExactFold, hExactFold⟩ :=
    logSlack_linear_bound cExact
      (cBetter + cBetterFold + 1) (cBetter + cBetterFold)
  obtain ⟨cSimpleFold, hSimpleFold⟩ :=
    logSlack_linear_bound cSimple (2 * (cBetter + 1)) (2 * cBetter)
  let C := cBetter + cBetterFold + cExactFold + cSimpleFold + cRand + 2
  refine ⟨C, fun x alpha beta A hA hxA hAComplexity hAOptimality => ?_⟩
  let M := x.length + alpha + beta
  have hIFinite : setComplexity U A hA ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top alpha) hAComplexity
  obtain ⟨i, hi⟩ : ∃ i : ℕ, setComplexity U A hA = (i : ENat) :=
    (ENat.ne_top_iff_exists.mp hIFinite).imp fun _ h => h.symm
  have hiAlpha : i ≤ alpha := by
    rw [hi] at hAComplexity
    exact_mod_cast hAComplexity
  obtain ⟨j, hjLower, hjUpper⟩ := exists_card_dyadic_bracket A hA
  have hDescription : IsIJDescription U x A hA i j :=
    ⟨hxA, le_of_eq hi, hjUpper⟩
  obtain ⟨m, r, hxB, hmBound, hBCard, hBPlain, hBPrefix, _hmLower,
      hBTwoPart, _hBGivenA⟩ :=
    hBetter x x.length i j A hA rfl hDescription
  let B := standardBlock c m r x
  let hB : B.Nonempty := ⟨x, hxB⟩
  have hmVisible : m ≤ x.length + logSlack cBetter x.length := by
    exact hmBound.trans (Nat.add_le_add_right (Nat.min_le_left _ _) _)
  have hLengthSlack : logSlack cBetter x.length ≤ cBetter * M + cBetter := by
    unfold logSlack
    have hBits : (Nat.bits x.length).length ≤ M :=
      (length_natBits_mono (show x.length ≤ M by dsimp [M]; omega)).trans
        (length_natBits_le_self M)
    nlinarith
  have hmLinear : m ≤ (cBetter + 1) * M + cBetter := by
    calc
      m ≤ x.length + logSlack cBetter x.length := hmVisible
      _ ≤ M + (cBetter * M + cBetter) := by omega
      _ = (cBetter + 1) * M + cBetter := by ring
  have hBetterAtM : logSlack cBetter m ≤ logSlack cBetterFold M :=
    (logSlack_mono_right cBetter hmLinear).trans (hBetterFold M)
  have hBetterFoldLinear :
      logSlack cBetterFold M ≤ cBetterFold * M + cBetterFold := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left cBetterFold (length_natBits_le_self M)) cBetterFold
  let N := m + logSlack cBetter m
  have hNLinear :
      N ≤ (cBetter + cBetterFold + 1) * M + (cBetter + cBetterFold) := by
    dsimp [N]
    calc
      m + logSlack cBetter m ≤
          ((cBetter + 1) * M + cBetter) +
            (cBetterFold * M + cBetterFold) := by omega
      _ = (cBetter + cBetterFold + 1) * M + (cBetter + cBetterFold) := by ring
  have hExactAtN : logSlack cExact N ≤ logSlack cExactFold M :=
    (logSlack_mono_right cExact hNLinear).trans (hExactFold M)
  have hrm : r ≤ m := standardBlock_exponent_le c m r x hxB
  have hSimpleArg :
      m + r ≤ 2 * (cBetter + 1) * M + 2 * cBetter := by
    calc
      m + r ≤ 2 * m := by omega
      _ ≤ 2 * ((cBetter + 1) * M + cBetter) :=
        Nat.mul_le_mul_left 2 hmLinear
      _ = 2 * (cBetter + 1) * M + 2 * cBetter := by ring
  have hSimpleAtM : logSlack cSimple (m + r) ≤ logSlack cSimpleFold M :=
    (logSlack_mono_right cSimple hSimpleArg).trans (hSimpleFold M)
  obtain ⟨jOpt, hjOptUpper, hjOptBound⟩ :=
    setOptimalityCardBound hxA hi hAOptimality
  have hjBracket : j - 1 ≤ jOpt :=
    dyadic_bracket_lower_bound
      (hjLower.trans (by exact_mod_cast hjOptUpper))
  have hijBound :
      (i : ENat) + (j : ENat) ≤ KPPlain U x + ((beta + 1 : ℕ) : ENat) := by
    calc
      (i : ENat) + (j : ENat) ≤ (i : ENat) + ((jOpt + 1 : ℕ) : ENat) := by
        exact_mod_cast (show i + j ≤ i + (jOpt + 1) by omega)
      _ = (jOpt : ENat) + (i : ENat) + (1 : ENat) := by push_cast; ring
      _ ≤ (KPPlain U x + (beta : ENat)) + (1 : ENat) := by gcongr
      _ = KPPlain U x + ((beta + 1 : ℕ) : ENat) := by push_cast; ring
  have hBPlainFinite : plainK V (codedUniformOn B hB).code ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top (i + logSlack cBetter m)) hBPlain
  obtain ⟨b, hb⟩ : ∃ b : ℕ, plainK V (codedUniformOn B hB).code = (b : ENat) :=
    (ENat.ne_top_iff_exists.mp hBPlainFinite).imp fun _ h => h.symm
  have hbN : b ≤ N := by
    have h := hBTwoPart
    change plainK V (codedUniformOn B hB).code + (r : ENat) ≤
      (m : ENat) + (logSlack cBetter m : ENat) at h
    rw [hb] at h
    exact_mod_cast (show b ≤ N by
      dsimp [N]
      norm_cast at h
      omega)
  have hBPrefixExact :
      setComplexity U B hB ≤ ((b + logSlack cExact N : ℕ) : ENat) := by
    change KPPlain U (codedUniformOn B hB).code ≤
      ((b + logSlack cExact N : ℕ) : ENat)
    simpa [logSlack, Nat.add_assoc] using
      hExact (codedUniformOn B hB).code b N hb hbN
  have hBTotal :
      setComplexity U B hB + (r : ENat) ≤
        KPPlain U x +
          ((beta + 1 + logSlack cBetter x.length +
            logSlack cBetter m + logSlack cExact N : ℕ) : ENat) := by
    calc
      setComplexity U B hB + (r : ENat)
          ≤ ((b + logSlack cExact N : ℕ) : ENat) + (r : ENat) := by gcongr
      _ = (b : ENat) + (r : ENat) + (logSlack cExact N : ENat) := by push_cast; ring
      _ ≤ (m : ENat) + (logSlack cBetter m : ENat) +
          (logSlack cExact N : ENat) := by
        have h := hBTwoPart
        change plainK V (codedUniformOn B hB).code + (r : ENat) ≤
          (m : ENat) + (logSlack cBetter m : ENat) at h
        rw [hb] at h
        exact add_le_add h le_rfl
      _ ≤ ((i + j + logSlack cBetter x.length : ℕ) : ENat) +
          (logSlack cBetter m : ENat) + (logSlack cExact N : ENat) := by
        have hm : (m : ENat) ≤
            ((i + j + logSlack cBetter x.length : ℕ) : ENat) := by
          exact_mod_cast (show m ≤ i + j + logSlack cBetter x.length by
            exact hmBound.trans (Nat.add_le_add_right (Nat.min_le_right _ _) _))
        exact add_le_add (add_le_add hm le_rfl) le_rfl
      _ = (i : ENat) + (j : ENat) +
          ((logSlack cBetter x.length + logSlack cBetter m +
            logSlack cExact N : ℕ) : ENat) := by push_cast; ring
      _ ≤ (KPPlain U x + ((beta + 1 : ℕ) : ENat)) +
          ((logSlack cBetter x.length + logSlack cBetter m +
            logSlack cExact N : ℕ) : ENat) := by gcongr
      _ = KPPlain U x +
          ((beta + 1 + logSlack cBetter x.length +
            logSlack cBetter m + logSlack cExact N : ℕ) : ENat) := by
        push_cast
        ring
  have hLocalSlack :
      1 + logSlack cBetter x.length + logSlack cBetter m +
          logSlack cExact N + cRand ≤ logSlack C M := by
    have hxM : logSlack cBetter x.length ≤ logSlack cBetter M :=
      logSlack_mono_right cBetter (by dsimp [M]; omega)
    have hSum :
        logSlack cBetter M + logSlack cBetterFold M +
            logSlack cExactFold M + cRand + 1 ≤ logSlack C M := by
      dsimp [C]
      unfold logSlack
      nlinarith [Nat.zero_le ((Nat.bits M).length),
        Nat.zero_le (cSimpleFold * (Nat.bits M).length)]
    omega
  have hBOptimality : SetOptimalityDeficiencyLe U B hB x
      (beta + 1 + logSlack cBetter x.length + logSlack cBetter m +
        logSlack cExact N) := by
    have hBPrefixFinite : setComplexity U B hB ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top (b + logSlack cExact N)) hBPrefixExact
    let s := (setComplexity U B hB).toNat
    have hs : setComplexity U B hB = (s : ENat) :=
      (ENat.coe_toNat hBPrefixFinite).symm
    apply setOptimalityDeficiencyLe_of_profile hxB (le_of_eq hs) (le_of_eq hBCard)
    simpa [hs] using hBTotal
  have hBRandom := hRand (codedUniformOn B hB) x
    (beta + 1 + logSlack cBetter x.length + logSlack cBetter m +
      logSlack cExact N) hBOptimality
  refine ⟨m, r, hxB, ?_, ?_, ?_⟩
  · change setComplexity U B hB ≤ ((alpha + logSlack C M : ℕ) : ENat)
    refine hBPrefix.trans ?_
    exact_mod_cast (show i + logSlack cBetter m ≤ alpha + logSlack C M by
      have hFoldLe : logSlack cBetterFold M ≤ logSlack C M :=
        logSlack_mono_left (show cBetterFold ≤ C by dsimp [C]; omega) M
      omega)
  · change DeficiencyLe U (codedUniformOn B hB) x (beta + logSlack C M)
    apply DeficiencyLe.mono_beta
      (show beta + 1 + logSlack cBetter x.length + logSlack cBetter m +
          logSlack cExact N + cRand ≤ beta + logSlack C M by omega)
    exact hBRandom
  · change KP U (codedUniformOn B hB).code x ≤ (logSlack C M : ENat)
    refine (hSimple m r x hxB).trans ?_
    exact_mod_cast (hSimpleAtM.trans
      (logSlack_mono_left (show cSimpleFold ≤ C by dsimp [C]; omega) M))

/-- The exact deficiency-only leaf drafted for the iteration.  Its conclusion
is true, but by itself it does not identify the `prop_better_std` block or
preserve the input model's complexity: a standard block at `plainK V x` already
has logarithmic deficiency.  The stronger theorem above is the leaf actually
needed by `stochastic_witness_purification`. -/
theorem deficiencyLe_prop_better_std_block
    (V U : Map) (hV : isOptimalConditional V) (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n i j d : ℕ)
      (A : Finset BitString) (hA : A.Nonempty),
      x.length = n →
      IsIJDescription U x A hA i j →
      (2 : ENNReal) ^ j / 2 ≤ (A.card : ENNReal) →
      DeficiencyLe U (codedUniformOn A hA) x d →
      ∃ (m r : ℕ) (hxB : x ∈ standardBlock c m r x),
        DeficiencyLe U
          (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩) x
          (d + logSlack C (n + i + j)) := by
  obtain ⟨cPos, hPos⟩ := prop_std_pos V U hV hU c hc
  obtain ⟨cRand, hRand⟩ := randomness_optimality U hU
  obtain ⟨cBridge, hBridge⟩ :=
    plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  obtain ⟨cFold, hFold⟩ := logSlack_linear_bound cPos 1 cLen
  let C := cFold + (cBridge + cRand)
  refine ⟨C, fun x n i j d A hA hn _hDescription _hTight _hDeficiency ↦ ?_⟩
  have hxFinite : plainK V x ≠ ⊤ := by
    have h := hLen x
    refine ne_top_of_le_ne_top ?_ h
    rw [← Nat.cast_add]
    exact ENat.coe_ne_top _
  obtain ⟨m, hmRaw⟩ := ENat.ne_top_iff_exists.mp hxFinite
  have hm : plainK V x = (m : ENat) := hmRaw.symm
  have hmn : m ≤ n + cLen := by
    have h := hLen x
    rw [hm] at h
    change (m : ENat) ≤ (x.length : ENat) + (cLen : ENat) at h
    rw [hn] at h
    exact_mod_cast h
  have hxCompleted : x ∈ completedBoundedOutput c m :=
    (mem_completedBoundedOutput_iff_plainK_le hc m x).2 (le_of_eq hm)
  obtain ⟨r, hxB⟩ := exists_standardBlock_of_mem_completed c m x hxCompleted
  have hrm : r ≤ m := standardBlock_exponent_le c m r x hxB
  have hSet :
      setComplexity U (standardBlock c m r x) ⟨x, hxB⟩ ≤
        ((m - r + logSlack cPos m : ℕ) : ENat) :=
    (hPos m r x hxB).2.2.2.1
  have hPlainBridge : (m : ENat) ≤ KPPlain U x + (cBridge : ENat) := by
    have h := hBridge x
    rw [hm] at h
    exact h
  have hTotal :
      ((m - r + logSlack cPos m : ℕ) : ENat) + (r : ENat) ≤
        KPPlain U x + ((cBridge + logSlack cPos m : ℕ) : ENat) := by
    calc
      ((m - r + logSlack cPos m : ℕ) : ENat) + (r : ENat)
          = ((m + logSlack cPos m : ℕ) : ENat) := by
            exact_mod_cast (show
              m - r + logSlack cPos m + r = m + logSlack cPos m by omega)
      _ = (m : ENat) + (logSlack cPos m : ENat) := by rw [Nat.cast_add]
      _ ≤ (KPPlain U x + (cBridge : ENat)) + (logSlack cPos m : ENat) := by
        gcongr
      _ = KPPlain U x + ((cBridge + logSlack cPos m : ℕ) : ENat) := by
        push_cast
        ring
  have hOptimality :
      SetOptimalityDeficiencyLe U (standardBlock c m r x) ⟨x, hxB⟩ x
        (cBridge + logSlack cPos m) :=
    setOptimalityDeficiencyLe_of_profile hxB hSet
      (le_of_eq (card_standardBlock_of_mem c m r x hxB)) hTotal
  have hRandom := hRand
    (codedUniformOn (standardBlock c m r x) ⟨x, hxB⟩) x
    (cBridge + logSlack cPos m) hOptimality
  have hPosFold : logSlack cPos m ≤ logSlack cFold n := by
    calc
      logSlack cPos m ≤ logSlack cPos (n + cLen) :=
        logSlack_mono_right cPos hmn
      _ = logSlack cPos (1 * n + cLen) := by rw [one_mul]
      _ ≤ logSlack cFold n := hFold n
  have hLocal :
      cBridge + logSlack cPos m + cRand ≤ logSlack C (n + i + j) := by
    calc
      cBridge + logSlack cPos m + cRand
          ≤ logSlack cFold n + (cBridge + cRand) := by omega
      _ ≤ logSlack cFold n + logSlack (cBridge + cRand) n := by
        gcongr
        exact const_le_logSlack le_rfl
      _ = logSlack C n := by
        dsimp [C]
        rw [logSlack_add_same]
      _ ≤ logSlack C (n + i + j) :=
        logSlack_mono_right C (by omega)
  refine ⟨m, r, hxB, ?_⟩
  apply DeficiencyLe.mono_beta
    (show cBridge + logSlack cPos m + cRand ≤
      d + logSlack C (n + i + j) by omega)
  exact hRandom

theorem stochastic_witness_purification
    (U V : Map) (hU : IsOptimalPrefixConditional U) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ x alpha beta, IsStochastic U x alpha beta →
      ∃ P : CodedFiniteDistribution, P.IsProbability ∧
        P.complexity U ≤ ((alpha + logSlack C (x.length + alpha + beta) : ℕ) : ENat) ∧
        DeficiencyLe U P x (beta + logSlack C (x.length + alpha + beta)) ∧
        KP U P.code x ≤ (logSlack C (x.length + alpha + beta) : ENat) := by
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c V :=
    Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cOpt, hOpt⟩ := stochasticity_to_optimal_set_thm U hU
  obtain ⟨cBlock, hBlock⟩ :=
    standardBlock_witness_of_setOptimalityDeficiency V U hV hU c hc
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cBlock (2 * cOpt + 3) (2 * cOpt)
  let C := cOpt + cFold
  refine ⟨C, fun x alpha beta hstoch => ?_⟩
  let M := x.length + alpha + beta
  obtain ⟨A, hA, hxA, hAComplexity, hAOptimality⟩ :=
    hOpt x x.length alpha beta rfl hstoch
  obtain ⟨m, r, hxB, hBComplexity, hBDeficiency, hBSimple⟩ :=
    hBlock x (alpha + logSlack cOpt M) (beta + logSlack cOpt M)
      A hA hxA hAComplexity hAOptimality
  let B := standardBlock c m r x
  let hB : B.Nonempty := ⟨x, hxB⟩
  have hOptSlackLinear :
      logSlack cOpt M ≤ cOpt * M + cOpt := by
    unfold logSlack
    exact Nat.add_le_add_right (Nat.mul_le_mul_left cOpt (length_natBits_le_self M)) cOpt
  have hNestedEq :
      x.length + (alpha + logSlack cOpt M) + (beta + logSlack cOpt M) =
        M + 2 * logSlack cOpt M := by
    dsimp [M]
    omega
  have hNestedBudget :
      x.length + (alpha + logSlack cOpt M) + (beta + logSlack cOpt M) ≤
        (2 * cOpt + 3) * M + 2 * cOpt := by
    rw [hNestedEq]
    calc
      M + 2 * logSlack cOpt M ≤ M + 2 * (cOpt * M + cOpt) := by
        gcongr
      _ ≤ (2 * cOpt + 3) * M + 2 * cOpt := by
        nlinarith
  have hBlockSlack :
      logSlack cBlock
          (x.length + (alpha + logSlack cOpt M) + (beta + logSlack cOpt M)) ≤
        logSlack cFold M := by
    exact (logSlack_mono_right cBlock hNestedBudget).trans (hFold M)
  have hCombinedSlack :
      logSlack cOpt M + logSlack cFold M = logSlack C M := by
    dsimp [C]
    unfold logSlack
    ring
  refine ⟨codedUniformOn B hB, codedUniformOn_isProbability B hB, ?_, ?_, ?_⟩
  · change setComplexity U B hB ≤ ((alpha + logSlack C M : ℕ) : ENat)
    change setComplexity U B hB ≤
      ((alpha + logSlack cOpt M +
        logSlack cBlock
          (x.length + (alpha + logSlack cOpt M) +
            (beta + logSlack cOpt M)) : ℕ) : ENat) at hBComplexity
    refine hBComplexity.trans ?_
    exact_mod_cast (show
      alpha + logSlack cOpt M +
          logSlack cBlock
            (x.length + (alpha + logSlack cOpt M) +
              (beta + logSlack cOpt M)) ≤
        alpha + logSlack C M by
      rw [← hCombinedSlack]
      omega)
  · change DeficiencyLe U (codedUniformOn B hB) x (beta + logSlack C M)
    apply DeficiencyLe.mono_beta
      (show beta + logSlack cOpt M +
          logSlack cBlock
            (x.length + (alpha + logSlack cOpt M) +
              (beta + logSlack cOpt M)) ≤
          beta + logSlack C M by
        rw [← hCombinedSlack]
        omega)
    exact hBDeficiency
  · refine hBSimple.trans ?_
    exact_mod_cast (hBlockSlack.trans
      (logSlack_mono_left (show cFold ≤ C by simp [C]) M))

end Kolmogorov
