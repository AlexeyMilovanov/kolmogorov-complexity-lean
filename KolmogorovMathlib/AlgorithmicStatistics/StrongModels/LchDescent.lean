import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongProfile
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalMaps
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.MinimalModelBounds
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StrongSufficientStatistic
-- `logSlack_add_logSlack_absorb` was relocated from `MinimalModelBounds` to
-- `PropMinHereditary` in the accepted baseline; import it here so this restored
-- descent file resolves that arithmetic lemma.
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PropMinHereditary

/-!
# LCH descent steps (VS40 Lemma `lch`)

The source proof of Lemma `lch` builds a sequence
`B₀ = A, A₁, B₁, A₂, B₂, …` where each `Aᵢ₊₁` is a strong statistic obtained
from `Bᵢ` using normality of `x`, and each `Bᵢ` is a standard-block improvement
of `Aᵢ` (Proposition `prop:better-std`).

This file provides the two atomic transitions of that descent as reusable,
kernel-checked lemmas:

* `exists_strong_model_near_of_normal` — the `Bᵢ → Aᵢ₊₁` normality step;
* `exists_descent_round` — one full loop iteration `Aᵢ → Bᵢ → Aᵢ₊₁`, composing
  the source-faithful standardization `standardModel_package` with the normality step;
* `lch_complexity_drop_of_gap`, `descent_mul_le_of_step`,
  `exists_lch_terminal_gap`, and `plainK_forward_gap_of_condK` — the descent
  and terminal-gap arithmetic;
* `lch_closing_condK` — the closing symmetry-of-information chain for
  `C(H | Ω_{C(H)})`.

The dependent construction of the full `N = O(√n)` model sequence, application
of the abstract stopping index to it, and the final uniform slack absorption remain.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

theorem exists_strong_model_near_of_normal
    (V T : Map) (hV : isOptimalConditional V) :
    ∀ x A (hA : A.Nonempty) epsilon alpha,
      x ∈ A →
      IsNormalString V T x epsilon alpha →
      ∃ H, ∃ hH : H.Nonempty,
        x ∈ H ∧
        IsStrongSetModel T x H hH epsilon ∧
        plainSetComplexity V H hH ≤
          plainSetComplexity V A hA + (alpha : ENat) ∧
        finiteSetLogCard H ≤ finiteSetLogCard A + alpha := by
  intro x A hA epsilon alpha hxA hnorm
  have H_not_top : plainSetComplexity V A hA ≠ ⊤ := by
    obtain ⟨c, hc⟩ := plainKLeLength V hV
    have hc' := hc (codedUniformOn A hA).code
    have h_ne : (programLength (codedUniformOn A hA).code : ENat) + c ≠ ⊤ := by
      rw [← Nat.cast_add]
      exact ENat.coe_ne_top _
    exact ne_top_of_le_ne_top h_ne hc'
  have H_val : ∃ v : ℕ, plainSetComplexity V A hA = ↑v := by
    obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp H_not_top
    exact ⟨v, hv.symm⟩
  rcases H_val with ⟨v, hv⟩
  have h_in_plain : (v, finiteSetLogCard A) ∈ plainDescriptionProfileSet V x := by
    use A, hA
    unfold IsPlainIJDescription
    exact ⟨hxA, by simp [hv], (finiteSetLogCard_le_iff A (finiteSetLogCard A)).mp le_rfl⟩
  unfold IsNormalString ProfileSetsWithinNeighborhood at hnorm
  rcases hnorm.1 _ h_in_plain with ⟨q', hq', hdist⟩
  have h_upper := strongDescriptionProfileSet_isUpperSet V T x epsilon
  have hq'_le : q'.1 ≤ v + alpha ∧ q'.2 ≤ finiteSetLogCard A + alpha := by
    unfold natPairLInfDistance at hdist
    have h1 := le_trans (Nat.le_max_left _ _) hdist
    have h2 := le_trans (Nat.le_max_right _ _) hdist
    omega
  have h_in_strong : (v + alpha, finiteSetLogCard A + alpha) ∈
      strongDescriptionProfileSet V T x epsilon := by
    apply h_upper hq'_le hq'
  rcases h_in_strong with ⟨H, hH, ⟨h_plain, h_strong⟩⟩
  use H, hH
  refine ⟨h_plain.1, h_strong, ?_, ?_⟩
  · have h_c : (v + alpha : ENat) = (v : ENat) + (alpha : ENat) := rfl
    rw [hv]
    exact h_plain.2.1.trans h_c.le
  · exact (finiteSetLogCard_le_iff H (finiteSetLogCard A + alpha)).mpr h_plain.2.2

/-- The arithmetic decrease in one nonterminal LCH round.  If the standard
model has saved more than `s` bits of plain complexity and the following
normality step adds at most `alpha`, where `2 * alpha < s`, then the next strong
model saves at least `s / 2 + 1` bits. -/
theorem lch_complexity_drop_of_gap
    (a b next s alpha : Nat)
    (hgap : s < a - b)
    (hnext : next ≤ b + alpha)
    (halpha : alpha * 2 < s) :
    next + (s / 2 + 1) ≤ a := by
  omega

/-- Iterating a fixed positive decrease: if every one of the first `N` steps
saves at least `d`, then the accumulated saving `N * d` fits below the initial
value.  This is the induction kernel used to bound the number of LCH rounds. -/
theorem descent_mul_le_of_step
    (f : Nat → Nat) (N d : Nat)
    (hstep : ∀ i, i < N → f (i + 1) + d ≤ f i) :
    f N + N * d ≤ f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hlast : f (N + 1) + d ≤ f N := hstep N (Nat.lt_succ_self N)
      have hprefix : ∀ i, i < N → f (i + 1) + d ≤ f i := by
        intro i hi
        exact hstep i (hi.trans (Nat.lt_succ_self N))
      have hih := ih hprefix
      calc
        f (N + 1) + (N + 1) * d = (f (N + 1) + d) + N * d := by ring
        _ ≤ f N + N * d := Nat.add_le_add_right hlast _
        _ ≤ f 0 := hih

/-- Any infinite sequence of LCH rounds reaches a small complexity gap after
at most `C(A₀) / (⌊s/2⌋+1) + 1` rounds.  This is the stopping-index
argument, separated from the dependent construction of the model sequence. -/
theorem exists_lch_terminal_gap
    (f g : Nat → Nat) (s alpha : Nat)
    (halpha : alpha * 2 < s)
    (hnext : ∀ i, f (i + 1) ≤ g i + alpha) :
    ∃ i, i ≤ f 0 / (s / 2 + 1) + 1 ∧ f i - g i ≤ s := by
  let d := s / 2 + 1
  let N := f 0 / d + 1
  have hd : 0 < d := by
    dsimp [d]
    omega
  by_contra hterminal
  push_neg at hterminal
  have hstep : ∀ i, i < N → f (i + 1) + d ≤ f i := by
    intro i hi
    have hgap : s < f i - g i := hterminal i (Nat.le_of_lt hi)
    simpa [d] using
      lch_complexity_drop_of_gap (f i) (g i) (f (i + 1)) s alpha
        hgap (hnext i) halpha
  have hbound := descent_mul_le_of_step f N d hstep
  have hover : f 0 < N * d := by
    dsimp [N]
    rw [Nat.mul_comm]
    exact Nat.lt_mul_div_succ (f 0) hd
  omega

/-- The easy direction of the plain-complexity gap used at the terminal LCH
round.  A short program for `B` conditional on `A` bounds `C(B) - C(A)` with
only logarithmic overhead in a visible bound for `C(A)`. -/
theorem plainK_forward_gap_of_condK
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (A B : BitString) (N a b s : Nat),
      plainK V A = (a : ENat) →
      plainK V B = (b : ENat) →
      a ≤ N →
      condK V B A ≤ (s : ENat) →
      b ≤ a + s + logSlack c N := by
  obtain ⟨cTwo, hTwo⟩ := plainK_two_stage V hV
  refine ⟨cTwo + 2, ?_⟩
  intro A B N a b s ha hb haN hBA
  have hraw := hTwo B A a s (by rw [ha]) hBA
  rw [hb] at hraw
  have hnat : b ≤ a + s + 2 * (Nat.bits a).length + cTwo := by
    exact_mod_cast hraw
  calc
    b ≤ a + s + 2 * (Nat.bits a).length + cTwo := hnat
    _ ≤ a + s + logSlack (cTwo + 2) N := by
      have hbits := length_natBits_mono haN
      unfold logSlack
      nlinarith [Nat.zero_le ((Nat.bits N).length)]

/-- The closing conditional-complexity chain in the proof of Lemma `lch`.

At the terminal round, `A` and its standard improvement `B` have small
complexity gaps in both directions, `B` is simple given `A`, and `B` is simple
given its own Omega code.  Plain symmetry of information reverses `B | A`, the
Omega bridge moves from `Omega_{C(A)}` to `Omega_{C(B)}`, and two applications
of transitivity give `C(A | Omega_{C(A)})`.  The expensive `delta` term occurs
only in the final (undoubled) link. -/
theorem lch_closing_condK
    (V : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) :
    ∃ c : Nat, ∀ (A B : BitString) (N a b delta tau s : Nat),
      plainK V A = (a : ENat) →
      plainK V B = (b : ENat) →
      a ≤ N →
      b ≤ N →
      condK V B A ≤ (s : ENat) →
      s ≤ N →
      a ≤ b + delta →
      b ≤ a + tau →
      condK V B (omegaFixedCode q b) ≤ (s : ENat) →
      condK V A (omegaFixedCode q a) ≤
        (4 * tau + delta + 3 * s + logSlack c N : ENat) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cRev, hRev⟩ := condK_reverse_of_plain_complexity_gap V U hV hU
  obtain ⟨cBridge, hBridge⟩ := omegaFixedCode_bridge_linear V hV q hq 0
  obtain ⟨cTrans, hTrans⟩ := condK_trans_nat V hV
  refine ⟨4 * cBridge + cRev + 3 * cTrans, ?_⟩
  intro A B N a b delta tau s ha hb haN hbN hBA hsN hab hba hBOmega
  have hOmegaRaw := hBridge N b a (by simpa [logSlack] using hbN)
    (by simpa [logSlack] using haN)
  have hOmega :
      condK V (omegaFixedCode q b) (omegaFixedCode q a) ≤
        ((tau + logSlack cBridge N : Nat) : ENat) := by
    calc
      condK V (omegaFixedCode q b) (omegaFixedCode q a)
          ≤ ((b - a) + logSlack cBridge N : ENat) := hOmegaRaw
      _ ≤ ((tau + logSlack cBridge N : Nat) : ENat) := by
        exact_mod_cast (show b - a + logSlack cBridge N ≤
          tau + logSlack cBridge N by omega)
  have hReverse :
      condK V A B ≤ ((delta + s + logSlack cRev N : Nat) : ENat) := by
    calc
      condK V A B
          ≤ ((delta + s : Nat) : ENat) + (logSlack cRev N : ENat) :=
            hRev A B N delta s (by simpa [ha] using haN)
              (by simpa [hb] using hbN) hBA hsN (by
                rw [ha, hb]
                exact_mod_cast hab)
      _ = ((delta + s + logSlack cRev N : Nat) : ENat) := by
        push_cast
        ring
  have hFirst := hTrans (omegaFixedCode q a) (omegaFixedCode q b) B
    (tau + logSlack cBridge N) s hOmega hBOmega
  have hFinal := hTrans (omegaFixedCode q a) B A
    (2 * (tau + logSlack cBridge N) + s + cTrans)
    (delta + s + logSlack cRev N) hFirst hReverse
  calc
    condK V A (omegaFixedCode q a)
        ≤ ((2 * (2 * (tau + logSlack cBridge N) + s + cTrans) +
          (delta + s + logSlack cRev N) + cTrans : Nat) : ENat) := hFinal
    _ ≤ ((4 * tau + delta + 3 * s +
          logSlack (4 * cBridge + cRev + 3 * cTrans) N : Nat) : ENat) := by
      apply Nat.cast_le.mpr
      unfold logSlack
      ring_nf
      omega

/-- **One LCH descent round `Aᵢ → Bᵢ → Aᵢ₊₁`.**

For a normal string `x` and any model `A ∋ x` of length `n`, standardization
(`standardModel_package`) yields a standard block `B ∋ x` whose two-part
parameters are no worse than those of `A`, which is simple given `A` and
interchangeable with its own Omega code, and the normality step
(`exists_strong_model_near_of_normal`) then yields a strong statistic `H ∋ x`
with the profile coordinates shifted by at most `alpha`.  This is exactly one
iteration of the source's descent loop, packaged for the eventual
`N = O(√n)`-step induction of Lemma `lch`.

The `q`-Omega interchange conclusion is retained so the eventual claim (3)
`K(H | Ω_{K(H)}) = O(√n)` can be assembled with a consistent Omega code `q`. -/
theorem exists_descent_round
    (V T : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) :
    ∃ c : Nat, ∀ x n A (hA : A.Nonempty) epsilon alpha,
      x.length = n →
      x ∈ A →
      IsNormalString V T x epsilon alpha →
      ∃ (B : Finset BitString) (hB : B.Nonempty)
        (H : Finset BitString) (hH : H.Nonempty),
        x ∈ B ∧ x ∈ H ∧
        IsStrongSetModel T x H hH epsilon ∧
        plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
          plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
            (logSlack c n : ENat) ∧
        plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
          (n + logSlack c n : ENat) ∧
        condK V (codedUniformOn B hB).code (codedUniformOn A hA).code ≤
          (logSlack c n : ENat) ∧
        condK V (codedUniformOn B hB).code
            (omegaFixedCode q (plainSetComplexity V B hB).toNat) ≤
          (logSlack c n : ENat) ∧
        plainSetComplexity V H hH + (finiteSetLogCard H : ENat) ≤
          plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
            (2 * alpha + logSlack c n : ENat) ∧
        plainSetComplexity V H hH ≤
          (n + alpha + logSlack c n : ENat) ∧
        plainSetComplexity V H hH ≤ plainSetComplexity V B hB + (alpha : ENat) ∧
        finiteSetLogCard H ≤ finiteSetLogCard B + alpha := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cStd, hpkg⟩ := standardModel_package V U hV hU q hq
  obtain ⟨cFold, hFold⟩ := logSlack_add_logSlack_absorb cStd cStd
  obtain ⟨cBlock, hBlock⟩ := plainK_standardBlock_upper V hV q hq
  obtain ⟨cCapFold, hCapFold⟩ := logSlack_add_logSlack_absorb cBlock cStd
  let C := cStd + cFold + cBlock + cCapFold
  refine ⟨C, fun x n A hA epsilon alpha hn hxA hnorm => ?_⟩
  have hAFinite : plainSetComplexity V A hA ≠ ⊤ :=
    condK_ne_top_of_optimal V hV (codedUniformOn A hA).code []
  let a := (plainSetComplexity V A hA).toNat
  have haValue : plainSetComplexity V A hA = (a : ENat) :=
    (ENat.coe_toNat hAFinite).symm
  let j := finiteSetLogCard A
  obtain ⟨m, r, hxB, hm, hcardB, htwoB, hBA, hBOmega, _hOmegaB⟩ :=
    hpkg x n a j A hA hn hxA haValue rfl
  let B := standardBlock q m r x
  let hB : B.Nonempty := ⟨x, hxB⟩
  have hlogB : finiteSetLogCard B = r := by
    unfold finiteSetLogCard B
    rw [hcardB, Nat.clog_pow 2 r (by norm_num)]
  have hStdLe : logSlack cStd n ≤ logSlack C n :=
    logSlack_mono_left (by dsimp [C]; omega) n
  have hmVisible : m ≤ n + logSlack cStd n :=
    hm.trans (Nat.add_le_add_right (min_le_left _ _) _)
  have hOmegaVisible :
      condK V (codedUniformOn B hB).code
          (omegaFixedCode q (plainSetComplexity V B hB).toNat) ≤
        (logSlack C n : ENat) := by
    calc
      condK V (codedUniformOn B hB).code
          (omegaFixedCode q (plainSetComplexity V B hB).toNat)
          ≤ (logSlack cStd m : ENat) := hBOmega
      _ ≤ (logSlack cStd (n + logSlack cStd n) : ENat) := by
        exact_mod_cast logSlack_mono_right cStd hmVisible
      _ ≤ (logSlack cFold n : ENat) := by
        exact_mod_cast hFold n
      _ ≤ (logSlack C n : ENat) := by
        exact_mod_cast logSlack_mono_left (by dsimp [C]; omega) n
  have hTwoB :
      plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
        plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
          (logSlack C n : ENat) := by
    rw [hlogB, haValue]
    exact htwoB.trans (by
      have hnat : a + j + logSlack cStd n ≤ a + j + logSlack C n := by
        omega
      exact_mod_cast hnat)
  have hCapB :
      plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
        (n + logSlack C n : ENat) := by
    rw [hlogB]
    have hrm : r ≤ m := standardBlock_exponent_le q m r x hxB
    have hBlockRaw := hBlock m r x hxB
    change plainSetComplexity V B hB ≤
      ((m - r + logSlack cBlock m : Nat) : ENat) at hBlockRaw
    calc
      plainSetComplexity V B hB + (r : ENat)
          ≤ ((m - r + logSlack cBlock m : Nat) : ENat) + (r : ENat) := by
            gcongr
      _ ≤ ((m + logSlack cBlock m : Nat) : ENat) := by
        exact_mod_cast (show (m - r + logSlack cBlock m) + r ≤
          m + logSlack cBlock m by omega)
      _ ≤ ((n + logSlack cStd n +
          logSlack cBlock (n + logSlack cStd n) : Nat) : ENat) := by
        have hlog := logSlack_mono_right cBlock hmVisible
        exact_mod_cast Nat.add_le_add hmVisible hlog
      _ ≤ ((n + logSlack C n : Nat) : ENat) := by
        exact_mod_cast (show n + logSlack cStd n +
          logSlack cBlock (n + logSlack cStd n) ≤ n + logSlack C n by
            have hfold := hCapFold n
            have hmono : logSlack cStd n + logSlack cCapFold n ≤
                logSlack C n := by
              unfold logSlack
              dsimp [C]
              nlinarith [Nat.zero_le (Nat.bits n).length]
            omega)
  obtain ⟨H, hH, hxH, hstrong, hcompH, hcardH⟩ :=
    exists_strong_model_near_of_normal V T hV x B hB epsilon alpha hxB hnorm
  have hTwoH :
      plainSetComplexity V H hH + (finiteSetLogCard H : ENat) ≤
        plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
          (2 * alpha + logSlack C n : ENat) := by
    calc
      plainSetComplexity V H hH + (finiteSetLogCard H : ENat)
          ≤ (plainSetComplexity V B hB + (alpha : ENat)) +
              ((finiteSetLogCard B + alpha : Nat) : ENat) := by
            gcongr
      _ = plainSetComplexity V B hB + (finiteSetLogCard B : ENat) +
            ((2 * alpha : Nat) : ENat) := by
            push_cast
            ring
      _ ≤ (plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
              (logSlack C n : ENat)) + ((2 * alpha : Nat) : ENat) := by
            gcongr
      _ = plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
            (2 * alpha + logSlack C n : ENat) := by
            push_cast
            ring
  have hCapH : plainSetComplexity V H hH ≤
      (n + alpha + logSlack C n : ENat) := by
    calc
      plainSetComplexity V H hH
          ≤ plainSetComplexity V B hB + (alpha : ENat) := hcompH
      _ ≤ (plainSetComplexity V B hB + (finiteSetLogCard B : ENat)) +
            (alpha : ENat) := by
        exact add_le_add (le_add_of_nonneg_right (zero_le _)) le_rfl
      _ ≤ (n + logSlack C n : ENat) + (alpha : ENat) := by gcongr
      _ = (n + alpha + logSlack C n : ENat) := by
        ring
  exact ⟨B, hB, H, hH, hxB, hxH, hstrong, hTwoB, hCapB,
    hBA.trans (by exact_mod_cast hStdLe), hOmegaVisible, hTwoH, hCapH,
    hcompH, hcardH⟩

end Kolmogorov
