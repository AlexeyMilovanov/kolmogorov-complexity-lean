import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith

/-!
# Plain conditional randomness of fixed-width model ordinals

This module supplies the general plain-to-prefix bridge needed to convert the
proved prefix-randomness lower bound for `strongModelOrdinalBits` back to the
source's ordinary conditional complexity.  The exact program length is first
made visible in the condition and is then removed at logarithmic cost.
-/

namespace Kolmogorov

/-- Conditional plain complexity is finite for an optimal conditional
decompressor. -/
theorem condK_ne_top_of_optimal
    (V : Map) (hV : isOptimalConditional V) (x y : BitString) :
    condK V x y ≠ ⊤ := by
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  have hbound :
      condK V x y ≤ ((x.length + cLen + cCond : Nat) : ENat) := by
    calc
      condK V x y ≤ plainK V x + (cCond : ENat) := hCond x y
      _ ≤ ((x.length : Nat) : ENat) + (cLen : ENat) +
          (cCond : ENat) := by
            gcongr
            exact hLen x
      _ = ((x.length + cLen + cCond : Nat) : ENat) := by
            push_cast
            rfl
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound

/-- Prefix conditional complexity is at most ordinary conditional complexity
plus logarithmic overhead in the visible output length.  The constant is
uniform in both strings. -/
theorem KP_le_condK_logSlack
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ x y,
      KP U x y ≤ condK V x y + (logSlack c x.length : ENat) := by
  obtain ⟨cExact, hExact⟩ :=
    KP_le_condK_given_plain_program_length V U hV hU
  obtain ⟨cRemove, hRemove⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cBits, hBits⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨cLen, hLen⟩ := plainKLeLength V hV
  let cLocal := 2 + cExact + cBits + cRemove
  obtain ⟨C, hC⟩ :=
    logSlack_linear_bound cLocal 1 (cLen + cCond)
  refine ⟨C, ?_⟩
  intro x y
  obtain ⟨k, hk⟩ : ∃ k : Nat, condK V x y = (k : ENat) :=
    (ENat.ne_top_iff_exists.mp
      (condK_ne_top_of_optimal V hV x y)).imp fun m hm => hm.symm
  have hkBound : k ≤ x.length + (cLen + cCond) := by
    have hbound : (k : ENat) ≤
        ((x.length + (cLen + cCond) : Nat) : ENat) := by
      rw [← hk]
      calc
        condK V x y ≤ plainK V x + (cCond : ENat) := hCond x y
        _ ≤ ((x.length : Nat) : ENat) + (cLen : ENat) +
            (cCond : ENat) := by
              gcongr
              exact hLen x
        _ = ((x.length + (cLen + cCond) : Nat) : ENat) := by
              push_cast
              ac_rfl
    exact_mod_cast hbound
  have hLocal :
      cExact + 2 * (Nat.bits k).length + cBits + cRemove ≤
        logSlack cLocal k := by
    unfold cLocal logSlack
    nlinarith [Nat.zero_le ((Nat.bits k).length)]
  have hVisible : logSlack cLocal k ≤ logSlack C x.length := by
    calc
      logSlack cLocal k
          ≤ logSlack cLocal (1 * x.length + (cLen + cCond)) :=
            logSlack_mono_right cLocal (by simpa using hkBound)
      _ ≤ logSlack C x.length := hC x.length
  calc
    KP U x y
        ≤ KP U x (pairCode y (Nat.bits k)) +
            KPPlain U (Nat.bits k) + (cRemove : ENat) :=
          hRemove x y (Nat.bits k)
    _ ≤ ((k : ENat) + (cExact : ENat)) +
          ((2 * (Nat.bits k).length + cBits : Nat) : ENat) +
          (cRemove : ENat) := by
            gcongr
            · exact hExact x y k hk
            · exact hBits (Nat.bits k)
    _ = ((k + (cExact + 2 * (Nat.bits k).length + cBits + cRemove) : Nat) :
          ENat) := by
            push_cast
            ring
    _ ≤ ((k + logSlack C x.length : Nat) : ENat) := by
          have hNat := Nat.add_le_add_left (hLocal.trans hVisible) k
          exact_mod_cast hNat
    _ = condK V x y + (logSlack C x.length : ENat) := by
          rw [hk]
          rfl

/-- Pure arithmetic absorption used by the fixed-width ordinal theorem.  If
the ordinal width is bounded by the visible string length and deficiency, then
all logarithmic bridge costs fit into `O(epsilon + log n)`. -/
theorem ordinal_randomness_slack_absorb_visible
    (cCard cBridge c₀ : Nat) :
    ∃ C : Nat, ∀ n epsilon m,
      m ≤ n + epsilon + logSlack cCard n →
      epsilon + c₀ + logSlack cBridge m ≤
        C * epsilon + logSlack C n := by
  obtain ⟨bCard, hbCard⟩ := logSlack_le_add_const cCard
  obtain ⟨cFold, hFold⟩ :=
    logSlack_linear_bound cBridge 2 bCard
  let C := 2 * cFold + c₀ + 2
  refine ⟨C, ?_⟩
  intro n epsilon m hm
  have hmLinear : m ≤ 2 * (n + epsilon) + bCard := by
    have := hbCard n
    omega
  have hLogM : logSlack cBridge m ≤ logSlack cFold (n + epsilon) := by
    calc
      logSlack cBridge m
          ≤ logSlack cBridge (2 * (n + epsilon) + bCard) :=
            logSlack_mono_right cBridge hmLinear
      _ ≤ logSlack cFold (n + epsilon) := hFold (n + epsilon)
  have hSplit :
      logSlack cFold (n + epsilon) ≤
        logSlack cFold n + logSlack cFold epsilon :=
    logSlack_add_le cFold n epsilon
  have hEpsilon :
      logSlack cFold epsilon ≤ cFold * epsilon + cFold := by
    unfold logSlack
    have hbits := length_natBits_le_self epsilon
    nlinarith
  have hLogMFinal :
      logSlack cBridge m ≤
        logSlack cFold n + cFold * epsilon + cFold :=
    (hLogM.trans hSplit).trans (by
      simpa [Nat.add_assoc] using
        Nat.add_le_add_left hEpsilon (logSlack cFold n))
  unfold C at ⊢
  unfold logSlack at hLogMFinal ⊢
  nlinarith [hLogMFinal,
    Nat.zero_le ((Nat.bits n).length)]

/-- The canonical fixed-width ordinal of a low-deficiency finite-set member is
random in the source's ordinary conditional-complexity sense.  All slack is
uniform and depends only on the visible member length and deficiency, never on
the model-code length. -/
theorem strongModelOrdinalBits_plain_random_given_model
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ A (hA : A.Nonempty) x n epsilon,
      x.length = n →
      x ∈ A →
      DeficiencyLe U (codedUniformOn A hA) x epsilon →
      (finiteSetLogCard A : ENat) ≤
        condK V (strongModelOrdinalBits A x)
          (codedUniformOn A hA).code +
        (c * epsilon + logSlack c n : Nat) := by
  obtain ⟨cPrefix, hPrefix⟩ :=
    strongModelOrdinalBits_random_given_model U hU
  obtain ⟨cBridge, hBridge⟩ := KP_le_condK_logSlack V U hV hU
  obtain ⟨cCard, hCard⟩ :=
    finiteSetLogCard_le_length_add_deficiency_log U hU
  obtain ⟨C, hAbsorb⟩ :=
    ordinal_randomness_slack_absorb_visible cCard cBridge cPrefix
  refine ⟨C, ?_⟩
  intro A hA x n epsilon hxn hx hdef
  let u := strongModelOrdinalBits A x
  have huLen : u.length = finiteSetLogCard A :=
    strongModelOrdinalBits_length A x hx
  have hWidth :
      finiteSetLogCard A ≤ n + epsilon + logSlack cCard n :=
    hCard A hA x n epsilon hxn hx hdef
  have hSlack :
      epsilon + cPrefix + logSlack cBridge (finiteSetLogCard A) ≤
        C * epsilon + logSlack C n :=
    hAbsorb n epsilon (finiteSetLogCard A) hWidth
  calc
    (finiteSetLogCard A : ENat)
        ≤ KP U u (codedUniformOn A hA).code +
            (epsilon + cPrefix : Nat) :=
          hPrefix A hA x epsilon hx hdef
    _ ≤ (condK V u (codedUniformOn A hA).code +
          (logSlack cBridge u.length : ENat)) +
          (epsilon + cPrefix : Nat) := by
            gcongr
            exact hBridge u (codedUniformOn A hA).code
    _ = condK V u (codedUniformOn A hA).code +
          ((epsilon + cPrefix +
            logSlack cBridge (finiteSetLogCard A) : Nat) : ENat) := by
            simp only [huLen, Nat.cast_add]
            simp [add_comm, add_assoc]
    _ ≤ condK V u (codedUniformOn A hA).code +
          ((C * epsilon + logSlack C n : Nat) : ENat) := by
            have hCast :
                ((epsilon + cPrefix +
                  logSlack cBridge (finiteSetLogCard A) : Nat) : ENat) ≤
                ((C * epsilon + logSlack C n : Nat) : ENat) := by
              exact_mod_cast hSlack
            exact add_le_add_right hCast _

end Kolmogorov
