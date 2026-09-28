import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock.OmegaCode
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.OptimalityDeficiency
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.StandardBlock
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest

/-!
# The dilemma: a standard block is either stochastic or informative
This module proves the two branches of the VS40 section 5 dilemma. A string in its standard
block is either stochastic through the uniform model on that block, or carries mutual
information with high bits of finite `Ω`.
`stochastic_of_standardBlock_at_plainK` supplies the stochastic branch.
`KP_information_of_standardBlock_additive` supplies the information branch from the two
conditional descriptions and symmetry of information. The condition-transport lemmas used by
both branches are developed here; their final combination is in `Part02`.
-/

namespace Kolmogorov

open CodedFiniteDistribution
open Nat.Partrec (Code)
open scoped ENNReal

/-- Every length-`n` string is `(n + O(log n), 0)`-stochastic via the uniform
model on its own singleton.  This makes the improved counting bound vacuous once
`alpha` exceeds `n + O(log n)`, where the source `prop:dilemma` no longer
applies (its `i ≤ n` hypothesis fails). -/
theorem isStochastic_singleton_length
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ), x.length = n →
      IsStochastic U x (n + logSlack c n) 0 := by
  obtain ⟨cg, hcg⟩ := singletonSetComplexityGate U hU
  obtain ⟨cl, hcl⟩ := KPPlain_le_length_add_log U hU
  refine ⟨cg + cl + 2, fun x n hn => ?_⟩
  have hcl' :
      KPPlain U x ≤
        ((x.length + 2 * (Nat.bits x.length).length + cl : ℕ) : ENat) := by
    exact_mod_cast hcl x
  have hne : KPPlain U x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hcl'
  obtain ⟨kx, hkx⟩ := ENat.ne_top_iff_exists.mp hne
  rw [hn] at hcl'
  have hkx_le : kx ≤ n + 2 * (Nat.bits n).length + cl := by
    have hcast : (kx : ENat) ≤ ((n + 2 * (Nat.bits n).length + cl : ℕ) : ENat) := by
      rw [hkx]; exact hcl'
    exact_mod_cast hcast
  have hgate :
      setComplexity U {x} (Finset.singleton_nonempty x) ≤
        ((kx + logSlack cg n : ℕ) : ENat) := by
    have h := hcg x n kx hn hkx.symm
    exact_mod_cast h
  refine isStochastic_of_model U x
    (codedUniformOn {x} (Finset.singleton_nonempty x))
    (n + logSlack (cg + cl + 2) n) 0
    (codedUniformOn_isProbability _ _) ?_ ?_
  · have hcomp_eq :
        (codedUniformOn {x} (Finset.singleton_nonempty x)).complexity U =
          setComplexity U {x} (Finset.singleton_nonempty x) := rfl
    rw [hcomp_eq]
    refine le_trans hgate ?_
    have harith : kx + logSlack cg n ≤ n + logSlack (cg + cl + 2) n := by
      unfold logSlack
      nlinarith [hkx_le, Nat.zero_le ((Nat.bits n).length),
        Nat.zero_le (cl * (Nat.bits n).length)]
    exact_mod_cast harith
  · apply deficiencyLe_zero_of_mass_one
    rw [codedUniformOn_mass_of_mem {x} (Finset.singleton_nonempty x) x
      (Finset.mem_singleton_self x)]
    simp

/-- The canonical code of a genuine standard block is prefix-simple given the
corresponding high prefix of finite Omega.  This is the prefix-machine version
of `condK_standardBlock_le_omegaPrefix`, proved directly from the same
partial-recursive selector so that the plain and prefix machines remain
explicitly distinct. -/
theorem KP_standardBlock_given_omegaPrefix
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) :
    ∃ C : ℕ, ∀ (m r : ℕ) (x : BitString)
      (hx : x ∈ standardBlock c m r x),
      let hB : (standardBlock c m r x).Nonempty := ⟨x, hx⟩
      KP U
          (codedUniformOn (standardBlock c m r x) hB).code
          ((omegaFixedCode c m).take (m - r)) ≤
        (logSlack C m : ENat) := by
  have hselectorSwapped :
      Partrec (fun q : BitString × BitString =>
        standardBlockFromOmegaPrefixSelector c q.2 q.1) := by
    let swap : (BitString × BitString) →
        BitString × BitString := fun q => (q.2, q.1)
    have hswap : Computable swap :=
      Computable.pair Computable.snd Computable.fst
    have hcomp :=
      Partrec.comp
        (standardBlockFromOmegaPrefixSelector_partrec c)
        hswap
    exact hcomp.of_eq (fun _ => rfl)
  obtain ⟨Cmap, hmap⟩ :=
    KP_partrec_cond_first_map_le U hU
      (standardBlockFromOmegaPrefixSelector c)
      hselectorSwapped
  obtain ⟨Ccond, hcond⟩ := KP_le_KPPlain U hU
  obtain ⟨Clen, hlen⟩ := KPPlain_le_two_mul_length U hU
  let C := Cmap + Ccond + Clen + 6
  refine ⟨C, fun m r x hx => ?_⟩
  intro hB
  let z := standardBlockAdvice m r
  have hrm : r ≤ m :=
    standardBlock_exponent_le c m r x hx
  have hrBits :
      (Nat.bits r).length ≤ (Nat.bits m).length :=
    length_natBits_mono hrm
  have hrec :
      (codedUniformOn (standardBlock c m r x) hB).code ∈
        standardBlockFromOmegaPrefixSelector c
          ((omegaFixedCode c m).take (m - r)) z := by
    simpa [z, hB] using
      standardBlockFromOmegaPrefixSelector_recovers c m r x hx
  have hadvice :
      KPPlain U z ≤
        ((2 * z.length + Clen : ℕ) : ENat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hlen z
  calc
    KP U
          (codedUniformOn (standardBlock c m r x) hB).code
          ((omegaFixedCode c m).take (m - r))
        ≤ KP U z ((omegaFixedCode c m).take (m - r)) +
            (Cmap : ENat) :=
      hmap z
        (codedUniformOn (standardBlock c m r x) hB).code
        ((omegaFixedCode c m).take (m - r)) hrec
    _ ≤ (KPPlain U z + (Ccond : ENat)) +
          (Cmap : ENat) := by
      gcongr
      exact hcond z ((omegaFixedCode c m).take (m - r))
    _ ≤ ((2 * z.length + Clen : ℕ) : ENat) +
          (Ccond : ENat) + (Cmap : ENat) := by
      gcongr
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        2 * z.length + Clen + Ccond + Cmap ≤
          logSlack C m by
        rw [show z.length =
            2 * (Nat.bits m).length +
              (Nat.bits r).length + 1 by
          simpa [z] using standardBlockAdvice_length m r]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- The high `m-r` bits of finite Omega have prefix complexity at least
`m-r-O(log m)` whenever they select a genuine exponent-`r` standard block.
The proof combines the lower set-complexity clause of `prop_std_pos` with the
explicit prefix reconstruction of that block from the high Omega prefix. -/
theorem KPPlain_omegaPrefix_lower_of_standardBlock
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m r : ℕ) (x : BitString)
      (_hx : x ∈ standardBlock c m r x),
      ((m - r : ℕ) : ENat) ≤
        KPPlain U ((omegaFixedCode c m).take (m - r)) +
          (logSlack C m : ENat) := by
  obtain ⟨Cpos, hpos⟩ :=
    prop_std_pos V U hV hU c hc
  obtain ⟨Csimple, hsimple⟩ :=
    KP_standardBlock_given_omegaPrefix U hU c
  obtain ⟨Cchain, hchain⟩ :=
    KPPlain_le_KPPlain_add_KP U hU
  let C := Cpos + Csimple + Cchain
  refine ⟨C, fun m r x hx => ?_⟩
  let hB : (standardBlock c m r x).Nonempty := ⟨x, hx⟩
  let BCode :=
    (codedUniformOn (standardBlock c m r x) hB).code
  let pref := (omegaFixedCode c m).take (m - r)
  have hlower :
      ((m - r : ℕ) : ENat) ≤
        KPPlain U BCode + (logSlack Cpos m : ENat) := by
    simpa [BCode, hB, setComplexity] using
      (hpos m r x hx).2.2.1
  have hsimple' :
      KP U BCode pref ≤
        (logSlack Csimple m : ENat) := by
    simpa [BCode, pref, hB] using
      hsimple m r x hx
  have hchain' :
      KPPlain U BCode ≤
        KPPlain U pref + KP U BCode pref +
          (Cchain : ENat) :=
    hchain BCode pref
  have habsorb :
      logSlack Csimple m + Cchain +
          logSlack Cpos m ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le (Cchain * (Nat.bits m).length)]
  calc
    ((m - r : ℕ) : ENat)
        ≤ KPPlain U BCode +
            (logSlack Cpos m : ENat) := hlower
    _ ≤ (KPPlain U pref + KP U BCode pref +
          (Cchain : ENat)) +
            (logSlack Cpos m : ENat) := by
      gcongr
    _ ≤ (KPPlain U pref +
          (logSlack Csimple m : ENat) +
          (Cchain : ENat)) +
            (logSlack Cpos m : ENat) := by
      gcongr
    _ = KPPlain U pref +
          ((logSlack Csimple m + Cchain +
            logSlack Cpos m : ℕ) : ENat) := by
      push_cast
      ring
    _ ≤ KPPlain U pref + (logSlack C m : ENat) := by
      gcongr

/-- Compose the already-proved member-to-block and block-to-Omega-prefix
selectors.  Given a standard-block member `x` and the common advice `(m,r)`,
first recover the canonical code of its block and then recover the high
`m-r`-bit prefix of `omegaFixedCode c m`. -/
noncomputable def omegaPrefixFromMemberSelector
    (c : Code) : BitString → BitString →. BitString := fun x z =>
  (standardBlockFromMemberSelector c x z).bind fun BCode =>
    omegaPrefixFromStandardBlockSelector c BCode z

/-- The selector that reads a member of a standard block together with an advice string and
returns candidate prefixes of the halting sequence is partial recursive. -/
theorem omegaPrefixFromMemberSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      omegaPrefixFromMemberSelector c q.1 q.2) := by
  have hblock :
      Partrec (fun q : BitString × BitString =>
        standardBlockFromMemberSelector c q.1 q.2) :=
    standardBlockFromMemberSelector_partrec c
  have homega :
      Partrec₂ (fun (q : BitString × BitString) (BCode : BitString) =>
        omegaPrefixFromStandardBlockSelector c BCode q.2) := by
    let swap : ((BitString × BitString) × BitString) →
        BitString × BitString := fun q => (q.2, q.1.2)
    have hswap : Computable swap :=
      Computable.pair Computable.snd
        (Computable.snd.comp Computable.fst)
    have hcomp :=
      Partrec.comp
        (omegaPrefixFromStandardBlockSelector_partrec c)
        hswap
    exact hcomp.of_eq (fun _ => rfl)
  have hbind := Partrec.bind hblock homega
  exact hbind.of_eq (fun _ => rfl)

/-- From any member of the standard block `standardBlock c m r x`, together with the advice
`standardBlockAdvice m r`, the selector recovers the first `m - r` bits of the halting
sequence `omegaFixedCode c m`. -/
theorem omegaPrefixFromMemberSelector_recovers
    (c : Code) (m r : ℕ) (x : BitString)
    (hx : x ∈ standardBlock c m r x) :
    (omegaFixedCode c m).take (m - r) ∈
      omegaPrefixFromMemberSelector c x
        (standardBlockAdvice m r) := by
  let hB : (standardBlock c m r x).Nonempty := ⟨x, hx⟩
  have hblock :
      (codedUniformOn (standardBlock c m r x) hB).code ∈
        standardBlockFromMemberSelector c x
          (standardBlockAdvice m r) := by
    simpa [hB] using
      standardBlockFromMemberSelector_recovers c m r x hx
  have homega :
      (omegaFixedCode c m).take (m - r) ∈
        omegaPrefixFromStandardBlockSelector c
          (codedUniformOn (standardBlock c m r x) hB).code
          (standardBlockAdvice m r) := by
    simpa [hB] using
      omegaPrefixFromStandardBlockSelector_recovers c m r x hx
  unfold omegaPrefixFromMemberSelector
  exact Part.mem_bind_iff.mpr ⟨_, hblock, homega⟩

/-- The high Omega prefix associated with a genuine standard block is simple
given any member of that block.  All charged advice is the explicit pair
`(m,r)`, whose length is logarithmic in `m` because genuine block exponents
satisfy `r ≤ m`. -/
theorem KP_omegaPrefix_given_standardBlock_member
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) :
    ∃ C : ℕ, ∀ (m r : ℕ) (x : BitString),
      x ∈ standardBlock c m r x →
      KP U ((omegaFixedCode c m).take (m - r)) x ≤
        (logSlack C m : ENat) := by
  have hselectorSwapped :
      Partrec (fun q : BitString × BitString =>
        omegaPrefixFromMemberSelector c q.2 q.1) := by
    let swap : (BitString × BitString) →
        BitString × BitString := fun q => (q.2, q.1)
    have hswap : Computable swap :=
      Computable.pair Computable.snd Computable.fst
    have hcomp :=
      Partrec.comp
        (omegaPrefixFromMemberSelector_partrec c)
        hswap
    exact hcomp.of_eq (fun _ => rfl)
  obtain ⟨Cmap, hmap⟩ :=
    KP_partrec_cond_first_map_le U hU
      (omegaPrefixFromMemberSelector c) hselectorSwapped
  obtain ⟨Ccond, hcond⟩ := KP_le_KPPlain U hU
  obtain ⟨Clen, hlen⟩ := KPPlain_le_two_mul_length U hU
  let C := Cmap + Ccond + Clen + 6
  refine ⟨C, fun m r x hx => ?_⟩
  let z := standardBlockAdvice m r
  have hrm : r ≤ m :=
    standardBlock_exponent_le c m r x hx
  have hrBits :
      (Nat.bits r).length ≤ (Nat.bits m).length :=
    length_natBits_mono hrm
  have hrec :
      (omegaFixedCode c m).take (m - r) ∈
        omegaPrefixFromMemberSelector c x z := by
    simpa [z] using
      omegaPrefixFromMemberSelector_recovers c m r x hx
  have hadvice :
      KPPlain U z ≤
        ((2 * z.length + Clen : ℕ) : ENat) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hlen z
  calc
    KP U ((omegaFixedCode c m).take (m - r)) x
        ≤ KP U z x + (Cmap : ENat) :=
      hmap z ((omegaFixedCode c m).take (m - r)) x hrec
    _ ≤ (KPPlain U z + (Ccond : ENat)) +
          (Cmap : ENat) := by
      gcongr
      exact hcond z x
    _ ≤ ((2 * z.length + Clen : ℕ) : ENat) +
          (Ccond : ENat) + (Cmap : ENat) := by
      gcongr
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast (show
        2 * z.length + Clen + Ccond + Cmap ≤
          logSlack C m by
        rw [show z.length =
            2 * (Nat.bits m).length +
              (Nat.bits r).length + 1 by
          simpa [z] using standardBlockAdvice_length m r]
        dsimp [C]
        unfold logSlack
        nlinarith [Nat.zero_le ((Nat.bits m).length)])

/-- **Stochastic branch of `prop:dilemma`.**  If `x` lies in the exponent-`r`
standard block of the completed bound-`m` list where `m = C(x)` is the *exact*
plain complexity of `x`, then `x` is `((m-r)+O(log n), O(log n))`-stochastic via
the uniform model on that block.  This is the "large block / small gap"
alternative of the source dichotomy: `prop_std_pos` makes the block a model of
`x` with `O(log)` optimality deficiency, which `randomness_optimality` converts
into `O(log)` randomness deficiency.  Consumed by `prop_dilemma` when the gap
`m-r ≤ i`. -/
theorem stochastic_of_standardBlock_at_plainK
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (n m r : ℕ),
      x.length = n →
      plainK V x = (m : ENat) →
      x ∈ standardBlock c m r x →
      IsStochastic U x ((m - r) + logSlack C n) (logSlack C n) := by
  obtain ⟨Cpos, hpos⟩ := prop_std_pos V U hV hU c hc
  obtain ⟨Crand, hrand⟩ := randomness_optimality U hU
  obtain ⟨Cbridge, hbridge⟩ := plain_le_prefix V U hV hU.isPrefixDecompressor
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  obtain ⟨C₁, hC₁⟩ := logSlack_linear_bound Cpos 1 Clen
  refine ⟨C₁ + Cbridge + Crand, fun x n m r hn hm hx => ?_⟩
  -- The setComplexity upper bound (4th conjunct of `prop_std_pos`).
  have hUpperSet :
      setComplexity U (standardBlock c m r x) ⟨x, hx⟩ ≤
        ((m - r + logSlack Cpos m : ℕ) : ENat) := (hpos m r x hx).2.2.2.1
  -- `m = C(x) ≤ |x| + O(1) = n + O(1)`, so the `logSlack` in `m` fits in one in `n`.
  have hmn : m ≤ n + Clen := by
    have h := hlen x
    rw [hm] at h
    have h' : (m : ENat) ≤ ((x.length : ℕ) : ENat) + (Clen : ENat) := h
    rw [hn] at h'
    exact_mod_cast h'
  have hr_le_m : r ≤ m := standardBlock_exponent_le c m r x hx
  have hbridgex : (m : ENat) ≤ KPPlain U x + (Cbridge : ENat) := by
    have h := hbridge x; rw [hm] at h; exact h
  -- The optimality-deficiency arithmetic: `(m-r) + logSlack + r = m + logSlack ≤ C(x) + beta`.
  have h_arith :
      (((m - r) + logSlack Cpos m : ℕ) : ENat) + (r : ENat)
        ≤ KPPlain U x + ((Cbridge + logSlack Cpos m : ℕ) : ENat) := by
    have hsr : ((m - r) + logSlack Cpos m) + r = m + logSlack Cpos m := by omega
    calc (((m - r) + logSlack Cpos m : ℕ) : ENat) + (r : ENat)
        = ((((m - r) + logSlack Cpos m) + r : ℕ) : ENat) := by push_cast; ring
      _ = ((m + logSlack Cpos m : ℕ) : ENat) := by rw [hsr]
      _ = (m : ENat) + (logSlack Cpos m : ENat) := by push_cast; ring
      _ ≤ (KPPlain U x + (Cbridge : ENat)) + (logSlack Cpos m : ENat) := by
          gcongr
      _ = KPPlain U x + ((Cbridge + logSlack Cpos m : ℕ) : ENat) := by push_cast; ac_rfl
  have hsod :
      SetOptimalityDeficiencyLe U (standardBlock c m r x) ⟨x, hx⟩ x
        (Cbridge + logSlack Cpos m) :=
    setOptimalityDeficiencyLe_of_profile hx hUpperSet
      (le_of_eq (card_standardBlock_of_mem c m r x hx)) h_arith
  have hopt :
      OptimalityDeficiencyLe U (codedUniformOn (standardBlock c m r x) ⟨x, hx⟩) x
        (Cbridge + logSlack Cpos m) := hsod
  have hdef :=
    hrand (codedUniformOn (standardBlock c m r x) ⟨x, hx⟩) x
      (Cbridge + logSlack Cpos m) hopt
  -- Assemble `IsStochastic` at the local constants, then absorb into one `logSlack`.
  have hstoch0 :
      IsStochastic U x ((m - r) + logSlack Cpos m)
        ((Cbridge + logSlack Cpos m) + Crand) :=
    isStochastic_of_model U x
      (codedUniformOn (standardBlock c m r x) ⟨x, hx⟩)
      ((m - r) + logSlack Cpos m) ((Cbridge + logSlack Cpos m) + Crand)
      (codedUniformOn_isProbability _ _) hUpperSet hdef
  have hslack : logSlack Cpos m ≤ logSlack C₁ n := by
    calc logSlack Cpos m
        ≤ logSlack Cpos (n + Clen) := logSlack_mono_right Cpos hmn
      _ = logSlack Cpos (1 * n + Clen) := by rw [one_mul]
      _ ≤ logSlack C₁ n := hC₁ n
  refine (hstoch0.mono_alpha ?_).mono_beta ?_
  · have hle : logSlack Cpos m ≤ logSlack (C₁ + Cbridge + Crand) n :=
      hslack.trans (logSlack_mono_left (by omega) n)
    omega
  · have hmul :
        (C₁ + Cbridge + Crand) * (Nat.bits n).length
          = C₁ * (Nat.bits n).length + (Cbridge + Crand) * (Nat.bits n).length := by ring
    have hle : logSlack Cpos m ≤ logSlack C₁ n := hslack
    unfold logSlack at hle ⊢
    omega

/-- **Additive prefix mutual-information symmetry (`I(x:y) ≥ I(y:x) - O(log)`).**
The abstract core of the information branch of `prop:dilemma`, in a numerically
*safe* additive form:
`K(y) + K(x | y) ≤ K(x) + K(y | x) + O(log N)` whenever `K(y) ≤ N`.
The slack depends only on that complexity budget and not on either output
length.  The former length-budget statement is retained below as a corollary.

This replaces the truncated-subtraction leaf proposed in the strategy
(`K(x|y) + (k - a - b - logSlack) ≤ K(x)`), which is **false** in the corner
case where the subtraction bottoms out to `0`: it would force
`K(x|y) ≤ K(x)` with no constant, contradicting the genuine `O(1)` of
`KP_le_KPPlain`.  The additive form above has no such degeneracy and
implies the truncated statement wherever the latter is true.

Derivation: prefix symmetry of information
(`KPPair_symmetryOfInformation_staged`) plus pair symmetry, then convert the
complexity-tagged conditions `⟨x,K(x)⟩`, `⟨y,K(y)⟩` back to the plain conditions
`x`, `y` using `KP_cond_map_le` and `KP_cond_remove_short_info`; the removal cost
is `K(K(y)) = O(log N)`. -/
theorem KP_mutual_symm_le_of_complexity_budget (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x y : BitString) (N : ℕ),
      KPPlain U y ≤ (N : ENat) →
      KPPlain U y + KP U x y ≤
        KPPlain U x + KP U y x + (logSlack C N : ENat) := by
  obtain ⟨cU, cL, hSOI⟩ := KPPair_symmetryOfInformation_staged U hU
  obtain ⟨cS, hSymm⟩ := KPPair_symm U hU
  obtain ⟨cRem, hRem⟩ := KP_cond_remove_short_info U hU
  obtain ⟨cMap, hMap⟩ := KP_cond_map_le U hU decodeFirst decodeFirst_computable
  obtain ⟨cLog, hLog⟩ := KPPlain_natCode_le_log U hU
  let C := cLog + cMap + cU + cS + cL + cRem + 2
  refine ⟨C, fun x y N hyN => ?_⟩
  have hne : KPPlain U y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top N) hyN
  obtain ⟨ky, hky⟩ := ENat.ne_top_iff_exists.mp hne
  have hkyN : ky ≤ N := by
    have h : (ky : ENat) ≤ (N : ENat) := by
      calc (ky : ENat)
        _ = KPPlain U y := hky
        _ ≤ (N : ENat) := hyN
    exact_mod_cast h
  obtain ⟨cTwo, hTwo⟩ := KPPlain_le_two_mul_length U hU
  have hfinx : ∃ k : ℕ, KPPlain U x = (k : ENat) := by
    have hbeq : (2 * (x.length : ENat) + (cTwo : ENat))
        = ((2 * x.length + cTwo : ℕ) : ENat) := by push_cast; ring
    have hne : KPPlain U x ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (hTwo x)
      rw [hbeq]; exact ENat.coe_ne_top _
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨k, hk.symm⟩
  obtain ⟨kx, hkx⟩ := hfinx
  -- SOI, normalized to `pairCode` conditions.
  have h_val_x : HasPrefixComplexityValue U x kx := by
    change (kx : ENat) = KPPlain U x
    exact hkx.symm
  have h_val_y : HasPrefixComplexityValue U y ky := by
    change (ky : ENat) = KPPlain U y
    exact hky
  have hU1 :
      KPPair U x y ≤ KPPlain U x + KP U y (pairCode x (natCode kx)) + (cU : ENat) := by
    have h := (hSOI x y kx h_val_x).1
    simpa [prefixComplexityContext_eq_pairCode] using h
  have hL1 :
      KPPlain U y + KP U x (pairCode y (natCode ky)) ≤ KPPair U y x + (cL : ENat) := by
    have h := (hSOI y x ky h_val_y).2
    simpa [prefixComplexityContext_eq_pairCode] using h
  have hchain :
      KPPlain U y + KP U x (pairCode y (natCode ky))
        ≤ KPPlain U x + KP U y (pairCode x (natCode kx)) + ((cU + cS + cL : ℕ) : ENat) := by
    calc KPPlain U y + KP U x (pairCode y (natCode ky))
        ≤ KPPair U y x + (cL : ENat) := hL1
      _ ≤ (KPPair U x y + (cS : ENat)) + (cL : ENat) := by gcongr; exact hSymm y x
      _ ≤ ((KPPlain U x + KP U y (pairCode x (natCode kx)) + (cU : ENat)) + (cS : ENat))
            + (cL : ENat) := by gcongr
      _ = KPPlain U x + KP U y (pairCode x (natCode kx)) + ((cU + cS + cL : ℕ) : ENat) := by
            push_cast; abel
  have hrem :
      KP U x y ≤ KP U x (pairCode y (natCode ky)) + KPPlain U (natCode ky) + (cRem : ENat) :=
    hRem x y (natCode ky)
  have hmap :
      KP U y (pairCode x (natCode kx)) ≤ KP U y x + (cMap : ENat) := by
    have h := hMap y (pairCode x (natCode kx))
    simpa [decodeFirst_pairCode] using h
  have hlog :
      KPPlain U (natCode ky) ≤ ((2 * (Nat.bits ky).length + cLog : ℕ) : ENat) := by
    have h := hLog ky; exact_mod_cast h
  -- Combine the monotone chain, keeping `K(natCode ky)` and the constants separate.
  have hcombine :
      KPPlain U y + KP U x y ≤
        KPPlain U x + KP U y x + KPPlain U (natCode ky)
          + ((cMap + cU + cS + cL + cRem : ℕ) : ENat) := by
    calc KPPlain U y + KP U x y
        ≤ KPPlain U y
            + (KP U x (pairCode y (natCode ky)) + KPPlain U (natCode ky) + (cRem : ENat)) := by
          gcongr
      _ = (KPPlain U y + KP U x (pairCode y (natCode ky)))
            + KPPlain U (natCode ky) + (cRem : ENat) := by abel
      _ ≤ (KPPlain U x + KP U y (pairCode x (natCode kx)) + ((cU + cS + cL : ℕ) : ENat))
            + KPPlain U (natCode ky) + (cRem : ENat) := by gcongr
      _ ≤ (KPPlain U x + (KP U y x + (cMap : ENat)) + ((cU + cS + cL : ℕ) : ENat))
            + KPPlain U (natCode ky) + (cRem : ENat) := by gcongr
      _ = KPPlain U x + KP U y x + KPPlain U (natCode ky)
            + ((cMap + cU + cS + cL + cRem : ℕ) : ENat) := by push_cast; abel
  have habsorb :
      2 * (Nat.bits ky).length + cLog + (cMap + cU + cS + cL + cRem) ≤ logSlack C N := by
    have hk_len : (Nat.bits ky).length ≤ (Nat.bits N).length := length_natBits_mono hkyN
    unfold logSlack
    dsimp [C]
    nlinarith [Nat.zero_le (Nat.bits N).length]
  have htail :
      KPPlain U (natCode ky) + ((cMap + cU + cS + cL + cRem : ℕ) : ENat)
        ≤ (logSlack C N : ENat) := by
    calc KPPlain U (natCode ky) + ((cMap + cU + cS + cL + cRem : ℕ) : ENat)
        ≤ ((2 * (Nat.bits ky).length + cLog : ℕ) : ENat)
            + ((cMap + cU + cS + cL + cRem : ℕ) : ENat) := by gcongr
      _ = ((2 * (Nat.bits ky).length + cLog + (cMap + cU + cS + cL + cRem) : ℕ) : ENat) := by
          push_cast; ring
      _ ≤ (logSlack C N : ENat) := by exact_mod_cast habsorb
  calc KPPlain U y + KP U x y
      ≤ KPPlain U x + KP U y x + KPPlain U (natCode ky)
          + ((cMap + cU + cS + cL + cRem : ℕ) : ENat) := hcombine
    _ = KPPlain U x + KP U y x
          + (KPPlain U (natCode ky) + ((cMap + cU + cS + cL + cRem : ℕ) : ENat)) := by abel
    _ ≤ KPPlain U x + KP U y x + (logSlack C N : ENat) := by gcongr

/-- Length-budget corollary of `KP_mutual_symm_le_of_complexity_budget`. -/
theorem KP_mutual_symm_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x y : BitString) (N : ℕ),
      y.length ≤ N →
      KPPlain U y + KP U x y ≤
        KPPlain U x + KP U y x + (logSlack C N : ENat) := by
  obtain ⟨C_budget, hC_budget⟩ := KP_mutual_symm_le_of_complexity_budget U hU
  obtain ⟨cTwo, hTwo⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨C, hC⟩ := logSlack_linear_bound C_budget 2 cTwo
  use C
  intro x y N hyN
  have hy : KPPlain U y ≤ ((2 * N + cTwo : ℕ) : ENat) := by
    calc KPPlain U y
      _ ≤ 2 * (y.length : ENat) + (cTwo : ENat) := by exact_mod_cast hTwo y
      _ ≤ 2 * (N : ENat) + (cTwo : ENat) := by gcongr
      _ = ((2 * N + cTwo : ℕ) : ENat) := by push_cast; ring
  calc KPPlain U y + KP U x y
    _ ≤ KPPlain U x + KP U y x + (logSlack C_budget (2 * N + cTwo) : ENat) :=
        hC_budget x y (2 * N + cTwo) hy
    _ ≤ KPPlain U x + KP U y x + (logSlack C N : ENat) := by
        have h_bound : logSlack C_budget (2 * N + cTwo) ≤ logSlack C N := hC N
        gcongr

/-- The information branch supplied by a standard block, in the stable additive
form.  If `x` lies in an exponent-`r` block at plain bound `m`, then conditioning
on the corresponding high `m-r` bits of finite Omega saves `m-r` bits, up to one
uniform logarithmic term on the right.  Keeping the slack additive is essential:
moving a truncated slack to the left would incorrectly erase the fixed
conditioning overhead when the subtraction is zero. -/
theorem KP_information_of_standardBlock_additive
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (x : BitString) (m r : ℕ),
      x ∈ standardBlock c m r x →
      KP U x ((omegaFixedCode c m).take (m - r)) +
          ((m - r : ℕ) : ENat) ≤
        KPPlain U x + (logSlack C m : ENat) := by
  obtain ⟨Clower, hlower⟩ :=
    KPPlain_omegaPrefix_lower_of_standardBlock V U hV hU c hc
  obtain ⟨Csimple, hsimple⟩ :=
    KP_omegaPrefix_given_standardBlock_member U hU c
  obtain ⟨Csymm, hsymm⟩ := KP_mutual_symm_le U hU
  let C := Clower + Csimple + Csymm
  refine ⟨C, fun x m r hx => ?_⟩
  let pref := (omegaFixedCode c m).take (m - r)
  have hprefLength : pref.length ≤ m := by
    dsimp [pref]
    exact (List.length_take_le _ _).trans (Nat.sub_le m r)
  have hlower' :
      ((m - r : ℕ) : ENat) ≤
        KPPlain U pref + (logSlack Clower m : ENat) := by
    simpa [pref] using hlower m r x hx
  have hsimple' :
      KP U pref x ≤ (logSlack Csimple m : ENat) := by
    simpa [pref] using hsimple m r x hx
  have hsymm' :
      KPPlain U pref + KP U x pref ≤
        KPPlain U x + KP U pref x +
          (logSlack Csymm m : ENat) :=
    hsymm x pref m hprefLength
  have habsorb :
      logSlack Clower m + logSlack Csimple m +
          logSlack Csymm m ≤
        logSlack C m := by
    dsimp [C]
    unfold logSlack
    ring_nf
    exact le_rfl
  calc
    KP U x pref + ((m - r : ℕ) : ENat)
        ≤ KP U x pref +
            (KPPlain U pref +
              (logSlack Clower m : ENat)) := by
          gcongr
    _ = (KPPlain U pref + KP U x pref) +
          (logSlack Clower m : ENat) := by abel
    _ ≤ (KPPlain U x + KP U pref x +
          (logSlack Csymm m : ENat)) +
          (logSlack Clower m : ENat) := by
        gcongr
    _ ≤ (KPPlain U x +
          (logSlack Csimple m : ENat) +
          (logSlack Csymm m : ENat)) +
          (logSlack Clower m : ENat) := by
        gcongr
    _ = KPPlain U x +
          ((logSlack Clower m + logSlack Csimple m +
            logSlack Csymm m : ℕ) : ENat) := by
        push_cast
        abel
    _ ≤ KPPlain U x + (logSlack C m : ENat) := by
      gcongr

/-- Conditions may be replaced by anything a partial recursive map computes from them: for a
partial recursive `f` there is a constant `C` with `KP U x y ≤ KP U x z + C` whenever `z` is
a value of `f y`. -/
theorem KP_cond_partrec_map_le
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString →. BitString) (hf : Partrec f) :
    ∃ C : ℕ, ∀ x y z, z ∈ f y →
      KP U x y ≤ KP U x z + (C : ENat) := by
  set D : Map := fun pr =>
    (f pr.2).bind fun z => U (pr.1, z) with hDdef
  have hD_decomp : isDecompressor D := by
    have hfirst : Partrec (fun pr : BitString × BitString => f pr.2) :=
      hf.comp Computable.snd
    have hsecond :
        Partrec₂ (fun (pr : BitString × BitString) (z : BitString) =>
          U (pr.1, z)) := by
      exact hU.isDecompressor.comp
        ((Computable.fst.comp Computable.fst).pair Computable.snd)
    exact Partrec.bind hfirst hsecond
  have hD_prefix : IsPrefixMachine D := by
    intro y p hp q hq hpq
    obtain ⟨xp, hxp⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨zp, hzp, hpU⟩ := Part.mem_bind_iff.mp hxp
    obtain ⟨xq, hxq⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨zq, hzq, hqU⟩ := Part.mem_bind_iff.mp hxq
    have hz : zp = zq := Part.mem_unique hzp hzq
    subst zq
    exact hU.isPrefixMachine zp
      (Part.dom_iff_mem.mpr ⟨xp, hpU⟩)
      (Part.dom_iff_mem.mpr ⟨xq, hqU⟩) hpq
  have hD : IsPrefixDecompressor D :=
    ⟨hD_decomp, hD_prefix⟩
  obtain ⟨C, hC⟩ := hU.invariance hD
  refine ⟨C, fun x y z hz => ?_⟩
  by_cases hx : KP U x z = ⊤
  · rw [hx, top_add]
    exact le_top
  · obtain ⟨p, hp, hpLength⟩ :=
      exists_program_of_KP_ne_top hx
    have hpD : produces D p y x := by
      simp only [produces, hDdef]
      exact Part.mem_bind_iff.mpr ⟨z, hz, hp⟩
    calc
      KP U x y ≤ KP D x y + (C : ENat) := hC x y
      _ ≤ (p.length : ENat) + (C : ENat) := by
        gcongr
        exact KP_le_programLength_of_produces hpD
      _ = KP U x z + (C : ENat) := by rw [hpLength]

/-- If a partial-recursive selector obtains a new condition `z` from the
current condition `y` and explicit advice `p`, then changing the condition from
`y` to `z` costs at most the prefix complexity of `p`, plus a fixed constant. -/
theorem KP_cond_partrec_advice_map_le
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (g : BitString → BitString →. BitString)
    (hg : Partrec (fun q : BitString × BitString =>
      g q.1 q.2)) :
    ∃ C : ℕ, ∀ x y p z, z ∈ g y p →
      KP U x y ≤
        KP U x z + KPPlain U p + (C : ENat) := by
  let f : BitString →. BitString := fun s =>
    g (decodeFirst s) (decodeSecond s)
  have hf : Partrec f := by
    exact hg.comp
      (decodeFirst_computable.pair
        decodeSecond_computable)
  obtain ⟨Cmap, hmap⟩ :=
    KP_cond_partrec_map_le U hU f hf
  obtain ⟨Cremove, hremove⟩ :=
    KP_cond_remove_short_info U hU
  refine ⟨Cmap + Cremove, fun x y p z hz => ?_⟩
  have hz' :
      z ∈ f (pairCode y p) := by
    simpa [f, decodeFirst_pairCode,
      decodeSecond_pairCode] using hz
  calc
    KP U x y ≤ KP U x (pairCode y p) +
        KPPlain U p + (Cremove : ENat) :=
      hremove x y p
    _ ≤ (KP U x z + (Cmap : ENat)) +
        KPPlain U p + (Cremove : ENat) := by
      gcongr
      exact hmap x (pairCode y p) z hz'
    _ = KP U x z + KPPlain U p +
        ((Cmap + Cremove : ℕ) : ENat) := by
      push_cast
      abel

/-- A short plain conditional program for a new condition may be supplied as
explicit advice to a prefix program using the old condition.  The factor two
comes from the elementary self-delimiting encoding of that plain program. -/
theorem KP_cond_change_of_condK_le
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ x y z (q : ℕ),
      condK V z y ≤ (q : ENat) →
      KP U x y ≤
        KP U x z + ((2 * q + C : ℕ) : ENat) := by
  let g : BitString → BitString →. BitString :=
    fun y p => V (p, y)
  have hg :
      Partrec (fun q : BitString × BitString =>
        g q.1 q.2) := by
    exact hV.1.comp
      (Computable.snd.pair Computable.fst)
  obtain ⟨Cmap, hmap⟩ :=
    KP_cond_partrec_advice_map_le U hU g hg
  obtain ⟨Clen, hlen⟩ :=
    KPPlain_le_two_mul_length U hU
  refine ⟨Clen + Cmap, fun x y z q hq => ?_⟩
  obtain ⟨p, hpLength, hp⟩ :=
    (condK_le_iff V z y q).mp hq
  have hz : z ∈ g y p := by
    exact hp
  calc
    KP U x y ≤
        KP U x z + KPPlain U p +
          (Cmap : ENat) :=
      hmap x y p z hz
    _ ≤ KP U x z +
        ((2 * p.length + Clen : ℕ) : ENat) +
          (Cmap : ENat) := by
      gcongr
      exact hlen p
    _ ≤ KP U x z +
        ((2 * q + Clen : ℕ) : ENat) +
          (Cmap : ENat) := by
      have hnat :
          2 * p.length + Clen ≤ 2 * q + Clen := by
        change p.length ≤ q at hpLength
        omega
      have henat :
          ((2 * p.length + Clen : ℕ) : ENat) ≤
            ((2 * q + Clen : ℕ) : ENat) := by
        exact_mod_cast hnat
      calc
        KP U x z +
              ((2 * p.length + Clen : ℕ) : ENat) +
              (Cmap : ENat) =
            (Cmap : ENat) + (KP U x z +
              ((2 * p.length + Clen : ℕ) : ENat)) := by
                abel
        _ ≤ (Cmap : ENat) + (KP U x z +
              ((2 * q + Clen : ℕ) : ENat)) := by
                gcongr
        _ = KP U x z +
              ((2 * q + Clen : ℕ) : ENat) +
              (Cmap : ENat) := by
                abel
    _ = KP U x z +
        ((2 * q + (Clen + Cmap) : ℕ) : ENat) := by
      push_cast
      abel

/-- A prefix of a later fixed point of the omega code is described from an earlier one within a
logarithmic slack, whether the later index is below or above the earlier one.

The four quantified hypotheses are interface assumptions about an arbitrary conditional machine
`V` and an arbitrary code `c`, each with its own constant, and the sole consumer
`KP_omegaPrefix_condition_transport` proves all four for the optimal machine: `heq` is the
two-way omega-prefix equivalence (`prop_omega_equivalence`, `Ceq`), `htake` the cost of a prefix
given the string (`condK_take_le`, `Ctake`), `htrans` the conditional chain rule
(`condK_trans_nat`, `Ctrans`), and `hclose` the two-way closeness of two fixed points within
`logSlack D` of each other (`omegaFixedCode_close_logSlack`, `Cclose`). -/
private lemma condK_takeOmega_le_logSlack {V : Map} {c : Code} {Ceq Ctake Ctrans Cclose D : ℕ}
    (heq : ∀ m k : ℕ, k ≤ m →
      condK V (omegaFixedCode c k) ((omegaFixedCode c m).take k) ≤ (logSlack Ceq m : ENat) ∧
      condK V ((omegaFixedCode c m).take k) (omegaFixedCode c k) ≤ (logSlack Ceq m : ENat))
    (htake : ∀ (y : BitString) (k : ℕ),
      condK V (y.take k) y ≤ (((Nat.bits k).length + Ctake : ℕ) : ENat))
    (htrans : ∀ (x y z : BitString) (a b : ℕ),
      condK V y x ≤ (a : ENat) → condK V z y ≤ (b : ENat) →
      condK V z x ≤ ((2 * a + b + Ctrans : ℕ) : ENat))
    (hclose : ∀ (m a b : ℕ), a ≤ m + logSlack D m → b ≤ m + logSlack D m →
      a ≤ b + logSlack D m → b ≤ a + logSlack D m →
      condK V (omegaFixedCode c a) (omegaFixedCode c b) ≤ (logSlack Cclose m : ENat) ∧
      condK V (omegaFixedCode c b) (omegaFixedCode c a) ≤ (logSlack Cclose m : ENat))
    (n m k : ℕ) (hkm : k ≤ m) (hmn : m ≤ n + D) :
    condK V ((omegaFixedCode c m).take k) (omegaFixedCode c n) ≤
      (logSlack (2 * Ceq + 5 + 5 * Ctake + 3 * Ctrans +
        (2 * Cclose + (Nat.bits D).length + 1 + Ctake + Ctrans)) n : ENat) := by
  let Csmall := 2 * Ceq + 5 + 5 * Ctake + 3 * Ctrans
  let Cbig := 2 * Cclose + (Nat.bits D).length + 1 + Ctake + Ctrans
  let Ccond := Csmall + Cbig
  let omegaN := omegaFixedCode c n
  let omegaM := omegaFixedCode c m
  let target := omegaM.take k
  change condK V target omegaN ≤ (logSlack Ccond n : ENat)
  by_cases hmnOrder : m ≤ n
  · let prefixM := omegaN.take m
    have htakeM : condK V prefixM omegaN ≤ (((Nat.bits m).length + Ctake : ℕ) : ENat) := by
      simpa [prefixM, omegaN] using htake omegaN m
    have heqM : condK V omegaM prefixM ≤ (logSlack Ceq n : ENat) := by
      simpa [omegaM, omegaN, prefixM] using
        (heq n m hmnOrder).1
    have homegaM :
        condK V omegaM omegaN ≤
          ((2 * ((Nat.bits m).length + Ctake) +
            logSlack Ceq n + Ctrans : ℕ) : ENat) :=
      htrans omegaN prefixM omegaM
        ((Nat.bits m).length + Ctake)
        (logSlack Ceq n) htakeM heqM
    have htakeK : condK V target omegaM ≤ (((Nat.bits k).length + Ctake : ℕ) : ENat) := by
      simpa [target, omegaM] using htake omegaM k
    have hcomposed :=
      htrans omegaN omegaM target
        (2 * ((Nat.bits m).length + Ctake) +
          logSlack Ceq n + Ctrans)
        ((Nat.bits k).length + Ctake)
        homegaM htakeK
    have hmBits : (Nat.bits m).length ≤ (Nat.bits n).length := length_natBits_mono hmnOrder
    have hkBits : (Nat.bits k).length ≤ (Nat.bits n).length :=
      length_natBits_mono (hkm.trans hmnOrder)
    have hbudget :
        2 * (2 * ((Nat.bits m).length + Ctake) +
            logSlack Ceq n + Ctrans) +
            ((Nat.bits k).length + Ctake) + Ctrans ≤
          logSlack Ccond n := by
      have hsmall :
          2 * (2 * ((Nat.bits m).length + Ctake) +
              logSlack Ceq n + Ctrans) +
              ((Nat.bits k).length + Ctake) + Ctrans ≤
            logSlack Csmall n := by
        dsimp [Csmall]
        unfold logSlack
        nlinarith
          [Nat.zero_le ((Nat.bits n).length),
            Nat.zero_le (Ceq * (Nat.bits n).length)]
      exact hsmall.trans
        (logSlack_mono_left
          (show Csmall ≤ Ccond by
            dsimp [Ccond]
            omega) n)
    exact hcomposed.trans (by exact_mod_cast hbudget)
  · have hnmOrder : n ≤ m :=
      Nat.le_of_lt (Nat.lt_of_not_ge hmnOrder)
    have hDSlack : D ≤ logSlack D n := by
      unfold logSlack
      nlinarith
        [Nat.zero_le (D * (Nat.bits n).length)]
    have hmSlack :
        m ≤ n + logSlack D n :=
      hmn.trans (Nat.add_le_add_left hDSlack n)
    have hnSlack :
        n ≤ m + logSlack D n := by omega
    have hcloseMN :
        condK V omegaM omegaN ≤
          (logSlack Cclose n : ENat) := by
      simpa [omegaM, omegaN] using
        (hclose n m n
          hmSlack
          (Nat.le_add_right n (logSlack D n))
          hmSlack
          hnSlack).1
    have htakeK : condK V target omegaM ≤ (((Nat.bits k).length + Ctake : ℕ) : ENat) := by
      simpa [target, omegaM] using htake omegaM k
    have hcomposed :=
      htrans omegaN omegaM target
        (logSlack Cclose n)
        ((Nat.bits k).length + Ctake)
        hcloseMN htakeK
    have hkND : k ≤ n + D :=
      hkm.trans hmn
    have hkBits :
        (Nat.bits k).length ≤
          (Nat.bits n).length +
            (Nat.bits D).length + 1 := by
      exact (length_natBits_mono hkND).trans
        (length_natBits_add_le n D)
    have hbudget :
        2 * logSlack Cclose n +
            ((Nat.bits k).length + Ctake) + Ctrans ≤
          logSlack Ccond n := by
      have hbig :
          2 * logSlack Cclose n +
              ((Nat.bits k).length + Ctake) + Ctrans ≤
            logSlack Cbig n := by
        dsimp [Cbig]
        unfold logSlack
        nlinarith
          [Nat.zero_le ((Nat.bits n).length),
            Nat.zero_le
              (Cclose * (Nat.bits n).length)]
      exact hbig.trans
        (logSlack_mono_left
          (show Cbig ≤ Ccond by
            dsimp [Ccond]
            omega) n)
    exact hcomposed.trans (by exact_mod_cast hbudget)

/-- Conditioning on the halting sequence `omegaFixedCode c n` costs at most `logSlack C n` more
than conditioning on the first `k` bits of `omegaFixedCode c m`, provided `k ≤ m` and
`m ≤ n + D`. -/
theorem KP_omegaPrefix_condition_transport
    (V U : Map) (hV : isOptimalConditional V)
    (hU : IsOptimalPrefixConditional U)
    (c : Code) (hc : IsCodeFor c V) (D : ℕ) :
    ∃ C : ℕ, ∀ x n m k,
      k ≤ m → m ≤ n + D →
      KP U x (omegaFixedCode c n) ≤
        KP U x ((omegaFixedCode c m).take k) +
          (logSlack C n : ENat) := by
  obtain ⟨Ceq, heq⟩ := prop_omega_equivalence V hV c hc
  obtain ⟨Ctake, htake⟩ := condK_take_le V hV
  obtain ⟨Ctrans, htrans⟩ := condK_trans_nat V hV
  obtain ⟨Cclose, hclose⟩ := omegaFixedCode_close_logSlack V hV c hc D
  obtain ⟨Cchange, hchange⟩ := KP_cond_change_of_condK_le V U hV hU
  let Csmall := 2 * Ceq + 5 + 5 * Ctake + 3 * Ctrans
  let Cbig := 2 * Cclose + (Nat.bits D).length + 1 + Ctake + Ctrans
  let Ccond := Csmall + Cbig
  let C := 2 * Ccond + Cchange
  refine ⟨C, fun x n m k hkm hmn => ?_⟩
  let omegaN := omegaFixedCode c n
  let target := (omegaFixedCode c m).take k
  have hchanged := hchange x omegaN target (logSlack Ccond n)
    (condK_takeOmega_le_logSlack heq htake htrans hclose n m k hkm hmn)
  have hfinal : 2 * logSlack Ccond n + Cchange ≤ logSlack C n := by
    dsimp [C]
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits n).length),
      Nat.zero_le (Cchange * (Nat.bits n).length)]
  calc
    KP U x (omegaFixedCode c n) = KP U x omegaN := rfl
    _ ≤ KP U x target + ((2 * logSlack Ccond n + Cchange : ℕ) : ENat) := hchanged
    _ ≤ KP U x target + (logSlack C n : ENat) := by gcongr
    _ = KP U x ((omegaFixedCode c m).take k) + (logSlack C n : ENat) := rfl

/-- Arithmetic in `ℕ∞`: from `a + k ≤ b + S` and `S + i ≤ k` one gets `a + (i - T) ≤ b`, the
truncated subtraction being taken in `ℕ`. -/
theorem ENat_add_truncated_le_of_add_gap
    (a b : ENat) (i k S T : ℕ)
    (hinfo : a + (k : ENat) ≤ b + (S : ENat))
    (hgap : S + i ≤ k) :
    a + ((i - T : ℕ) : ENat) ≤ b := by
  cases b with
  | top => exact le_top
  | coe bn =>
    cases a with
    | top =>
      have h1 : (⊤ : ENat) ≤ (bn : ENat) + (S : ENat) := by
        calc ⊤ = (⊤ : ENat) + (k : ENat) := by rw [top_add]
          _ ≤ (bn : ENat) + (S : ENat) := hinfo
      have h2 : ((bn + S : ℕ) : ENat) = ⊤ := top_le_iff.mp (by exact_mod_cast h1)
      exact False.elim (ENat.coe_ne_top _ h2)
    | coe an =>
      have hinfo_nat : an + k ≤ bn + S := by
        exact_mod_cast hinfo
      have hgoal : an + (i - T) ≤ bn := by omega
      exact_mod_cast hgoal

end Kolmogorov
