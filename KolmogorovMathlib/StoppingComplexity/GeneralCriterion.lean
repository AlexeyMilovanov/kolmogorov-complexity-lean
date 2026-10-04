import KolmogorovMathlib.StoppingComplexity.Diagonalization
import KolmogorovMathlib.StoppingComplexity.AdmissibleDiscount
import KolmogorovMathlib.StoppingComplexity.UpperBound

/-!
# The general criterion: the stopping gap exceeds every admissible discount

Blueprint 01 F0 (Target GENERAL) and F5 (the central interface RAW), and 04 §4 (Theorem E′ in
its explicit quantified form, with its infinitude clause).

For an admissible discount `f` (`IsAdmissibleDiscount`: total computable, nondecreasing, R1,
SHIFT, DIV) the generic diagonalization theorem, applied to the reply bound `b c n = n + f n + c`
and the constructed variable-discount family `variableWordFamily f hf`, gives RAW: ONE natural
constant `a`, quantified before the tag `c`, and for every `c` a string `z` extending the tag
`natCode c = 1^c 0` and an exponent `n` with `K_stop(z) > n + f(n) + c` and
`M_stop(z) ≥ 2^{-(n+a)}`, stated in `ℕ∞` and `ℝ≥0∞` without logarithms. The transfer of 03 §8
and the integer-ceiling shift (module `MassDepth`) turn RAW into the excess
`g(z) > f(⌈m(z)⌉) + c - a - D_a`; the local upper bound U-local (module `UpperBound`) moves the
witnesses into the domain of large mass depth. This gives Theorem E′ (`m(z) > T`), its
infinitude clause, and Target GENERAL in the F0 form (`m(z) ≥ max(16, T)`).

All four statements are about the fixed universal stopping machine (`univStopComplexity`,
`univStopProb`, `massDepth`, `stoppingGap`). Their only hypothesis is `IsAdmissibleDiscount f` on
the free discount `f`, as in the blueprint; no strategy, computability of a strategy,
realization, horizon search or domination constant is a hypothesis.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **RAW**, the central interface: for an admissible discount `f` there is ONE natural constant
`a`, quantified before the tag `c`, such that for every `c` some string `z` extending the tag
`natCode c = 1^c 0` and some exponent `n` satisfy `K_stop(z) > n + f(n) + c` (in `ℕ∞`) and
`M_stop(z) ≥ 2^{-(n+a)}` (in `ℝ≥0∞`). The constant may depend on `f` and on the whole strategy
family, never on `c`. It is the generic diagonalization theorem for the reply bound
`b c n = n + f n + c` and the constructed family `variableWordFamily f hf`.
Blueprint F5 (RAW). -/
theorem raw_inequality (f : ℕ → ℕ) (hf : IsAdmissibleDiscount f) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ (z : BitString) (n : ℕ), natCode c <+: z ∧
      (n + f n + c : ℕ∞) < univStopComplexity z ∧ (2 : ℝ≥0∞)⁻¹ ^ (n + a) ≤ univStopProb z := by
  have hb : Computable₂ (fun c n => n + f n + c) := by
    exact Computable.of_eq (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.snd (hf.computable.comp Computable.snd))
      Computable.fst) (by intro ⟨c, n⟩; rfl)
  obtain ⟨a, ha⟩ := diagonalization (fun c n => n + f n + c) hb (variableWordFamily f hf)
    (variableWordFamily_computable hf) _ (variableWordFamily_winning hf)
  use a
  intro c
  obtain ⟨x, n, _, hk, hm⟩ := ha c
  use natCode c ++ x, n
  exact ⟨List.prefix_append _ _, hk, hm⟩

/-- **Theorem E′** (explicit quantified form): for an admissible discount `f`, every natural `q`
and every real `T ≥ 0` there is a string `z` with mass depth `m(z) > T` and stopping gap
`g(z) > f(⌈m(z)⌉) + q`. Part 1 (the excess `g(z_c) > f(⌈m(z_c)⌉) + c - a - D_a`) is RAW with the
03 §8 transfer and the integer-ceiling shift; part 2 (escaping `m ≤ T`) is U-local.
Blueprint 04 Theorem E′. -/
theorem stoppingGap_exceeds_discount (f : ℕ → ℕ) (hf : IsAdmissibleDiscount f) (q : ℕ) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ z : BitString, T < massDepth z ∧ (f ⌈massDepth z⌉₊ : ℝ) + q < stoppingGap z := by
  have _ := hT
  obtain ⟨a, ha⟩ := raw_inequality f hf
  obtain ⟨D, hD⟩ := hf.shift a
  obtain ⟨G, hG⟩ := exists_stoppingGap_bound_of_massDepth_le T
  have c_exists : ∃ c : ℕ, (max G 0 + a + q + D : ℝ) < c :=
    exists_nat_gt (max G 0 + a + q + D)
  obtain ⟨c, hc⟩ := c_exists
  obtain ⟨z, n, _, hk, hm⟩ := ha c
  have h_gap : (f ⌈massDepth z⌉₊ : ℝ) + c - a - D < stoppingGap z :=
    stoppingGap_gt_discount_ceil hf.mono hD hk hm
  have h_gap2 : (f ⌈massDepth z⌉₊ : ℝ) + q + max G 0 < stoppingGap z := by
    linarith
  have hG_gap : G < stoppingGap z := by
    have h_f : 0 ≤ (f ⌈massDepth z⌉₊ : ℝ) := Nat.cast_nonneg _
    have h_max : G ≤ max G 0 := le_max_left G 0
    linarith
  have h_massDepth : T < massDepth z := by
    by_contra h_contra
    push Not at h_contra
    have hG_gap_contra := hG z h_contra
    linarith
  use z
  refine ⟨h_massDepth, ?_⟩
  calc
    (f ⌈massDepth z⌉₊ : ℝ) + q ≤ (f ⌈massDepth z⌉₊ : ℝ) + q + max G 0 := by
      have : (0 : ℝ) ≤ max G 0 := le_max_right G 0
      linarith
    _ < stoppingGap z := h_gap2

/-- Infinitude clause of Theorem E′: for an admissible discount `f` and every natural `q`,
infinitely many distinct strings `z` satisfy `g(z) > f(⌈m(z)⌉) + q` (the mass depths of finitely
many strings would have a maximum, contradicted by E′ with a larger cutoff).
Blueprint 04 Theorem E′ ("infinitely many distinct strings satisfy the second inequality"). -/
theorem stoppingGap_exceeds_discount_infinite (f : ℕ → ℕ) (hf : IsAdmissibleDiscount f)
    (q : ℕ) : {z : BitString | (f ⌈massDepth z⌉₊ : ℝ) + q < stoppingGap z}.Infinite := by
  intro h_fin
  have h_bdd : BddAbove
      (massDepth '' {z : BitString | (f ⌈massDepth z⌉₊ : ℝ) + q < stoppingGap z}) :=
    Set.Finite.bddAbove (Set.Finite.image massDepth h_fin)
  obtain ⟨T, hT_bdd⟩ := h_bdd
  obtain ⟨z, h_mass, h_gap⟩ := stoppingGap_exceeds_discount f hf q
    (T := max T 0) (le_max_right T 0)
  have h_mem : z ∈ {z : BitString | (f ⌈massDepth z⌉₊ : ℝ) + q < stoppingGap z} :=
    h_gap
  have h_le : massDepth z ≤ T := hT_bdd (Set.mem_image_of_mem massDepth h_mem)
  have h_T_le : T ≤ max T 0 := le_max_left T 0
  linarith

/-- **Target GENERAL**: for an admissible discount `f` (total computable, nondecreasing, R1,
SHIFT, DIV), every natural `c` and every real `T`, some string `z` has mass depth
`m(z) ≥ max(16, T)` and stopping gap `g(z) > f(⌈m(z)⌉) + c`. Stated unconditionally about the
fixed universal machine, in the F0 form `max 16 T ≤ m(z)`; it is Theorem E′ at the cutoff
`max(16, T)`. Blueprint F0 Target GENERAL. -/
theorem stoppingGap_exceeds_admissibleDiscount (f : ℕ → ℕ) (hf : IsAdmissibleDiscount f)
    (c : ℕ) (T : ℝ) :
    ∃ z : BitString, max 16 T ≤ massDepth z ∧ (f ⌈massDepth z⌉₊ : ℝ) + c < stoppingGap z := by
  obtain ⟨z, h_mass, h_gap⟩ := stoppingGap_exceeds_discount f hf c (T := max 16 T) (by
    calc
      0 ≤ 16 := by norm_num
      _ ≤ max 16 T := le_max_left 16 T)
  use z
  exact ⟨le_of_lt h_mass, h_gap⟩

end Kolmogorov
