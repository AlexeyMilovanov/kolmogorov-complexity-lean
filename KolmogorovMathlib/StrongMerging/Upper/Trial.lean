import KolmogorovMathlib.StrongMerging.Upper.CoreDecoders
import KolmogorovMathlib.StrongMerging.Upper.Profiles
import KolmogorovMathlib.StrongMerging.Upper.Tradeoff

/-!
# Finite trials and quadratic stopping (blueprint T01, T02, T03)

`sublinear-merging.tex`, subsection "Adjacent comparisons and finite trial algorithms"
(tex ~834–902) and the blueprint section `bp-upper-portfolio` (tex ~3943–4024).

* **T01 (`UpperTrial`).**  `trialRun P L big z` is the finite trial on a shape `P` with step
  `L = L_r`: if `min a b ≤ L` it returns the fallback `big` (the larger-bucket original model,
  `largerModel`) with stopping index `0`; a missing initial core gives `(big, 1)`; otherwise the
  loop `trialLoop` runs from state `j = 1` with the core `F_L`.  At state `j` (`s = jL`) it
  returns `(big, j)` if `min a b ≤ s + L` or the core `F_{s+L}` is missing, returns `(F_s, j)` if
  `|F_s| ≤ 2^s |F_{s+L}|` (exact integer comparison) and advances otherwise.  The fuel
  `min a b + 1` is never exhausted before the degree test fires when `L ≥ 1`.  The observable cost
  is `T_r = (j_r + 1) L_r`.  `TrialReached` is the analysis predicate `Reached(j)` (state `j`
  entered, every comparison at `1 ≤ i < j` failed); a computed look-ahead core is not a reached
  state.  `trialRun_exit` classifies the four exits (`TrialExit`).
* **T02 (`UpperTrialQuadratic`).**  `upperTrialQuadratic`: at a qualifying instance
  `T_r ≤ (b + 7) c_* (H + r + √((H + r) max {0, I - 𝓔_p(r)}))`, from the telescoped failures
  (`trialReached_telescope`), the initial profile cap M07, the core mass bound
  `core_mass_lower` (common information and containment) and the elementary quadratic estimate
  `trial_quadratic_arith`.
* **T03 (`UpperCandidateBounds`).**  `upperCandidateBounds`: the candidate contains `x` and has
  score and both endpoint costs at most `b_cand T_r`: the degree stop by the fallback bounds,
  the comparison stop by the adjacent cap M08 and the local decoder M03; missing-core exits are
  impossible by the coverage M04.

The minimum-core nodes M04, M07, M08 (`Upper.CoreCaps`, cluster M_CORES) enter as the explicitly
named hypotheses `CoverageStmt`, `InitialProfileCapStmt`, `AdjacentCapStmt`, whose bodies are
verbatim copies of `upperMinCoreCoverage`, `upperInitialProfileCap`, `upperAdjacentCap`.  M03 is
used directly (`upperMinCoreLocalDecoder`).
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### The minimum-core hypotheses (statements of M04, M07, M08) -/

/-- The statement of M04 (`upperMinCoreCoverage`, `Upper.CoreCaps`): a containing core exists at
every budget `c₀ H ≤ s < min (a, b)` of a qualifying instance. -/
def CoverageStmt (V : Map) : Prop :=
  ∃ c₀ : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ),
    IsCoreInstance V n e pA pB x A B → (c₀ : ℝ) * baseBudget n e ≤ s →
      s < Nat.log 2 A.card → s < Nat.log 2 B.card →
        ∃ F, coreOf (coreShape pA pB n A B) s x = some F

/-- The statement of M07 (`upperInitialProfileCap`, `Upper.CoreCaps`):
`log₂ |F_{L_r}| ≤ k - 𝓔_p(r) + b (H + r)` for `c_* ≥ c_min`. -/
def InitialProfileCapStmt (V : Map) : Prop :=
  ∃ cmin bini : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r : ℕ) (pA pB x : BitString)
    (A B : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
      cstar * (baseBudget n e + r) < Nat.log 2 A.card →
      cstar * (baseBudget n e + r) < Nat.log 2 B.card →
        ∃ F, coreOf (coreShape pA pB n A B) (cstar * (baseBudget n e + r)) x = some F ∧
          Real.logb 2 F.card ≤ plainC V x - ordinaryCommonProfile V A B r +
            bini * (baseBudget n e + r)

/-- The statement of M08 (`upperAdjacentCap`, `Upper.CoreCaps`): the next core exists and
`Score(F_s, x) ≤ log₂ |F_s| - log₂ |F_{s+L}| + b H` for `c_* ≥ c_min`. -/
def AdjacentCapStmt (V : Map) : Prop :=
  ∃ cmin badj : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r s : ℕ) (pA pB x : BitString)
    (A B Fs : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
      s + cstar * (baseBudget n e + r) < Nat.log 2 A.card →
      s + cstar * (baseBudget n e + r) < Nat.log 2 B.card →
      coreOf (coreShape pA pB n A B) s x = some Fs →
        ∃ F', coreOf (coreShape pA pB n A B) (s + cstar * (baseBudget n e + r)) x = some F' ∧
          Real.logb 2 F'.card ≤ condC V x (canonicalFiniteSetCode Fs) + 1 ∧
          modelScore V Fs x ≤ Real.logb 2 Fs.card - Real.logb 2 F'.card +
            badj * baseBudget n e

/-! ### T01: the finite trial -/

/-- The step `L_r = c_* (H + r)` of the `r`-th trial, with `H = e + ⌈log₂ (n + 2)⌉`. -/
def trialStep (cs n e r : ℕ) : ℕ :=
  cs * (baseBudget n e + r)

/-- The original model in the larger size bucket, ties to the column model `B` (the fallback
of the trials). -/
noncomputable def largerModel (A B : Finset BitString) : Finset BitString :=
  if Nat.log 2 A.card ≤ Nat.log 2 B.card then B else A

/-- **The trial loop** at state `j` with the current core `F = F_{jL}` and fuel `fuel`: degree
test, look-ahead core, exact size comparison `|F_s| ≤ 2^s |F_{s+L}|`, advance. -/
noncomputable def trialLoop (P : ShapeParams) (L : ℕ) (big : Finset BitString) (z : BitString) :
    ℕ → ℕ → Finset BitString → Finset BitString × ℕ
  | 0, j, _ => (big, j)
  | fuel + 1, j, F =>
    if min P.a P.b ≤ (j + 1) * L then (big, j)
    else
      match coreOf P ((j + 1) * L) z with
      | none => (big, j)
      | some F' =>
        if F.card ≤ 2 ^ (j * L) * F'.card then (F, j)
        else trialLoop P L big z fuel (j + 1) F'

/-- **The finite trial** (T01, tex ~851–871): candidate and stopping index `j_r`. -/
noncomputable def trialRun (P : ShapeParams) (L : ℕ) (big : Finset BitString) (z : BitString) :
    Finset BitString × ℕ :=
  if min P.a P.b ≤ L then (big, 0)
  else
    match coreOf P L z with
    | none => (big, 1)
    | some F => trialLoop P L big z (min P.a P.b + 1) 1 F

/-- **`Reached(j)`** (blueprint, tex ~3970): the loop enters state `j ≥ 1`: `jL < min a b`, the
cores `F_{iL}` exist for `1 ≤ i ≤ j`, and every comparison at `1 ≤ i < j` failed. -/
def TrialReached (P : ShapeParams) (L : ℕ) (z : BitString) (j : ℕ) : Prop :=
  1 ≤ j ∧ j * L < min P.a P.b ∧ (∀ i, 1 ≤ i → i ≤ j → ∃ F, coreOf P (i * L) z = some F) ∧
    ∀ i, 1 ≤ i → i < j → ∀ F F' : Finset BitString, coreOf P (i * L) z = some F →
      coreOf P ((i + 1) * L) z = some F' → 2 ^ (i * L) * F'.card < F.card

/-- **The four exits of a trial** with result `(D, j)`: the immediate degree stop, the missing
initial core, a degree or missing-core stop at a reached state, and a comparison stop. -/
def TrialExit (P : ShapeParams) (L : ℕ) (big : Finset BitString) (z : BitString)
    (D : Finset BitString) (j : ℕ) : Prop :=
  (j = 0 ∧ D = big ∧ min P.a P.b ≤ L) ∨
    (j = 1 ∧ D = big ∧ L < min P.a P.b ∧ coreOf P L z = none) ∨
    (TrialReached P L z j ∧ D = big ∧
      (min P.a P.b ≤ (j + 1) * L ∨ coreOf P ((j + 1) * L) z = none)) ∨
    (TrialReached P L z j ∧ (j + 1) * L < min P.a P.b ∧ coreOf P (j * L) z = some D ∧
      ∃ F', coreOf P ((j + 1) * L) z = some F' ∧ D.card ≤ 2 ^ (j * L) * F'.card)

/-- **Exits of the loop.**  From a reached state `j` with current core `F_{jL} = F` and fuel with
`min a b ≤ j + fuel`, the loop exits in one of the last two ways of `TrialExit` (induction on the
fuel; a failed comparison makes `j + 1` reached, by uniqueness of `coreOf` values). -/
theorem trialLoop_exit (P : ShapeParams) {L : ℕ} (hL : 1 ≤ L) (big : Finset BitString)
    (z : BitString) :
    ∀ (fuel j : ℕ) (F : Finset BitString), TrialReached P L z j → coreOf P (j * L) z = some F →
      min P.a P.b ≤ j + fuel →
        TrialExit P L big z (trialLoop P L big z fuel j F).1 (trialLoop P L big z fuel j F).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro j F hR _ hfuel
    change TrialExit P L big z big j
    refine Or.inr (Or.inr (Or.inl ⟨hR, rfl, Or.inl ?_⟩))
    have := Nat.le_mul_of_pos_right (j + 1) hL
    omega
  | succ fuel ih =>
    intro j F hR hF hfuel
    simp only [trialLoop]
    split_ifs with h1
    · exact Or.inr (Or.inr (Or.inl ⟨hR, rfl, Or.inl h1⟩))
    · cases hc : coreOf P ((j + 1) * L) z with
      | none => exact Or.inr (Or.inr (Or.inl ⟨hR, rfl, Or.inr hc⟩))
      | some F' =>
        dsimp only
        split_ifs with h2
        · exact Or.inr (Or.inr (Or.inr ⟨hR, not_le.mp h1, hF, F', hc, h2⟩))
        · obtain ⟨hj1, -, hcores, hfail⟩ := hR
          refine ih (j + 1) F' ⟨by omega, not_le.mp h1, fun i hi1 hi2 => ?_,
            fun i hi1 hi2 G G' hG hG' => ?_⟩ hc (by omega)
          · rcases Nat.lt_or_ge i (j + 1) with hlt | hge
            · exact hcores i hi1 (by omega)
            · obtain rfl : i = j + 1 := by omega
              exact ⟨F', hc⟩
          · rcases Nat.lt_or_ge i j with hlt | hge
            · exact hfail i hi1 hlt G G' hG hG'
            · obtain rfl : i = j := by omega
              have e1 : G = F := Option.some_inj.mp (hG.symm.trans hF)
              have e2 : G' = F' := Option.some_inj.mp (hG'.symm.trans hc)
              subst e1
              subst e2
              exact not_le.mp h2

/-- **T01: the exits of a trial.**  For `L ≥ 1` the trial result `(D, j)` satisfies
`TrialExit`. -/
theorem trialRun_exit (P : ShapeParams) {L : ℕ} (hL : 1 ≤ L) (big : Finset BitString)
    (z : BitString) : TrialExit P L big z (trialRun P L big z).1 (trialRun P L big z).2 := by
  unfold trialRun
  split_ifs with h0
  · exact Or.inl ⟨rfl, rfl, h0⟩
  · cases hc : coreOf P L z with
    | none => exact Or.inr (Or.inl ⟨rfl, rfl, not_le.mp h0, hc⟩)
    | some F =>
      dsimp only
      have hc1 : coreOf P (1 * L) z = some F := by rw [one_mul]; exact hc
      refine trialLoop_exit P hL big z _ 1 F ⟨le_rfl, by rw [one_mul]; exact not_le.mp h0,
        fun i hi1 hi2 => ?_, fun i hi1 hi2 => by omega⟩ hc1 (by omega)
      obtain rfl : i = 1 := by omega
      exact ⟨F, hc1⟩

/-- Reached states are downward closed. -/
theorem trialReached_of_succ {P : ShapeParams} {L : ℕ} {z : BitString} {j : ℕ}
    (h : TrialReached P L z (j + 1)) (hj : 1 ≤ j) : TrialReached P L z j := by
  obtain ⟨-, hlt, hcores, hfail⟩ := h
  exact ⟨hj, lt_of_le_of_lt (Nat.mul_le_mul_right L (Nat.le_succ j)) hlt,
    fun i hi1 hi2 => hcores i hi1 (by omega), fun i hi1 hi2 => hfail i hi1 (by omega)⟩

/-- **A size comparison in logarithms**: if `2^s |G| ≤ |F|` and `G` is nonempty, then
`s + log₂ |G| ≤ log₂ |F|`. -/
theorem add_logb_le_of_pow_mul_le {F G : Finset BitString} {s : ℕ}
    (h : 2 ^ s * G.card ≤ F.card) (hG : G.Nonempty) :
    (s : ℝ) + Real.logb 2 G.card ≤ Real.logb 2 F.card := by
  have hGpos : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  have hle : (2 : ℝ) ^ s * G.card ≤ F.card := by exact_mod_cast h
  have h1 := Real.logb_le_logb_of_le one_lt_two (mul_pos hpow hGpos) hle
  rw [Real.logb_mul hpow.ne' hGpos.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
    mul_one] at h1
  exact h1

/-- **Telescoped failures** (tex ~3977): at a reached state `j`, the cores `F_L` and `F_{jL}`
exist and `L j (j - 1) / 2 ≤ log₂ |F_L| - log₂ |F_{jL}|` (induction on `j`; each failed
comparison at `i` contributes `iL`). -/
theorem trialReached_telescope {P : ShapeParams} {L : ℕ} {z : BitString} {j : ℕ}
    (h : TrialReached P L z j) :
    ∃ F₁ Fj : Finset BitString, coreOf P L z = some F₁ ∧ coreOf P (j * L) z = some Fj ∧
      (L : ℝ) * ((j : ℝ) * ((j : ℝ) - 1)) / 2 ≤ Real.logb 2 F₁.card - Real.logb 2 Fj.card := by
  induction j with
  | zero => exact absurd h.1 (by norm_num)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · obtain ⟨F, hF⟩ := h.2.2.1 1 le_rfl le_rfl
      rw [one_mul] at hF
      refine ⟨F, F, hF, by rw [zero_add, one_mul]; exact hF, ?_⟩
      norm_num
    · obtain ⟨F₁, Fj, hF₁, hFj, hb⟩ := ih (trialReached_of_succ h hjpos)
      obtain ⟨G, hG⟩ := h.2.2.1 (j + 1) (by omega) le_rfl
      have hfail := h.2.2.2 j hjpos (by omega) Fj G hFj hG
      have hGne : G.Nonempty := ⟨z, (coreOf_spec hG).2⟩
      have hlog := add_logb_le_of_pow_mul_le hfail.le hGne
      refine ⟨F₁, G, hF₁, hG, ?_⟩
      push_cast at hlog ⊢
      linarith

/-- The loop returns `big` or a current core; both contain `z` when `big` and the starting core
do. -/
theorem trialLoop_mem (P : ShapeParams) (L : ℕ) {big : Finset BitString} {z : BitString}
    (hz : z ∈ big) : ∀ (fuel j : ℕ) (F : Finset BitString), z ∈ F →
      z ∈ (trialLoop P L big z fuel j F).1 := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ => hz
  | succ fuel ih =>
    intro j F hF
    simp only [trialLoop]
    split_ifs with h1
    · exact hz
    · cases hc : coreOf P ((j + 1) * L) z with
      | none => exact hz
      | some F' =>
        dsimp only
        split_ifs with h2
        · exact hF
        · exact ih (j + 1) F' (coreOf_spec hc).2

/-- **The candidate contains the input** whenever the fallback does: every trial output is
`big` or a selected core containing `z` (`coreOf_spec`). -/
theorem mem_trialRun (P : ShapeParams) (L : ℕ) {big : Finset BitString} {z : BitString}
    (hz : z ∈ big) : z ∈ (trialRun P L big z).1 := by
  unfold trialRun
  split_ifs
  · exact hz
  · cases hc : coreOf P L z with
    | none => exact hz
    | some F => exact trialLoop_mem P L hz _ 1 F (coreOf_spec hc).2

/-- **Congruence of trials**: shapes that agree at the data length give the same trial on a
string of that length (`coreOf_congr` at every budget). -/
theorem trialRun_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (L : ℕ) (big : Finset BitString)
    {z : BitString} (hz : z.length = P.n) : trialRun P L big z = trialRun Q L big z := by
  have hc : ∀ s, coreOf P s z = coreOf Q s z := fun s => coreOf_congr h s hz
  have hloop : ∀ fuel j F, trialLoop P L big z fuel j F = trialLoop Q L big z fuel j F := by
    intro fuel
    induction fuel with
    | zero => exact fun _ _ => rfl
    | succ fuel ih =>
      intro j F
      simp only [trialLoop, h.2.1, h.2.2.1, hc, ih]
  unfold trialRun
  simp only [h.2.1, h.2.2.1, hc, hloop]

/-! ### Elementary leaves -/

/-- **A successful size comparison in logarithms**: if `|F| ≤ 2^s |F'|` and `F'` is nonempty,
then `log₂ |F| ≤ s + log₂ |F'|`. -/
theorem logb_card_le_of_le_pow_mul {F F' : Finset BitString} {s : ℕ}
    (h : F.card ≤ 2 ^ s * F'.card) (hF' : F'.Nonempty) :
    Real.logb 2 F.card ≤ s + Real.logb 2 F'.card := by
  have hF'pos : (0 : ℝ) < F'.card := by exact_mod_cast hF'.card_pos
  have hl0 : 0 ≤ Real.logb 2 F'.card := Real.logb_nonneg one_lt_two (Nat.one_le_cast.2 hF'.card_pos)
  rcases Nat.eq_zero_or_pos F.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  · have hpow : (0 : ℝ) < 2 ^ s := by positivity
    have hle : (F.card : ℝ) ≤ 2 ^ s * F'.card := by exact_mod_cast h
    have h1 := Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hpos) hle
    rw [Real.logb_mul hpow.ne' hF'pos.ne', Real.logb_pow, Real.logb_self_eq_one one_lt_two,
      mul_one] at h1
    exact h1

/-- **The quadratic stopping estimate** (tex ~3987–3997): with `L = c_* h`, `c_* ≥ 1`, `h ≥ 1`,
`Δ ≥ 0`, the inequality `L j (j - 1) / 2 ≤ Δ + 2 j L + b h` implies
`(j + 1) L ≤ (b + 7) c_* (h + √(h Δ))`.  With `s = √(h Δ)` one shows `(j + 1) h ≤ (b + 7) (h + s)`
by contradiction (the negation gives `h j ≥ (b + 6) h + (b + 7) s`, whose product with
`h j - 5 h` exceeds the bound `2 s² + 2 b h²` on `h² j (j - 5)` from the hypothesis), then
multiplies by `c_* ≥ 1`. -/
theorem trial_quadratic_arith {cs b j : ℕ} {h Δ : ℝ} (hcs : 1 ≤ cs) (hh : 1 ≤ h) (hΔ : 0 ≤ Δ)
    (hkey : ((cs : ℝ) * h) * ((j : ℝ) * ((j : ℝ) - 1)) / 2 ≤
      Δ + 2 * (j : ℝ) * ((cs : ℝ) * h) + (b : ℝ) * h) :
    ((j : ℝ) + 1) * ((cs : ℝ) * h) ≤ (((b + 7) * cs : ℕ) : ℝ) * (h + Real.sqrt (h * Δ)) := by
  have hc : (1 : ℝ) ≤ (cs : ℝ) := by exact_mod_cast hcs
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hy : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hh0 : (0 : ℝ) < h := by linarith
  have hs0 : 0 ≤ Real.sqrt (h * Δ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (h * Δ) * Real.sqrt (h * Δ) = h * Δ :=
    Real.mul_self_sqrt (mul_nonneg hh0.le hΔ)
  push_cast
  generalize Real.sqrt (h * Δ) = s at hs0 hs2 ⊢
  generalize (cs : ℝ) = c at hc hkey ⊢
  generalize (b : ℝ) = B at hb hkey ⊢
  generalize (j : ℝ) = y at hy hkey ⊢
  -- the `c`-free inequality
  have hmain : (y + 1) * h ≤ (B + 7) * (h + s) := by
    rw [← not_lt]
    intro hcon
    have hkh := mul_le_mul_of_nonneg_left hkey hh0.le
    have hkey' : c * (h * h * (y * (y - 5))) ≤ 2 * (s * s) + 2 * B * (h * h) := by
      nlinarith [hs2]
    have hBs : 0 ≤ (B + 7) * s := mul_nonneg (by linarith) hs0
    have hBh : 0 ≤ B * h := mul_nonneg hb hh0.le
    have hA : (B + 6) * h + (B + 7) * s ≤ h * y := by nlinarith
    have hy5 : 5 ≤ y := by
      rw [← not_lt]
      intro hlt
      nlinarith
    have hyy : 0 ≤ h * h * (y * (y - 5)) :=
      mul_nonneg (mul_nonneg hh0.le hh0.le) (mul_nonneg hy (by linarith))
    have hstep : h * h * (y * (y - 5)) ≤ 2 * (s * s) + 2 * B * (h * h) := by
      nlinarith
    have hA' : (B + 1) * h + (B + 7) * s ≤ h * y - 5 * h := by linarith
    have hprod : ((B + 6) * h + (B + 7) * s) * ((B + 1) * h + (B + 7) * s) ≤
        (h * y) * (h * y - 5 * h) :=
      mul_le_mul hA hA' (by nlinarith) (by nlinarith)
    have he : (h * y) * (h * y - 5 * h) = h * h * (y * (y - 5)) := by ring
    rw [he] at hprod
    have h1 : 0 ≤ B * B * (h * h) := by positivity
    have h2 : 0 ≤ B * (h * h) := by positivity
    have h3 : 0 ≤ h * s := mul_nonneg hh0.le hs0
    have h4 : 0 ≤ B * (h * s) := by positivity
    have h5 : 0 ≤ B * B * (h * s) := by positivity
    have h6 : 0 ≤ B * (s * s) := by positivity
    have h7 : 0 ≤ B * B * (s * s) := by positivity
    have h8 : 1 ≤ h * h := by nlinarith
    have h9 : 0 ≤ s * s := mul_nonneg hs0 hs0
    nlinarith
  calc (y + 1) * (c * h) = c * ((y + 1) * h) := by ring
    _ ≤ c * ((B + 7) * (h + s)) := mul_le_mul_of_nonneg_left hmain (by linarith)
    _ = (B + 7) * c * (h + s) := by ring

/-! ### Core mass at a qualifying instance -/

/-- `⌈log₂ (n + 2)⌉ ≤ n + 1`, so `H ≤ 2 (n + 1)` when `e ≤ n`. -/
theorem trC_headerLog_le (n : ℕ) : headerLog n ≤ n + 1 := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h1 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

/-- **Linear complexity of a selected core**: at a qualifying instance a selected core `F_s` has
`C(F_s) ≤ K (n + 1)`, by the chain rule with the empty condition from `C(x) ≤ n + O(1)` and the
point bound `C(F_s | x) ≤ c H` of M03 (`upperMinCoreLocalDecoder`), with `H ≤ 2 (n + 1)`. -/
theorem trC_setC_core_le (V : Map) (hV : isOptimalConditional V) :
    ∃ K : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ)
      (F : Finset BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some F →
          setC V F ≤ K * ((n : ℝ) + 1) := by
  obtain ⟨cH, hM⟩ := upperMinCoreLocalDecoder V hV
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨blit, hblit⟩ := plainC_le_length_add V hV
  refine ⟨(1 + 2 * c₃) * (1 + blit + 2 * cH) + 2 * c₃,
    fun n e pA pB x A B s F h hsa hsb hF => ?_⟩
  have hDx : condC V (canonicalFiniteSetCode F) x ≤ cH * baseBudget n e :=
    (hM n e pA pB x A B s F h hsa hsb hF).2.2
  have hX : plainC V x ≤ n + blit := by
    have h1 := hblit x
    rw [h.length_x] at h1
    exact h1
  have hHn : baseBudget n e ≤ 2 * (n + 1) := by
    have h1 := h.le_n
    have h2 := trC_headerLog_le n
    unfold baseBudget
    omega
  have hH : (baseBudget n e : ℝ) ≤ 2 * ((n : ℝ) + 1) := by exact_mod_cast hHn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbl : (0 : ℝ) ≤ blit := Nat.cast_nonneg blit
  have hc₃ : (0 : ℝ) ≤ c₃ := Nat.cast_nonneg c₃
  have hcH : (0 : ℝ) ≤ cH := Nat.cast_nonneg cH
  have hX0 := plainC_nonneg V x
  have hD0 := condC_nonneg V (canonicalFiniteSetCode F) x
  have hchain : plainC V (canonicalFiniteSetCode F) ≤ plainC V x +
      condC V (canonicalFiniteSetCode F) x + c₃ * Real.logb 2
        (plainC V x + condC V (canonicalFiniteSetCode F) x + 2) :=
    h₃ (canonicalFiniteSetCode F) x []
  have hlg := mul_le_mul_of_nonneg_left (logb_add_two_le (add_nonneg hX0 hD0)) hc₃
  have hHb := mul_le_mul_of_nonneg_left hH hcH
  have hblM : (blit : ℝ) ≤ blit * ((n : ℝ) + 1) := le_mul_of_one_le_right hbl (by linarith)
  have hsum : plainC V x + condC V (canonicalFiniteSetCode F) x ≤
      (1 + blit + 2 * cH) * ((n : ℝ) + 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 + 2 * c₃)
  have hc₃M : (c₃ : ℝ) ≤ c₃ * ((n : ℝ) + 1) := le_mul_of_one_le_right hc₃ (by linarith)
  change plainC V (canonicalFiniteSetCode F) ≤ _
  push_cast
  linarith

/-- **Common-information bound for a core** (tex ~886): at a qualifying instance, a selected core
`F_s` at a budget `s ≤ a, b` has `C(F_s) ≤ I(A : B) + 2 s + b H`.

Proof sketch: M03 (`upperMinCoreLocalDecoder`) gives `CT(F_s | A), CT(F_s | B) ≤ s + c H` and
`C(F_s | x) ≤ c H`.  The joint complexities `C(F_s)`, `C(A, B)`, `C(A, F_s)`, `C(B, F_s)` are
`O(n + 1)`: `upperJointBound`, and `C(F_s) ≤ C(x) + C(F_s | x) + O(log)`
(`upperComplexityChain_trans` with the empty condition, `plainC_le_length_add`), then
`pairC_le_crude`.  Apply `upperCommonInformation_total` with `T = s + c H` and bound
`log₂ (N + 2)` by `logb_le_baseBudget`. -/
theorem core_setC_le_info (V : Map) (hV : isOptimalConditional V) :
    ∃ b : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ)
      (F : Finset BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some F →
          setC V F ≤ setMutualInfo V A B + 2 * s + b * baseBudget n e := by
  obtain ⟨cH, hM⟩ := upperMinCoreLocalDecoder V hV
  obtain ⟨cci, hci⟩ := upperCommonInformation_total V hV
  obtain ⟨bj, hbj⟩ := upperJointBound V hV
  obtain ⟨K₁, hK₁⟩ := trC_setC_core_le V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  obtain ⟨k, hk⟩ := logb_le_baseBudget (3 * bj + K₁ + ccr)
  refine ⟨2 * cH + cci * k, fun n e pA pB x A B s F h hsa hsb hF => ?_⟩
  obtain ⟨hTA, hTB, -⟩ := hM n e pA pB x A B s F h hsa hsb hF
  have hF1 := hK₁ n e pA pB x A B s F h hsa hsb hF
  obtain ⟨hA1, hAB, -⟩ := hbj n e x A B h.length_x h.le_n h.sufA h.sufB
  obtain ⟨hB1, -, -⟩ := hbj n e x B A h.length_x h.le_n h.sufB h.sufA
  have hAF := hcr (canonicalFiniteSetCode A) (canonicalFiniteSetCode F)
  have hBF := hcr (canonicalFiniteSetCode B) (canonicalFiniteSetCode F)
  change plainC V (canonicalFiniteSetCode A) ≤ bj * ((n : ℝ) + 1) at hA1
  change plainC V (canonicalFiniteSetCode B) ≤ bj * ((n : ℝ) + 1) at hB1
  change plainC V (canonicalFiniteSetCode F) ≤ K₁ * ((n : ℝ) + 1) at hF1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have p0 : (0 : ℝ) ≤ ccr := Nat.cast_nonneg ccr
  have p1 : (0 : ℝ) ≤ bj * ((n : ℝ) + 1) := mul_nonneg (Nat.cast_nonneg _) hn0
  have p2 : (0 : ℝ) ≤ K₁ * ((n : ℝ) + 1) := mul_nonneg (Nat.cast_nonneg _) hn0
  have p3 : (ccr : ℝ) ≤ ccr * ((n : ℝ) + 1) :=
    le_mul_of_one_le_right p0 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hNF : setC V F ≤ ((3 * bj + K₁ + ccr : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    change plainC V (canonicalFiniteSetCode F) ≤ _
    push_cast
    linarith
  have hNAB : setPairC V A B ≤ ((3 * bj + K₁ + ccr : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    push_cast
    linarith
  have hNAF : setPairC V A F ≤ ((3 * bj + K₁ + ccr : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    change pairC V (canonicalFiniteSetCode A) (canonicalFiniteSetCode F) ≤ _
    push_cast
    linarith
  have hNBF : setPairC V B F ≤ ((3 * bj + K₁ + ccr : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    change pairC V (canonicalFiniteSetCode B) (canonicalFiniteSetCode F) ≤ _
    push_cast
    linarith
  have key := hci _ ((s : ℝ) + cH * baseBudget n e) A B F hNF hNAB hNAF hNBF hTA hTB
  have hlog := mul_le_mul_of_nonneg_left (hk n e) (Nat.cast_nonneg (α := ℝ) cci)
  push_cast
  linarith

/-- A selected core of a qualifying shape consists of `n`-bit strings: `|F_s| ≤ 2 ^ n`
(`coreRunAux_mem`, `shapeComponent_subset`, `card_shapeEdges_le`). -/
theorem trC_card_core_le {pA pB x : BitString} {n s : ℕ} {A B F : Finset BitString}
    (hF : coreOf (coreShape pA pB n A B) s x = some F) : F.card ≤ 2 ^ n := by
  have hmem := (coreOf_spec hF).1
  unfold vertexCores coreFamily at hmem
  have hFC := (coreRunAux_mem _ _ _ _ _ F hmem).2.1
  exact (Finset.card_le_card (hFC.trans (shapeComponent_subset _ _ _))).trans
    (card_shapeEdges_le _)

/-- A selected core of a qualifying shape has `log₂ |F_s| ≤ n` (`trC_card_core_le`). -/
theorem trC_logb_card_core_le {pA pB x : BitString} {n s : ℕ} {A B F : Finset BitString}
    (hF : coreOf (coreShape pA pB n A B) s x = some F) : Real.logb 2 F.card ≤ n := by
  have hpos : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.2 ⟨x, (coreOf_spec hF).2⟩
  have hle : (F.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast trC_card_core_le hF
  have h1 := Real.logb_le_logb_of_le one_lt_two hpos hle
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h1
  exact h1

/-- **Containment bound for a core** (tex ~887): at a qualifying instance, a selected core
`F_s ∋ x` at a budget `s ≤ a, b` has `C(x) ≤ C(F_s) + log₂ |F_s| + b H`.

Proof sketch: `x ∈ F_s` (`coreOf_spec`) and `condC_le_logb_card` give
`C(x | F_s) ≤ log₂ |F_s| + c`; `upperComplexityChain_trans` (empty condition) gives
`C(x) ≤ C(F_s) + C(x | F_s) + c log₂ (C(F_s) + C(x | F_s) + 2)`.  The core consists of `n`-bit
strings (`coreRunAux_mem`, `shapeComponent_subset`, `mem_stringsOfLength`), so
`log₂ |F_s| ≤ n`, and `C(F_s) ≤ C(x) + C(F_s | x) + O(log) = O(n + H)` by M03; the logarithm is
`O(H)` (`logb_le_baseBudget`). -/
theorem plainC_le_core_mass (V : Map) (hV : isOptimalConditional V) :
    ∃ b : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ)
      (F : Finset BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some F →
          plainC V x ≤ setC V F + Real.logb 2 F.card + b * baseBudget n e := by
  obtain ⟨K₁, hK₁⟩ := trC_setC_core_le V hV
  obtain ⟨c₃, h₃⟩ := upperComplexityChain_trans V hV
  obtain ⟨cidx, hidx⟩ := condC_le_logb_card V hV
  obtain ⟨k, hk⟩ := logb_le_baseBudget (K₁ + 1 + cidx)
  refine ⟨cidx + c₃ * k, fun n e pA pB x A B s F h hsa hsb hF => ?_⟩
  have hF1 := hK₁ n e pA pB x A B s F h hsa hsb hF
  have hix := hidx F x (coreOf_spec hF).2
  have hlogF := trC_logb_card_core_le hF
  have hchain : plainC V x ≤ setC V F + condC V x (canonicalFiniteSetCode F) +
      c₃ * Real.logb 2 (setC V F + condC V x (canonicalFiniteSetCode F) + 2) :=
    h₃ x (canonicalFiniteSetCode F) []
  have hF0 : 0 ≤ setC V F := plainC_nonneg V _
  have hi0 := condC_nonneg V x (canonicalFiniteSetCode F)
  have hci0 : (0 : ℝ) ≤ cidx := Nat.cast_nonneg cidx
  have hcM : (cidx : ℝ) ≤ cidx * ((n : ℝ) + 1) :=
    le_mul_of_one_le_right hci0 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hsum : setC V F + condC V x (canonicalFiniteSetCode F) ≤
      ((K₁ + 1 + cidx : ℕ) : ℝ) * ((n : ℝ) + 1) := by
    push_cast
    linarith
  have hm := mul_le_mul_of_nonneg_left ((logb_add_two_mono (add_nonneg hF0 hi0) hsum).trans
    (hk n e)) (Nat.cast_nonneg (α := ℝ) c₃)
  have hH : (1 : ℝ) ≤ baseBudget n e := by
    have h1 := one_le_headerLog n
    have h2 : 1 ≤ baseBudget n e := by
      unfold baseBudget
      omega
    exact_mod_cast h2
  have hcH : (cidx : ℝ) ≤ cidx * (baseBudget n e : ℝ) := le_mul_of_one_le_right hci0 hH
  push_cast
  linarith

/-- **Core mass lower bound** (tex ~886–888): a selected core `F_s` at a budget `s ≤ a, b` of a
qualifying instance has `log₂ |F_s| ≥ k - I - 2 s - b H`. -/
theorem core_mass_lower (V : Map) (hV : isOptimalConditional V) :
    ∃ b : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ)
      (F : Finset BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some F →
          plainC V x - setMutualInfo V A B - 2 * s - b * baseBudget n e ≤
            Real.logb 2 F.card := by
  obtain ⟨b₁, h₁⟩ := core_setC_le_info V hV
  obtain ⟨b₂, h₂⟩ := plainC_le_core_mass V hV
  refine ⟨b₁ + b₂, fun n e pA pB x A B s F h hsa hsb hF => ?_⟩
  have e1 := h₁ n e pA pB x A B s F h hsa hsb hF
  have e2 := h₂ n e pA pB x A B s F h hsa hsb hF
  push_cast
  linarith

/-! ### T02: quadratic stopping -/

/-- The trial of a qualifying instance at `x`: shape `coreShape pA pB n A B`, step `L_r`, fallback
the larger-bucket original model. -/
noncomputable def instTrial (cs n e r : ℕ) (pA pB x : BitString) (A B : Finset BitString) :
    Finset BitString × ℕ :=
  trialRun (coreShape pA pB n A B) (trialStep cs n e r) (largerModel A B) x

/-- The base budget is at least one. -/
theorem one_le_baseBudget (n e : ℕ) : 1 ≤ baseBudget n e := by
  have := one_le_headerLog n
  unfold baseBudget
  omega

/-- **T02: quadratic stopping (blueprint `UpperTrialQuadratic`, eq.
`extractability-trial-bound`).**  Given M07, for an optimal `V` there are `c_min` and `b` such
that for every `c_* ≥ c_min`, at every qualifying instance and `0 ≤ r ≤ n`, the observable cost of
the `r`-th trial is
`T_r = (j_r + 1) L_r ≤ (b + 7) c_* (H + r + √((H + r) max {0, I - 𝓔_p(r)}))`. -/
theorem upperTrialQuadratic (V : Map) (hV : isOptimalConditional V)
    (hM07 : InitialProfileCapStmt V) :
    ∃ cmin b : ℕ, ∀ cs : ℕ, cmin ≤ cs → ∀ (n e r : ℕ) (pA pB x : BitString)
      (A B : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
        ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) ≤
          (((b + 7) * cs : ℕ) : ℝ) * (((baseBudget n e + r : ℕ) : ℝ) +
            Real.sqrt (((baseBudget n e + r : ℕ) : ℝ) *
              max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r))) := by
  obtain ⟨cmin₇, bini, h₇⟩ := hM07
  obtain ⟨blow, hlow⟩ := core_mass_lower V hV
  refine ⟨cmin₇ + 1, bini + blow, fun cs hcs n e r pA pB x A B h hrn => ?_⟩
  set P := coreShape pA pB n A B with hP
  set L := trialStep cs n e r with hLdef
  set hh : ℝ := ((baseBudget n e + r : ℕ) : ℝ) with hhh
  set Δ : ℝ := max 0 (setMutualInfo V A B - ordinaryCommonProfile V A B r) with hΔdef
  have hcs1 : 1 ≤ cs := by omega
  have hB1 := one_le_baseBudget n e
  have hh1 : (1 : ℝ) ≤ hh := by
    rw [hhh]
    exact_mod_cast (by omega : 1 ≤ baseBudget n e + r)
  have hL1 : 1 ≤ L := by
    rw [hLdef, trialStep]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hLreal : (L : ℝ) = (cs : ℝ) * hh := by
    rw [hLdef, trialStep, hhh]
    push_cast
    ring
  have hΔ0 : 0 ≤ Δ := le_max_left _ _
  have hHh : (baseBudget n e : ℝ) ≤ hh := by
    rw [hhh]
    exact_mod_cast Nat.le_add_right _ _
  -- the quadratic inequality at a reached state
  have hreach : ∀ j : ℕ, TrialReached P L x j →
      ((cs : ℝ) * hh) * ((j : ℝ) * ((j : ℝ) - 1)) / 2 ≤
        Δ + 2 * (j : ℝ) * ((cs : ℝ) * hh) + ((bini + blow : ℕ) : ℝ) * hh := by
    intro j hR
    obtain ⟨F₁, Fj, hF₁, hFj, htel⟩ := trialReached_telescope hR
    obtain ⟨hj1, hjL, -, -⟩ := hR
    have hLj : L ≤ j * L := Nat.le_mul_of_pos_left L hj1
    have hLa : cs * (baseBudget n e + r) < Nat.log 2 A.card :=
      lt_of_le_of_lt hLj (lt_of_lt_of_le hjL (min_le_left _ _))
    have hLb : cs * (baseBudget n e + r) < Nat.log 2 B.card :=
      lt_of_le_of_lt hLj (lt_of_lt_of_le hjL (min_le_right _ _))
    obtain ⟨F, hF, hcap⟩ := h₇ cs (by omega) n e r pA pB x A B h hrn hLa hLb
    have hFF : F = F₁ := Option.some_inj.mp (hF.symm.trans hF₁)
    subst hFF
    have hlow' := hlow n e pA pB x A B (j * L) Fj h
      (le_of_lt (lt_of_lt_of_le hjL (min_le_left _ _)))
      (le_of_lt (lt_of_lt_of_le hjL (min_le_right _ _))) hFj
    have hI : setMutualInfo V A B - ordinaryCommonProfile V A B r ≤ Δ := le_max_right _ _
    have hjLr : ((j * L : ℕ) : ℝ) = (j : ℝ) * ((cs : ℝ) * hh) := by
      push_cast
      rw [hLreal]
    rw [hjLr] at hlow'
    have hbl : (blow : ℝ) * baseBudget n e ≤ (blow : ℝ) * hh :=
      mul_le_mul_of_nonneg_left hHh (Nat.cast_nonneg _)
    have hbi : (bini : ℝ) * (baseBudget n e + r) = (bini : ℝ) * hh := by
      rw [hhh]
      push_cast
      ring
    rw [hLreal] at htel
    push_cast
    linarith
  have hkey : ((cs : ℝ) * hh) * (((instTrial cs n e r pA pB x A B).2 : ℝ) *
      (((instTrial cs n e r pA pB x A B).2 : ℝ) - 1)) / 2 ≤
      Δ + 2 * ((instTrial cs n e r pA pB x A B).2 : ℝ) * ((cs : ℝ) * hh) +
        ((bini + blow : ℕ) : ℝ) * hh := by
    have hb0 : 0 ≤ ((bini + blow : ℕ) : ℝ) * hh := by positivity
    have hc0 : 0 ≤ (cs : ℝ) * hh := by positivity
    rcases trialRun_exit P hL1 (largerModel A B) x with
      ⟨hj, -, -⟩ | ⟨hj, -, -, -⟩ | ⟨hR, -, -⟩ | ⟨hR, -, -, -⟩
    · have hj' : ((instTrial cs n e r pA pB x A B).2 : ℝ) = 0 := by
        unfold instTrial
        exact_mod_cast hj
      rw [hj']
      have h0 : (cs : ℝ) * hh * ((0 : ℝ) * ((0 : ℝ) - 1)) / 2 = 0 := by ring
      have h0' : 2 * (0 : ℝ) * ((cs : ℝ) * hh) = 0 := by ring
      linarith
    · have hj' : ((instTrial cs n e r pA pB x A B).2 : ℝ) = 1 := by
        unfold instTrial
        exact_mod_cast hj
      rw [hj']
      have h0 : (cs : ℝ) * hh * ((1 : ℝ) * ((1 : ℝ) - 1)) / 2 = 0 := by ring
      linarith
    · exact hreach _ hR
    · exact hreach _ hR
  have hfin := trial_quadratic_arith (b := bini + blow) hcs1 hh1 hΔ0 hkey
  have hcast : ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) =
      (((instTrial cs n e r pA pB x A B).2 : ℝ) + 1) * ((cs : ℝ) * hh) := by
    rw [← hLreal]
    push_cast
    ring
  rw [hcast]
  exact hfin

/-! ### T03: candidate bounds -/

/-- **The fallback bounds** (degree stop, tex ~896): at a qualifying instance with
`min (a, b) ≤ M`, the larger-bucket original model has score at most `k H` and endpoint costs at
most `M + k H`.

Proof sketch: score: `isSufficientModel_iff_modelScore_le` gives `Score ≤ e ≤ H`.  Endpoints, if
`a ≤ b` (model `B`): `CT(B | B) ≤ c` (`totalC_self_le`), and `CT(B | A)` by indexing `x` in `A` and
running `p_B` (`totalC_fallback_le`): `log₂ |A| + |p_B| + 2 log₂ (log₂ |A| + 2) + c` with
`log₂ |A| < a + 1` (`logb_card_lt_log_add_one`), `|p_B| ≤ e ≤ H`, `a ≤ 2 n + b_size`
(`upperTypicality`) and `log₂ (2 n + b_size + 3) = O(H)` (`logb_le_baseBudget`); symmetric if
`a > b`.  As `rawBounds_small`. -/
theorem fallback_bounds (V : Map) (hV : isOptimalConditional V) :
    ∃ k : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (M : ℕ),
      IsCoreInstance V n e pA pB x A B → min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤ M →
        modelScore V (largerModel A B) x ≤ k * baseBudget n e ∧
        setTotalC (largerModel A B) A ≤ M + k * baseBudget n e ∧
        setTotalC (largerModel A B) B ≤ M + k * baseBudget n e := by
  obtain ⟨cfb, hfb⟩ := totalC_fallback_le
  obtain ⟨cid, hid⟩ := totalC_self_le
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨kl, hkl⟩ := logb_le_baseBudget (bsize + 3)
  refine ⟨2 + 2 * kl + cfb + cid, fun n e pA pB x A B M I hsmall => ?_⟩
  have hxA : x ∈ A := I.sufA.1
  have hxB : x ∈ B := I.sufB.1
  have hH1 : (1 : ℝ) ≤ (baseBudget n e : ℝ) := by exact_mod_cast one_le_baseBudget n e
  have heH : (e : ℝ) ≤ (baseBudget n e : ℝ) := by
    exact_mod_cast (show e ≤ baseBudget n e by unfold baseBudget; omega)
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hkl0 : (0 : ℝ) ≤ kl := Nat.cast_nonneg kl
  have hcfb0 : (0 : ℝ) ≤ cfb := Nat.cast_nonneg cfb
  have hcid0 : (0 : ℝ) ≤ cid := Nat.cast_nonneg cid
  have hfall : ∀ (X Y : Finset BitString) (p : BitString), x ∈ X →
      IsTotalProgram universalDecompressor p → p.length ≤ e →
      canonicalFiniteSetCode Y ∈ universalDecompressor (p, x) → IsSufficientModel V x X e →
      Nat.log 2 X.card ≤ M →
      setTotalC Y X ≤ (M : ℝ) + (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro X Y p hxX hp hpl hpY hsX hXM
    have h1 := hfb x X p _ hxX hp hpY
    have h2 := logb_card_lt_log_add_one (⟨x, hxX⟩ : X.Nonempty)
    have hXb := (htyp n e x X I.length_x I.le_n hsX).2
    have h3 : Real.logb 2 (Real.logb 2 X.card + 2) ≤ kl * baseBudget n e := by
      refine le_trans ?_ (hkl n e)
      apply logb_add_two_mono (logb_card_nonneg_of_mem hxX)
      have hb : (Nat.log 2 X.card : ℝ) ≤ 2 * n + bsize := by exact_mod_cast hXb
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hbs0 : (0 : ℝ) ≤ bsize := Nat.cast_nonneg bsize
      have hprod : (0 : ℝ) ≤ (bsize : ℝ) * n := mul_nonneg hbs0 hn0
      push_cast
      nlinarith
    have hXM' : (Nat.log 2 X.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hXM
    have hpl' : (p.length : ℝ) ≤ e := by exact_mod_cast hpl
    exact arith_fallback h1 h2 h3 hXM' hpl' heH hH1 hcfb0 (by linarith)
  have hself : ∀ Y : Finset BitString, setTotalC Y Y ≤
      (M : ℝ) + (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro Y
    exact arith_const (hid _) hM0 hH1 hcid0 (by linarith)
  have hscore : ∀ Y : Finset BitString, IsSufficientModel V x Y e →
      modelScore V Y x ≤ (2 + 2 * (kl : ℝ) + cfb + cid) * (baseBudget n e : ℝ) := by
    intro Y hY
    have h1 := ((isSufficientModel_iff_modelScore_le V x Y e).1 hY).2
    have h2 : (1 : ℝ) * baseBudget n e ≤ (2 + 2 * (kl : ℝ) + cfb + cid) * baseBudget n e :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hK : ((2 + 2 * kl + cfb + cid : ℕ) : ℝ) = 2 + 2 * (kl : ℝ) + cfb + cid := by
    push_cast
    ring
  rw [hK]
  unfold largerModel
  split_ifs with hab
  · refine ⟨hscore B I.sufB, ?_, hself B⟩
    exact hfall A B pB hxA I.totalB I.lenB I.prodB I.sufA (by rwa [min_eq_left hab] at hsmall)
  · refine ⟨hscore A I.sufA, hself A, ?_⟩
    exact hfall B A pA hxB I.totalA I.lenA I.prodA I.sufB
      (by rwa [min_eq_right (by omega)] at hsmall)

/-- The larger-bucket model contains `x`. -/
theorem mem_largerModel {x : BitString} {A B : Finset BitString} (hA : x ∈ A) (hB : x ∈ B) :
    x ∈ largerModel A B := by
  unfold largerModel
  split_ifs
  · exact hB
  · exact hA

/-- **T03: candidate bounds (blueprint `UpperCandidateBounds`).**  Given M04 and M08, for an
optimal `V` there are `c_min` and `b_cand` such that for every `c_* ≥ c_min`, at every qualifying
instance and `0 ≤ r ≤ n`, the candidate `D` of the `r`-th trial contains `x` and has score and both
endpoint costs at most `b_cand T_r`, `T_r = (j_r + 1) L_r`. -/
theorem upperCandidateBounds (V : Map) (hV : isOptimalConditional V)
    (hM04 : CoverageStmt V) (hM08 : AdjacentCapStmt V) :
    ∃ cmin bcand : ℕ, ∀ cs : ℕ, cmin ≤ cs → ∀ (n e r : ℕ) (pA pB x : BitString)
      (A B : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
        x ∈ (instTrial cs n e r pA pB x A B).1 ∧
        modelScore V (instTrial cs n e r pA pB x A B).1 x ≤
          bcand * ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) ∧
        setTotalC (instTrial cs n e r pA pB x A B).1 A ≤
          bcand * ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) ∧
        setTotalC (instTrial cs n e r pA pB x A B).1 B ≤
          bcand * ((((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r : ℕ) : ℝ) := by
  obtain ⟨c₀, hc₀⟩ := hM04
  obtain ⟨cmin₈, badj, h₈⟩ := hM08
  obtain ⟨cpt, hpt⟩ := upperMinCoreLocalDecoder V hV
  obtain ⟨kf, hkf⟩ := fallback_bounds V hV
  refine ⟨c₀ + cmin₈ + 1, kf + badj + cpt + 1,
    fun cs hcs n e r pA pB x A B h hrn => ?_⟩
  set P := coreShape pA pB n A B with hP
  set L := trialStep cs n e r with hLdef
  have hB1 := one_le_baseBudget n e
  have hH1 : (1 : ℝ) ≤ baseBudget n e := by exact_mod_cast hB1
  have hL1 : 1 ≤ L := by
    rw [hLdef, trialStep]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcovL : (c₀ : ℝ) * baseBudget n e ≤ L := by
    have h1 : c₀ * baseBudget n e ≤ L := by
      rw [hLdef, trialStep]
      exact Nat.mul_le_mul (by omega) (Nat.le_add_right _ _)
    exact_mod_cast h1
  have hHL : (baseBudget n e : ℝ) ≤ L := by
    have h1 : baseBudget n e ≤ L := by
      rw [hLdef, trialStep]
      calc baseBudget n e ≤ baseBudget n e + r := Nat.le_add_right _ _
        _ ≤ cs * (baseBudget n e + r) := Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast h1
  have hxA := h.sufA.1
  have hxB := h.sufB.1
  have hPa : P.a = Nat.log 2 A.card := rfl
  have hPb : P.b = Nat.log 2 B.card := rfl
  -- generalize the trial result
  have hexit := trialRun_exit P hL1 (largerModel A B) x
  change TrialExit P L (largerModel A B) x (instTrial cs n e r pA pB x A B).1
    (instTrial cs n e r pA pB x A B).2 at hexit
  generalize (instTrial cs n e r pA pB x A B) = res at hexit ⊢
  obtain ⟨D, j⟩ := res
  simp only at hexit ⊢
  set T : ℝ := (((j + 1) * L : ℕ) : ℝ) with hTdef
  have hLT : (L : ℝ) ≤ T := by
    rw [hTdef]
    exact_mod_cast Nat.le_mul_of_pos_left L (Nat.succ_pos j)
  have hHT : (baseBudget n e : ℝ) ≤ T := hHL.trans hLT
  have hT0 : 0 ≤ T := by positivity
  have hjLT : ((j * L : ℕ) : ℝ) ≤ T := by
    rw [hTdef]
    exact_mod_cast Nat.mul_le_mul_right L (Nat.le_succ j)
  have hbc : (1 : ℝ) + kf ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hbc' : (1 : ℝ) + badj ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hbc'' : (1 : ℝ) + cpt ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hkfT : (kf : ℝ) * baseBudget n e ≤ kf * T :=
    mul_le_mul_of_nonneg_left hHT (Nat.cast_nonneg _)
  have hbaT : (badj : ℝ) * baseBudget n e ≤ badj * T :=
    mul_le_mul_of_nonneg_left hHT (Nat.cast_nonneg _)
  have hcpT : (cpt : ℝ) * baseBudget n e ≤ cpt * T :=
    mul_le_mul_of_nonneg_left hHT (Nat.cast_nonneg _)
  -- the fallback branch with threshold `M ≤ T`
  have hfall : ∀ M : ℕ, min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤ M → (M : ℝ) ≤ T →
      D = largerModel A B →
      x ∈ D ∧ modelScore V D x ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T ∧
        setTotalC D A ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T ∧
        setTotalC D B ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T := by
    intro M hM hMT hD
    subst hD
    obtain ⟨f1, f2, f3⟩ := hkf n e pA pB x A B M h hM
    have hm1 : ((1 : ℝ) + kf) * T ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T :=
      mul_le_mul_of_nonneg_right hbc hT0
    refine ⟨mem_largerModel hxA hxB, by linarith, by linarith, by linarith⟩
  -- a missing core at a budget `c₀ H ≤ s < min (a, b)` is impossible
  have hcov : ∀ s : ℕ, L ≤ s → s < min P.a P.b → coreOf P s x ≠ none := by
    intro s hLs hs hnone
    have hs' : (c₀ : ℝ) * baseBudget n e ≤ s := hcovL.trans (by exact_mod_cast hLs)
    obtain ⟨F, hF⟩ := hc₀ n e pA pB x A B s h hs' (lt_of_lt_of_le hs (min_le_left _ _))
      (lt_of_lt_of_le hs (min_le_right _ _))
    have hF' : coreOf P s x = some F := hF
    rw [hnone] at hF'
    exact Option.some_ne_none F hF'.symm
  rcases hexit with ⟨hj, hD, hdeg⟩ | ⟨hj, hD, hlt, hnone⟩ | ⟨hR, hD, hdeg | hnone⟩ |
      ⟨hR, hlt, hcore, F', hF', hcmp⟩
  · exact hfall L hdeg hLT hD
  · exact absurd hnone (hcov L le_rfl hlt)
  · exact hfall _ hdeg le_rfl hD
  · by_cases hdeg : min P.a P.b ≤ (j + 1) * L
    · exact hfall _ hdeg le_rfl hD
    · exact absurd hnone (hcov _ (Nat.le_mul_of_pos_left L (Nat.succ_pos j)) (not_le.mp hdeg))
  · -- comparison stop
    obtain ⟨hj1, -, -, -⟩ := hR
    have hxD : x ∈ D := (coreOf_spec hcore).2
    have hsa : j * L ≤ Nat.log 2 A.card := by
      have := lt_of_lt_of_le hlt (min_le_left _ _)
      rw [hPa] at this
      nlinarith
    have hsb : j * L ≤ Nat.log 2 B.card := by
      have := lt_of_lt_of_le hlt (min_le_right _ _)
      rw [hPb] at this
      nlinarith
    have hsL : j * L + cs * (baseBudget n e + r) = (j + 1) * L := by
      rw [hLdef, trialStep]
      ring
    obtain ⟨F'', hF'', -, hsc⟩ := h₈ cs (by omega) n e r (j * L) pA pB x A B D h hrn
      (by rw [hsL]; exact lt_of_lt_of_le hlt (min_le_left _ _))
      (by rw [hsL]; exact lt_of_lt_of_le hlt (min_le_right _ _)) hcore
    rw [hsL] at hF''
    have hFF : F'' = F' := Option.some_inj.mp (hF''.symm.trans hF')
    subst hFF
    have hne : F''.Nonempty := ⟨x, (coreOf_spec hF').2⟩
    have hlog := logb_card_le_of_le_pow_mul hcmp hne
    obtain ⟨e1, e2, e3⟩ := hpt n e pA pB x A B (j * L) D h hsa hsb hcore
    have hm2 : ((1 : ℝ) + badj) * T ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T :=
      mul_le_mul_of_nonneg_right hbc' hT0
    have hm3 : ((1 : ℝ) + cpt) * T ≤ ((kf + badj + cpt + 1 : ℕ) : ℝ) * T :=
      mul_le_mul_of_nonneg_right hbc'' hT0
    refine ⟨hxD, by linarith, ?_, ?_⟩
    · unfold setTotalC
      linarith
    · unfold setTotalC
      linarith

end Kolmogorov.StrongMerging.Upper
