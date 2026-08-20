import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import KolmogorovMathlib.CommonInformation.FiniteQuadruple

/-!
# Conditional independence chains (SUV Exercise 315)

SUV Exercise 315 (p. 364) extends the conditionally-independent-but-dependent
Boolean pair of Theorem 217 / Exercise 314 (`FiniteQuadruple.lean`) to an
arbitrary agreement probability `c ∈ (0, 1)`.  The source asks for **finite
chains** of Boolean random variables `α₀, α₁, …, α_k` and `β₀, β₁, …, β_k` on a
common probability space such that

* `α₀` and `β₀` are uniformly distributed in `{0,1}`;
* `Pr[α₀ = β₀] = c`;
* `αᵢ` and `βᵢ` are independent given `α_{i+1}`  (for `0 ≤ i < k`);
* `αᵢ` and `βᵢ` are independent given `β_{i+1}`  (for `0 ≤ i < k`);
* `α_k` and `β_k` are independent.

## Encoding

A joint law of the `2k+2` Boolean variables is a nonnegative weight function on
`Fin (2k+2) → Bool` of total mass `1` (`Kolmogorov.ChainDist`).  Coordinate `i`
(`0 ≤ i ≤ k`) is `αᵢ`; coordinate `k+1+i` is `βᵢ`
(`Kolmogorov.chainAlphaIdx`, `Kolmogorov.chainBetaIdx`).  Conditional
independence is stated in the **division-free** product form
`Pr[X=x, Y=y, Z=z] · Pr[Z=z] = Pr[X=x, Z=z] · Pr[Y=y, Z=z]`, which is correct
even on null conditioning fibers, matching `QuadDist.CondIndepGivenGamma`.

## Main results

* `Kolmogorov.ChainDist.IsIndep315Chain` — the full chain of conditional
  independence relations of the source, quantified over `i : Fin k` with the
  `Fin.castSucc`/`Fin.succ`/`Fin.last` indexing.
* `Kolmogorov.base_chain` — **fully proved**: for `c ∈ [3/8, 5/8]` a length-`1`
  chain exists.  This is precisely the Exercise-314 quadruple `(α, β, γ, δ)`
  reread as `(α₀, β₀, α₁, β₁)`: `CondIndepGivenGamma` becomes
  `α₀ ⫫ β₀ | α₁`, `CondIndepGivenDelta` becomes `α₀ ⫫ β₀ | β₁`, and
  `GammaDeltaIndep` becomes the top relation `α₁ ⫫ β₁`.
* `Kolmogorov.exercise_315_conditional_independence_chains` — the honest full
  statement for every `c ∈ (0, 1)`.  The base range `[3/8, 5/8]` is discharged
  by `base_chain`, and the range below `3/8` by the proved `α₀`-inversion
  construction.  The high range is obtained from the explicit distribution
  extension `extend_independence_chain` and the proved iteration-surjectivity
  theorem `iterate_reaches`.
-/

open Finset

namespace Kolmogorov

/-! ### Summation bridge for `Fin 4 → Bool` -/

/-- The evaluation equivalence `(Fin 4 → Bool) ≃ Bool⁴`. -/
def boolFinFourEquiv : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun v := (v 0, v 1, v 2, v 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv p := by rfl

/-- A sum over all `Fin 4 → Bool` unfolds into a fourfold Boolean sum. -/
theorem sum_boolFinFour (F : (Fin 4 → Bool) → ℝ) :
    ∑ v, F v = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, F ![a, b, c, d] := by
  rw [← Equiv.sum_comp boolFinFourEquiv.symm F]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, boolFinFourEquiv,
    Equiv.coe_fn_symm_mk]

/-! ### Chain distributions -/

/-- Coordinate of `αᵢ` in a length-`k` chain. -/
def chainAlphaIdx {k : ℕ} (i : Fin (k + 1)) : Fin (2 * k + 2) := ⟨i.val, by omega⟩

/-- Coordinate of `βᵢ` in a length-`k` chain. -/
def chainBetaIdx {k : ℕ} (i : Fin (k + 1)) : Fin (2 * k + 2) := ⟨k + 1 + i.val, by omega⟩

/-- A joint distribution of the `2k+2` Boolean variables `α₀,…,α_k, β₀,…,β_k`,
given by a nonnegative weight function of total mass `1`. -/
structure ChainDist (k : ℕ) where
  /-- The elementary probabilities `Pr[(αᵢ)ᵢ, (βᵢ)ᵢ = v]`. -/
  w : (Fin (2 * k + 2) → Bool) → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ v, 0 ≤ w v
  /-- The total mass is one. -/
  total : ∑ v, w v = 1

namespace ChainDist

variable {k : ℕ} (D : ChainDist k)

/-- The probability of the event described by the Boolean predicate `S`. -/
def pr (S : (Fin (2 * k + 2) → Bool) → Bool) : ℝ := ∑ v, if S v then D.w v else 0

/-- `Pr[coord j = v]`. -/
def prAt (j : Fin (2 * k + 2)) (v : Bool) : ℝ := D.pr fun w => w j == v

/-- `Pr[coord j₁ = v₁, coord j₂ = v₂]`. -/
def prAt2 (j₁ j₂ : Fin (2 * k + 2)) (v₁ v₂ : Bool) : ℝ :=
  D.pr fun w => (w j₁ == v₁) && (w j₂ == v₂)

/-- `Pr[coord j₁ = v₁, coord j₂ = v₂, coord j₃ = v₃]`. -/
def prAt3 (j₁ j₂ j₃ : Fin (2 * k + 2)) (v₁ v₂ v₃ : Bool) : ℝ :=
  D.pr fun w => (w j₁ == v₁) && (w j₂ == v₂) && (w j₃ == v₃)

/-- Coordinates `j₁` and `j₂` are independent given `j₃` (division-free form). -/
def CondIndepCoords (j₁ j₂ j₃ : Fin (2 * k + 2)) : Prop :=
  ∀ v₁ v₂ v₃, D.prAt3 j₁ j₂ j₃ v₁ v₂ v₃ * D.prAt j₃ v₃
    = D.prAt2 j₁ j₃ v₁ v₃ * D.prAt2 j₂ j₃ v₂ v₃

/-- Coordinates `j₁` and `j₂` are independent. -/
def IndepCoords (j₁ j₂ : Fin (2 * k + 2)) : Prop :=
  ∀ v₁ v₂, D.prAt2 j₁ j₂ v₁ v₂ = D.prAt j₁ v₁ * D.prAt j₂ v₂

/-- The agreement probability `Pr[α₀ = β₀]`. -/
def prAgree01 : ℝ := D.pr fun w => w (chainAlphaIdx 0) == w (chainBetaIdx 0)

/-- The full chain of conditional-independence relations of SUV Exercise 315:
for every link `i`, `αᵢ ⫫ βᵢ | α_{i+1}` and `αᵢ ⫫ βᵢ | β_{i+1}`, and at the top
`α_k ⫫ β_k`. -/
def IsIndep315Chain : Prop :=
  (∀ i : Fin k, D.CondIndepCoords (chainAlphaIdx i.castSucc) (chainBetaIdx i.castSucc)
      (chainAlphaIdx i.succ)) ∧
  (∀ i : Fin k, D.CondIndepCoords (chainAlphaIdx i.castSucc) (chainBetaIdx i.castSucc)
      (chainBetaIdx i.succ)) ∧
  D.IndepCoords (chainAlphaIdx (Fin.last k)) (chainBetaIdx (Fin.last k))

end ChainDist

/-! ### The length-1 chain built from an Exercise-314 quadruple -/

open ChainDist QuadDist

/-- Reread an Exercise-314 quadruple `(α, β, γ, δ)` as a length-`1` chain
`(α₀, β₀, α₁, β₁) = (α, β, γ, δ)`.  Coordinates: `α₀ = v 0`, `α₁ = v 1`,
`β₀ = v 2`, `β₁ = v 3`. -/
noncomputable def chainOfQuad (D : QuadDist) : ChainDist 1 where
  w v := D.w (v 0) (v 2) (v 1) (v 3)
  nonneg v := D.nonneg _ _ _ _
  total := by
    rw [sum_boolFinFour (fun v => D.w (v 0) (v 2) (v 1) (v 3))]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    have hD := D.total
    simp only [Fintype.sum_bool] at hD ⊢
    ring_nf
    ring_nf at hD
    linarith [hD]

namespace chainOfQuad

variable (Q : QuadDist)

/-- Master reduction: a `chainOfQuad` probability of a coordinatewise event is
the corresponding `QuadDist` sum (with the `α₁ = γ`, `β₀ = β` transposition). -/
theorem pr_eq (S : Bool → Bool → Bool → Bool → Bool) :
    (chainOfQuad Q).pr (fun v => S (v 0) (v 1) (v 2) (v 3))
      = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
          if S a b c d then Q.w a c b d else 0 := by
  unfold ChainDist.pr chainOfQuad
  rw [sum_boolFinFour]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

theorem prAt0 (a : Bool) : (chainOfQuad Q).prAt 0 a = Q.prAlpha a := by
  unfold ChainDist.prAt QuadDist.prAlpha
  rw [pr_eq Q (fun x0 _ _ _ => x0 == a)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt1 (g : Bool) : (chainOfQuad Q).prAt 1 g = Q.prGamma g := by
  unfold ChainDist.prAt QuadDist.prGamma
  rw [pr_eq Q (fun _ x1 _ _ => x1 == g)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2c (b : Bool) : (chainOfQuad Q).prAt 2 b = Q.prBeta b := by
  unfold ChainDist.prAt QuadDist.prBeta
  rw [pr_eq Q (fun _ _ x2 _ => x2 == b)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt3c (d : Bool) : (chainOfQuad Q).prAt 3 d = Q.prDelta d := by
  unfold ChainDist.prAt QuadDist.prDelta
  rw [pr_eq Q (fun _ _ _ x3 => x3 == d)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2_01 (a g : Bool) : (chainOfQuad Q).prAt2 0 1 a g = Q.prAlphaGamma a g := by
  unfold ChainDist.prAt2 QuadDist.prAlphaGamma
  rw [pr_eq Q (fun x0 x1 _ _ => (x0 == a) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2_21 (b g : Bool) : (chainOfQuad Q).prAt2 2 1 b g = Q.prBetaGamma b g := by
  unfold ChainDist.prAt2 QuadDist.prBetaGamma
  rw [pr_eq Q (fun _ x1 x2 _ => (x2 == b) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2_03 (a d : Bool) : (chainOfQuad Q).prAt2 0 3 a d = Q.prAlphaDelta a d := by
  unfold ChainDist.prAt2 QuadDist.prAlphaDelta
  rw [pr_eq Q (fun x0 _ _ x3 => (x0 == a) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2_23 (b d : Bool) : (chainOfQuad Q).prAt2 2 3 b d = Q.prBetaDelta b d := by
  unfold ChainDist.prAt2 QuadDist.prBetaDelta
  rw [pr_eq Q (fun _ _ x2 x3 => (x2 == b) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt2_13 (g d : Bool) : (chainOfQuad Q).prAt2 1 3 g d = Q.prGammaDelta g d := by
  unfold ChainDist.prAt2 QuadDist.prGammaDelta
  rw [pr_eq Q (fun _ x1 _ x3 => (x1 == g) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt3_021 (a b g : Bool) :
    (chainOfQuad Q).prAt3 0 2 1 a b g = Q.prAlphaBetaGamma a b g := by
  unfold ChainDist.prAt3 QuadDist.prAlphaBetaGamma
  rw [pr_eq Q (fun x0 x1 x2 _ => (x0 == a) && (x2 == b) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem prAt3_023 (a b d : Bool) :
    (chainOfQuad Q).prAt3 0 2 3 a b d = Q.prAlphaBetaDelta a b d := by
  unfold ChainDist.prAt3 QuadDist.prAlphaBetaDelta
  rw [pr_eq Q (fun x0 _ x2 x3 => (x0 == a) && (x2 == b) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

theorem idxA0 : chainAlphaIdx (0 : Fin 2) = (0 : Fin 4) := by decide
theorem idxB0 : chainBetaIdx (0 : Fin 2) = (2 : Fin 4) := by decide

theorem prAgree01_eq : (chainOfQuad Q).prAgree01 = Q.prAgree := by
  unfold ChainDist.prAgree01 QuadDist.prAgree
  rw [idxA0, idxB0, pr_eq Q (fun x0 _ x2 _ => x0 == x2)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

end chainOfQuad


/-! ### Chain inversion (α₀ flip) -/

def flip0 {k : ℕ} (v : Fin (2 * k + 2) → Bool) : Fin (2 * k + 2) → Bool :=
  Function.update v (chainAlphaIdx 0) (! v (chainAlphaIdx 0))

theorem flip0_involutive {k : ℕ} : Function.Involutive (@flip0 k) := by
  intro v; ext j; unfold flip0; by_cases h : j = chainAlphaIdx 0 <;> simp [h]

def flip0Equiv {k : ℕ} : Equiv (Fin (2 * k + 2) → Bool) (Fin (2 * k + 2) → Bool) :=
  Equiv.mk flip0 flip0 flip0_involutive flip0_involutive

def invertChainDist {k : ℕ} (D : ChainDist k) : ChainDist k where
  w v := D.w (flip0 v)
  nonneg v := D.nonneg (flip0 v)
  total := by
    have h : ∑ v, D.w (flip0 v) = ∑ v, D.w v := Equiv.sum_comp flip0Equiv D.w
    rw [h]; exact D.total

theorem flip0_pr {k : ℕ} (D : ChainDist k) (S : (Fin (2 * k + 2) → Bool) → Bool) :
    (invertChainDist D).pr S = D.pr (fun v => S (flip0 v)) := by
  unfold ChainDist.pr invertChainDist
  change ∑ v, (if S v then D.w (flip0 v) else 0) =
    ∑ v, (if S (flip0 v) then D.w v else 0)
  have h : ∑ v, (if S v then D.w (flip0 v) else 0) =
      ∑ v, (if S (flip0 v) then D.w (flip0 (flip0 v)) else 0) :=
    (Equiv.sum_comp (flip0Equiv (k := k)) (fun v => if S v then D.w (flip0 v) else 0)).symm
  rw [h]; congr; ext v; rw [flip0_involutive v]

def eval0 {k : ℕ} (j : Fin (2 * k + 2)) (v : Bool) : Bool :=
  if j = chainAlphaIdx 0 then !v else v

theorem flip0_eval {k : ℕ} (v : Fin (2 * k + 2) → Bool) (j : Fin (2 * k + 2)) :
    (flip0 v) j = eval0 j (v j) := by
  unfold flip0 eval0 Function.update; split_ifs with h <;> [subst h; skip] <;> rfl

theorem eval0_eq {k : ℕ} (j : Fin (2 * k + 2)) (x v : Bool) :
    (eval0 j x == v) = (x == eval0 j v) := by
  unfold eval0; split_ifs; cases x <;> cases v <;> decide; rfl

theorem invert_chain_prAt {k : ℕ} (D : ChainDist k) (j : Fin (2 * k + 2)) (v : Bool) :
    (invertChainDist D).prAt j v = D.prAt j (eval0 j v) := by
  unfold ChainDist.prAt; rw [flip0_pr]
  have h : (fun w => (flip0 w) j == v) = (fun w => w j == eval0 j v) := by
    ext w; rw [flip0_eval, eval0_eq]
  rw [h]

theorem invert_chain_prAt2 {k : ℕ} (D : ChainDist k) (j₁ j₂ : Fin (2 * k + 2)) (v₁ v₂ : Bool) :
    (invertChainDist D).prAt2 j₁ j₂ v₁ v₂ = D.prAt2 j₁ j₂ (eval0 j₁ v₁) (eval0 j₂ v₂) := by
  unfold ChainDist.prAt2; rw [flip0_pr]
  have h : (fun w => ((flip0 w) j₁ == v₁) && ((flip0 w) j₂ == v₂)) =
           (fun w => (w j₁ == eval0 j₁ v₁) && (w j₂ == eval0 j₂ v₂)) := by
    ext w; rw [flip0_eval, flip0_eval, eval0_eq, eval0_eq]
  rw [h]

theorem invert_chain_prAt3 {k : ℕ} (D : ChainDist k)
    (j₁ j₂ j₃ : Fin (2 * k + 2)) (v₁ v₂ v₃ : Bool) :
    (invertChainDist D).prAt3 j₁ j₂ j₃ v₁ v₂ v₃ =
      D.prAt3 j₁ j₂ j₃ (eval0 j₁ v₁) (eval0 j₂ v₂) (eval0 j₃ v₃) := by
  unfold ChainDist.prAt3; rw [flip0_pr]
  have h :
      (fun w => ((flip0 w) j₁ == v₁) && ((flip0 w) j₂ == v₂) && ((flip0 w) j₃ == v₃)) =
        (fun w =>
          (w j₁ == eval0 j₁ v₁) && (w j₂ == eval0 j₂ v₂) && (w j₃ == eval0 j₃ v₃)) := by
    ext w; rw [flip0_eval, flip0_eval, flip0_eval, eval0_eq, eval0_eq, eval0_eq]
  rw [h]

theorem invert_chain_IsIndep315Chain {k : ℕ} (D : ChainDist k)
    (hchain : D.IsIndep315Chain) : (invertChainDist D).IsIndep315Chain := by
  unfold ChainDist.IsIndep315Chain at hchain ⊢; rcases hchain with ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i; unfold ChainDist.CondIndepCoords; intro v₁ v₂ v₃
    rw [invert_chain_prAt3, invert_chain_prAt, invert_chain_prAt2, invert_chain_prAt2]
    exact h1 i _ _ _
  · intro i; unfold ChainDist.CondIndepCoords; intro v₁ v₂ v₃
    rw [invert_chain_prAt3, invert_chain_prAt, invert_chain_prAt2, invert_chain_prAt2]
    exact h2 i _ _ _
  · unfold ChainDist.IndepCoords; intro v₁ v₂
    rw [invert_chain_prAt2, invert_chain_prAt, invert_chain_prAt]
    exact h3 _ _

theorem invert_chain {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) :
    ∃ D' : ChainDist k, (∀ a, D'.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D'.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D'.prAgree01 = 1 - c ∧ D'.IsIndep315Chain := by
  refine ⟨invertChainDist D, ?_, ?_, ?_, ?_⟩
  · intro a; rw [invert_chain_prAt]; exact hα _
  · intro b; rw [invert_chain_prAt]; exact hβ _
  · unfold ChainDist.prAgree01; rw [flip0_pr]
    have h :
        (fun (w : Fin (2 * k + 2) → Bool) =>
          (flip0 w) (chainAlphaIdx 0) == (flip0 w) (chainBetaIdx 0)) =
          (fun w => !(w (chainAlphaIdx 0) == w (chainBetaIdx 0))) := by
      ext w; rw [flip0_eval, flip0_eval]; unfold eval0
      have h_ne : (chainBetaIdx 0 : Fin (2 * k + 2)) ≠ chainAlphaIdx 0 := by
        intro h
        have h1 : (chainBetaIdx 0 : Fin (2 * k + 2)).val =
            (chainAlphaIdx 0 : Fin (2 * k + 2)).val := congr_arg Fin.val h
        unfold chainBetaIdx chainAlphaIdx at h1; revert h1; simp
      rw [if_pos rfl, if_neg h_ne]
      cases (w (chainAlphaIdx 0)) <;> cases (w (chainBetaIdx 0)) <;> decide
    rw [h]
    unfold ChainDist.prAgree01 at hagree; unfold ChainDist.pr at hagree ⊢
    change (∑ w, if w (chainAlphaIdx 0) == w (chainBetaIdx 0) then D.w w else 0) = c at hagree
    have h_total := D.total
    have h_split : (∑ v : Fin (2 * k + 2) → Bool, D.w v) =
        (∑ v : Fin (2 * k + 2) → Bool,
          if !(v (chainAlphaIdx 0) == v (chainBetaIdx 0)) then D.w v else 0) +
        (∑ v : Fin (2 * k + 2) → Bool,
          if v (chainAlphaIdx 0) == v (chainBetaIdx 0) then D.w v else 0) := by
      rw [← sum_add_distrib]
      congr
      ext v
      by_cases hv : v (chainAlphaIdx 0) == v (chainBetaIdx 0) <;> simp [hv]
    linarith
  · exact invert_chain_IsIndep315Chain D hchain

def chainHalvesEquiv (k : ℕ) :
    (Fin (2 * k + 2) → Bool) ≃
      (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool) :=
  let eidx : Fin (2 * k + 2) ≃ Fin (k + 1) ⊕ Fin (k + 1) :=
    (finCongr (by omega : 2 * k + 2 = (k + 1) + (k + 1))).trans finSumFinEquiv.symm
  (Equiv.piCongrLeft (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => Bool) eidx).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => Bool))

theorem chainHalvesEquiv_alpha (k : ℕ) (v : Fin (2 * k + 2) → Bool)
    (i : Fin (k + 1)) :
    (chainHalvesEquiv k v).1 i = v (chainAlphaIdx i) := by
  simp only [chainHalvesEquiv, Equiv.piCongrLeft, Equiv.symm_symm, Equiv.trans_apply,
    finCongr_apply, Equiv.piCongrLeft'_symm, Equiv.sumPiEquivProdPi_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_trans_apply, finCongr_symm,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat]
  apply congrArg v
  apply Fin.ext
  simp [chainAlphaIdx]

theorem chainHalvesEquiv_beta (k : ℕ) (v : Fin (2 * k + 2) → Bool)
    (i : Fin (k + 1)) :
    (chainHalvesEquiv k v).2 i = v (chainBetaIdx i) := by
  simp only [chainHalvesEquiv, Equiv.piCongrLeft, Equiv.symm_symm, Equiv.trans_apply,
    finCongr_apply, Equiv.piCongrLeft'_symm, Equiv.sumPiEquivProdPi_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_trans_apply, finCongr_symm,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat]
  apply congrArg v
  apply Fin.ext
  simp [chainBetaIdx]
  omega

theorem chainHalvesEquiv_symm_alpha (k : ℕ)
    (p : (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) (i : Fin (k + 1)) :
    (chainHalvesEquiv k).symm p (chainAlphaIdx i) = p.1 i := by
  have h := chainHalvesEquiv_alpha k ((chainHalvesEquiv k).symm p) i
  simpa using h.symm

theorem chainHalvesEquiv_symm_beta (k : ℕ)
    (p : (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) (i : Fin (k + 1)) :
    (chainHalvesEquiv k).symm p (chainBetaIdx i) = p.2 i := by
  have h := chainHalvesEquiv_beta k ((chainHalvesEquiv k).symm p) i
  simpa using h.symm

def rearrangeStep (k : ℕ) :
    ((Bool × (Fin (k + 1) → Bool)) × (Bool × (Fin (k + 1) → Bool))) ≃
      (((Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) × Bool × Bool) where
  toFun p := ((p.1.2, p.2.2), p.1.1, p.2.1)
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def extensionEquiv (k : ℕ) :
    (Fin (2 * (k + 1) + 2) → Bool) ≃
      (Fin (2 * k + 2) → Bool) × Bool × Bool :=
  (chainHalvesEquiv (k + 1)).trans
    (((Fin.consEquiv (fun _ : Fin (k + 2) => Bool)).symm).prodCongr
      (Fin.consEquiv (fun _ : Fin (k + 2) => Bool)).symm) |>.trans
    (rearrangeStep k) |>.trans
    ((chainHalvesEquiv k).symm.prodCongr (Equiv.refl (Bool × Bool)))

theorem extensionEquiv_newAlpha (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool) :
    (extensionEquiv k v).2.1 = v (chainAlphaIdx 0) := by
  rfl

theorem extensionEquiv_newBeta (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool) :
    (extensionEquiv k v).2.2 = v (chainBetaIdx 0) := by
  change (chainHalvesEquiv (k + 1) v).2 0 = _
  exact chainHalvesEquiv_beta (k + 1) v 0

theorem extensionEquiv_oldAlpha (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool)
    (i : Fin (k + 1)) :
    (extensionEquiv k v).1 (chainAlphaIdx i) = v (chainAlphaIdx i.succ) := by
  change (chainHalvesEquiv k).symm
      ((Fin.tail (chainHalvesEquiv (k + 1) v).1),
        (Fin.tail (chainHalvesEquiv (k + 1) v).2)) (chainAlphaIdx i) = _
  rw [chainHalvesEquiv_symm_alpha]
  change (chainHalvesEquiv (k + 1) v).1 i.succ = _
  exact chainHalvesEquiv_alpha (k + 1) v i.succ

theorem extensionEquiv_oldBeta (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool)
    (i : Fin (k + 1)) :
    (extensionEquiv k v).1 (chainBetaIdx i) = v (chainBetaIdx i.succ) := by
  change (chainHalvesEquiv k).symm
      ((Fin.tail (chainHalvesEquiv (k + 1) v).1),
        (Fin.tail (chainHalvesEquiv (k + 1) v).2)) (chainBetaIdx i) = _
  rw [chainHalvesEquiv_symm_beta]
  change (chainHalvesEquiv (k + 1) v).2 i.succ = _
  exact chainHalvesEquiv_beta (k + 1) v i.succ

noncomputable def chainStepKernel (c : ℝ) (a b g d : Bool) : ℝ :=
  if g = d then
    if a = g ∧ b = g then 1 else 0
  else if a = b then (1 - c) / 4 else (1 + c) / 4

theorem chainStepKernel_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (a b g d : Bool) : 0 ≤ chainStepKernel c a b g d := by
  cases a <;> cases b <;> cases g <;> cases d <;>
    simp [chainStepKernel] <;> linarith

theorem chainStepKernel_sum (c : ℝ) (g d : Bool) :
    ∑ a : Bool, ∑ b : Bool, chainStepKernel c a b g d = 1 := by
  cases g <;> cases d <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

noncomputable def extendChainDist {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : ChainDist (k + 1) where
  w v :=
    let p := extensionEquiv k v
    D.w p.1 * chainStepKernel c p.2.1 p.2.2
      (p.1 (chainAlphaIdx 0)) (p.1 (chainBetaIdx 0))
  nonneg v := mul_nonneg (D.nonneg _) (chainStepKernel_nonneg hc0 hc1 _ _ _ _)
  total := by
    change ∑ v, D.w (extensionEquiv k v).1 *
      chainStepKernel c (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
        ((extensionEquiv k v).1 (chainAlphaIdx 0))
        ((extensionEquiv k v).1 (chainBetaIdx 0)) = 1
    rw [← Equiv.sum_comp (extensionEquiv k).symm]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
    calc
      ∑ old, ∑ a, ∑ b, D.w old * chainStepKernel c a b
          (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) = ∑ old, D.w old := by
        apply Finset.sum_congr rfl
        intro old _
        simp_rw [← Finset.mul_sum]
        rw [chainStepKernel_sum, mul_one]
      _ = 1 := D.total

theorem extendChainDist_pr_eq {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (S : Bool → Bool → (Fin (2 * k + 2) → Bool) → Bool) :
    (extendChainDist D c hc0 hc1).pr
        (fun v => S (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
          (extensionEquiv k v).1) =
      ∑ old, ∑ a : Bool, ∑ b : Bool,
        if S a b old then
          D.w old * chainStepKernel c a b
            (old (chainAlphaIdx 0)) (old (chainBetaIdx 0))
        else 0 := by
  unfold ChainDist.pr extendChainDist
  rw [← Equiv.sum_comp (extensionEquiv k).symm]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]

theorem extendChainDist_pr_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (S : (Fin (2 * k + 2) → Bool) → Bool) :
    (extendChainDist D c hc0 hc1).pr (fun v => S (extensionEquiv k v).1) =
      D.pr S := by
  rw [extendChainDist_pr_eq D c hc0 hc1 (fun _ _ old => S old)]
  unfold ChainDist.pr
  apply Finset.sum_congr rfl
  intro old _
  by_cases h : S old
  · simp only [h, if_true]
    simp_rw [← Finset.mul_sum]
    rw [chainStepKernel_sum, mul_one]
  · simp [h]

def oldCoordInNew {k : ℕ} (j : Fin (2 * k + 2)) : Fin (2 * (k + 1) + 2) :=
  if h : j.val < k + 1 then ⟨j.val + 1, by omega⟩ else ⟨j.val + 2, by omega⟩

theorem oldCoordInNew_alpha {k : ℕ} (i : Fin (k + 1)) :
    oldCoordInNew (chainAlphaIdx i) = chainAlphaIdx i.succ := by
  have hi : i.val ≤ k := by omega
  apply Fin.ext
  simp [oldCoordInNew, chainAlphaIdx, hi]

theorem oldCoordInNew_beta {k : ℕ} (i : Fin (k + 1)) :
    oldCoordInNew (chainBetaIdx i) = chainBetaIdx i.succ := by
  have hi : ¬k + 1 + i.val ≤ k := by omega
  apply Fin.ext
  simp [oldCoordInNew, chainBetaIdx, hi]
  omega

theorem extensionEquiv_old_apply {k : ℕ}
    (v : Fin (2 * (k + 1) + 2) → Bool) (j : Fin (2 * k + 2)) :
    (extensionEquiv k v).1 j = v (oldCoordInNew j) := by
  by_cases h : j.val < k + 1
  · let i : Fin (k + 1) := ⟨j.val, h⟩
    have hj : j = chainAlphaIdx i := by apply Fin.ext; rfl
    rw [hj, extensionEquiv_oldAlpha, oldCoordInNew_alpha]
  · let i : Fin (k + 1) := ⟨j.val - (k + 1), by omega⟩
    have hj : j = chainBetaIdx i := by apply Fin.ext; simp [i, chainBetaIdx]; omega
    rw [hj, extensionEquiv_oldBeta, oldCoordInNew_beta]

theorem extendChainDist_prAt_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j : Fin (2 * k + 2)) (x : Bool) :
    (extendChainDist D c hc0 hc1).prAt (oldCoordInNew j) x = D.prAt j x := by
  unfold ChainDist.prAt
  have hevent : (fun w => w (oldCoordInNew j) == x) =
      (fun v => (extensionEquiv k v).1 j == x) := by
    funext v
    rw [extensionEquiv_old_apply]
  rw [hevent]
  exact extendChainDist_pr_old D c hc0 hc1 (fun old => old j == x)

theorem extendChainDist_prAt2_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ : Fin (2 * k + 2)) (x₁ x₂ : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (oldCoordInNew j₁) (oldCoordInNew j₂)
        x₁ x₂ = D.prAt2 j₁ j₂ x₁ x₂ := by
  unfold ChainDist.prAt2
  have hevent :
      (fun w => (w (oldCoordInNew j₁) == x₁) && (w (oldCoordInNew j₂) == x₂)) =
      (fun v => ((extensionEquiv k v).1 j₁ == x₁) &&
        ((extensionEquiv k v).1 j₂ == x₂)) := by
    funext v
    rw [extensionEquiv_old_apply, extensionEquiv_old_apply]
  rw [hevent]
  exact extendChainDist_pr_old D c hc0 hc1
    (fun old => (old j₁ == x₁) && (old j₂ == x₂))

theorem extendChainDist_prAt3_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ j₃ : Fin (2 * k + 2))
    (x₁ x₂ x₃ : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (oldCoordInNew j₁) (oldCoordInNew j₂)
        (oldCoordInNew j₃) x₁ x₂ x₃ = D.prAt3 j₁ j₂ j₃ x₁ x₂ x₃ := by
  unfold ChainDist.prAt3
  have hevent :
      (fun w => (w (oldCoordInNew j₁) == x₁) && (w (oldCoordInNew j₂) == x₂) &&
        (w (oldCoordInNew j₃) == x₃)) =
      (fun v => ((extensionEquiv k v).1 j₁ == x₁) &&
        ((extensionEquiv k v).1 j₂ == x₂) &&
        ((extensionEquiv k v).1 j₃ == x₃)) := by
    funext v
    rw [extensionEquiv_old_apply, extensionEquiv_old_apply,
      extensionEquiv_old_apply]
  rw [hevent]
  exact extendChainDist_pr_old D c hc0 hc1
    (fun old => (old j₁ == x₁) && (old j₂ == x₂) && (old j₃ == x₃))

theorem ChainDist.prAt_eq_sum_prAt2_right {k : ℕ} (D : ChainDist k)
    (j₁ j₂ : Fin (2 * k + 2)) (x : Bool) :
    D.prAt j₁ x = ∑ y : Bool, D.prAt2 j₁ j₂ x y := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  simp only [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v j₁ = false ∨ v j₁ = true := by cases v j₁ <;> simp
  have h₂ : v j₂ = false ∨ v j₂ = true := by cases v j₂ <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    cases x <;> simp [h₁, h₂]

theorem ChainDist.prAt_eq_sum_prAt2_left {k : ℕ} (D : ChainDist k)
    (j₁ j₂ : Fin (2 * k + 2)) (y : Bool) :
    D.prAt j₂ y = ∑ x : Bool, D.prAt2 j₁ j₂ x y := by
  unfold ChainDist.prAt ChainDist.prAt2 ChainDist.pr
  simp only [Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v j₁ = false ∨ v j₁ = true := by cases v j₁ <;> simp
  have h₂ : v j₂ = false ∨ v j₂ = true := by cases v j₂ <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    cases y <;> simp [h₁, h₂]

theorem ChainDist.prAgree01_eq_diag {k : ℕ} (D : ChainDist k) :
    D.prAgree01 = D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) false false +
      D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) true true := by
  unfold ChainDist.prAgree01 ChainDist.prAt2 ChainDist.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v (chainAlphaIdx 0) = false ∨ v (chainAlphaIdx 0) = true := by
    cases v (chainAlphaIdx 0) <;> simp
  have h₂ : v (chainBetaIdx 0) = false ∨ v (chainBetaIdx 0) = true := by
    cases v (chainBetaIdx 0) <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

theorem ChainDist.uniform_pair_joint {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (a b : Bool) :
    D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) a b =
      if a = b then c / 2 else (1 - c) / 2 := by
  have hr0 := D.prAt_eq_sum_prAt2_right (chainAlphaIdx 0) (chainBetaIdx 0) false
  have hr1 := D.prAt_eq_sum_prAt2_right (chainAlphaIdx 0) (chainBetaIdx 0) true
  have hc0 := D.prAt_eq_sum_prAt2_left (chainAlphaIdx 0) (chainBetaIdx 0) false
  have hd := D.prAgree01_eq_diag
  simp only [Fintype.sum_bool] at hr0 hr1 hc0
  rw [hα false] at hr0
  rw [hα true] at hr1
  rw [hβ false] at hc0
  rw [hagree] at hd
  cases a <;> cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte] <;> linarith

theorem ChainDist.sum_weight_mul_pair {k : ℕ} (D : ChainDist k)
    (F : Bool → Bool → ℝ) :
    ∑ v, D.w v * F (v (chainAlphaIdx 0)) (v (chainBetaIdx 0)) =
      ∑ g : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d * F g d := by
  simp only [Fintype.sum_bool]
  unfold ChainDist.prAt2 ChainDist.pr
  simp_rw [Finset.sum_mul]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ : v (chainAlphaIdx 0) = false ∨ v (chainAlphaIdx 0) = true := by
    cases v (chainAlphaIdx 0) <;> simp
  have h₂ : v (chainBetaIdx 0) = false ∨ v (chainBetaIdx 0) = true := by
    cases v (chainBetaIdx 0) <;> simp
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

theorem extendChainDist_pr_pair_sum {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (S : Bool → Bool → Bool → Bool → Bool) :
    (extendChainDist D c hc0 hc1).pr (fun v =>
        S (v (chainAlphaIdx 0)) (v (chainBetaIdx 0))
          (v (chainAlphaIdx (Fin.succ 0))) (v (chainBetaIdx (Fin.succ 0)))) =
      ∑ g : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d *
          (∑ a : Bool, ∑ b : Bool,
            if S a b g d then chainStepKernel c a b g d else 0) := by
  have hevent :
      (fun v : Fin (2 * (k + 1) + 2) → Bool =>
        S (v (chainAlphaIdx 0)) (v (chainBetaIdx 0))
          (v (chainAlphaIdx (Fin.succ 0))) (v (chainBetaIdx (Fin.succ 0)))) =
      (fun v => S (extensionEquiv k v).2.1 (extensionEquiv k v).2.2
        ((extensionEquiv k v).1 (chainAlphaIdx 0))
        ((extensionEquiv k v).1 (chainBetaIdx 0))) := by
    funext v
    rw [extensionEquiv_newAlpha, extensionEquiv_newBeta,
      extensionEquiv_oldAlpha, extensionEquiv_oldBeta]
  rw [hevent]
  rw [extendChainDist_pr_eq D c hc0 hc1
    (fun a b old => S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)))]
  calc
    (∑ old, ∑ a : Bool, ∑ b : Bool,
        if S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) then
          D.w old * chainStepKernel c a b
            (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) else 0) =
        ∑ old, D.w old *
          (∑ a : Bool, ∑ b : Bool,
            if S a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) then
              chainStepKernel c a b (old (chainAlphaIdx 0)) (old (chainBetaIdx 0))
            else 0) := by
      apply Finset.sum_congr rfl
      intro old _
      simp only [Fintype.sum_bool]
      by_cases hTT : S true true (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hTF : S true false (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hFT : S false true (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        by_cases hFF : S false false (old (chainAlphaIdx 0)) (old (chainBetaIdx 0)) <;>
        simp [hTT, hTF, hFT, hFF] <;> ring
    _ = _ := D.sum_weight_mul_pair (fun g d =>
      ∑ a : Bool, ∑ b : Bool,
        if S a b g d then chainStepKernel c a b g d else 0)

theorem extendChainDist_prAlpha {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (a : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainAlphaIdx 0) a = 1 / 2 := by
  unfold ChainDist.prAt
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun a' _ _ _ => a' == a)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> simp only [Fintype.sum_bool] <;> simp [chainStepKernel] <;> ring

theorem extendChainDist_prBeta {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (b : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainBetaIdx 0) b = 1 / 2 := by
  unfold ChainDist.prAt
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun _ b' _ _ => b' == b)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases b <;> simp only [Fintype.sum_bool] <;> simp [chainStepKernel] <;> ring

theorem extendChainDist_prAgree {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).prAgree01 = (c ^ 2 + 1) / 2 := by
  unfold ChainDist.prAgree01
  rw [extendChainDist_pr_pair_sum D c hc0 hc1 (fun a b _ _ => a == b)]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  simp only [Fintype.sum_bool]
  simp [chainStepKernel]
  ring

theorem extendChainDist_prAt3_new_givenAlpha {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b g : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (chainAlphaIdx 0) (chainBetaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) a b g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (b' == b) && (g' == g) then
              chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt3] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' b' g' _ => (a' == a) && (b' == b) && (g' == g))

theorem extendChainDist_prAt_newAlphaNext {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (g : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainAlphaIdx (Fin.succ 0)) g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if g' == g then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ _ g' _ => g' == g)

theorem extendChainDist_prAt2_newAlpha_alphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a g : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainAlphaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) a g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (g' == g) then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' _ g' _ => (a' == a) && (g' == g))

theorem extendChainDist_prAt2_newBeta_alphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (b g : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainBetaIdx 0)
        (chainAlphaIdx (Fin.succ 0)) b g =
      ∑ g' : Bool, ∑ d : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g' d *
          (∑ a' : Bool, ∑ b' : Bool,
            if (b' == b) && (g' == g) then chainStepKernel c a' b' g' d else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ b' g' _ => (b' == b) && (g' == g))

theorem extendChainDist_condIndepGivenAlphaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (chainAlphaIdx 0) (chainBetaIdx 0) (chainAlphaIdx (Fin.succ 0)) := by
  intro a b g
  rw [extendChainDist_prAt3_new_givenAlpha,
    extendChainDist_prAt_newAlphaNext,
    extendChainDist_prAt2_newAlpha_alphaNext,
    extendChainDist_prAt2_newBeta_alphaNext]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> cases b <;> cases g <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

theorem extendChainDist_prAt3_new_givenBeta {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b d : Bool) :
    (extendChainDist D c hc0 hc1).prAt3 (chainAlphaIdx 0) (chainBetaIdx 0)
        (chainBetaIdx (Fin.succ 0)) a b d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (b' == b) && (d' == d) then
              chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt3] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' b' _ d' => (a' == a) && (b' == b) && (d' == d))

theorem extendChainDist_prAt_newBetaNext {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (d : Bool) :
    (extendChainDist D c hc0 hc1).prAt (chainBetaIdx (Fin.succ 0)) d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if d' == d then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ _ _ d' => d' == d)

theorem extendChainDist_prAt2_newAlpha_betaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a d : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainAlphaIdx 0)
        (chainBetaIdx (Fin.succ 0)) a d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (a' == a) && (d' == d) then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun a' _ _ d' => (a' == a) && (d' == d))

theorem extendChainDist_prAt2_newBeta_betaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (b d : Bool) :
    (extendChainDist D c hc0 hc1).prAt2 (chainBetaIdx 0)
        (chainBetaIdx (Fin.succ 0)) b d =
      ∑ g : Bool, ∑ d' : Bool,
        D.prAt2 (chainAlphaIdx 0) (chainBetaIdx 0) g d' *
          (∑ a' : Bool, ∑ b' : Bool,
            if (b' == b) && (d' == d) then chainStepKernel c a' b' g d' else 0) := by
  simpa [ChainDist.prAt2] using extendChainDist_pr_pair_sum D c hc0 hc1
    (fun _ b' _ d' => (b' == b) && (d' == d))

theorem extendChainDist_condIndepGivenBetaNext {k : ℕ}
    (D : ChainDist k) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (chainAlphaIdx 0) (chainBetaIdx 0) (chainBetaIdx (Fin.succ 0)) := by
  intro a b d
  rw [extendChainDist_prAt3_new_givenBeta,
    extendChainDist_prAt_newBetaNext,
    extendChainDist_prAt2_newAlpha_betaNext,
    extendChainDist_prAt2_newBeta_betaNext]
  simp_rw [D.uniform_pair_joint hα hβ hagree]
  cases a <;> cases b <;> cases d <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

theorem extendChainDist_condIndep_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ j₃ : Fin (2 * k + 2))
    (h : D.CondIndepCoords j₁ j₂ j₃) :
    (extendChainDist D c hc0 hc1).CondIndepCoords
      (oldCoordInNew j₁) (oldCoordInNew j₂) (oldCoordInNew j₃) := by
  intro x₁ x₂ x₃
  rw [extendChainDist_prAt3_old, extendChainDist_prAt_old,
    extendChainDist_prAt2_old, extendChainDist_prAt2_old]
  exact h x₁ x₂ x₃

theorem extendChainDist_indep_old {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (j₁ j₂ : Fin (2 * k + 2))
    (h : D.IndepCoords j₁ j₂) :
    (extendChainDist D c hc0 hc1).IndepCoords
      (oldCoordInNew j₁) (oldCoordInNew j₂) := by
  intro x₁ x₂
  rw [extendChainDist_prAt2_old, extendChainDist_prAt_old,
    extendChainDist_prAt_old]
  exact h x₁ x₂

theorem extendChainDist_isChain {k : ℕ} (D : ChainDist k) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) :
    (extendChainDist D c hc0 hc1).IsIndep315Chain := by
  rcases hchain with ⟨hchainα, hchainβ, htop⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact extendChainDist_condIndepGivenAlphaNext D c hc0 hc1 hα hβ hagree
    · have h := extendChainDist_condIndep_old D c hc0 hc1
        (chainAlphaIdx j.castSucc) (chainBetaIdx j.castSucc) (chainAlphaIdx j.succ)
        (hchainα j)
      simpa only [oldCoordInNew_alpha, oldCoordInNew_beta] using h
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact extendChainDist_condIndepGivenBetaNext D c hc0 hc1 hα hβ hagree
    · have h := extendChainDist_condIndep_old D c hc0 hc1
        (chainAlphaIdx j.castSucc) (chainBetaIdx j.castSucc) (chainBetaIdx j.succ)
        (hchainβ j)
      simpa only [oldCoordInNew_alpha, oldCoordInNew_beta] using h
  · have h := extendChainDist_indep_old D c hc0 hc1
      (chainAlphaIdx (Fin.last k)) (chainBetaIdx (Fin.last k)) htop
    simpa only [oldCoordInNew_alpha, oldCoordInNew_beta] using h

/-- The exact construction step from the hint to SUV Exercise 315.  A chain
realizing `c` can be extended by one link to realize `(c²+1)/2`.  The new
bottom pair is conditionally independent given either coordinate of the old
bottom pair; all old links are shifted up unchanged. -/
theorem extend_independence_chain {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) :
    ∃ D' : ChainDist (k + 1),
      (∀ a, D'.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D'.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D'.prAgree01 = (c ^ 2 + 1) / 2 ∧ D'.IsIndep315Chain := by
  refine ⟨extendChainDist D c hc0 hc1, ?_, ?_, ?_, ?_⟩
  · exact extendChainDist_prAlpha D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_prBeta D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_prAgree D c hc0 hc1 hα hβ hagree
  · exact extendChainDist_isChain D c hc0 hc1 hα hβ hagree hchain

theorem iterate_reaches (c : ℝ) (h1 : 1 / 2 < c) (h2 : c < 1) :
    ∃ (n : ℕ) (c₀ : ℝ), 1 / 2 < c₀ ∧ c₀ ≤ 5 / 8 ∧
      (fun x => (x ^ 2 + 1) / 2)^[n] c₀ = c := by
  let f : ℝ → ℝ := fun x => (x ^ 2 + 1) / 2
  let a : ℕ → ℝ := fun n => f^[n] (1 / 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have ha_succ (n : ℕ) : a (n + 1) = f (a n) := by
    simp only [a, Function.iterate_succ_apply']
  have ha_bounds : ∀ n, 1 / 2 ≤ a n ∧ a n ≤ 1 := by
    intro n
    induction n with
    | zero => norm_num [a]
    | succ n ih =>
        rw [show n + 1 = n.succ from rfl, ha_succ]
        dsimp [f]
        constructor <;> nlinarith [sq_nonneg (a n), sq_nonneg (a n - 1)]
  have ha_step (n : ℕ) : a n ≤ a (n + 1) := by
    rw [ha_succ]
    dsimp [f]
    nlinarith [sq_nonneg (a n - 1)]
  have ha_mono : Monotone a := monotone_nat_of_le_succ ha_step
  have ha_bdd : BddAbove (Set.range a) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (ha_bounds n).2
  let l : ℝ := ⨆ n, a n
  have hl : Filter.Tendsto a Filter.atTop (nhds l) :=
    tendsto_atTop_ciSup ha_mono ha_bdd
  have hl_shift : Filter.Tendsto (fun n => a (n + 1)) Filter.atTop (nhds l) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  have hl_map : Filter.Tendsto (fun n => f (a n)) Filter.atTop (nhds (f l)) :=
    hf.continuousAt.tendsto.comp hl
  have hfix : f l = l := by
    apply tendsto_nhds_unique hl_map
    convert hl_shift using 1
    ext n
    exact (ha_succ n).symm
  have hl_one : l = 1 := by
    dsimp [f] at hfix
    nlinarith [sq_nonneg (l - 1)]
  rw [hl_one] at hl
  have hex : ∃ n, c ≤ a n := by
    have hev : ∀ᶠ n in Filter.atTop, c < a n := (tendsto_order.1 hl).1 c h2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    exact ⟨N, (hN N le_rfl).le⟩
  let N := Nat.find hex
  have hN : c ≤ a N := Nat.find_spec hex
  have hN_ne : N ≠ 0 := by
    intro hzero
    have hN' := hN
    rw [hzero] at hN'
    norm_num [a] at hN'
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN_ne
  have hn_lt : a n < c := by
    have hnot : ¬ c ≤ a n := by
      apply Nat.find_min hex
      omega
    exact lt_of_not_ge hnot
  have hc_mem : c ∈ Set.Icc ((f^[n]) (1 / 2)) ((f^[n]) (5 / 8)) := by
    have hfive : (5 / 8 : ℝ) = f (1 / 2) := by
      dsimp [f]
      norm_num
    have hlo : (f^[n]) (1 / 2) = a n := rfl
    have hhi : (f^[n]) (5 / 8) = a N := by
      rw [hfive]
      change f^[n] (f (1 / 2)) = f^[N] (1 / 2)
      rw [hn, Function.iterate_succ_apply]
    rw [hlo, hhi]
    exact ⟨hn_lt.le, hN⟩
  obtain ⟨c₀, hc₀, hc₀eq⟩ :=
    intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8)
      (hf.iterate n).continuousOn hc_mem
  refine ⟨n, c₀, ?_, hc₀.2, ?_⟩
  · apply lt_of_le_of_ne hc₀.1
    intro heq
    have hc₀half : c₀ = 1 / 2 := heq.symm
    rw [hc₀half] at hc₀eq
    change a n = c at hc₀eq
    linarith
  · exact hc₀eq

/-- Iterating `extend_independence_chain` realizes every finite forward iterate
of the agreement transformation. -/
theorem extend_independence_chain_iterate {k : ℕ} (D : ChainDist k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hα : ∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2)
    (hβ : ∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2)
    (hagree : D.prAgree01 = c) (hchain : D.IsIndep315Chain) (n : ℕ) :
    ∃ (k' : ℕ) (D' : ChainDist k'),
      (∀ a, D'.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D'.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D'.prAgree01 = (fun x => (x ^ 2 + 1) / 2)^[n] c ∧
      D'.IsIndep315Chain := by
  let f : ℝ → ℝ := fun x => (x ^ 2 + 1) / 2
  have hiter_bounds : ∀ m, 0 ≤ f^[m] c ∧ f^[m] c ≤ 1 := by
    intro m
    induction m with
    | zero => simpa [f] using And.intro hc0 hc1
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        dsimp [f]
        constructor <;> nlinarith [sq_nonneg (f^[m] c), sq_nonneg (f^[m] c - 1)]
  induction n with
  | zero =>
      exact ⟨k, D, hα, hβ, by simpa [f] using hagree, hchain⟩
  | succ n ih =>
      obtain ⟨k', D', hα', hβ', hagree', hchain'⟩ := ih
      obtain ⟨D'', hα'', hβ'', hagree'', hchain''⟩ :=
        extend_independence_chain D' (hiter_bounds n).1 (hiter_bounds n).2
          hα' hβ' hagree' hchain'
      refine ⟨k' + 1, D'', hα'', hβ'', ?_, hchain''⟩
      rw [Function.iterate_succ_apply']
      exact hagree''


/-! ### Exercise 315 -/

/-- **Exercise 315, base range.**  For every `c ∈ [3/8, 5/8]` there is a
length-`1` conditional-independence chain with `Pr[α₀ = β₀] = c` and uniform
`α₀, β₀`.  This is the Exercise-314 quadruple reread as a chain, and it
discharges the base of the general statement below. -/
theorem base_chain (c : ℝ) (hc0 : 3 / 8 ≤ c) (hc1 : c ≤ 5 / 8) :
    ∃ D : ChainDist 1,
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  obtain ⟨Q, hα, hβ, hγδ, hcg, hcd, hagree, _hjoint⟩ :=
    exercise_314_conditionally_independent_uniform_pair c hc0 hc1
  refine ⟨chainOfQuad Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [show (0 : Fin (1 + 1)) = (0 : Fin 2) from rfl, chainOfQuad.idxA0,
      chainOfQuad.prAt0]
    exact hα a
  · intro b
    rw [show (0 : Fin (1 + 1)) = (0 : Fin 2) from rfl, chainOfQuad.idxB0,
      chainOfQuad.prAt2c]
    exact hβ b
  · rw [chainOfQuad.prAgree01_eq]; exact hagree
  · -- `αᵢ ⫫ βᵢ | α_{i+1}` at the single link `i = 0`, i.e. `α₀ ⫫ β₀ | α₁`.
    refine Fin.forall_fin_one.mpr ?_
    change (chainOfQuad Q).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (1 : Fin 4)
    intro v₁ v₂ v₃
    rw [chainOfQuad.prAt3_021, chainOfQuad.prAt1, chainOfQuad.prAt2_01,
      chainOfQuad.prAt2_21]
    exact hcg v₁ v₂ v₃
  · -- `αᵢ ⫫ βᵢ | β_{i+1}` at the single link `i = 0`, i.e. `α₀ ⫫ β₀ | β₁`.
    refine Fin.forall_fin_one.mpr ?_
    change (chainOfQuad Q).CondIndepCoords (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
    intro v₁ v₂ v₃
    rw [chainOfQuad.prAt3_023, chainOfQuad.prAt3c, chainOfQuad.prAt2_03,
      chainOfQuad.prAt2_23]
    exact hcd v₁ v₂ v₃
  · -- Top relation `α₁ ⫫ β₁`.
    change (chainOfQuad Q).IndepCoords (1 : Fin 4) (3 : Fin 4)
    intro v₁ v₂
    rw [chainOfQuad.prAt2_13, chainOfQuad.prAt1, chainOfQuad.prAt3c]
    exact hγδ v₁ v₂


theorem exercise_315_chain_of_ge_3_8 (c : ℝ) (hc0 : 3 / 8 ≤ c) (hc1 : c < 1) :
    ∃ (k : ℕ) (D : ChainDist k),
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  by_cases hhi : c ≤ 5 / 8
  · -- Base range `c ∈ [3/8, 5/8]`: the Exercise-314 quadruple as a chain.
    obtain ⟨D, h1, h2, h3, h4⟩ := base_chain c hc0 hhi
    exact ⟨1, D, h1, h2, h3, h4⟩
  · -- `c ∈ (5/8, 1)`: pull `c` back to the base interval and extend the
    -- resulting chain by the required number of source construction steps.
    have hc_half : 1 / 2 < c := by
      have : 5 / 8 < c := lt_of_not_ge hhi
      norm_num at this ⊢
      linarith
    obtain ⟨n, c₀, hc₀half, hc₀base, hciterate⟩ := iterate_reaches c hc_half hc1
    have hc₀low : 3 / 8 ≤ c₀ := by linarith
    obtain ⟨D, hα, hβ, hagree, hchain⟩ := base_chain c₀ hc₀low hc₀base
    obtain ⟨k', D', hα', hβ', hagree', hchain'⟩ :=
      extend_independence_chain_iterate D (by linarith : 0 ≤ c₀) (by linarith : c₀ ≤ 1)
        hα hβ hagree hchain n
    rw [hciterate] at hagree'
    exact ⟨k', D', hα', hβ', hagree', hchain'⟩

/-- **SUV Exercise 315.**  For every `c ∈ (0, 1)` there is a finite chain
`α₀,…,α_k, β₀,…,β_k` of Boolean random variables with uniform `α₀, β₀`,
`Pr[α₀ = β₀] = c`, and the full chain of conditional-independence relations
`IsIndep315Chain`.

The base range `c ∈ [3/8, 5/8]` is proved (via `base_chain`, i.e. Theorem 217 /
Exercise 314), the high range by iterating `extend_independence_chain`, and the
low range by the proved `α₀`-inversion construction. -/
theorem exercise_315_conditional_independence_chains (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ (k : ℕ) (D : ChainDist k),
      (∀ a, D.prAt (chainAlphaIdx 0) a = 1 / 2) ∧
      (∀ b, D.prAt (chainBetaIdx 0) b = 1 / 2) ∧
      D.prAgree01 = c ∧
      D.IsIndep315Chain := by
  by_cases hlo : 3 / 8 ≤ c
  · exact exercise_315_chain_of_ge_3_8 c hlo hc1
  · have hc_1 : 3 / 8 ≤ 1 - c := by linarith
    have hc_2 : 1 - c < 1 := by linarith
    obtain ⟨k, D, h1, h2, h3, h4⟩ := exercise_315_chain_of_ge_3_8 (1 - c) hc_1 hc_2
    obtain ⟨D', h1', h2', h3', h4'⟩ := invert_chain D h1 h2 h3 h4
    rw [sub_sub_cancel] at h3'
    exact ⟨k, D', h1', h2', h3', h4'⟩

end Kolmogorov
