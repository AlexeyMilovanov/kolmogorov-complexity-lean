import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import KolmogorovMathlib.CommonInformation.FiniteQuadruple



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
  simp only [Fintype.sum_prod_type]
  rfl

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

/-- Coordinate `0` of `chainOfQuad Q` is distributed as the `α` marginal of `Q`. -/
theorem prAt0 (a : Bool) : (chainOfQuad Q).prAt 0 a = Q.prAlpha a := by
  unfold ChainDist.prAt QuadDist.prAlpha
  rw [pr_eq Q (fun x0 _ _ _ => x0 == a)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinate `1` of `chainOfQuad Q` is distributed as the `γ` marginal of `Q`. -/
theorem prAt1 (g : Bool) : (chainOfQuad Q).prAt 1 g = Q.prGamma g := by
  unfold ChainDist.prAt QuadDist.prGamma
  rw [pr_eq Q (fun _ x1 _ _ => x1 == g)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinate `2` of `chainOfQuad Q` is distributed as the `β` marginal of `Q`. -/
theorem prAt2c (b : Bool) : (chainOfQuad Q).prAt 2 b = Q.prBeta b := by
  unfold ChainDist.prAt QuadDist.prBeta
  rw [pr_eq Q (fun _ _ x2 _ => x2 == b)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinate `3` of `chainOfQuad Q` is distributed as the `δ` marginal of `Q`. -/
theorem prAt3c (d : Bool) : (chainOfQuad Q).prAt 3 d = Q.prDelta d := by
  unfold ChainDist.prAt QuadDist.prDelta
  rw [pr_eq Q (fun _ _ _ x3 => x3 == d)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `0, 1` of `chainOfQuad Q` have the joint law of `(α, γ)` under `Q`. -/
theorem prAt2_01 (a g : Bool) : (chainOfQuad Q).prAt2 0 1 a g = Q.prAlphaGamma a g := by
  unfold ChainDist.prAt2 QuadDist.prAlphaGamma
  rw [pr_eq Q (fun x0 x1 _ _ => (x0 == a) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `2, 1` of `chainOfQuad Q` have the joint law of `(β, γ)` under `Q`. -/
theorem prAt2_21 (b g : Bool) : (chainOfQuad Q).prAt2 2 1 b g = Q.prBetaGamma b g := by
  unfold ChainDist.prAt2 QuadDist.prBetaGamma
  rw [pr_eq Q (fun _ x1 x2 _ => (x2 == b) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `0, 3` of `chainOfQuad Q` have the joint law of `(α, δ)` under `Q`. -/
theorem prAt2_03 (a d : Bool) : (chainOfQuad Q).prAt2 0 3 a d = Q.prAlphaDelta a d := by
  unfold ChainDist.prAt2 QuadDist.prAlphaDelta
  rw [pr_eq Q (fun x0 _ _ x3 => (x0 == a) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `2, 3` of `chainOfQuad Q` have the joint law of `(β, δ)` under `Q`. -/
theorem prAt2_23 (b d : Bool) : (chainOfQuad Q).prAt2 2 3 b d = Q.prBetaDelta b d := by
  unfold ChainDist.prAt2 QuadDist.prBetaDelta
  rw [pr_eq Q (fun _ _ x2 x3 => (x2 == b) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `1, 3` of `chainOfQuad Q` have the joint law of `(γ, δ)` under `Q`. -/
theorem prAt2_13 (g d : Bool) : (chainOfQuad Q).prAt2 1 3 g d = Q.prGammaDelta g d := by
  unfold ChainDist.prAt2 QuadDist.prGammaDelta
  rw [pr_eq Q (fun _ x1 _ x3 => (x1 == g) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `0, 2, 1` of `chainOfQuad Q` have the joint law of `(α, β, γ)` under
`Q`. -/
theorem prAt3_021 (a b g : Bool) :
    (chainOfQuad Q).prAt3 0 2 1 a b g = Q.prAlphaBetaGamma a b g := by
  unfold ChainDist.prAt3 QuadDist.prAlphaBetaGamma
  rw [pr_eq Q (fun x0 x1 x2 _ => (x0 == a) && (x2 == b) && (x1 == g))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- Coordinates `0, 2, 3` of `chainOfQuad Q` have the joint law of `(α, β, δ)` under
`Q`. -/
theorem prAt3_023 (a b d : Bool) :
    (chainOfQuad Q).prAt3 0 2 3 a b d = Q.prAlphaBetaDelta a b d := by
  unfold ChainDist.prAt3 QuadDist.prAlphaBetaDelta
  rw [pr_eq Q (fun x0 _ x2 x3 => (x0 == a) && (x2 == b) && (x3 == d))]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

/-- The coordinate of `α₀` in a length-one chain is `0`. -/
theorem idxA0 : chainAlphaIdx (0 : Fin 2) = (0 : Fin 4) := by decide
/-- The coordinate of `β₀` in a length-one chain is `2`. -/
theorem idxB0 : chainBetaIdx (0 : Fin 2) = (2 : Fin 4) := by decide

/-- The probability that the two initial coordinates of `chainOfQuad Q` agree is the
agreement probability of `Q`. -/
theorem prAgree01_eq : (chainOfQuad Q).prAgree01 = Q.prAgree := by
  unfold ChainDist.prAgree01 QuadDist.prAgree
  rw [idxA0, idxB0, pr_eq Q (fun x0 _ x2 _ => x0 == x2)]; unfold QuadDist.pr
  simp only [Fintype.sum_bool]; ring

end chainOfQuad


/-! ### Chain inversion (α₀ flip) -/

/-- Negation of the coordinate `α₀` of a chain configuration, leaving all other
coordinates unchanged. -/
def flip0 {k : ℕ} (v : Fin (2 * k + 2) → Bool) : Fin (2 * k + 2) → Bool :=
  Function.update v (chainAlphaIdx 0) (! v (chainAlphaIdx 0))

/-- Flipping the coordinate `α₀` twice is the identity. -/
theorem flip0_involutive {k : ℕ} : Function.Involutive (@flip0 k) := by
  intro v; ext j; unfold flip0; by_cases h : j = chainAlphaIdx 0 <;> simp [h]

/-- The involution `flip0` as a permutation of chain configurations. -/
def flip0Equiv {k : ℕ} : Equiv (Fin (2 * k + 2) → Bool) (Fin (2 * k + 2) → Bool) :=
  Equiv.mk flip0 flip0 flip0_involutive flip0_involutive

/-- The distribution obtained by negating the coordinate `α₀`, which turns the
agreement probability `c` into `1 - c`. -/
def invertChainDist {k : ℕ} (D : ChainDist k) : ChainDist k where
  w v := D.w (flip0 v)
  nonneg v := D.nonneg (flip0 v)
  total := by
    have h : ∑ v, D.w (flip0 v) = ∑ v, D.w v := Equiv.sum_comp flip0Equiv D.w
    rw [h]; exact D.total

/-- An event has the same probability under the flipped distribution as its preimage
under `flip0` has under the original. -/
theorem flip0_pr {k : ℕ} (D : ChainDist k) (S : (Fin (2 * k + 2) → Bool) → Bool) :
    (invertChainDist D).pr S = D.pr (fun v => S (flip0 v)) := by
  unfold ChainDist.pr invertChainDist
  change ∑ v, (if S v then D.w (flip0 v) else 0) =
    ∑ v, (if S (flip0 v) then D.w v else 0)
  have h : ∑ v, (if S v then D.w (flip0 v) else 0) =
      ∑ v, (if S (flip0 v) then D.w (flip0 (flip0 v)) else 0) :=
    (Equiv.sum_comp (flip0Equiv (k := k)) (fun v => if S v then D.w (flip0 v) else 0)).symm
  rw [h]; congr; ext v; rw [flip0_involutive v]

/-- The value that the coordinate `j` takes after the flip, given its value before:
negated at `α₀` and unchanged elsewhere. -/
def eval0 {k : ℕ} (j : Fin (2 * k + 2)) (v : Bool) : Bool :=
  if j = chainAlphaIdx 0 then !v else v

/-- The flipped configuration read at `j` is `eval0 j` applied to the original value. -/
theorem flip0_eval {k : ℕ} (v : Fin (2 * k + 2) → Bool) (j : Fin (2 * k + 2)) :
    (flip0 v) j = eval0 j (v j) := by
  unfold flip0 eval0 Function.update; split_ifs with h <;> [subst h; skip] <;> rfl

/-- The test `eval0 j x = v` is equivalent to `x = eval0 j v`, since `eval0 j` is an
involution of `Bool`. -/
theorem eval0_eq {k : ℕ} (j : Fin (2 * k + 2)) (x v : Bool) :
    (eval0 j x == v) = (x == eval0 j v) := by
  unfold eval0; split_ifs; cases x <;> cases v <;> decide; rfl

/-- A one-coordinate marginal of the flipped distribution is the marginal of the
original at the flipped value. -/
theorem invert_chain_prAt {k : ℕ} (D : ChainDist k) (j : Fin (2 * k + 2)) (v : Bool) :
    (invertChainDist D).prAt j v = D.prAt j (eval0 j v) := by
  unfold ChainDist.prAt; rw [flip0_pr]
  have h : (fun w => (flip0 w) j == v) = (fun w => w j == eval0 j v) := by
    ext w; rw [flip0_eval, eval0_eq]
  rw [h]

/-- A two-coordinate marginal of the flipped distribution is the marginal of the
original at the flipped values. -/
theorem invert_chain_prAt2 {k : ℕ} (D : ChainDist k) (j₁ j₂ : Fin (2 * k + 2)) (v₁ v₂ : Bool) :
    (invertChainDist D).prAt2 j₁ j₂ v₁ v₂ = D.prAt2 j₁ j₂ (eval0 j₁ v₁) (eval0 j₂ v₂) := by
  unfold ChainDist.prAt2; rw [flip0_pr]
  have h : (fun w => ((flip0 w) j₁ == v₁) && ((flip0 w) j₂ == v₂)) =
           (fun w => (w j₁ == eval0 j₁ v₁) && (w j₂ == eval0 j₂ v₂)) := by
    ext w; rw [flip0_eval, flip0_eval, eval0_eq, eval0_eq]
  rw [h]

/-- A three-coordinate marginal of the flipped distribution is the marginal of the
original at the flipped values. -/
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

/-- Flipping `α₀` preserves the independence pattern required of a chain. -/
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

/-- From a chain with uniform initial coordinates and agreement probability `c` one
obtains a chain with the same properties and agreement probability `1 - c`. -/
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

/-- Splitting a chain configuration into its `α` half and its `β` half. -/
def chainHalvesEquiv (k : ℕ) :
    (Fin (2 * k + 2) → Bool) ≃
      (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool) :=
  let eidx : Fin (2 * k + 2) ≃ Fin (k + 1) ⊕ Fin (k + 1) :=
    (finCongr (by omega : 2 * k + 2 = (k + 1) + (k + 1))).trans finSumFinEquiv.symm
  (Equiv.piCongrLeft (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => Bool) eidx).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => Bool))

/-- The `α` half of a configuration reads the coordinates `αᵢ`. -/
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

/-- The `β` half of a configuration reads the coordinates `βᵢ`. -/
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

/-- Reassembling two halves gives back the first half at the coordinates `αᵢ`. -/
theorem chainHalvesEquiv_symm_alpha (k : ℕ)
    (p : (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) (i : Fin (k + 1)) :
    (chainHalvesEquiv k).symm p (chainAlphaIdx i) = p.1 i := by
  have h := chainHalvesEquiv_alpha k ((chainHalvesEquiv k).symm p) i
  simpa using h.symm

/-- Reassembling two halves gives back the second half at the coordinates `βᵢ`. -/
theorem chainHalvesEquiv_symm_beta (k : ℕ)
    (p : (Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) (i : Fin (k + 1)) :
    (chainHalvesEquiv k).symm p (chainBetaIdx i) = p.2 i := by
  have h := chainHalvesEquiv_beta k ((chainHalvesEquiv k).symm p) i
  simpa using h.symm

/-- Rearranging a pair of head-and-tail decompositions into the pair of tails
together with the two heads. -/
def rearrangeStep (k : ℕ) :
    ((Bool × (Fin (k + 1) → Bool)) × (Bool × (Fin (k + 1) → Bool))) ≃
      (((Fin (k + 1) → Bool) × (Fin (k + 1) → Bool)) × Bool × Bool) where
  toFun p := ((p.1.2, p.2.2), p.1.1, p.2.1)
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A configuration of a chain of length `k + 1` is a configuration of length `k`
together with the two new initial coordinates `α₀` and `β₀`. -/
def extensionEquiv (k : ℕ) :
    (Fin (2 * (k + 1) + 2) → Bool) ≃
      (Fin (2 * k + 2) → Bool) × Bool × Bool :=
  (chainHalvesEquiv (k + 1)).trans
    (((Fin.consEquiv (fun _ : Fin (k + 2) => Bool)).symm).prodCongr
      (Fin.consEquiv (fun _ : Fin (k + 2) => Bool)).symm) |>.trans
    (rearrangeStep k) |>.trans
    ((chainHalvesEquiv k).symm.prodCongr (Equiv.refl (Bool × Bool)))

/-- The first new coordinate of the decomposition is `α₀`. -/
theorem extensionEquiv_newAlpha (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool) :
    (extensionEquiv k v).2.1 = v (chainAlphaIdx 0) := by
  rfl

/-- The second new coordinate of the decomposition is `β₀`. -/
theorem extensionEquiv_newBeta (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool) :
    (extensionEquiv k v).2.2 = v (chainBetaIdx 0) := by
  change (chainHalvesEquiv (k + 1) v).2 0 = _
  exact chainHalvesEquiv_beta (k + 1) v 0

/-- The shorter configuration reads `αᵢ` as the coordinate `αᵢ₊₁` of the longer one. -/
theorem extensionEquiv_oldAlpha (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool)
    (i : Fin (k + 1)) :
    (extensionEquiv k v).1 (chainAlphaIdx i) = v (chainAlphaIdx i.succ) := by
  change (chainHalvesEquiv k).symm
      ((Fin.tail (chainHalvesEquiv (k + 1) v).1),
        (Fin.tail (chainHalvesEquiv (k + 1) v).2)) (chainAlphaIdx i) = _
  rw [chainHalvesEquiv_symm_alpha]
  change (chainHalvesEquiv (k + 1) v).1 i.succ = _
  exact chainHalvesEquiv_alpha (k + 1) v i.succ

/-- The shorter configuration reads `βᵢ` as the coordinate `βᵢ₊₁` of the longer one. -/
theorem extensionEquiv_oldBeta (k : ℕ) (v : Fin (2 * (k + 1) + 2) → Bool)
    (i : Fin (k + 1)) :
    (extensionEquiv k v).1 (chainBetaIdx i) = v (chainBetaIdx i.succ) := by
  change (chainHalvesEquiv k).symm
      ((Fin.tail (chainHalvesEquiv (k + 1) v).1),
        (Fin.tail (chainHalvesEquiv (k + 1) v).2)) (chainBetaIdx i) = _
  rw [chainHalvesEquiv_symm_beta]
  change (chainHalvesEquiv (k + 1) v).2 i.succ = _
  exact chainHalvesEquiv_beta (k + 1) v i.succ

/-- The transition kernel of one chain extension step: given the previous pair
`(g, d)`, the new pair `(a, b)` copies `g` when `g = d`, and otherwise agrees
with probability `(1 - c) / 2`. -/
noncomputable def chainStepKernel (c : ℝ) (a b g d : Bool) : ℝ :=
  if g = d then
    if a = g ∧ b = g then 1 else 0
  else if a = b then (1 - c) / 4 else (1 + c) / 4

/-- For `c` in the unit interval the step kernel is nonnegative. -/
theorem chainStepKernel_nonneg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (a b g d : Bool) : 0 ≤ chainStepKernel c a b g d := by
  cases a <;> cases b <;> cases g <;> cases d <;>
    simp [chainStepKernel] <;> linarith

/-- The step kernel is a probability distribution on the new pair, for each previous
pair. -/
theorem chainStepKernel_sum (c : ℝ) (g d : Bool) :
    ∑ a : Bool, ∑ b : Bool, chainStepKernel c a b g d = 1 := by
  cases g <;> cases d <;> simp only [Fintype.sum_bool] <;>
    simp [chainStepKernel] <;> ring

/-- The chain of length `k + 1` obtained from a chain of length `k` by prepending a
pair drawn from the step kernel with parameter `c`. -/
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

/-- Probability of an event of the extended chain, written as a sum over the old
configuration and the two new coordinates weighted by the step kernel. -/
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

/-- An event depending only on the old coordinates has the same probability under
the extended chain as under the original. -/
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

/-- The coordinate of the longer chain corresponding to a coordinate of the shorter
one. -/
def oldCoordInNew {k : ℕ} (j : Fin (2 * k + 2)) : Fin (2 * (k + 1) + 2) :=
  if h : j.val < k + 1 then ⟨j.val + 1, by omega⟩ else ⟨j.val + 2, by omega⟩

/-- The old coordinate `αᵢ` sits at `αᵢ₊₁` of the longer chain. -/
theorem oldCoordInNew_alpha {k : ℕ} (i : Fin (k + 1)) :
    oldCoordInNew (chainAlphaIdx i) = chainAlphaIdx i.succ := by
  have hi : i.val ≤ k := by omega
  apply Fin.ext
  simp [oldCoordInNew, chainAlphaIdx, hi]

/-- The old coordinate `βᵢ` sits at `βᵢ₊₁` of the longer chain. -/
theorem oldCoordInNew_beta {k : ℕ} (i : Fin (k + 1)) :
    oldCoordInNew (chainBetaIdx i) = chainBetaIdx i.succ := by
  have hi : ¬k + 1 + i.val ≤ k := by omega
  apply Fin.ext
  simp [oldCoordInNew, chainBetaIdx, hi]
  omega

/-- The old part of a decomposed configuration reads coordinate `j` as the longer
configuration reads `oldCoordInNew j`. -/
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

/-- A one-coordinate marginal at an old coordinate is unchanged by the extension. -/
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

/-- A two-coordinate marginal at old coordinates is unchanged by the extension. -/
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

end Kolmogorov
