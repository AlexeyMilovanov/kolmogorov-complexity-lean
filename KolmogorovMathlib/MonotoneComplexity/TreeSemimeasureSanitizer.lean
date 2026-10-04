import KolmogorovMathlib.MonotoneComplexity.SimpleTreeApproximation

/-!
# Forcing an arbitrary approximation to be a continuous tree semimeasure

An arbitrary computable stage approximation need not obey the semimeasure axioms; the sanitiser
freezes it as soon as it misbehaves. `rootBudgetOK` is the test that stage `s` still respects the
root budget and `freezeStage` the last stage up to `s` at which it has held without interruption
(`freezeStage_le`, `freezeStage_self_iff`), the sanitised approximation being the frozen one. The
outcome is an approximation that is coherent away from the root
(`simpleApprox_coherent_of_ne_nil`), non-decreasing in the stage (`treeSanitize_stage_mono`) and
computable whenever the input is (`computable_rootBudgetOK`, `computable_freezeStage`,
`computable_treeSanitize`) — the input the standard enumeration needs.
-/

namespace Kolmogorov

open scoped ENNReal

/-- Away from the root the simple approximation is supermultiplicative over the two children,
with no hypothesis on the raw approximation. -/
lemma simpleApprox_coherent_of_ne_nil (approx : ℕ → BitString → BitString → ℕ)
    (s : ℕ) (x : BitString) (hx : x ≠ []) :
    simpleApprox approx s (x ++ [false]) + simpleApprox approx s (x ++ [true])
      ≤ simpleApprox approx s x := by
  have hlenf : (x ++ [false]).length = x.length + 1 := by simp
  have hlent : (x ++ [true]).length = x.length + 1 := by simp
  have hnef : x ++ [false] ≠ [] := by simp
  have hnet : x ++ [true] ≠ [] := by simp
  by_cases hlen : s < x.length + 1
  · have hf : simpleApprox approx s (x ++ [false]) = 0 :=
      simpleApprox_vanishes_below_frontier approx s _ (by omega)
    have ht : simpleApprox approx s (x ++ [true]) = 0 :=
      simpleApprox_vanishes_below_frontier approx s _ (by omega)
    simp [hf, ht]
  · push Not at hlen
    have hcf : simpleApprox approx s (x ++ [false])
        = simpleApproxClosure approx s (s - (x.length + 1)) (x ++ [false]) := by
      rw [simpleApprox_eq_closure approx s _ hnef (by omega), hlenf]
    have hct : simpleApprox approx s (x ++ [true])
        = simpleApproxClosure approx s (s - (x.length + 1)) (x ++ [true]) := by
      rw [simpleApprox_eq_closure approx s _ hnet (by omega), hlent]
    rw [hcf, hct]
    rw [simpleApprox_eq_closure approx s x hx (by omega)]
    have hd : s - x.length = (s - (x.length + 1)) + 1 := by omega
    rw [hd]
    exact simpleApproxClosure_coherent approx s _ x

/-- The stage-`s` approximation respects the root budget. -/
@[reducible] def rootBudgetOK (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) : Prop :=
  simpleApprox approx s [false] + simpleApprox approx s [true] ≤ 2 ^ s

/-- The root budget holds at stage zero. -/
lemma rootBudgetOK_zero (approx : ℕ → BitString → BitString → ℕ) :
    rootBudgetOK approx 0 := by
  dsimp [rootBudgetOK]
  have h1 : simpleApprox approx 0 [false] = 0 :=
    simpleApprox_vanishes_below_frontier approx 0 [false] (by decide)
  have h2 : simpleApprox approx 0 [true] = 0 :=
    simpleApprox_vanishes_below_frontier approx 0 [true] (by decide)
  rw [h1, h2]
  simp

/-- The last stage up to `s` at which the root budget has held without interruption; the
sanitiser freezes there. -/
def freezeStage (approx : ℕ → BitString → BitString → ℕ) : ℕ → ℕ
  | 0       => 0
  | (s + 1) => if freezeStage approx s = s ∧ rootBudgetOK approx (s + 1) then s + 1
               else freezeStage approx s

/-- The freezing stage never exceeds the current stage. -/
lemma freezeStage_le (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    freezeStage approx s ≤ s := by
  induction s with
  | zero => simp [freezeStage]
  | succ s ih =>
    dsimp [freezeStage]
    split_ifs
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

/-- The sanitiser has not frozen by stage `s` exactly when the root budget held at every stage up
to `s`. -/
lemma freezeStage_self_iff (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    freezeStage approx s = s ↔ ∀ t ≤ s, rootBudgetOK approx t := by
  induction s with
  | zero =>
    simp only [freezeStage, nonpos_iff_eq_zero, forall_eq, rootBudgetOK_zero]
  | succ s ih =>
    dsimp [freezeStage]
    constructor
    · intro h
      split_ifs at h with hif
      · intro t ht
        rcases Nat.of_le_succ ht with ht_le | rfl
        · exact ih.mp hif.1 t ht_le
        · exact hif.2
      · have hle := freezeStage_le approx s
        omega
    · intro h
      have h1 : ∀ t ≤ s, rootBudgetOK approx t := fun t ht => h t (Nat.le_trans ht (Nat.le_succ s))
      have h2 : rootBudgetOK approx (s + 1) := h (s + 1) (Nat.le_refl _)
      have h3 : freezeStage approx s = s := ih.mpr h1
      rw [ite_eq_left ⟨h3, h2⟩]

/-- At each stage the sanitiser either advances or stays at its freezing stage. -/
lemma freezeStage_step_cases (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    freezeStage approx (s + 1) = s + 1 ∨ freezeStage approx (s + 1) = freezeStage approx s := by
  dsimp [freezeStage]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The root budget holds at the freezing stage. -/
lemma rootBudgetOK_freezeStage (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    rootBudgetOK approx (freezeStage approx s) := by
  induction s with
  | zero => exact rootBudgetOK_zero approx
  | succ s ih =>
    dsimp [freezeStage]
    split_ifs with h
    · exact h.2
    · exact ih

/-- The sanitised approximation: the simple approximation at the freezing stage, rescaled to the
current stage. -/
def treeSanitize (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) : ℕ :=
  2 ^ (s - freezeStage approx s) * simpleApprox approx (freezeStage approx s) x

/-- The sanitised approximation carries the full stage mass at the root. -/
theorem treeSanitize_root (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    treeSanitize approx s [] = 2 ^ s := by
  dsimp [treeSanitize]
  rw [simpleApprox_root]
  rw [← pow_add]
  congr 1
  exact Nat.sub_add_cancel (freezeStage_le approx s)

/-- The sanitised approximation is supermultiplicative over the two children. -/
theorem treeSanitize_coherent (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (x : BitString) :
    treeSanitize approx s (x ++ [false]) + treeSanitize approx s (x ++ [true])
      ≤ treeSanitize approx s x := by
  dsimp [treeSanitize]
  rw [← mul_add]
  apply Nat.mul_le_mul_left
  by_cases hx : x = []
  · subst hx
    exact rootBudgetOK_freezeStage approx s
  · exact simpleApprox_coherent_of_ne_nil approx _ _ hx

/-- The dyadic values of the sanitised approximation are non-decreasing in the stage. -/
theorem treeSanitize_stage_mono (approx : ℕ → BitString → BitString → ℕ)
    (H_mono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1)) (s x) :
    dyadicValue (treeSanitize approx s x) s
      ≤ dyadicValue (treeSanitize approx (s + 1) x) (s + 1) := by
  dsimp [treeSanitize]
  have h1 : s = freezeStage approx s + (s - freezeStage approx s) :=
    (Nat.add_sub_cancel' (freezeStage_le approx s)).symm
  have h2 : s + 1 = freezeStage approx (s + 1) + (s + 1 - freezeStage approx (s + 1)) :=
    (Nat.add_sub_cancel' (freezeStage_le approx (s + 1))).symm
  have step1 :
      dyadicValue
          (2 ^ (s - freezeStage approx s) * simpleApprox approx (freezeStage approx s) x) s
        = dyadicValue (simpleApprox approx (freezeStage approx s) x) (freezeStage approx s) := by
    conv => lhs; arg 2; rw [h1]
    exact dyadicValue_two_pow_mul_add _ _ (s - freezeStage approx s)
  have step2 :
      dyadicValue
          (2 ^ (s + 1 - freezeStage approx (s + 1))
            * simpleApprox approx (freezeStage approx (s + 1)) x) (s + 1)
        = dyadicValue (simpleApprox approx (freezeStage approx (s + 1)) x)
            (freezeStage approx (s + 1)) := by
    conv => lhs; arg 2; rw [h2]
    exact dyadicValue_two_pow_mul_add _ _ (s + 1 - freezeStage approx (s + 1))
  rw [step1, step2]
  rcases freezeStage_step_cases approx s with h_succ | h_eq
  · have h_s : freezeStage approx s = s := by
      have hdef : freezeStage approx (s + 1)
          = if freezeStage approx s = s ∧ rootBudgetOK approx (s + 1) then s + 1
            else freezeStage approx s := rfl
      rw [hdef] at h_succ
      split_ifs at h_succ with hcond
      · exact hcond.1
      · have hle := freezeStage_le approx s
        omega
    rw [h_succ, h_s]
    exact simpleApprox_stage_mono approx H_mono s x
  · rw [h_eq]

/-- The root budget test of a computable approximation is computable. -/
lemma computable_rootBudgetOK (approx : ℕ → BitString → BitString → ℕ)
    (h_comp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun s => Decidable.decide (rootBudgetOK approx s)) := by
  have hF : Computable (fun (s : ℕ) => ([false] : BitString)) := Computable.const [false]
  have hT : Computable (fun (s : ℕ) => ([true] : BitString)) := Computable.const [true]
  have hs : Computable (fun (s : ℕ) => s) := Computable.id
  have hpF : Computable (fun s : ℕ => (s, [false])) := hs.pair hF
  have hpT : Computable (fun s : ℕ => (s, [true])) := hs.pair hT
  have h1 : Computable (fun (s : ℕ) => simpleApprox approx s [false]) :=
    (computable_simpleApprox approx h_comp).comp hpF
  have h2 : Computable (fun (s : ℕ) => simpleApprox approx s [true]) :=
    (computable_simpleApprox approx h_comp).comp hpT
  have hadd : Computable (fun s => simpleApprox approx s [false] + simpleApprox approx s [true]) :=
    Primrec.nat_add.to_comp.comp h1 h2
  have hpow : Computable (fun (s : ℕ) => 2 ^ s) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp (Computable.const 2) hs
  have hle : Computable (fun s =>
      Decidable.decide (simpleApprox approx s [false] + simpleApprox approx s [true] ≤ 2 ^ s)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hadd hpow
  exact hle

/-- The freezing stage of a computable approximation is computable. -/
lemma computable_freezeStage (approx : ℕ → BitString → BitString → ℕ)
    (h : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun s => freezeStage approx s) := by
  have h_dec : Computable (fun s => Decidable.decide (rootBudgetOK approx s)) :=
    computable_rootBudgetOK approx h
  have h_n : Computable (fun (p : ℕ × (ℕ × ℕ)) => p.2.1) := Computable.fst.comp Computable.snd
  have h_IH : Computable (fun (p : ℕ × (ℕ × ℕ)) => p.2.2) := Computable.snd.comp Computable.snd
  have h_np1 : Computable (fun (p : ℕ × (ℕ × ℕ)) => p.2.1 + 1) := Primrec.succ.to_comp.comp h_n
  have h_eq : Computable (fun (p : ℕ × (ℕ × ℕ)) => Decidable.decide (p.2.2 = p.2.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp h_IH h_n
  have h_ok : Computable (fun (p : ℕ × (ℕ × ℕ)) =>
      Decidable.decide (rootBudgetOK approx (p.2.1 + 1))) :=
    h_dec.comp h_np1
  have h_and : Computable (fun (p : ℕ × (ℕ × ℕ)) =>
      Decidable.decide (p.2.2 = p.2.1 ∧ rootBudgetOK approx (p.2.1 + 1))) := by
    have H := Computable.cond h_eq h_ok (Computable.const false)
    exact H.of_eq (fun p => by
      rcases p with ⟨a, n, IH⟩
      dsimp
      cases h1 : decide (IH = n) <;> cases h2 : decide (rootBudgetOK approx (n + 1))
      <;> simp_all)
  have h_step : Computable₂ (fun (a : ℕ) (p2 : ℕ × ℕ) =>
      if p2.2 = p2.1 ∧ rootBudgetOK approx (p2.1 + 1) then p2.1 + 1 else p2.2) := by
    have H : Computable (fun (p : ℕ × (ℕ × ℕ)) =>
        cond (Decidable.decide (p.2.2 = p.2.1 ∧ rootBudgetOK approx (p.2.1 + 1)))
          (p.2.1 + 1) p.2.2) :=
      Computable.cond h_and h_np1 h_IH
    exact H.of_eq (fun p => by
      rcases p with ⟨a, n, IH⟩
      dsimp
      split_ifs with h_if
      · simp [h_if]
      · simp [h_if])
  have h_rec := Computable.nat_rec (f := @id ℕ) (g := fun _ => 0)
    (h := fun _ (n, IH) => if IH = n ∧ rootBudgetOK approx (n + 1) then n + 1 else IH)
    Computable.id (Computable.const 0) h_step
  have h_eq2 : ∀ s, Nat.rec 0
      (fun n IH => if IH = n ∧ rootBudgetOK approx (n + 1) then n + 1 else IH) s
      = freezeStage approx s := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
      dsimp [freezeStage, Nat.rec]
      rw [ih]
  exact h_rec.of_eq (fun n => by dsimp; exact h_eq2 n)

/-- The sanitised approximation of a computable approximation is computable. -/
theorem computable_treeSanitize (approx : ℕ → BitString → BitString → ℕ)
    (h : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString => treeSanitize approx p.1 p.2) := by
  have hF : Computable (fun s => freezeStage approx s) := computable_freezeStage approx h
  have hs : Computable (fun p : ℕ × BitString => p.1) := Computable.fst
  have hx : Computable (fun p : ℕ × BitString => p.2) := Computable.snd
  have hFs : Computable (fun p : ℕ × BitString => freezeStage approx p.1) := hF.comp hs
  have hsub : Computable (fun p : ℕ × BitString => p.1 - freezeStage approx p.1) :=
    Primrec.nat_sub.to_comp.comp hs hFs
  have hpow : Computable (fun p : ℕ × BitString => 2 ^ (p.1 - freezeStage approx p.1)) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp (Computable.const 2) hsub
  have hp : Computable (fun p : ℕ × BitString => (freezeStage approx p.1, p.2)) := hFs.pair hx
  have happrox : Computable (fun p : ℕ × BitString =>
      simpleApprox approx (freezeStage approx p.1) p.2) :=
    (computable_simpleApprox approx h).comp hp
  have hmul : Computable (fun p : ℕ × BitString =>
      2 ^ (p.1 - freezeStage approx p.1)
        * simpleApprox approx (freezeStage approx p.1) p.2) :=
    Primrec.nat_mul.to_comp.comp hpow happrox
  exact hmul

end Kolmogorov
