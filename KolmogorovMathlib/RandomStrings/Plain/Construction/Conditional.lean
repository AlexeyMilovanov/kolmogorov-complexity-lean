/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Plain.Basic

/-!
# The conditional machine with an arbitrary directive branch

The padding simulation is independent of computability of the directive branch.
The plain literal overhead is explicit data in addition to the frozen `Base`.
At padding zero the simulation branch takes precedence; all construction contracts
use positive padding, where the two branches are disjoint.
-/

namespace Kolmogorov.Milovanov

/-- A fixed plain literal overhead, chosen before any padding or directive function.
Blueprint node `constr:optimal`. This supplements, without modifying, `Base`. -/
structure PlainLiteral (B : Base) where
  /-- The additive overhead for literal descriptions on the fixed plain machine. -/
  cV : ℕ
  /-- The uniform literal bound at empty condition. -/
  bound : ∀ x : BitString, plainK B.V x ≤ (x.length + cV : ℕ)

/-- The repository's optimality theorem supplies the extra literal data.
Blueprint node `constr:optimal`. No machine or overhead is chosen globally. -/
theorem nonempty_plainLiteral (B : Base) : Nonempty (PlainLiteral B) := by
  obtain ⟨c, hc⟩ := plainK_le_length B.V B.optimalV
  exact ⟨⟨c, fun x => by simpa only [programLength, Nat.cast_add] using hc x⟩⟩

/-- The literal overhead of the constructed machine, with all padding charged explicitly.
Blueprint node `constr:optimal`. -/
def constructedLiteralConstant {B : Base} (literal : PlainLiteral B) (d : ℕ) : ℕ :=
  d + literal.cV

/-- Zero-prefixed programs simulate `V`; one-prefixed programs call the arbitrary `G`.
Blueprint node `constr:conditional`. The directive branch ignores the condition.
For `d = 0` the first branch is used on every input. -/
def constructed_conditional_machine (B : Base) (d : ℕ) (G : BitString →. BitString) :
    Map := fun input =>
  if input.1.take d = List.replicate d false then
    B.V (input.1.drop d, input.2)
  else
    match input.1 with
    | true :: p => G p
    | _ => Part.none

/-- The simulation branch has exactly the original conditional behavior.
Blueprint node `constr:conditional`. -/
theorem constructed_machine_simulation (B : Base) (d : ℕ) (G : BitString →. BitString)
    (p y : BitString) :
    constructed_conditional_machine B d G (List.replicate d false ++ p, y) =
      B.V (p, y) := by
  simp [constructed_conditional_machine]

/-- Positive padding makes the directive branch disjoint from the simulation branch.
Blueprint node `constr:conditional`. -/
theorem constructed_machine_directive (B : Base) (d : ℕ) (hd : 1 ≤ d)
    (G : BitString →. BitString) (p y : BitString) :
    constructed_conditional_machine B d G (true :: p, y) = G p := by
  cases d with
  | zero => omega
  | succ d => simp [constructed_conditional_machine, List.replicate_succ]

/-- Every conditional description on `V` transfers with exactly `d` extra bits.
Blueprint node `constr:optimal`. There is no computability premise on `G`. -/
theorem constructed_machine_condK_le (B : Base) (d : ℕ) (_hd : 1 ≤ d)
    (G : BitString →. BitString) (x y : BitString) :
    condK (constructed_conditional_machine B d G) x y ≤ condK B.V x y + d := by
  by_cases htop : condK B.V x y = ⊤
  · simp [htop]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨p, hp, hx⟩ := (condK_le_iff B.V x y k).mp hk.ge
  rw [← hk, ← Nat.cast_add]
  apply (condK_le_iff _ x y (k + d)).mpr
  refine ⟨List.replicate d false ++ p, ?_, ?_⟩
  · simp only [programLength, List.length_append, List.length_replicate] at *
    omega
  · simpa only [produces, constructed_machine_simulation] using hx

/-- A partial computable directive branch gives an actual conditional decompressor.
Blueprint node `constr:optimal`. `Partrec` is exactly `isDecompressor`'s notion. -/
theorem constructed_machine_partrec (B : Base) (d : ℕ) (G : BitString →. BitString)
    (hG : Partrec G) : Partrec (constructed_conditional_machine B d G) := by
  have : Partrec fun (input : BitString × BitString) =>
      bif decide (input.1.take d = List.replicate d false) then
        (fun (x : BitString × BitString) => B.V (x.1.drop d, x.2)) input
      else
        (fun (x : BitString × BitString) =>
          match x.1 with | true :: p => G p | _ => Part.none) input := by
    apply Partrec.cond
    · have Hc : Computable fun (input : BitString × BitString) =>
          decide (input.1.take d = List.replicate d false) := by
        apply Primrec.to_comp
        apply PrimrecPred.decide (PrimrecRel.comp Primrec.eq
          (Primrec.list_take.comp (Primrec.const d) Primrec.fst)
          (Primrec.const (List.replicate d false)))
      exact Hc
    · have h1 : Computable fun (input : BitString × BitString) => (input.1.drop d, input.2) := by
        apply Primrec.to_comp
        apply Primrec.pair (Primrec.list_drop.comp (Primrec.const d) Primrec.fst) Primrec.snd
      exact Partrec.comp B.optimalV.1 h1
    · have h_match : Partrec fun (input : BitString × BitString) =>
          match input.1 with | true :: p => G p | _ => Part.none := by
        have : Partrec fun (input : BitString × BitString) =>
            bif decide (input.1.head? = some true) then
              (fun (x : BitString × BitString) => G x.1.tail) input
            else
              Part.none := by
          apply Partrec.cond
          · have Hc : Computable fun (input : BitString × BitString) =>
                decide (input.1.head? = some true) := by
              apply Primrec.to_comp
              apply PrimrecPred.decide (PrimrecRel.comp Primrec.eq
                (Primrec.list_head?.comp Primrec.fst) (Primrec.const (some true)))
            exact Hc
          · have h1 : Computable fun (input : BitString × BitString) => input.1.tail := by
              apply Primrec.to_comp
              apply Primrec.list_tail.comp Primrec.fst
            exact Partrec.comp hG h1
          · exact Partrec.none
        refine Partrec.of_eq this ?_
        intro a
        by_cases h : a.1.head? = some true
        · simp only [h, cond_eq_ite, decide_eq_true_eq, ite_true]
          cases a_1 : a.1 with
          | nil =>
            exfalso
            rw [a_1, List.head?_nil] at h
            contradiction
          | cons hd tl =>
            have h_hd : hd = true := by
              rw [a_1, List.head?_cons] at h
              exact Option.some.inj h
            subst h_hd
            rfl
        · simp only [h, cond_eq_ite, decide_eq_true_eq, ite_false]
          cases a_1 : a.1 with
          | nil => rfl
          | cons hd tl =>
            cases hd
            · rfl
            · exfalso
              rw [a_1, List.head?_cons] at h
              contradiction
      exact h_match
  unfold constructed_conditional_machine
  refine (Partrec.of_eq this ?_)
  intro a
  by_cases h : a.1.take d = List.replicate d false
  · simp only [h, cond_eq_ite, decide_eq_true_eq, ite_true]
  · simp only [h, cond_eq_ite, decide_eq_true_eq, ite_false]



/-- Conditional optimality of the padded simulation with a partial computable branch.
Blueprint node `constr:optimal`. Effectivity of the eventual directive function is a later node. -/
theorem constructed_machine_optimal_conditional (B : Base) (d : ℕ) (hd : 1 ≤ d)
    (G : BitString →. BitString) (hG : Partrec G) :
    isOptimalConditional (constructed_conditional_machine B d G) := by
  refine ⟨constructed_machine_partrec B d G hG, ?_⟩
  intro D hD
  obtain ⟨c, hc⟩ := B.optimalV.2 D hD
  refine ⟨c + d, fun x y => ?_⟩
  calc
    condK (constructed_conditional_machine B d G) x y ≤ condK B.V x y + d :=
      constructed_machine_condK_le B d hd G x y
    _ ≤ (condK D x y + c) + d := add_le_add (hc x y) le_rfl
    _ = condK D x y + (c + d : ℕ) := by simp [add_assoc]

/-- Normalization may use the literal bound before directive computability is known.
Blueprint node `constr:optimal`. The same `cV` works for every padding and every branch. -/
theorem constructed_machine_literal_bound (B : Base) (literal : PlainLiteral B)
    (d : ℕ) (hd : 1 ≤ d) (G : BitString →. BitString) (x : BitString) :
    plainK (constructed_conditional_machine B d G) x ≤
      (x.length + constructedLiteralConstant literal d : ℕ) := by
  calc
    plainK (constructed_conditional_machine B d G) x ≤ plainK B.V x + d :=
      constructed_machine_condK_le B d hd G x []
    _ ≤ (x.length + literal.cV : ℕ) + (d : ENat) := add_le_add (literal.bound x) le_rfl
    _ = (x.length + constructedLiteralConstant literal d : ℕ) := by
      simp [constructedLiteralConstant, Nat.cast_add, add_comm, add_assoc]

end Kolmogorov.Milovanov
