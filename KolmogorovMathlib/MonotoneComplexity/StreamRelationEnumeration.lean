import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.MonotoneComplexity.REClosure
import Mathlib.Computability.Halting
import KolmogorovMathlib.Core.Basic

/-!
# A standard enumeration of the recursively enumerable relations on strings

`universalStreamRel i` is the relation decided by the `i`-th machine: `x` is related to `y` when
that machine halts on the pair. The bounded-step test `universalStreamStage` is computable in
all its arguments (`universalStreamStage_computable`, and its Boolean form
`universalStreamStagePred`), so the enumeration is recursively enumerable uniformly in the index
(`universalStreamRel_isRE_uniform`), and `universalStreamRel_complete` says every recursively
enumerable relation on pairs of strings occurs in it. This enumeration is the source of the
mixtures that produce maximal semimeasures and optimal decompressors.
-/

namespace Kolmogorov

/-- The `i`-th relation of the standard enumeration: `x` is related to `y` when the `i`-th partial
computable function halts on the code of the pair. -/
def universalStreamRel (i : ℕ) (x y : BitString) : Prop :=
  ∃ k, (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode i)
    (Encodable.encode (x, y))).isSome

/-- The bounded-step halting test of the `i`-th machine on a pair of strings is computable in the
index, the pair and the step bound. -/
lemma universalStreamStage_computable :
    Computable (fun p : ℕ × (BitString × BitString) × ℕ =>
      (Nat.Partrec.Code.evaln p.2.2 (Nat.Partrec.Code.ofNatCode p.1)
        (Encodable.encode p.2.1)).isSome) := by
  let f : (ℕ × Nat.Partrec.Code) × ℕ → Option ℕ :=
    fun p => Nat.Partrec.Code.evaln p.1.1 p.1.2 p.2
  have h_f : Computable f := Primrec.to_comp Nat.Partrec.Code.primrec_evaln
  let g1 : ℕ × (BitString × BitString) × ℕ → ℕ := fun p => p.2.2
  have h_g1 : Computable g1 := Computable.snd.comp Computable.snd
  let g2 : ℕ × (BitString × BitString) × ℕ → Nat.Partrec.Code :=
    fun p => Denumerable.ofNat Nat.Partrec.Code p.1
  have h_g2 : Computable g2 :=
    (Computable.ofNat Nat.Partrec.Code).comp Computable.fst
  let g3 : ℕ × (BitString × BitString) × ℕ → ℕ := fun p => Encodable.encode p.2.1
  have h_g3 : Computable g3 := Computable.encode.comp (Computable.fst.comp Computable.snd)
  let g : ℕ × (BitString × BitString) × ℕ → (ℕ × Nat.Partrec.Code) × ℕ :=
    fun p => ((g1 p, g2 p), g3 p)
  have h_g : Computable g :=
    Computable.pair (Computable.pair h_g1 h_g2) h_g3
  let fg := f ∘ g
  have h_fg : Computable fg := h_f.comp h_g
  let isSome_comp := Option.isSome ∘ fg
  have h_isSome : Computable isSome_comp :=
    (Primrec.to_comp Primrec.option_isSome).comp h_fg
  exact Computable.of_eq h_isSome (by
    intro p; dsimp [isSome_comp, fg, f, g, g1, g2, g3]
    rw [Nat.Partrec.Code.ofNatCode_eq])

/-- The `i`-th relation holds exactly when the `i`-th machine halts on the pair within some finite
number of steps. -/
lemma universalStreamRel_iff_exists_stage (i : ℕ) (x y : BitString) :
    universalStreamRel i x y ↔ ∃ k, (Nat.Partrec.Code.evaln k
      (Nat.Partrec.Code.ofNatCode i) (Encodable.encode (x, y))).isSome := Iff.rfl

/-- The always-true predicate is recursively enumerable. -/
lemma IsRE_true {α : Type*} [Primcodable α] : IsRE (fun _ : α => True) :=
  ⟨fun _ => Part.some (), (Computable.const ()).partrec, by simp⟩

/-- A decidable predicate given by a computable Boolean function is recursively enumerable. -/
lemma IsRE_of_computable {α : Type*} [Primcodable α] {p : α → Bool} (hp : Computable p) :
    IsRE (fun a => p a = true) := by
  have h := IsRE.and_computable IsRE_true hp
  have h_iff : ∀ a, (p a = true ∧ True) ↔ (p a = true) := by intro a; exact iff_of_eq (and_true _)
  exact @IsRE.of_iff _ _ (fun a => p a = true ∧ True) (fun a => p a = true) h h_iff

/-- The Boolean bounded-step halting test of the `i`-th machine on a pair of strings. -/
def universalStreamStagePred (p : (ℕ × (BitString × BitString)) × ℕ) : Bool :=
  (Nat.Partrec.Code.evaln p.2 (Nat.Partrec.Code.ofNatCode p.1.1) (Encodable.encode p.1.2)).isSome

/-- The Boolean bounded-step halting test is computable. -/
lemma universalStreamStage_pred_computable : Computable universalStreamStagePred := by
  let h : (ℕ × (BitString × BitString)) × ℕ → ℕ × (BitString × BitString) × ℕ :=
    fun p => (p.1.1, p.1.2, p.2)
  have h_h : Computable h :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
  have h_comp := universalStreamStage_computable.comp h_h
  exact Computable.of_eq h_comp (by intro p; rfl)

/-- The enumeration of relations is recursively enumerable uniformly in the index. -/
theorem universalStreamRel_isRE_uniform :
    IsRE (fun p : ℕ × (BitString × BitString) => universalStreamRel p.1 p.2.1 p.2.2) := by
  have h_isRE : IsRE (fun p : (ℕ × (BitString × BitString)) × ℕ =>
      universalStreamStagePred p = true) :=
    IsRE_of_computable universalStreamStage_pred_computable
  have h_exists := @IsRE.exists_encodable (ℕ × (BitString × BitString)) ℕ _ _
    (fun a b => universalStreamStagePred (a, b) = true) h_isRE
  have h_iff : ∀ p : ℕ × (BitString × BitString),
      (∃ b : ℕ, universalStreamStagePred (p, b) = true) ↔ universalStreamRel p.1 p.2.1 p.2.2 := by
    intro p
    dsimp [universalStreamStagePred, universalStreamRel]
    apply exists_congr
    intro k
    aesop
  exact @IsRE.of_iff _ _
    (fun p : ℕ × (BitString × BitString) => ∃ b : ℕ, universalStreamStagePred (p, b) = true)
    (fun p : ℕ × (BitString × BitString) => universalStreamRel p.1 p.2.1 p.2.2)
    h_exists h_iff

/-- Every recursively enumerable relation on pairs of strings occurs in the enumeration. -/
theorem universalStreamRel_complete {R : BitString → BitString → Prop}
    (hre : IsRE fun p : BitString × BitString => R p.1 p.2) :
    ∃ i, ∀ x y, universalStreamRel i x y ↔ R x y := by
  obtain ⟨f, hf_partrec, hf_dom⟩ := hre
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf_partrec
  let i := Encodable.encode c
  use i
  intro x y
  have heq : Nat.Partrec.Code.ofNatCode i = c := by
    change Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c
    rw [← Nat.Partrec.Code.ofNatCode_eq, Denumerable.ofNat_encode]
  rw [universalStreamRel_iff_exists_stage, heq]
  have hdom : (f (x, y)).Dom ↔ R x y := hf_dom (x, y)
  rw [← hdom]
  have heval : (c.eval (Encodable.encode (x, y))).Dom ↔ (f (x, y)).Dom := by aesop
  rw [← heval]
  simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Nat.Partrec.Code.evaln k c (Encodable.encode (x, y)) <;> aesop
  · rintro ⟨v, k, hk⟩
    exact ⟨k, by aesop⟩

end Kolmogorov
