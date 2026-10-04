import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Foundation.RSeparability
import KolmogorovMathlib.Foundation.FixedPointFree.HighComplexityTask

/-!
# Arslanov completeness criterion

Computable monotone approximations of enumerable sets, Kleene's recursion theorem with a
parameter, and the oracle-computability plumbing behind Arslanov's completeness criterion.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-! ### A computable monotone approximation of an enumerable set -/

/-! ### Kleene's recursion theorem with a parameter -/

/-! ### Oracle-computability plumbing -/

/-! ### The oracle prefix function is oracle-computable -/

/-! ### The objects of Arslanov's construction -/

/-! ### Arslanov's completeness criterion -/

private lemma exists_bound_forall_le {P : ℕ → ℕ → Prop}
    (hmono : ∀ j u u', u ≤ u' → P j u → P j u') :
    ∀ (k : ℕ), (∀ j ≤ k, ∃ u, P j u) → ∃ u, ∀ j ≤ k, P j u := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨u, hu⟩ := h 0 le_rfl
      exact ⟨u, fun j hj => by rw [Nat.le_zero.mp hj]; exact hu⟩
  | succ m ih =>
      intro h
      obtain ⟨u₁, hu₁⟩ := ih (fun j hj => h j (hj.trans (Nat.le_succ m)))
      obtain ⟨u₂, hu₂⟩ := h (m + 1) le_rfl
      refine ⟨max u₁ u₂, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (m + 1) with h' | h'
      · exact hmono j u₁ _ (le_max_left _ _) (hu₁ j (Nat.lt_succ_iff.mp h'))
      · have : j = m + 1 := le_antisymm hj h'
        subst this; exact hmono _ u₂ _ (le_max_right _ _) hu₂

/-- `Partrec` helper for the pair case of `exists_string_operator`. -/
private lemma exists_string_operator_partrec_pair {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hp₁ : Partrec Φ₁) (hp₂ : Partrec Φ₂) :
    Partrec (fun p : List ℕ × ℕ =>
      Φ₁ p >>= fun a => Φ₂ p >>= fun b => Part.some (Nat.pair a b)) := by
  have hg : Partrec fun q : (List ℕ × ℕ) × ℕ =>
        Φ₂ q.1 >>= fun b => Part.some (Nat.pair q.2 b) :=
      (hp₂.comp Computable.fst).bind (Computable₂.partrec₂
        (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  exact hp₁.bind hg.to₂

/-- Monotonicity helper for `exists_string_operator` in the `prec` case. -/
private lemma exists_string_operator_prec_mono {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (hm₂ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₂ (w, n) → v ∈ Φ₂ (w', n))
    (w w' : List ℕ) (hw : w <+: w') (a k v : ℕ)
    (hv : v ∈ (k.rec (Φ₁ (w, a))
      (fun y IH => IH.bind fun i => Φ₂ (w, Nat.pair a (Nat.pair y i))) : Part ℕ)) :
    v ∈ (k.rec (Φ₁ (w', a))
      (fun y IH => IH.bind fun i => Φ₂ (w', Nat.pair a (Nat.pair y i))) : Part ℕ) := by
  revert a v hv
  induction k with
  | zero => intro a v hv; exact hm₁ _ _ hw _ _ hv
  | succ m ih =>
      intro a v hv
      simp only [Part.mem_bind_iff] at hv ⊢
      obtain ⟨i, hi, hv⟩ := hv
      exact ⟨i, ih a i hi, hm₂ _ _ hw _ _ hv⟩

/-- `Partrec` helper for the primitive recursion case of `exists_string_operator`. -/
private lemma exists_string_operator_partrec_prec {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hp₁ : Partrec Φ₁) (hp₂ : Partrec Φ₂) :
    Partrec (fun p : List ℕ × ℕ =>
      (Nat.unpair p.2).2.rec (Φ₁ (p.1, (Nat.unpair p.2).1))
        (fun y IH => IH.bind fun i => Φ₂ (p.1, Nat.pair (Nat.unpair p.2).1 (Nat.pair y i)))) :=
  Partrec.nat_rec (f := fun p : List ℕ × ℕ => (Nat.unpair p.2).2)
    (g := fun p : List ℕ × ℕ => Φ₁ (p.1, (Nat.unpair p.2).1))
    (h := fun (p : List ℕ × ℕ) (q : ℕ × ℕ) =>
      Φ₂ (p.1, Nat.pair (Nat.unpair p.2).1 (Nat.pair q.1 q.2)))
    ((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    (hp₁.comp (Computable.fst.pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)))
    ((hp₂.comp ((Computable.fst.comp Computable.fst).pair
      (Primrec₂.natPair.to_comp.comp
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.comp Computable.fst)
        (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.snd))))).to₂)

/-- Prefix specification helper for the primitive recursion case of `exists_string_operator`.

The hypotheses `hm₁`, `hm₂`, `hc₁`, `hc₂` are the interface of two arbitrary oracle
operators `Φ₁`, `Φ₂`: each is monotone in its oracle prefix, and each computes the
corresponding partial function `f₁`, `f₂` from some finite prefix of `α₀`. -/
private lemma exists_string_operator_prec_correct {α₀ : ℕ → ℕ} {f₁ f₂ : ℕ →. ℕ}
    {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (hm₂ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₂ (w, n) → v ∈ Φ₂ (w', n))
    (hc₁ : ∀ n v, v ∈ f₁ n → ∃ u, v ∈ Φ₁ (oraclePrefix α₀ u, n))
    (hc₂ : ∀ n v, v ∈ f₂ n → ∃ u, v ∈ Φ₂ (oraclePrefix α₀ u, n))
    (a k v : ℕ)
    (hv : v ∈ (Nat.rec (f₁ a)
      (fun y IH => IH.bind fun i => f₂ (Nat.pair a (Nat.pair y i))) k : Part ℕ)) :
    ∃ u, v ∈ (k.rec (Φ₁ (oraclePrefix α₀ u, a))
      (fun y IH => IH.bind fun i =>
        Φ₂ (oraclePrefix α₀ u, Nat.pair a (Nat.pair y i))) : Part ℕ) := by
  revert a v hv
  induction k with
  | zero => intro a v hv; exact hc₁ _ v hv
  | succ m ih =>
      intro a v hv
      simp only [Part.mem_bind_iff] at hv
      obtain ⟨i, hi, hv⟩ := hv
      obtain ⟨u₁, hu₁⟩ := ih a i hi
      obtain ⟨u₂, hu₂⟩ := hc₂ _ v hv
      refine ⟨max u₁ u₂, ?_⟩
      simp only [Part.mem_bind_iff]
      exact ⟨i, exists_string_operator_prec_mono hm₁ hm₂ _ _
          (oraclePrefix_prefix (le_max_left _ _)) _ _ _ hu₁,
        hm₂ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu₂⟩

/-- `Partrec` helper for the unbounded search case of `exists_string_operator`. -/
private lemma exists_string_operator_partrec_rfind {Φ₁ : List ℕ × ℕ →. ℕ} (hp₁ : Partrec Φ₁) :
    Partrec (fun p : List ℕ × ℕ => Nat.rfind fun k =>
      (fun m => decide (m = 0)) <$> Φ₁ (p.1, Nat.pair p.2 k)) := by
  refine Partrec.rfind ?_
  have h1 : Partrec fun q : (List ℕ × ℕ) × ℕ => Φ₁ (q.1.1, Nat.pair q.1.2 q.2) :=
    hp₁.comp ((Computable.fst.comp Computable.fst).pair
      (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  have hdec : Computable₂ (fun (_ : (List ℕ × ℕ) × ℕ) (m : ℕ) => decide (m = 0)) := by
    have h0 : PrimrecPred fun q : ((List ℕ × ℕ) × ℕ) × ℕ => q.2 = 0 :=
      PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)
    obtain ⟨_, h1⟩ := h0
    exact (h1.of_eq (fun q => by congr 1)).to_comp
  exact ((h1.map hdec).of_eq (fun q => rfl)).to₂

/-- Correctness helper for the unbounded search case of `exists_string_operator`. -/
private lemma exists_string_operator_rfind_correct {α₀ : ℕ → ℕ} {f₁ : ℕ →. ℕ}
    {Φ₁ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (hc₁ : ∀ n v, v ∈ f₁ n → ∃ u, v ∈ Φ₁ (oraclePrefix α₀ u, n))
    (n v : ℕ)
    (hv : v ∈ Nat.rfind fun k => (fun m => decide (m = 0)) <$> f₁ (Nat.pair n k)) :
    ∃ u, v ∈ Nat.rfind fun k =>
      (fun m => decide (m = 0)) <$> Φ₁ (oraclePrefix α₀ u, Nat.pair n k) := by
  replace hv := Nat.mem_rfind.mp hv
  obtain ⟨hT, hF⟩ := hv
  have key : ∀ j, ∃ u, ∀ b : Bool,
      b ∈ ((fun m => decide (m = 0)) <$> f₁ (Nat.pair n j)) →
      b ∈ ((fun m => decide (m = 0)) <$> Φ₁ (oraclePrefix α₀ u, Nat.pair n j)) := by
    intro j
    by_cases hd : (f₁ (Nat.pair n j)).Dom
    · obtain ⟨u, hu⟩ := hc₁ (Nat.pair n j) ((f₁ (Nat.pair n j)).get hd) (Part.get_mem hd)
      refine ⟨u, fun b hb => ?_⟩
      simp only [Part.map_eq_map, Part.mem_map_iff] at hb ⊢
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, (Part.mem_unique (Part.get_mem hd) ha) ▸ hu, rfl⟩
    · refine ⟨0, fun b hb => ?_⟩
      simp only [Part.map_eq_map, Part.mem_map_iff] at hb
      obtain ⟨a, ha, -⟩ := hb
      exact absurd (Part.dom_iff_mem.2 ⟨a, ha⟩) hd
  obtain ⟨u, hu⟩ := exists_bound_forall_le
    (P := fun j u => ∀ b : Bool, b ∈ ((fun m => decide (m = 0)) <$> f₁ (Nat.pair n j)) →
      b ∈ ((fun m => decide (m = 0)) <$> Φ₁ (oraclePrefix α₀ u, Nat.pair n j)))
    (fun j u u' huu' hP b hb => by
      simp only [Part.map_eq_map, Part.mem_map_iff] at hP ⊢
      obtain ⟨a, ha, hab⟩ := hP b (by simpa [Part.map_eq_map, Part.mem_map_iff] using hb)
      exact ⟨a, hm₁ _ _ (oraclePrefix_prefix huu') _ _ ha, hab⟩)
    v (fun j _ => key j)
  refine ⟨u, Nat.mem_rfind.2 ⟨hu v le_rfl _ hT, ?_⟩⟩
  intro j hj
  exact hu j (le_of_lt hj) _ (hF hj)

/-- **Use principle.**  A function recursive in a total oracle `α₀` is computed by a
partial computable *operator* taking a finite oracle string as an extra argument;
the operator is monotone under extension of the oracle string, and on prefixes of
`α₀` it reproduces every value of `f`. -/
theorem exists_string_operator {α₀ : ℕ → ℕ} {f : ℕ →. ℕ}
    (hf : RecursiveIn {totalOracle α₀} f) :
    ∃ Φ : List ℕ × ℕ →. ℕ, Partrec Φ ∧
      (∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ (w, n) → v ∈ Φ (w', n)) ∧
      (∀ n v, v ∈ f n → ∃ u, v ∈ Φ (oraclePrefix α₀ u, n)) := by
  replace hf := RecursiveIn.iff_nat.mp hf
  induction hf with
  | zero =>
      refine ⟨fun _ => Part.some 0, (Computable.const 0).partrec, fun w w' _ n v hv => hv, ?_⟩
      exact fun n v hv => ⟨0, hv⟩
  | succ =>
      refine ⟨fun p => Part.some (p.2 + 1),
        (Computable.succ.comp Computable.snd).partrec, fun w w' _ n v hv => hv, ?_⟩
      exact fun n v hv => ⟨0, hv⟩
  | left =>
      refine ⟨fun p => Part.some (Nat.unpair p.2).1,
        ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd).partrec,
        fun w w' _ n v hv => hv, ?_⟩
      exact fun n v hv => ⟨0, hv⟩
  | right =>
      refine ⟨fun p => Part.some (Nat.unpair p.2).2,
        ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd).partrec,
        fun w w' _ n v hv => hv, ?_⟩
      exact fun n v hv => ⟨0, hv⟩
  | oracle g hg =>
      rw [Set.mem_singleton_iff] at hg
      subst hg
      refine ⟨fun p => (p.1[p.2]? : Part ℕ),
        Computable.ofOption (Computable.list_getElem?.comp Computable.fst Computable.snd), ?_, ?_⟩
      · intro w w' hw n v hv
        simp only [Part.mem_ofOption] at hv ⊢
        obtain ⟨t, rfl⟩ := hw
        have hn : n < w.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hv
          simp at hv
        rw [List.getElem?_append_left hn]
        exact hv
      · intro n v hv
        refine ⟨n + 1, ?_⟩
        simp only [Part.mem_ofOption]
        have hv' : v = α₀ n := by simpa [totalOracle] using hv
        subst hv'
        simp [oraclePrefix]
  | @pair f₁ f₂ hf hh ih1 ih2 =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih1
      obtain ⟨Φ₂, hp₂, hm₂, hc₂⟩ := ih2
      refine ⟨fun p => Φ₁ p >>= fun a => Φ₂ p >>= fun b => Part.some (Nat.pair a b),
        exists_string_operator_partrec_pair hp₁ hp₂, ?_, ?_⟩
      · intro w w' hw n v hv
        simp only [Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff] at hv ⊢
        obtain ⟨a, ha, b, hb, rfl⟩ := hv
        exact ⟨a, hm₁ _ _ hw _ _ ha, b, hm₂ _ _ hw _ _ hb, rfl⟩
      · intro n v hv
        simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff] at hv
        obtain ⟨g, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := hv
        obtain ⟨u₁, hu₁⟩ := hc₁ n a ha
        obtain ⟨u₂, hu₂⟩ := hc₂ n b hb
        refine ⟨max u₁ u₂, ?_⟩
        simp only [Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff]
        exact ⟨a, hm₁ _ _ (oraclePrefix_prefix (le_max_left _ _)) _ _ hu₁,
          b, hm₂ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu₂, rfl⟩
  | @comp f₁ f₂ hf hh ih1 ih2 =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih1
      obtain ⟨Φ₂, hp₂, hm₂, hc₂⟩ := ih2
      refine ⟨fun p => Φ₂ p >>= fun m => Φ₁ (p.1, m), ?_, ?_, ?_⟩
      · exact hp₂.bind ((hp₁.comp ((Computable.fst.comp Computable.fst).pair
          Computable.snd)).to₂)
      · intro w w' hw n v hv
        simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hv ⊢
        obtain ⟨m, hm, hv⟩ := hv
        exact ⟨m, hm₂ _ _ hw _ _ hm, hm₁ _ _ hw _ _ hv⟩
      · intro n v hv
        obtain ⟨m, hm, hv⟩ := Part.mem_bind_iff.mp hv
        obtain ⟨u₁, hu₁⟩ := hc₂ n m hm
        obtain ⟨u₂, hu₂⟩ := hc₁ m v hv
        refine ⟨max u₁ u₂, Part.mem_bind_iff.mpr ⟨m, ?_, ?_⟩⟩
        · exact hm₂ _ _ (oraclePrefix_prefix (le_max_left _ _)) _ _ hu₁
        · exact hm₁ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu₂
  | @prec f₁ f₂ hf hh ih1 ih2 =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih1
      obtain ⟨Φ₂, hp₂, hm₂, hc₂⟩ := ih2
      set R : List ℕ → ℕ → ℕ → Part ℕ := fun w a k =>
        k.rec (Φ₁ (w, a)) (fun y IH => IH.bind fun i => Φ₂ (w, Nat.pair a (Nat.pair y i)))
      refine ⟨fun p => R p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2,
        exists_string_operator_partrec_prec hp₁ hp₂, ?_, ?_⟩
      · intro w w' hw n v hv
        exact exists_string_operator_prec_mono hm₁ hm₂ w w' hw _ _ v hv
      · intro n v hv
        exact exists_string_operator_prec_correct hm₁ hm₂ hc₁ hc₂ _ _ v hv
  | @rfind f₁ hf ih =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih
      refine ⟨fun p => Nat.rfind fun k =>
          (fun m => decide (m = 0)) <$> Φ₁ (p.1, Nat.pair p.2 k),
        exists_string_operator_partrec_rfind hp₁, ?_, ?_⟩
      · intro w w' hw n v hv
        replace hv := Nat.mem_rfind.mp hv
        refine Nat.mem_rfind.mpr ?_
        obtain ⟨h1, h2⟩ := hv
        constructor
        · simp only [Part.map_eq_map, Part.mem_map_iff] at h1 ⊢
          obtain ⟨a, ha, hb⟩ := h1
          exact ⟨a, hm₁ _ _ hw _ _ ha, hb⟩
        · intro j hj
          have := h2 hj
          simp only [Part.map_eq_map, Part.mem_map_iff] at this ⊢
          obtain ⟨a, ha, hb⟩ := this
          exact ⟨a, hm₁ _ _ hw _ _ ha, hb⟩
      · intro n v hv
        exact exists_string_operator_rfind_correct hm₁ hc₁ n v hv


private lemma exists_re_approx {A : Set ℕ} (hA : IsEnumerableSet A) :
    ∃ mem : ℕ → ℕ → Bool, Primrec₂ mem ∧
      (∀ s s' n, s ≤ s' → mem s n = true → mem s' n = true) ∧
      (∀ n, n ∈ A ↔ ∃ s, mem s n = true) := by
  obtain ⟨f, hf, hfA⟩ := hA
  have hg : Nat.Partrec (fun n => (f n).map (fun _ => 0)) := by
    have h1 : Partrec (fun n : ℕ => (f n).map (fun _ => (0 : ℕ))) :=
      hf.map (Computable.const (0 : ℕ)).to₂
    exact Partrec.nat_iff.mp h1
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  refine ⟨fun s n => (Code.evaln s c n).isSome, ?_, ?_, ?_⟩
  · have h1 : Primrec fun p : ℕ × ℕ => Code.evaln p.1 c p.2 :=
      Code.primrec_evaln.comp ((Primrec.fst.pair (Primrec.const c)).pair Primrec.snd)
    exact Primrec.option_isSome.comp h1
  · intro s s' n hss hmem
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hmem
    exact Option.isSome_iff_exists.mpr ⟨x, Code.evaln_mono hss hx⟩
  · intro n
    have key : (f n).Dom ↔ ∃ s, (Code.evaln s c n).isSome = true := by
      constructor
      · intro hdom
        have hmem : (0 : ℕ) ∈ Code.eval c n := by
          rw [hc]; exact ⟨hdom, rfl⟩
        obtain ⟨s, hs⟩ := Code.evaln_complete.mp hmem
        exact ⟨s, Option.isSome_iff_exists.mpr ⟨0, hs⟩⟩
      · rintro ⟨s, hs⟩
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
        have hx' := Code.evaln_sound hx
        rw [hc] at hx'
        exact hx'.fst
    exact ⟨fun hn => key.mp ((hfA n).mpr hn), fun hs => (hfA n).mp (key.mpr hs)⟩

open Classical in
/-- The characteristic function of a set of naturals, as a total function. -/
private noncomputable def charFun (A : Set ℕ) : ℕ → ℕ := fun n => if n ∈ A then 1 else 0

private lemma charOracle_eq_totalOracle (A : Set ℕ) :
    charOracle A = totalOracle (charFun A) := rfl

private lemma oraclePrefix_congr {α β : ℕ → ℕ} {u : ℕ} (h : ∀ m < u, α m = β m) :
    oraclePrefix α u = oraclePrefix β u := by
  unfold oraclePrefix
  refine List.map_congr_left ?_
  intro m hm
  exact h m (List.mem_range.mp hm)

private lemma oraclePrefix_agree {α β : ℕ → ℕ} {u : ℕ} (h : oraclePrefix α u = oraclePrefix β u) :
    ∀ m < u, α m = β m := by
  intro m hm
  have h1 : (oraclePrefix α u)[m]? = (oraclePrefix β u)[m]? := by rw [h]
  simp only [oraclePrefix, List.getElem?_map, List.getElem?_range, hm,
    Option.map_some] at h1
  exact Option.some.inj h1

private lemma exists_param_fixed_point (psi : ℕ → ℕ →. ℕ) (hpsi : Partrec₂ psi) :
    ∃ dfun : ℕ → ℕ, Computable dfun ∧
      ∀ n x, (Denumerable.ofNat Code (dfun n)).eval x = psi n (dfun n) := by
  obtain ⟨sm, hsm_comp, hsm⟩ := Code.smn
  have hF : Partrec₂ (fun (c : Code) (p : ℕ) =>
      psi (Nat.unpair p).1 (Encodable.encode (sm c (Nat.unpair p).1))) := by
    have h1 : Computable fun q : Code × ℕ => (Nat.unpair q.2).1 :=
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
    have h2 : Computable fun q : Code × ℕ => Encodable.encode (sm q.1 (Nat.unpair q.2).1) :=
      Computable.encode.comp (hsm_comp.comp Computable.fst h1)
    exact (hpsi.comp h1 h2).to₂
  obtain ⟨c, hcfix⟩ := Code.fixed_point₂ hF
  refine ⟨fun n => Encodable.encode (sm c n), Computable.encode.comp
    (hsm_comp.comp (Computable.const c) Computable.id), ?_⟩
  intro n x
  have h1 : Denumerable.ofNat Code (Encodable.encode (sm c n)) = sm c n :=
    Denumerable.ofNat_encode _
  rw [h1, hsm c n x, hcfix]
  simp [Nat.unpair_pair]


private theorem recIn_pair_comp {O : Set (ℕ →. ℕ)} {f g F : ℕ →. ℕ}
    (hf : RecursiveIn O f) (hg : RecursiveIn O g) (hF : RecursiveIn O F) :
    RecursiveIn O (fun n => f n >>= fun a => g n >>= fun b => F (Nat.pair a b)) := by
  have h2 := RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp hF)
    (Nat.RecursiveIn.pair (RecursiveIn.iff_nat.mp hf) (RecursiveIn.iff_nat.mp hg)))
  refine recursiveIn_congr h2 (fun n => ?_)
  apply Part.ext
  intro v
  simp only [Seq.seq, Part.map_eq_map, Part.bind_eq_bind]
  constructor
  · intro hv
    obtain ⟨x, hx, hv⟩ := Part.mem_bind_iff.mp hv
    obtain ⟨y, hy, hx⟩ := Part.mem_bind_iff.mp hx
    obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).mp hy
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hx
    exact Part.mem_bind_iff.mpr ⟨a, ha, Part.mem_bind_iff.mpr ⟨b, hb, hv⟩⟩
  · intro hv
    obtain ⟨a, ha, hv⟩ := Part.mem_bind_iff.mp hv
    obtain ⟨b, hb, hv⟩ := Part.mem_bind_iff.mp hv
    refine Part.mem_bind_iff.mpr ⟨Nat.pair a b, ?_, hv⟩
    exact Part.mem_bind_iff.mpr ⟨Nat.pair a, (Part.mem_map_iff _).mpr ⟨a, ha, rfl⟩,
      (Part.mem_map_iff _).mpr ⟨b, hb, rfl⟩⟩

private theorem recIn_query {O : Set (ℕ →. ℕ)} {k : ℕ → ℕ}
    (hk : RecursiveIn O (totalOracle k)) {g : ℕ → ℕ} (hg : Computable g)
    {F : ℕ → ℕ → ℕ} (hF : Computable₂ F) :
    RecursiveIn O (totalOracle (fun q => F q (k (g q)))) := by
  have hid : RecursiveIn O (fun q : ℕ => Part.some q) :=
    recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec Computable.id))
  have hgp : RecursiveIn O (fun q : ℕ => Part.some (g q)) :=
    recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec hg))
  have h2 : RecursiveIn O (fun q : ℕ => totalOracle k (g q)) := by
    refine recursiveIn_congr (RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp
      (RecursiveIn.iff_nat.mp hk) (RecursiveIn.iff_nat.mp hgp))) (fun q => ?_)
    exact Part.bind_some (g q) (totalOracle k)
  have hFp : RecursiveIn O
      (fun m : ℕ => Part.some (F (Nat.unpair m).1 (Nat.unpair m).2)) := by
    refine recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec ?_))
    exact hF.comp (Computable.fst.comp (Primrec.unpair.to_comp))
      (Computable.snd.comp (Primrec.unpair.to_comp))
  refine recursiveIn_congr (recIn_pair_comp hid h2 hFp) (fun q => ?_)
  simp [totalOracle, Nat.unpair_pair]

private theorem recIn_oraclePrefixEncode (A : Set ℕ) :
    RecursiveIn {charOracle A}
      (totalOracle (fun u => Encodable.encode (oraclePrefix (charFun A) u))) := by
  have hchar : RecursiveIn {charOracle A} (totalOracle (charFun A)) := by
    rw [← charOracle_eq_totalOracle A]
    exact RecursiveIn.oracle _ (Set.mem_singleton _)
  have hstep : RecursiveIn {charOracle A} (totalOracle (fun q : ℕ =>
      Encodable.encode
        (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair q).2).2).getD []) ++
          [charFun A (Nat.unpair (Nat.unpair q).2).1]))) := by
    refine recIn_query hchar
      (g := fun q : ℕ => (Nat.unpair (Nat.unpair q).2).1)
      (F := fun q kv => Encodable.encode
        (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair q).2).2).getD []) ++ [kv]))
      ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp) ?_
    have hdec : Computable fun p : ℕ × ℕ =>
        (Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair p.1).2).2).getD [] :=
      Computable.option_getD
        (Computable.decode.comp
          ((Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
            Computable.fst))
        (Computable.const [])
    exact Computable.encode.comp
      (Computable.list_append.comp hdec
        (Computable.list_cons.comp Computable.snd (Computable.const [])))
  have hzero : RecursiveIn {charOracle A}
      (fun _ : ℕ => Part.some (Encodable.encode ([] : List ℕ))) :=
    recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec (Computable.const _)))
  have hprec := Nat.RecursiveIn.prec (RecursiveIn.iff_nat.mp hzero)
    (RecursiveIn.iff_nat.mp hstep)
  have hval : ∀ a n : ℕ,
      (Nat.rec (motive := fun _ => Part ℕ) (Part.some (Encodable.encode ([] : List ℕ)))
        (fun y IH => IH.bind fun i => totalOracle (fun q : ℕ =>
          Encodable.encode
            (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair q).2).2).getD []) ++
              [charFun A (Nat.unpair (Nat.unpair q).2).1])) (Nat.pair a (Nat.pair y i))) n) =
        Part.some (Encodable.encode (oraclePrefix (charFun A) n)) := by
    intro a n
    induction n with
    | zero => rfl
    | succ m ih =>
        change ((Nat.rec (motive := fun _ => Part ℕ) (Part.some (Encodable.encode ([] : List ℕ)))
          (fun y IH => IH.bind fun i => totalOracle (fun q : ℕ =>
            Encodable.encode
              (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair q).2).2).getD []) ++
                [charFun A (Nat.unpair (Nat.unpair q).2).1])) (Nat.pair a (Nat.pair y i))) m).bind
          (fun i => totalOracle (fun q : ℕ =>
            Encodable.encode
              (((Encodable.decode (α := List ℕ) (Nat.unpair (Nat.unpair q).2).2).getD []) ++
                [charFun A (Nat.unpair (Nat.unpair q).2).1])) (Nat.pair a (Nat.pair m i)))) = _
        rw [ih]
        simp only [Part.bind_some, totalOracle, Nat.unpair_pair, Encodable.encodek,
          Option.getD_some]
        congr 1
        unfold oraclePrefix
        rw [List.range_succ, List.map_append]
        rfl
  have hfinal : RecursiveIn {charOracle A}
      (fun u : ℕ => Part.some (Encodable.encode (oraclePrefix (charFun A) u))) := by
    have hcomp := RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp hprec
      (RecursiveIn.iff_nat.mp (recursiveIn_of_natPartrec (Partrec.nat_iff.mp
        (Computable.partrec (f := fun u : ℕ => Nat.pair 0 u)
        ((Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp))))))
    refine recursiveIn_congr hcomp (fun u => ?_)
    simp only [PFun.coe_val, Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
    exact hval 0 u
  exact hfinal


private lemma arslanov_primrec_decide_eq {α β : Type} [Primcodable α] [Primcodable β]
    [DecidableEq β] {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a = g a) := by
  have h0 : PrimrecPred fun a => f a = g a := PrimrecRel.comp Primrec.eq hf hg
  obtain ⟨_, h1⟩ := h0
  exact h1.of_eq (fun a => by congr 1)

/-- The stage-`s` approximation of the oracle. -/
private def approxFun (mem : ℕ → ℕ → Bool) (s m : ℕ) : ℕ := bif mem s m then 1 else 0

/-- The length-`u` prefix of the stage-`s` approximation of the oracle. -/
private def approxPrefix (mem : ℕ → ℕ → Bool) (s u : ℕ) : List ℕ :=
  oraclePrefix (approxFun mem s) u

/-- `n`'s self-application halts within `s` steps. -/
private def haltsBy (s n : ℕ) : Bool := (Code.evaln s (Denumerable.ofNat Code n) n).isSome

/-- A bounded run of the operator with oracle string `w` on input `e`. -/
private def runOp (cΦ : Code) (w : List ℕ) (e t : ℕ) : Option ℕ :=
  Code.evaln t cΦ (Encodable.encode (w, e))

/-- The program that Arslanov's argument feeds to the recursion theorem:  wait until
`n` enters the halting set, then run the operator against the corresponding finite
approximation of the oracle. -/
private noncomputable def arslanovPsi (mem : ℕ → ℕ → Bool) (cΦ : Code) (n d : ℕ) : Part ℕ :=
  (Nat.rfind fun s => Part.some (haltsBy s n)) >>= fun s =>
    Nat.rfindOpt fun z => runOp cΦ (approxPrefix mem s (Nat.unpair z).1) d (Nat.unpair z).2

private lemma primrec_approxPrefix {mem : ℕ → ℕ → Bool} (hmem : Primrec₂ mem) :
    Primrec₂ (approxPrefix mem) := by
  have h1 : Primrec₂ (approxFun mem) :=
    Primrec.cond hmem (Primrec.const 1) (Primrec.const 0)
  have h2 : Primrec fun q : (ℕ × ℕ) × ℕ => approxFun mem q.1.1 q.2 :=
    h1.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp Primrec.snd) h2

private lemma primrec_haltsBy : Primrec₂ haltsBy := by
  have h1 : Primrec fun p : ℕ × ℕ => Code.evaln p.1 (Denumerable.ofNat Code p.2) p.2 :=
    Code.primrec_evaln.comp
      ((Primrec.fst.pair ((Primrec.ofNat Code).comp Primrec.snd)).pair Primrec.snd)
  exact Primrec.option_isSome.comp h1

private lemma primrec_runOp (cΦ : Code) :
    Primrec fun q : (List ℕ × ℕ) × ℕ => runOp cΦ q.1.1 q.1.2 q.2 :=
  Code.primrec_evaln.comp
    ((Primrec.snd.pair (Primrec.const cΦ)).pair (Primrec.encode.comp Primrec.fst))

private lemma partrec_arslanovPsi {mem : ℕ → ℕ → Bool} (hmem : Primrec₂ mem) (cΦ : Code) :
    Partrec₂ (arslanovPsi mem cΦ) := by
  have hrf : Partrec fun p : ℕ × ℕ =>
      Nat.rfind (fun s => (Part.some (haltsBy s p.1) : Part Bool)) := by
    refine Partrec.rfind ?_
    exact ((primrec_haltsBy.to_comp).comp Computable.snd
      (Computable.fst.comp Computable.fst)).partrec
  have h1 : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      approxPrefix mem p.1.2 (Nat.unpair p.2).1 :=
    (primrec_approxPrefix hmem).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have h2 : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have h3 : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ => (Nat.unpair p.2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hinner : Primrec fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      runOp cΦ (approxPrefix mem p.1.2 (Nat.unpair p.2).1) p.1.1.2 (Nat.unpair p.2).2 :=
    (primrec_runOp cΦ).comp ((h1.pair h2).pair h3)
  have hopt : Partrec fun q : (ℕ × ℕ) × ℕ =>
      Nat.rfindOpt fun z => runOp cΦ (approxPrefix mem q.2 (Nat.unpair z).1) q.1.2
        (Nat.unpair z).2 := Partrec.rfindOpt hinner.to_comp
  exact (hrf.bind hopt.to₂).to₂

/-- The verification predicate of the oracle search:  at stage `s = (z)₁`, with an oracle
string of length `u`, the operator returns the expected value within `t` steps, and the
stage-`s` approximation agrees with the true oracle below `u` (checked against the oracle
answer `pc`). -/
private def arslanovCheck (mem : ℕ → ℕ → Bool) (cΦ : Code) (a z pc : ℕ) : Bool :=
  (decide (runOp cΦ (approxPrefix mem (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1)
      (Nat.unpair a).1 (Nat.unpair (Nat.unpair z).2).2 = some (Nat.unpair a).2)) &&
  (decide (Encodable.encode (approxPrefix mem (Nat.unpair z).1
      (Nat.unpair (Nat.unpair z).2).1) = pc))

private def arslanovStep (mem : ℕ → ℕ → Bool) (cΦ : Code) (q pc : ℕ) : ℕ :=
  bif arslanovCheck mem cΦ (Nat.unpair q).1 (Nat.unpair q).2 pc then 0 else 1

/-- The oracle query the search makes at the candidate `q = ⟨⟨e, v⟩, ⟨s, u, t⟩⟩`:  the
length `u` of the oracle string. -/
private def arslanovU (q : ℕ) : ℕ := (Nat.unpair (Nat.unpair (Nat.unpair q).2).2).1

private lemma computable_arslanovU : Computable arslanovU :=
  (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))).to_comp

private lemma computable_arslanovStep {mem : ℕ → ℕ → Bool} (hmem : Primrec₂ mem) (cΦ : Code) :
    Computable₂ (arslanovStep mem cΦ) := by
  have hq : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hpc : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  have ha : Primrec fun p : ℕ × ℕ => (Nat.unpair p.1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp hq)
  have hz : Primrec fun p : ℕ × ℕ => (Nat.unpair p.1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp hq)
  have hs : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp hz)
  have hut : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp hz)
  have hu : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp hut)
  have ht : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp hut)
  have he : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp ha)
  have hhv : Primrec fun p : ℕ × ℕ => (Nat.unpair (Nat.unpair p.1).1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp ha)
  have hpref : Primrec fun p : ℕ × ℕ =>
      approxPrefix mem (Nat.unpair (Nat.unpair p.1).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).1 :=
    (primrec_approxPrefix hmem).comp hs hu
  have hrun : Primrec fun p : ℕ × ℕ =>
      runOp cΦ (approxPrefix mem (Nat.unpair (Nat.unpair p.1).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).1)
        (Nat.unpair (Nat.unpair p.1).1).1
        (Nat.unpair (Nat.unpair (Nat.unpair p.1).2).2).2 :=
    (primrec_runOp cΦ).comp ((hpref.pair he).pair ht)
  have hc1 := arslanov_primrec_decide_eq hrun (Primrec.option_some.comp hhv)
  have hc2 := arslanov_primrec_decide_eq (Primrec.encode.comp hpref) hpc
  have hcheck : Primrec fun p : ℕ × ℕ =>
      arslanovCheck mem cΦ (Nat.unpair p.1).1 (Nat.unpair p.1).2 p.2 :=
    Primrec₂.comp Primrec.and hc1 hc2
  exact (Primrec.cond hcheck (Primrec.const 0) (Primrec.const 1)).to_comp


/-- The final decision function of Arslanov's argument, reading off the stage found by
the oracle search. -/
private def arslanovFinal (m : ℕ) : ℕ :=
  bif haltsBy (Nat.unpair (Nat.unpair m).2).1 (Nat.unpair (Nat.unpair m).1).1 then 1 else 0

private lemma computable_arslanovFinal : Computable arslanovFinal := by
  have h1 : Primrec fun m : ℕ => (Nat.unpair (Nat.unpair m).2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have h2 : Primrec fun m : ℕ => (Nat.unpair (Nat.unpair m).1).1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have h3 : Primrec fun m : ℕ =>
      haltsBy (Nat.unpair (Nat.unpair m).2).1 (Nat.unpair (Nat.unpair m).1).1 :=
    primrec_haltsBy.comp h1 h2
  exact (Primrec.cond h3 (Primrec.const 1) (Primrec.const 0)).to_comp

private lemma arslanov_bif_eq_zero_iff (b : Bool) :
    (bif b then (0 : ℕ) else 1) = 0 ↔ b = true := by
  cases b <;> simp

/-- Step approximation helper for `arslanov_completeness`. -/
private lemma arslanov_approx_step {A : Set ℕ} {mem : ℕ → ℕ → Bool}
    (hmemMono : ∀ s s' n, s ≤ s' → mem s n = true → mem s' n = true)
    (hmemA : ∀ n, n ∈ A ↔ ∃ s, mem s n = true)
    (s s' m : ℕ) (hss : s ≤ s') (hm : approxFun mem s m = charFun A m) :
    approxFun mem s' m = charFun A m := by
  by_cases hb : mem s' m = true
  · rw [approxFun, hb]
    have hmA : m ∈ A := (hmemA m).mpr ⟨s', hb⟩
    simp [charFun, hmA]
  · have hb' : mem s' m = false := Bool.not_eq_true _ |>.mp hb
    have hbs : mem s m = false := by
      by_contra hc
      have : mem s' m = true := hmemMono s s' m hss (Bool.not_eq_false _ |>.mp hc)
      rw [this] at hb'
      exact Bool.noConfusion hb'
    rw [approxFun, hb']
    rw [approxFun, hbs] at hm
    exact hm

/-- Existence of an oracle prefix approximation stage for `arslanov_completeness`. -/
private lemma arslanov_approx_ex {A : Set ℕ} {mem : ℕ → ℕ → Bool}
    (hmemMono : ∀ s s' n, s ≤ s' → mem s n = true → mem s' n = true)
    (hmemA : ∀ n, n ∈ A ↔ ∃ s, mem s n = true) (u : ℕ) :
    ∃ s, approxPrefix mem s u = oraclePrefix (charFun A) u := by
  have hpoint : ∀ m ≤ u, ∃ s, approxFun mem s m = charFun A m := by
    intro m _
    by_cases hmA : m ∈ A
    · obtain ⟨s, hs⟩ := (hmemA m).mp hmA
      exact ⟨s, by rw [approxFun, hs]; simp [charFun, hmA]⟩
    · refine ⟨0, ?_⟩
      have hb : mem 0 m = false := by
        by_contra hc
        exact hmA ((hmemA m).mpr ⟨0, Bool.not_eq_false _ |>.mp hc⟩)
      rw [approxFun, hb]
      simp [charFun, hmA]
  obtain ⟨s, hs⟩ := exists_bound_forall_le
    (P := fun m s => approxFun mem s m = charFun A m)
    (fun m s s' hss hP => arslanov_approx_step hmemMono hmemA s s' m hss hP) u hpoint
  exact ⟨s, oraclePrefix_congr (fun m hm => hs m (le_of_lt hm))⟩

/-- Claim B (halting equivalence) helper for `arslanov_completeness`.

The quantified hypotheses are interface assumptions about arbitrary machines: `hΦm` says
that the oracle operator `Φ` is monotone in its prefix, `hrun_sound` that the code `cΦ`
runs it, and `hmemMono`/`hmemA` that `mem` is a monotone enumeration of `A`. -/
private lemma arslanov_claimB {A : Set ℕ} {h : ℕ → ℕ} (hdiag : SolvesDiagonal h)
    {Φ : List ℕ × ℕ →. ℕ}
    (hΦm : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ (w, n) → v ∈ Φ (w', n))
    {mem : ℕ → ℕ → Bool}
    (hmemMono : ∀ s s' n, s ≤ s' → mem s n = true → mem s' n = true)
    (hmemA : ∀ n, n ∈ A ↔ ∃ s, mem s n = true)
    (cΦ : Code)
    (hrun_sound : ∀ (w : List ℕ) (e t v : ℕ), runOp cΦ w e t = some v → v ∈ Φ (w, e))
    (hcheck_iff : ∀ a z : ℕ, arslanovStep mem cΦ (Nat.pair a z)
        (Encodable.encode (oraclePrefix (charFun A) (arslanovU (Nat.pair a z)))) = 0 ↔
      (runOp cΦ (approxPrefix mem (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1)
          (Nat.unpair a).1 (Nat.unpair (Nat.unpair z).2).2 = some (Nat.unpair a).2 ∧
        approxPrefix mem (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1 =
          oraclePrefix (charFun A) (Nat.unpair (Nat.unpair z).2).1))
    (dfun : ℕ → ℕ)
    (hdfun : ∀ n x, (Denumerable.ofNat Code (dfun n)).eval x =
      arslanovPsi mem cΦ n (dfun n))
    (n z : ℕ)
    (hz : arslanovStep mem cΦ (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z)
        (Encodable.encode (oraclePrefix (charFun A)
          (arslanovU (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z)))) = 0) :
    n ∈ arslanovHaltingSet ↔ haltsBy (Nat.unpair z).1 n = true := by
  rw [hcheck_iff] at hz
  simp only [Nat.unpair_pair] at hz
  obtain ⟨hrun, hpref⟩ := hz
  set s := (Nat.unpair z).1 with hs_def
  set u := (Nat.unpair (Nat.unpair z).2).1 with hu_def
  set t := (Nat.unpair (Nat.unpair z).2).2 with ht_def
  constructor
  · intro hnK
    by_contra hnh
    have hnh' : haltsBy s n = false := Bool.not_eq_true _ |>.mp hnh
    have hex : ∃ s', haltsBy s' n = true := by
      obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hnK
      obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
      exact ⟨k, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩
    set sn := Nat.find hex with hsn_def
    have hsn : haltsBy sn n = true := Nat.find_spec hex
    have hsn_min : ∀ j < sn, haltsBy j n = false := by
      intro j hj
      have := Nat.find_min hex hj
      exact Bool.not_eq_true _ |>.mp this
    have hslt : s < sn := by
      rcases Nat.lt_or_ge s sn with hlt | hge
      · exact hlt
      · exfalso
        have : haltsBy s n = true := by
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsn
          exact Option.isSome_iff_exists.mpr ⟨x, Code.evaln_mono hge hx⟩
        rw [this] at hnh'
        exact Bool.noConfusion hnh'
    have hpref_sn : approxPrefix mem sn u = oraclePrefix (charFun A) u :=
      oraclePrefix_congr (fun m hm => arslanov_approx_step hmemMono hmemA s sn m (le_of_lt hslt)
        (oraclePrefix_agree hpref m hm))
    have hrun_sn : runOp cΦ (approxPrefix mem sn u) (dfun n) t = some (h (dfun n)) := by
      rw [hpref_sn, ← hpref]; exact hrun
    have hrfind_sn : sn ∈ Nat.rfind (fun s => (Part.some (haltsBy s n) : Part Bool)) := by
      refine Nat.mem_rfind.mpr ⟨by simp [hsn], fun {j} hj => ?_⟩
      simp [hsn_min j hj]
    have hoptdom : (Nat.rfindOpt fun z' =>
        runOp cΦ (approxPrefix mem sn (Nat.unpair z').1) (dfun n) (Nat.unpair z').2).Dom := by
      refine Nat.rfindOpt_dom.mpr ⟨Nat.pair u t, h (dfun n), ?_⟩
      simpa [Nat.unpair_pair] using hrun_sn
    obtain ⟨v, hvopt⟩ := Part.dom_iff_mem.mp hoptdom
    have hv : v ∈ arslanovPsi mem cΦ n (dfun n) := by
      rw [arslanovPsi, Part.bind_eq_bind, Part.mem_bind_iff]
      exact ⟨sn, hrfind_sn, hvopt⟩
    have hvmem : v ∈ (Denumerable.ofNat Code (dfun n)).eval 0 := by
      rw [hdfun n 0]; exact hv
    have hne : h (dfun n) ≠ v := hdiag (dfun n) v hvmem
    apply hne
    rw [arslanovPsi, Part.bind_eq_bind, Part.mem_bind_iff] at hv
    obtain ⟨s', hs'mem, hv'⟩ := hv
    have hs'eq : s' = sn := Part.mem_unique hs'mem hrfind_sn
    rw [hs'eq] at hv'
    obtain ⟨z', hz'⟩ := Nat.rfindOpt_spec hv'
    have hv1 : v ∈ Φ (approxPrefix mem sn (Nat.unpair z').1, dfun n) :=
      hrun_sound _ _ _ _ hz'
    have hv2 : h (dfun n) ∈ Φ (approxPrefix mem sn u, dfun n) :=
      hrun_sound _ _ _ _ hrun_sn
    rcases le_total u (Nat.unpair z').1 with hle | hle
    · have h1 : h (dfun n) ∈ Φ (approxPrefix mem sn (Nat.unpair z').1, dfun n) :=
        hΦm _ _ (oraclePrefix_prefix hle) _ _ hv2
      exact Part.mem_unique h1 hv1
    · have h1 : v ∈ Φ (approxPrefix mem sn u, dfun n) :=
        hΦm _ _ (oraclePrefix_prefix hle) _ _ hv1
      exact Part.mem_unique hv2 h1
  · intro hh
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hh
    exact Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩

/-- Oracle machine helper for `arslanov_completeness`. -/
private lemma arslanov_assembled_machine (A : Set ℕ) {h : ℕ → ℕ}
    (hrec0 : RecursiveIn {charOracle A} (totalOracle h))
    (dfun : ℕ → ℕ) (hdfun_comp : Computable dfun)
    (Search : ℕ →. ℕ) (hSearch : RecursiveIn {charOracle A} Search) :
    RecursiveIn {charOracle A} (fun x : ℕ =>
      totalOracle (fun n => Nat.pair n (Nat.pair (dfun n) (h (dfun n)))) x >>=
        fun r => Part.some r >>= fun a => Search (Nat.unpair r).2 >>= fun b =>
          Part.some (arslanovFinal (Nat.pair a b))) := by
  have hq1 : RecursiveIn {charOracle A}
      (totalOracle (fun n => Nat.pair n (Nat.pair (dfun n) (h (dfun n))))) := by
    have hF : Computable₂ (fun (n hv : ℕ) => Nat.pair n (Nat.pair (dfun n) hv)) := by
      have h1 : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
      exact (Primrec₂.natPair.to_comp.comp Computable.fst
        (Primrec₂.natPair.to_comp.comp (hdfun_comp.comp Computable.fst) Computable.snd))
    exact recIn_query hrec0 hdfun_comp hF
  have hSearch2 : RecursiveIn {charOracle A} (fun r : ℕ => Search (Nat.unpair r).2) := by
    have hid : RecursiveIn {charOracle A} (fun r : ℕ => Part.some (Nat.unpair r).2) :=
      recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec
        ((Primrec.snd.comp Primrec.unpair).to_comp)))
    refine recursiveIn_congr (RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp
      (RecursiveIn.iff_nat.mp hSearch) (RecursiveIn.iff_nat.mp hid))) (fun r => ?_)
    exact Part.bind_some (Nat.unpair r).2 Search
  have hFinPart : RecursiveIn {charOracle A}
      (fun r : ℕ => Part.some r >>= fun a => Search (Nat.unpair r).2 >>= fun b =>
        Part.some (arslanovFinal (Nat.pair a b))) := by
    have hid : RecursiveIn {charOracle A} (fun r : ℕ => Part.some r) :=
      recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec Computable.id))
    have hfin : RecursiveIn {charOracle A} (fun m : ℕ => Part.some (arslanovFinal m)) :=
      recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec computable_arslanovFinal))
    exact recIn_pair_comp hid hSearch2 hfin
  exact RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp hFinPart)
    (RecursiveIn.iff_nat.mp hq1))

/-- **Arslanov's completeness criterion.**  An enumerable oracle computing a solution of
the diagonal task computes the halting problem. -/
theorem arslanov_completeness :
    ∀ A : Set ℕ, IsEnumerableSet A → ∀ h : ℕ → ℕ, SolvesDiagonal h →
      RecursiveIn {charOracle A} (totalOracle h) →
        RecursiveIn {charOracle A} (charOracle arslanovHaltingSet) := by
  classical
  intro A hA h hdiag hrec
  have hrec0 := hrec
  rw [charOracle_eq_totalOracle A] at hrec
  obtain ⟨Φ, hΦp, hΦm, hΦc⟩ := exists_string_operator hrec
  obtain ⟨mem, hmemP, hmemMono, hmemA⟩ := exists_re_approx hA
  -- a code for the operator
  have hΦNp : Nat.Partrec
      (fun p => (Part.ofOption (Encodable.decode (α := List ℕ × ℕ) p)).bind Φ) := by
    refine Partrec.nat_iff.mp ?_
    exact (Computable.ofOption Computable.decode).bind (hΦp.comp Computable.snd).to₂
  obtain ⟨cΦ, hcΦ⟩ := Code.exists_code.mp hΦNp
  have hΦeval : ∀ (w : List ℕ) (e : ℕ), Code.eval cΦ (Encodable.encode (w, e)) = Φ (w, e) := by
    intro w e
    rw [hcΦ]
    simp only [Encodable.encodek]
    exact Part.bind_some (w, e) Φ
  have hrun_sound : ∀ (w : List ℕ) (e t v : ℕ), runOp cΦ w e t = some v → v ∈ Φ (w, e) := by
    intro w e t v hv
    have h1 : v ∈ Code.eval cΦ (Encodable.encode (w, e)) := Code.evaln_sound hv
    rwa [hΦeval] at h1
  have hrun_complete : ∀ (w : List ℕ) (e v : ℕ), v ∈ Φ (w, e) →
      ∃ t, runOp cΦ w e t = some v := by
    intro w e v hv
    rw [← hΦeval] at hv
    exact Code.evaln_complete.mp hv
  -- the recursion theorem
  obtain ⟨dfun, hdfun_comp, hdfun⟩ :=
    exists_param_fixed_point (arslanovPsi mem cΦ) (partrec_arslanovPsi hmemP cΦ)
  -- the oracle search
  set stepVal : ℕ → ℕ := fun q =>
    arslanovStep mem cΦ q (Encodable.encode (oraclePrefix (charFun A) (arslanovU q)))
    with hstepVal_def
  have hstepVal : RecursiveIn {charOracle A} (totalOracle stepVal) :=
    recIn_query (recIn_oraclePrefixEncode A) computable_arslanovU
      (computable_arslanovStep hmemP cΦ)
  set Search : ℕ →. ℕ := fun a =>
    Nat.rfind fun z => (fun m => m = 0) <$> totalOracle stepVal (Nat.pair a z) with hSearch_def
  have hSearch : RecursiveIn {charOracle A} Search :=
    RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.rfind (RecursiveIn.iff_nat.mp hstepVal))
  have hstepT : ∀ b : ℕ, true ∈ ((fun m => m = 0) <$>
      totalOracle stepVal b : Part Bool) ↔ stepVal b = 0 := by
    intro b
    by_cases h : stepVal b = 0 <;> simp [totalOracle, h]
  have hstepF : ∀ b : ℕ, false ∈ ((fun m => m = 0) <$>
      totalOracle stepVal b : Part Bool) ↔ stepVal b ≠ 0 := by
    intro b
    by_cases h : stepVal b = 0 <;> simp [totalOracle, h]
  have hSearch_mem : ∀ a z : ℕ, z ∈ Search a ↔
      (stepVal (Nat.pair a z) = 0 ∧ ∀ j < z, stepVal (Nat.pair a j) ≠ 0) := by
    intro a z
    rw [hSearch_def]
    refine Iff.trans Nat.mem_rfind ?_
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(hstepT (Nat.pair a z)).mp h1, fun j hj => ?_⟩
      exact (hstepF (Nat.pair a j)).mp (h2 hj)
    · rintro ⟨h1, h2⟩
      refine ⟨(hstepT (Nat.pair a z)).mpr h1, ?_⟩
      intro j hj
      exact (hstepF (Nat.pair a j)).mpr (h2 j hj)
  -- the two claims
  have hcheck_iff : ∀ a z : ℕ, stepVal (Nat.pair a z) = 0 ↔
      (runOp cΦ (approxPrefix mem (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1)
          (Nat.unpair a).1 (Nat.unpair (Nat.unpair z).2).2 = some (Nat.unpair a).2 ∧
        approxPrefix mem (Nat.unpair z).1 (Nat.unpair (Nat.unpair z).2).1 =
          oraclePrefix (charFun A) (Nat.unpair (Nat.unpair z).2).1) := by
    intro a z
    rw [hstepVal_def]
    simp only [arslanovStep, arslanovU, arslanovCheck, Nat.unpair_pair]
    rw [arslanov_bif_eq_zero_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Encodable.encode_injective h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]⟩
  have hclaimA : ∀ n : ℕ, ∃ z, stepVal (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z) = 0 := by
    intro n
    obtain ⟨u, hu⟩ := hΦc (dfun n) (h (dfun n)) (Part.mem_some _)
    obtain ⟨s, hs⟩ := arslanov_approx_ex hmemMono hmemA u
    have hu' : h (dfun n) ∈ Φ (approxPrefix mem s u, dfun n) := by rw [hs]; exact hu
    obtain ⟨t, ht⟩ := hrun_complete _ _ _ hu'
    refine ⟨Nat.pair s (Nat.pair u t), ?_⟩
    rw [hcheck_iff]
    simp only [Nat.unpair_pair]
    exact ⟨ht, hs⟩
  have hclaimB : ∀ (n z : ℕ), stepVal (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z) = 0 →
      (n ∈ arslanovHaltingSet ↔ haltsBy (Nat.unpair z).1 n = true) :=
    arslanov_claimB hdiag hΦm hmemMono hmemA cΦ hrun_sound hcheck_iff dfun hdfun
  -- assembling the oracle machine
  have hFinPart := arslanov_assembled_machine A hrec0 dfun hdfun_comp Search hSearch
  refine recursiveIn_congr hFinPart (fun n => ?_)
  -- the value of the assembled machine
  have hexz : ∃ z, stepVal (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z) = 0 := hclaimA n
  set z₀ := Nat.find hexz with hz₀_def
  have hz₀ : stepVal (Nat.pair (Nat.pair (dfun n) (h (dfun n))) z₀) = 0 := Nat.find_spec hexz
  have hz₀mem : z₀ ∈ Search (Nat.pair (dfun n) (h (dfun n))) := by
    rw [hSearch_mem]
    exact ⟨hz₀, fun j hj => Nat.find_min hexz hj⟩
  have hmemfinal : arslanovFinal (Nat.pair (Nat.pair n (Nat.pair (dfun n) (h (dfun n)))) z₀) ∈
      ((totalOracle (fun n => Nat.pair n (Nat.pair (dfun n) (h (dfun n))))) n >>=
        (fun r : ℕ => Part.some r >>= fun a => Search (Nat.unpair r).2 >>= fun b =>
          Part.some (arslanovFinal (Nat.pair a b)))) := by
    simp only [totalOracle, Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff]
    refine ⟨Nat.pair n (Nat.pair (dfun n) (h (dfun n))), rfl, ?_⟩
    refine ⟨Nat.pair n (Nat.pair (dfun n) (h (dfun n))), rfl, ?_⟩
    exact ⟨z₀, by simpa [Nat.unpair_pair] using hz₀mem, rfl⟩
  have hgoal : charOracle arslanovHaltingSet n =
      Part.some (arslanovFinal (Nat.pair (Nat.pair n (Nat.pair (dfun n) (h (dfun n)))) z₀)) := by
    rw [arslanovFinal]
    simp only [Nat.unpair_pair]
    by_cases hn : n ∈ arslanovHaltingSet
    · rw [(hclaimB n z₀ hz₀).mp hn]
      simp [charOracle, hn]
    · have hf : haltsBy (Nat.unpair z₀).1 n = false := by
        by_contra hc
        exact hn ((hclaimB n z₀ hz₀).mpr (Bool.not_eq_false _ |>.mp hc))
      rw [hf]
      simp [charOracle, hn]
  rw [hgoal]
  exact Part.eq_some_iff.mpr hmemfinal

end Kolmogorov


