/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Foundation.FixedPointFree.HighComplexityTask

/-!
# Exact finite-prefix operators

For a total oracle `α : ℕ → ℕ`, every partial function recursive in `α` is represented by an
ordinary partial computable operator `Φ` acting on pairs (finite initial segment of `α`, input),
which is monotone under extension of the segment, in the exact sense
`v ∈ f n ↔ ∃ u, v ∈ Φ (α↾u, n)` (`exists_exact_string_operator`, blueprint node
`oracle:operator`).  Compared with the one-sided representation of the older
`Kolmogorov.exists_string_operator`, the statement contains soundness as well as completeness.

The operator is built by induction over the generators of `RecursiveIn`; the auxiliary lemmas
below give, for pairing, primitive recursion and unbounded search, the computability of the
constructed operator and the exactness of its outputs.  The representation is the interface
through which the oracle prefix machines of `KolmogorovMathlib.Oracle` simulate oracle
computations by finite oracle queries.
-/

namespace Kolmogorov.PointToSet

/-- Pairing of two partial computable functions of the same argument is partial computable. -/
private lemma partrec_bind_pair {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hp₁ : Partrec Φ₁) (hp₂ : Partrec Φ₂) :
    Partrec (fun p : List ℕ × ℕ =>
      Φ₁ p >>= fun a => Φ₂ p >>= fun b => Part.some (Nat.pair a b)) := by
  have hg : Partrec fun q : (List ℕ × ℕ) × ℕ =>
        Φ₂ q.1 >>= fun b => Part.some (Nat.pair q.2 b) :=
      (hp₂.comp Computable.fst).bind (Computable₂.partrec₂
        (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  exact hp₁.bind hg.to₂

/-- The primitive-recursion scheme built from two operators that are monotone in the list
argument is again monotone in it. -/
private lemma mem_natRec_of_prefix {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
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

/-- The primitive-recursion scheme on the unpaired input is partial computable when its two
operators are. -/
private lemma partrec_natRec_unpair {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
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

/-- Unbounded search for a zero value of a partial computable operator is partial computable. -/
private lemma partrec_rfind_eq_zero {Φ₁ : List ℕ × ℕ →. ℕ} (hp₁ : Partrec Φ₁) :
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

/-- If `Φ₁`, `Φ₂` represent `f₁`, `f₂` exactly by finite oracle prefixes, then the
primitive-recursion scheme of the `Φ`s represents the primitive-recursion scheme of the `f`s
exactly. -/
private lemma mem_natRec_iff_exists_prefix {α : ℕ → ℕ} {f₁ f₂ : ℕ →. ℕ}
    {Φ₁ Φ₂ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (hm₂ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₂ (w, n) → v ∈ Φ₂ (w', n))
    (hc₁ : ∀ n v, v ∈ f₁ n ↔ ∃ u, v ∈ Φ₁ ((List.range u).map α, n))
    (hc₂ : ∀ n v, v ∈ f₂ n ↔ ∃ u, v ∈ Φ₂ ((List.range u).map α, n))
    (a k v : ℕ) :
    v ∈ (Nat.rec (f₁ a)
      (fun y IH => IH.bind fun i => f₂ (Nat.pair a (Nat.pair y i))) k : Part ℕ) ↔
    ∃ u, v ∈ (k.rec (Φ₁ ((List.range u).map α, a))
      (fun y IH => IH.bind fun i =>
        Φ₂ ((List.range u).map α, Nat.pair a (Nat.pair y i))) : Part ℕ) := by
  induction k generalizing v with
  | zero =>
    exact hc₁ a v
  | succ k ih =>
    simp only [Part.mem_bind_iff]
    constructor
    · rintro ⟨i, hi1, hi2⟩
      obtain ⟨u1, hu1⟩ := (ih i).mp hi1
      obtain ⟨u2, hu2⟩ := (hc₂ _ _).mp hi2
      use max u1 u2
      use i
      constructor
      · exact mem_natRec_of_prefix hm₁ hm₂ _ _
          (oraclePrefix_prefix (le_max_left _ _)) _ _ _ hu1
      · exact hm₂ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu2
    · rintro ⟨u, ⟨i, hi1, hi2⟩⟩
      use i
      constructor
      · exact (ih i).mpr ⟨u, hi1⟩
      · exact (hc₂ _ _).mpr ⟨u, hi2⟩

/-- Finitely many nonzero outputs of a monotone operator, each witnessed by some oracle prefix,
are witnessed simultaneously by one common prefix. -/
private lemma exists_prefix_bound_of_forall_lt {α : ℕ → ℕ} {Φ₁ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (n v : ℕ)
    (f : ∀ m < v,
      ∃ u a, decide (a = 0) = false ∧ a ∈ Φ₁ ((List.range u).map α, Nat.pair n m)) :
    ∃ U, ∀ m < v, ∃ a, decide (a = 0) = false ∧ a ∈ Φ₁ ((List.range U).map α, Nat.pair n m) := by
  induction v with
  | zero => exact ⟨0, fun m hm => by omega⟩
  | succ v ih =>
    obtain ⟨U_ih, hU_ih⟩ := ih fun m hm => f m (by omega)
    obtain ⟨u_v, a_v, ha_v, hv⟩ := f v (by omega)
    refine ⟨max U_ih u_v, fun m hm => ?_⟩
    obtain h_eq | h_lt := eq_or_lt_of_le (Nat.le_of_lt_succ hm)
    · subst h_eq
      refine ⟨a_v, ha_v, hm₁ _ _ ?_ _ _ hv⟩
      exact oraclePrefix_prefix (le_max_right _ _)
    · obtain ⟨a, ha, h_mem⟩ := hU_ih m h_lt
      refine ⟨a, ha, hm₁ _ _ ?_ _ _ h_mem⟩
      exact oraclePrefix_prefix (le_max_left _ _)

/-- If `Φ₁` represents `f₁` exactly by finite oracle prefixes, then the unbounded search over
`Φ₁` represents the unbounded search over `f₁` exactly. -/
private lemma mem_rfind_iff_exists_prefix {α : ℕ → ℕ} {f₁ : ℕ →. ℕ}
    {Φ₁ : List ℕ × ℕ →. ℕ}
    (hm₁ : ∀ w w' : List ℕ, w <+: w' → ∀ n v, v ∈ Φ₁ (w, n) → v ∈ Φ₁ (w', n))
    (hc₁ : ∀ n v, v ∈ f₁ n ↔ ∃ u, v ∈ Φ₁ ((List.range u).map α, n))
    (n v : ℕ) :
    v ∈ Nat.rfind (fun k => (fun m => decide (m = 0)) <$> f₁ (Nat.pair n k)) ↔
    ∃ u, v ∈ Nat.rfind (fun k =>
      (fun m => decide (m = 0)) <$> Φ₁ ((List.range u).map α, Nat.pair n k)) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Nat.mem_rfind.mp h
    simp only [Part.map_eq_map, Part.mem_map_iff] at h1
    obtain ⟨a1, ha1, e1⟩ := h1
    obtain ⟨u1, hu1⟩ := (hc₁ (Nat.pair n v) a1).mp ha1
    have H : ∀ m < v,
        ∃ u a, decide (a = 0) = false ∧ a ∈ Φ₁ ((List.range u).map α, Nat.pair n m) := by
      intro m hm
      have h2m := h2 hm
      simp only [Part.map_eq_map, Part.mem_map_iff] at h2m
      obtain ⟨a, ha, e⟩ := h2m
      obtain ⟨u, hu⟩ := (hc₁ (Nat.pair n m) a).mp ha
      exact ⟨u, a, e, hu⟩
    obtain ⟨U, hU⟩ := exists_prefix_bound_of_forall_lt hm₁ n v H
    refine ⟨max U u1, ?_⟩
    apply Nat.mem_rfind.mpr
    constructor
    · simp only [Part.map_eq_map, Part.mem_map_iff]
      refine ⟨a1, hm₁ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu1, e1⟩
    · intro m hm
      simp only [Part.map_eq_map, Part.mem_map_iff]
      obtain ⟨a, e, ha⟩ := hU m hm
      refine ⟨a, hm₁ _ _ (oraclePrefix_prefix (le_max_left _ _)) _ _ ha, e⟩
  · intro ⟨u, hu⟩
    obtain ⟨h1, h2⟩ := Nat.mem_rfind.mp hu
    apply Nat.mem_rfind.mpr
    constructor
    · simp only [Part.map_eq_map, Part.mem_map_iff] at h1 ⊢
      obtain ⟨a, ha, e⟩ := h1
      exact ⟨a, (hc₁ (Nat.pair n v) a).mpr ⟨u, ha⟩, e⟩
    · intro m hm
      have := h2 hm
      simp only [Part.map_eq_map, Part.mem_map_iff] at this ⊢
      obtain ⟨a, ha, e⟩ := this
      exact ⟨a, (hc₁ (Nat.pair n m) a).mpr ⟨u, ha⟩, e⟩

/-- Computations relative to a total natural-valued oracle have an ordinary partial
computable list operator, monotone in its finite oracle input, with exact outputs:
`v ∈ f n` iff some finite initial segment of the oracle makes the operator output `v`.
Blueprint node `oracle:operator`. -/
theorem exists_exact_string_operator (α : ℕ → ℕ) (f : ℕ →. ℕ)
    (hf : PartrecIn {totalOracle α} f) :
    ∃ Φ : List ℕ × ℕ →. ℕ, Partrec Φ ∧
      (∀ s t : List ℕ, s <+: t → ∀ n v, v ∈ Φ (s, n) → v ∈ Φ (t, n)) ∧
      ∀ n v, v ∈ f n ↔ ∃ u, v ∈ Φ ((List.range u).map α, n) := by
  replace hf := RecursiveIn.iff_nat.mp hf
  induction hf with
  | zero =>
      refine ⟨fun _ => Part.some 0, (Computable.const 0).partrec, fun w w' _ n v hv => hv, ?_⟩
      exact fun n v => ⟨fun hv => ⟨0, hv⟩, fun ⟨_, hv⟩ => hv⟩
  | succ =>
      refine ⟨fun p => Part.some (p.2 + 1),
        (Computable.succ.comp Computable.snd).partrec, fun w w' _ n v hv => hv, ?_⟩
      exact fun n v => ⟨fun hv => ⟨0, hv⟩, fun ⟨_, hv⟩ => hv⟩
  | left =>
      refine ⟨fun p => Part.some (Nat.unpair p.2).1,
        ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd).partrec,
        fun w w' _ n v hv => hv, ?_⟩
      exact fun n v => ⟨fun hv => ⟨0, hv⟩, fun ⟨_, hv⟩ => hv⟩
  | right =>
      refine ⟨fun p => Part.some (Nat.unpair p.2).2,
        ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd).partrec,
        fun w w' _ n v hv => hv, ?_⟩
      exact fun n v => ⟨fun hv => ⟨0, hv⟩, fun ⟨_, hv⟩ => hv⟩
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
      · intro n v
        constructor
        · intro hv
          refine ⟨n + 1, ?_⟩
          simp only [Part.mem_ofOption]
          have hv' : v = α n := by simpa [totalOracle] using hv
          subst hv'
          have : n < ((List.range (n + 1)).map α).length := by simp
          rw [List.getElem?_eq_getElem this]
          simp
        · intro ⟨u, hu⟩
          simp only [Part.mem_ofOption] at hu
          have hu2 : n < ((List.range u).map α).length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hu
            simp at hu
          rw [List.getElem?_eq_getElem hu2] at hu
          have hv' : α n = v := by
            simpa only [List.getElem_map, List.getElem_range, Option.mem_def,
              Option.some.injEq] using hu
          subst hv'
          simp [totalOracle]
  | @pair f₁ f₂ hf hh ih1 ih2 =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih1
      obtain ⟨Φ₂, hp₂, hm₂, hc₂⟩ := ih2
      refine ⟨fun p => Φ₁ p >>= fun a => Φ₂ p >>= fun b => Part.some (Nat.pair a b),
        partrec_bind_pair hp₁ hp₂, ?_, ?_⟩
      · intro w w' hw n v hv
        simp only [Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff] at hv ⊢
        obtain ⟨a, ha, b, hb, rfl⟩ := hv
        exact ⟨a, hm₁ _ _ hw _ _ ha, b, hm₂ _ _ hw _ _ hb, rfl⟩
      · intro n v
        constructor
        · intro hv
          simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff] at hv
          obtain ⟨g, ⟨a, ha, rfl⟩, b, hb, rfl⟩ := hv
          obtain ⟨u₁, hu₁⟩ := (hc₁ n a).mp ha
          obtain ⟨u₂, hu₂⟩ := (hc₂ n b).mp hb
          refine ⟨max u₁ u₂, ?_⟩
          simp only [Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff]
          exact ⟨a, hm₁ _ _ (oraclePrefix_prefix (le_max_left _ _)) _ _ hu₁,
            b, hm₂ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu₂, rfl⟩
        · intro ⟨u, hu⟩
          simp only [Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_some_iff] at hu
          obtain ⟨a, ha, b, hb, rfl⟩ := hu
          simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
          exact ⟨_, ⟨a, (hc₁ n a).mpr ⟨u, ha⟩, rfl⟩, b, (hc₂ n b).mpr ⟨u, hb⟩, rfl⟩
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
      · intro n v
        constructor
        · intro hv
          obtain ⟨m, hm, hv⟩ := Part.mem_bind_iff.mp hv
          obtain ⟨u₁, hu₁⟩ := (hc₂ n m).mp hm
          obtain ⟨u₂, hu₂⟩ := (hc₁ m v).mp hv
          refine ⟨max u₁ u₂, Part.mem_bind_iff.mpr ⟨m, ?_, ?_⟩⟩
          · exact hm₂ _ _ (oraclePrefix_prefix (le_max_left _ _)) _ _ hu₁
          · exact hm₁ _ _ (oraclePrefix_prefix (le_max_right _ _)) _ _ hu₂
        · intro ⟨u, hu⟩
          obtain ⟨m, hm, hv⟩ := Part.mem_bind_iff.mp hu
          exact Part.mem_bind_iff.mpr ⟨m, (hc₂ n m).mpr ⟨u, hm⟩, (hc₁ m v).mpr ⟨u, hv⟩⟩
  | @prec f₁ f₂ hf hh ih1 ih2 =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih1
      obtain ⟨Φ₂, hp₂, hm₂, hc₂⟩ := ih2
      set R : List ℕ → ℕ → ℕ → Part ℕ := fun w a k =>
        k.rec (Φ₁ (w, a)) (fun y IH => IH.bind fun i => Φ₂ (w, Nat.pair a (Nat.pair y i)))
      refine ⟨fun p => R p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2,
        partrec_natRec_unpair hp₁ hp₂, ?_, ?_⟩
      · intro w w' hw n v hv
        exact mem_natRec_of_prefix hm₁ hm₂ w w' hw _ _ v hv
      · intro n v
        exact mem_natRec_iff_exists_prefix hm₁ hm₂ hc₁ hc₂ _ _ v
  | @rfind f₁ hf ih =>
      obtain ⟨Φ₁, hp₁, hm₁, hc₁⟩ := ih
      refine ⟨fun p => Nat.rfind fun k =>
          (fun m => decide (m = 0)) <$> Φ₁ (p.1, Nat.pair p.2 k),
        partrec_rfind_eq_zero hp₁, ?_, ?_⟩
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
      · intro n v
        exact mem_rfind_iff_exists_prefix hm₁ hc₁ n v

end Kolmogorov.PointToSet
