/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.KLRules
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.NonMonotone.BoundedBetStrategy

/-!
# Muchnik Stages

The stage construction in the proof that a sequence whose plain complexity of prefixes is
sufficiently small is not Mises-Kolmogorov-Loveland random
(`not_isMisesKLRandom_of_plainK_lt`).  A finite automaton on the list of revealed bits runs two
competing searches on disjoint dyadic columns of the sequence, using only the complementary bits
as an oracle, with shared stage boundaries; its states, steps and runs are described by private
lemmas.

The main declaration is `not_isMisesKLRandom_of_plainK_lt_scheduler`: from a computable
enumeration of weighted words hitting prefixes of the columns and finite selectors with large
local discrepancy, it produces `2 * M` admissible Kolmogorov-Loveland rules, one of which has,
for every `N`, an output prefix of length at least `N` with discrepancy at least `ε / 4` times
its length.  This is the construction of the book by Shen, Uspensky and Vereshchagin
("Kolmogorov complexity and algorithmic randomness") for non-monotone selection rules.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology

open Classical in
/-- The initial segment `χ_B ↾ ℓ` of the characteristic function of `B`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_cp (B : Set ℕ) (ℓ : ℕ) :
    List Bool :=
  (List.range ℓ).map (fun n => decide (n ∈ B))

/-- `Ψ` simulates `f` along the approximations `sig`: sound for every approximation, complete
for all large ones. -/
private def not_isMisesKLRandom_of_plainK_lt_Sim (sig : ℕ → ℕ) (Ψ : ℕ × ℕ →. ℕ)
    (f : ℕ →. ℕ) : Prop :=
  Partrec Ψ ∧ (∀ n ℓ v, v ∈ Ψ (n, sig ℓ) → v ∈ f n) ∧
    (∀ n v, v ∈ f n → ∀ᶠ ℓ in atTop, v ∈ Ψ (n, sig ℓ))

private lemma not_isMisesKLRandom_of_plainK_lt_Sim_of_partrec (sig : ℕ → ℕ) {f : ℕ →. ℕ}
    (hf : Nat.Partrec f) :
    not_isMisesKLRandom_of_plainK_lt_Sim sig (fun p => f p.1) f :=
  ⟨(Partrec.nat_iff.mpr hf).comp Computable.fst, fun _ _ _ h => h,
    fun _ _ h => Filter.Eventually.of_forall (fun _ => h)⟩

private lemma not_isMisesKLRandom_of_plainK_lt_Sim_pair {sig : ℕ → ℕ}
    {Ψf Ψh : ℕ × ℕ →. ℕ} {f h : ℕ →. ℕ}
    (hf : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψf f)
    (hh : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψh h) :
    not_isMisesKLRandom_of_plainK_lt_Sim sig
      (fun p => (Ψf p).bind (fun x => (Ψh p).map (Nat.pair x)))
      (fun n => Nat.pair <$> f n <*> h n) := by
  obtain ⟨pf, sf, cf⟩ := hf
  obtain ⟨ph, sh, ch⟩ := hh
  refine ⟨?_, ?_, ?_⟩
  · refine Partrec.bind pf ?_
    refine Partrec.map (ph.comp Computable.fst) ?_
    exact (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp
  · intro n ℓ v hv
    simp only [Part.mem_bind_iff, Part.mem_map_iff] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    simp only [Seq.seq, Part.mem_bind_iff, Part.mem_map_iff, Functor.map]
    exact ⟨_, ⟨x, sf _ _ _ hx, rfl⟩, y, sh _ _ _ hy, rfl⟩
  · intro n v hv
    simp only [Seq.seq, Part.mem_bind_iff, Part.mem_map_iff, Functor.map] at hv
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := hv
    filter_upwards [cf _ _ hx, ch _ _ hy] with ℓ h1 h2
    simp only [Part.mem_bind_iff, Part.mem_map_iff]
    exact ⟨x, h1, y, h2, rfl⟩

private lemma not_isMisesKLRandom_of_plainK_lt_Sim_comp {sig : ℕ → ℕ}
    {Ψf Ψh : ℕ × ℕ →. ℕ} {f h : ℕ →. ℕ}
    (hf : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψf f)
    (hh : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψh h) :
    not_isMisesKLRandom_of_plainK_lt_Sim sig
      (fun p => (Ψh p).bind (fun m => Ψf (m, p.2)))
      (fun n => h n >>= f) := by
  obtain ⟨pf, sf, cf⟩ := hf
  obtain ⟨ph, sh, ch⟩ := hh
  refine ⟨?_, ?_, ?_⟩
  · refine Partrec.bind ph ?_
    exact pf.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))
  · intro n ℓ v hv
    simp only [Part.mem_bind_iff] at hv
    obtain ⟨m, hm, hv⟩ := hv
    exact Part.mem_bind_iff.mpr ⟨m, sh _ _ _ hm, sf _ _ _ hv⟩
  · intro n v hv
    obtain ⟨m, hm, hv⟩ := Part.mem_bind_iff.mp hv
    filter_upwards [ch _ _ hm, cf _ _ hv] with ℓ h1 h2
    exact Part.mem_bind_iff.mpr ⟨m, h1, h2⟩

private lemma not_isMisesKLRandom_of_plainK_lt_Sim_rfind {sig : ℕ → ℕ}
    {Ψf : ℕ × ℕ →. ℕ} {f : ℕ →. ℕ}
    (hf : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψf f) :
    not_isMisesKLRandom_of_plainK_lt_Sim sig
      (fun p => Nat.rfind fun n => (fun m => decide (m = 0)) <$> Ψf (Nat.pair p.1 n, p.2))
      (fun a => Nat.rfind fun n => (fun m => decide (m = 0)) <$> f (Nat.pair a n)) := by
  obtain ⟨pf, sf, cf⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · refine Partrec.rfind ?_
    simp only [Part.map_eq_map]
    refine Partrec.map ?_ ?_
    · exact pf.comp ((Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
        (Primrec.snd.comp Primrec.fst)).to_comp
    · exact ((PrimrecRel.decide Primrec.eq).comp Primrec.snd (Primrec.const 0)).to_comp
  · intro n ℓ v hv
    obtain ⟨hv1, hv2⟩ := Nat.mem_rfind.mp hv
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simp only [Part.map_eq_map, Part.mem_map_iff] at hv1 ⊢
      obtain ⟨c, hc, hc0⟩ := hv1
      exact ⟨c, sf _ _ _ hc, hc0⟩
    · intro m hm
      have h2 := hv2 hm
      simp only [Part.map_eq_map, Part.mem_map_iff] at h2 ⊢
      obtain ⟨c, hc, hc0⟩ := h2
      exact ⟨c, sf _ _ _ hc, hc0⟩
  · intro n v hv
    obtain ⟨hv1, hv2⟩ := Nat.mem_rfind.mp hv
    have e1 : ∀ᶠ ℓ in atTop, true ∈ (fun m => decide (m = 0)) <$>
        Ψf (Nat.pair n v, sig ℓ) := by
      simp only [Part.map_eq_map, Part.mem_map_iff] at hv1 ⊢
      obtain ⟨c, hc, hc0⟩ := hv1
      filter_upwards [cf _ _ hc] with ℓ h1
      exact ⟨c, h1, hc0⟩
    have e2 : ∀ m ∈ Finset.range v, ∀ᶠ ℓ in atTop, false ∈ (fun m => decide (m = 0)) <$>
        Ψf (Nat.pair n m, sig ℓ) := by
      intro m hm
      have h2 := hv2 (Finset.mem_range.mp hm)
      simp only [Part.map_eq_map, Part.mem_map_iff] at h2 ⊢
      obtain ⟨c, hc, hc0⟩ := h2
      filter_upwards [cf _ _ hc] with ℓ h1
      exact ⟨c, h1, hc0⟩
    have e3 := (Filter.eventually_all_finset (Finset.range v)).mpr e2
    filter_upwards [e1, e3] with ℓ h1 h3
    exact Nat.mem_rfind.mpr ⟨h1, fun {m} hm => h3 m (Finset.mem_range.mpr hm)⟩


private lemma not_isMisesKLRandom_of_plainK_lt_Sim_prec {sig : ℕ → ℕ}
    {Ψf Ψh : ℕ × ℕ →. ℕ} {f h : ℕ →. ℕ}
    (hf : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψf f)
    (hh : not_isMisesKLRandom_of_plainK_lt_Sim sig Ψh h) :
    not_isMisesKLRandom_of_plainK_lt_Sim sig
      (fun p => Nat.rec (motive := fun _ => Part ℕ) (Ψf ((Nat.unpair p.1).1, p.2))
        (fun y IH => IH.bind (fun i => Ψh (Nat.pair (Nat.unpair p.1).1 (Nat.pair y i), p.2)))
        (Nat.unpair p.1).2)
      (fun p => match Nat.unpair p with
        | (a, n) =>
          Nat.rec (motive := fun _ => Part ℕ) (f a)
            (fun y IH => IH.bind (fun i => h (Nat.pair a (Nat.pair y i)))) n) := by
  obtain ⟨pf, sf, cf⟩ := hf
  obtain ⟨ph, sh, ch⟩ := hh
  have sound : ∀ (N a ℓ v : ℕ),
      v ∈ (Nat.rec (motive := fun _ => Part ℕ) (Ψf (a, sig ℓ))
        (fun y IH => IH.bind (fun i => Ψh (Nat.pair a (Nat.pair y i), sig ℓ))) N) →
      v ∈ (Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun y IH => IH.bind (fun i => h (Nat.pair a (Nat.pair y i)))) N) := by
    intro N
    induction N with
    | zero => intro a ℓ v hv; exact sf _ _ _ hv
    | succ N ih =>
      intro a ℓ v hv
      obtain ⟨i, hi, hv'⟩ := Part.mem_bind_iff.mp hv
      exact Part.mem_bind_iff.mpr ⟨i, ih a ℓ i hi, sh _ _ _ hv'⟩
  have compl : ∀ (N a v : ℕ),
      v ∈ (Nat.rec (motive := fun _ => Part ℕ) (f a)
        (fun y IH => IH.bind (fun i => h (Nat.pair a (Nat.pair y i)))) N) →
      ∀ᶠ ℓ in atTop, v ∈ (Nat.rec (motive := fun _ => Part ℕ) (Ψf (a, sig ℓ))
        (fun y IH => IH.bind (fun i => Ψh (Nat.pair a (Nat.pair y i), sig ℓ))) N) := by
    intro N
    induction N with
    | zero => intro a v hv; exact cf _ _ hv
    | succ N ih =>
      intro a v hv
      obtain ⟨i, hi, hv'⟩ := Part.mem_bind_iff.mp hv
      filter_upwards [ih a i hi, ch _ _ hv'] with ℓ h1 h2
      exact Part.mem_bind_iff.mpr ⟨i, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Partrec.nat_rec
      (f := fun x : ℕ × ℕ => (Nat.unpair x.1).2)
      (g := fun x : ℕ × ℕ => Ψf ((Nat.unpair x.1).1, x.2))
      (h := fun (x : ℕ × ℕ) (yi : ℕ × ℕ) =>
        Ψh (Nat.pair (Nat.unpair x.1).1 (Nat.pair yi.1 yi.2), x.2)) ?_ ?_ ?_
    · exact Computable.snd.comp (Computable.unpair.comp Computable.fst)
    · exact pf.comp ((Computable.fst.comp (Computable.unpair.comp Computable.fst)).pair
        Computable.snd)
    · refine ph.comp ?_
      exact (((Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.snd.comp Primrec.fst))).to_comp
  · intro n ℓ v hv
    exact sound (Nat.unpair n).2 (Nat.unpair n).1 ℓ v hv
  · intro n v hv
    exact compl (Nat.unpair n).2 (Nat.unpair n).1 v hv



open Classical in
private lemma not_isMisesKLRandom_of_plainK_lt_step8_cp_getElem? (B : Set ℕ) (ℓ n : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_cp B ℓ)[n]? =
      if n < ℓ then some (decide (n ∈ B)) else none := by
  unfold not_isMisesKLRandom_of_plainK_lt_cp
  rw [List.getElem?_map]
  by_cases hn : n < ℓ
  · rw [List.getElem?_range hn]
    simp [hn]
  · rw [List.getElem?_eq_none (by simpa using not_lt.mp hn)]
    simp [hn]

private lemma not_isMisesKLRandom_of_plainK_lt_Sim_oracle (B : Set ℕ) :
    not_isMisesKLRandom_of_plainK_lt_Sim
      (fun ℓ => Encodable.encode (not_isMisesKLRandom_of_plainK_lt_cp B ℓ))
      (fun p => Part.ofOption ((Encodable.decode (α := List Bool) p.2).bind
        (fun σ => (σ[p.1]?).map (fun b => cond b 1 0))))
      (charOracle B) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine Computable.ofOption ?_
    refine Computable.option_bind (Computable.decode.comp Computable.snd) ?_
    refine Computable.option_map ?_ ?_
    · exact Computable.list_getElem?.comp Computable.snd (Computable.fst.comp Computable.fst)
    · exact (Primrec.dom_bool (fun b : Bool => cond b 1 0)).to_comp.comp Computable.snd
  · intro n ℓ v hv
    simp only [Part.mem_ofOption, Encodable.encodek, Option.bind_some, Option.mem_def] at hv
    rw [not_isMisesKLRandom_of_plainK_lt_step8_cp_getElem?] at hv
    by_cases hn : n < ℓ
    · simp only [hn, ↓reduceIte, Option.map_some, Option.some.injEq] at hv
      by_cases hB : n ∈ B <;> simp [charOracle, hB, ← hv]
    · simp [hn] at hv
  · intro n v hv
    have hv' : v = if n ∈ B then 1 else 0 := by simpa [charOracle] using hv
    filter_upwards [Filter.eventually_gt_atTop n] with ℓ hℓ
    simp only [Part.mem_ofOption, Encodable.encodek, Option.bind_some, Option.mem_def]
    rw [not_isMisesKLRandom_of_plainK_lt_step8_cp_getElem?]
    by_cases hB : n ∈ B <;> simp [hℓ, hB, hv']



private lemma not_isMisesKLRandom_of_plainK_lt_use_aux (B : Set ℕ) :
    ∀ f : ℕ →. ℕ, Nat.RecursiveIn {charOracle B} f →
      ∃ Ψ, not_isMisesKLRandom_of_plainK_lt_Sim
        (fun ℓ => Encodable.encode (not_isMisesKLRandom_of_plainK_lt_cp B ℓ)) Ψ f := by
  intro f hf
  induction hf with
  | zero => exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_of_partrec _ (by constructor)⟩
  | succ => exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_of_partrec _ (by constructor)⟩
  | left => exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_of_partrec _ (by constructor)⟩
  | right => exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_of_partrec _ (by constructor)⟩
  | oracle g hg =>
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_oracle B⟩
  | pair hf hh ihf ihh =>
    obtain ⟨Ψf, hΨf⟩ := ihf
    obtain ⟨Ψh, hΨh⟩ := ihh
    exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_pair hΨf hΨh⟩
  | comp hf hh ihf ihh =>
    obtain ⟨Ψf, hΨf⟩ := ihf
    obtain ⟨Ψh, hΨh⟩ := ihh
    exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_comp hΨf hΨh⟩
  | prec hf hh ihf ihh =>
    obtain ⟨Ψf, hΨf⟩ := ihf
    obtain ⟨Ψh, hΨh⟩ := ihh
    exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_prec hΨf hΨh⟩
  | rfind hf ihf =>
    obtain ⟨Ψf, hΨf⟩ := ihf
    exact ⟨_, not_isMisesKLRandom_of_plainK_lt_Sim_rfind hΨf⟩

/-- The word encoded by an output of the enumeration (if any). -/
private def not_isMisesKLRandom_of_plainK_lt_getU (v : ℕ) : Option BitString :=
  (Encodable.decode (α := Option BitString) v).bind id

/-- The finite-use enumeration of the code `c`: all words produced within `|σ|` steps on a prefix of
`σ`, at an index `≤ |σ|`. -/
private def not_isMisesKLRandom_of_plainK_lt_Dseq (c : Nat.Partrec.Code) (σ : List Bool) :
    List BitString :=
  (List.range (σ.length + 1)).flatMap (fun ℓ' =>
    (List.range (σ.length + 1)).filterMap (fun t =>
      (Nat.Partrec.Code.evaln σ.length c (Nat.pair t (Encodable.encode (σ.take ℓ')))).bind
        not_isMisesKLRandom_of_plainK_lt_getU))

private lemma not_isMisesKLRandom_of_plainK_lt_getU_primrec :
    Primrec not_isMisesKLRandom_of_plainK_lt_getU :=
  Primrec.option_bind Primrec.decode Primrec.snd

private lemma not_isMisesKLRandom_of_plainK_lt_Dseq_primrec (c : Nat.Partrec.Code) :
    Primrec (not_isMisesKLRandom_of_plainK_lt_Dseq c) := by
  unfold not_isMisesKLRandom_of_plainK_lt_Dseq
  refine Primrec.list_flatMap
    (f := fun σ : List Bool => List.range (σ.length + 1))
    (g := fun (σ : List Bool) (ℓ' : ℕ) => (List.range (σ.length + 1)).filterMap (fun t =>
      (Nat.Partrec.Code.evaln σ.length c (Nat.pair t (Encodable.encode (σ.take ℓ')))).bind
        not_isMisesKLRandom_of_plainK_lt_getU))
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length)) ?_
  refine Primrec.listFilterMap
    (f := fun p : List Bool × ℕ => List.range (p.1.length + 1))
    (g := fun (p : List Bool × ℕ) (t : ℕ) =>
      (Nat.Partrec.Code.evaln p.1.length c (Nat.pair t (Encodable.encode (p.1.take p.2)))).bind
        not_isMisesKLRandom_of_plainK_lt_getU)
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst))) ?_
  refine Primrec.option_bind
    (f := fun q : (List Bool × ℕ) × ℕ =>
      Nat.Partrec.Code.evaln q.1.1.length c
        (Nat.pair q.2 (Encodable.encode (q.1.1.take q.1.2))))
    (g := fun (_ : (List Bool × ℕ) × ℕ) (v : ℕ) =>
      not_isMisesKLRandom_of_plainK_lt_getU v) ?_
    (not_isMisesKLRandom_of_plainK_lt_getU_primrec.comp Primrec.snd)
  exact Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.const c)).pair
      (Primrec₂.natPair.comp Primrec.snd
        (Primrec.encode.comp (Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp Primrec.fst)))))



private lemma not_isMisesKLRandom_of_plainK_lt_cp_length (B : Set ℕ) (ℓ : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_cp B ℓ).length = ℓ := by
  simp [not_isMisesKLRandom_of_plainK_lt_cp]

private lemma not_isMisesKLRandom_of_plainK_lt_cp_take (B : Set ℕ) {ℓ' ℓ : ℕ}
    (h : ℓ' ≤ ℓ) :
    (not_isMisesKLRandom_of_plainK_lt_cp B ℓ).take ℓ' =
      not_isMisesKLRandom_of_plainK_lt_cp B ℓ' := by
  unfold not_isMisesKLRandom_of_plainK_lt_cp
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

private lemma not_isMisesKLRandom_of_plainK_lt_getU_encode (e : Option BitString) :
    not_isMisesKLRandom_of_plainK_lt_getU (Encodable.encode e) = e := by
  simp [not_isMisesKLRandom_of_plainK_lt_getU]

/-- Step 8 of the proof of `not_isMisesKLRandom_of_plainK_lt`: the finite-use form
(use principle) of an enumeration computable in the characteristic oracle of `B`.  There is a
computable monotone `Dseq` of finite lists of words whose values on the initial segments `χ_B ↾ ℓ`
list only enumerated words and eventually list every enumerated word.  Proof: induction on the
derivation of `Nat.RecursiveIn` simulates each oracle query by a lookup in the segment (all
combinators keep soundness for every segment and completeness for all large segments), then a code
of the simulation is run with the step bound `|σ|` on the prefixes of `σ` (`evaln`), and the union
over prefixes makes it monotone. -/
private lemma not_isMisesKLRandom_of_plainK_lt_use (B : Set ℕ) (E : ℕ → Option BitString)
    (hE : ComputableIn {charOracle B} E) :
    ∃ Dseq : List Bool → List BitString, Computable Dseq ∧
      (∀ σ σ' : List Bool, σ <+: σ' → ∀ u ∈ Dseq σ, u ∈ Dseq σ') ∧
      (∀ ℓ : ℕ, ∀ u ∈ Dseq (not_isMisesKLRandom_of_plainK_lt_cp B ℓ), ∃ t, E t = some u) ∧
      (∀ t u, E t = some u →
        ∃ ℓ0 : ℕ, ∀ ℓ ≥ ℓ0, u ∈ Dseq (not_isMisesKLRandom_of_plainK_lt_cp B ℓ)) := by
  have hE0 : Nat.RecursiveIn {charOracle B}
      (fun n => Part.bind (Encodable.decode (α := ℕ) n) fun a =>
        (Part.some (E a)).map Encodable.encode) := hE
  have hE' : Nat.RecursiveIn {charOracle B} (fun t => Part.some (Encodable.encode (E t))) := by
    refine Nat.RecursiveIn.of_eq hE0 ?_
    intro n
    simp
  obtain ⟨Ψ, pΨ, sΨ, cΨ⟩ := not_isMisesKLRandom_of_plainK_lt_use_aux B _ hE'
  have hnat : Nat.Partrec (fun x => Ψ (Nat.unpair x)) :=
    Partrec.nat_iff.mp (pΨ.comp Computable.unpair)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hnat
  refine ⟨not_isMisesKLRandom_of_plainK_lt_Dseq c,
    (not_isMisesKLRandom_of_plainK_lt_Dseq_primrec c).to_comp, ?_, ?_, ?_⟩
  · -- monotone
    intro σ σ' hσ u hu
    obtain ⟨τ, rfl⟩ := hσ
    unfold not_isMisesKLRandom_of_plainK_lt_Dseq at hu ⊢
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hu ⊢
    obtain ⟨ℓ', hℓ', t, ht, hv⟩ := hu
    refine ⟨ℓ', by simp only [List.length_append]; omega, t,
      by simp only [List.length_append]; omega, ?_⟩
    rw [List.take_append_of_le_length (by omega)]
    obtain ⟨v, hv1, hv2⟩ := Option.bind_eq_some_iff.mp hv
    refine Option.bind_eq_some_iff.mpr ⟨v, ?_, hv2⟩
    exact Nat.Partrec.Code.evaln_mono (by simp only [List.length_append]; omega) hv1
  · -- sound
    intro ℓ u hu
    unfold not_isMisesKLRandom_of_plainK_lt_Dseq at hu
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hu
    obtain ⟨ℓ', hℓ', t, ht, hv⟩ := hu
    obtain ⟨v, hv1, hv2⟩ := Option.bind_eq_some_iff.mp hv
    rw [not_isMisesKLRandom_of_plainK_lt_cp_length] at hℓ' ht
    rw [not_isMisesKLRandom_of_plainK_lt_cp_length,
      not_isMisesKLRandom_of_plainK_lt_cp_take B (by omega)] at hv1
    have hv3 := Nat.Partrec.Code.evaln_sound hv1
    rw [hc] at hv3
    simp only [Nat.unpair_pair] at hv3
    have hv4 := sΨ t ℓ' v hv3
    have hv5 : v = Encodable.encode (E t) := Part.mem_some_iff.mp hv4
    rw [hv5, not_isMisesKLRandom_of_plainK_lt_getU_encode] at hv2
    exact ⟨t, hv2⟩
  · -- complete
    intro t u hEt
    have hmem : Encodable.encode (E t) ∈ (Part.some (Encodable.encode (E t)) : Part ℕ) :=
      Part.mem_some _
    obtain ⟨ℓ0, h0⟩ := Filter.eventually_atTop.mp (cΨ t _ hmem)
    have hv0 := h0 ℓ0 le_rfl
    have hv1 : Encodable.encode (E t) ∈
        Nat.Partrec.Code.eval c (Nat.pair t (Encodable.encode
          (not_isMisesKLRandom_of_plainK_lt_cp B ℓ0))) := by
      rw [hc]
      simpa only [Nat.unpair_pair] using hv0
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv1
    refine ⟨max (max ℓ0 k) t, fun ℓ hℓ => ?_⟩
    unfold not_isMisesKLRandom_of_plainK_lt_Dseq
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨ℓ0, ?_, t, ?_, ?_⟩
    · rw [not_isMisesKLRandom_of_plainK_lt_cp_length]; omega
    · rw [not_isMisesKLRandom_of_plainK_lt_cp_length]; omega
    · rw [not_isMisesKLRandom_of_plainK_lt_cp_length,
        not_isMisesKLRandom_of_plainK_lt_cp_take B (by omega)]
      refine Option.bind_eq_some_iff.mpr ⟨Encodable.encode (E t), ?_, ?_⟩
      · exact Nat.Partrec.Code.evaln_mono (by omega) hk
      · rw [not_isMisesKLRandom_of_plainK_lt_getU_encode, hEt]


/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: a computable automaton
`(init, step, query, select)` over the alphabet `Bool` whose queries never repeat along a chain of
histories is a Kolmogorov-Loveland admissible rule: it reveals the position `query (x.foldl step
init)`
after the history `x` and selects the revealed bit iff `select (x.foldl step init)`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_rule_of_automaton
    {S : Type} [Primcodable S] (init : S) (step : S → Bool → S) (query : S → ℕ) (select : S → Bool)
    (hstep : Computable₂ step) (hquery : Computable query) (hselect : Computable select)
    (hnr : ∀ x y : List Bool, x <+: y → x ≠ y →
      query (x.foldl step init) ≠ query (y.foldl step init)) :
    ∃ ρ : KLRule, ρ.IsAdmissible ∧
      (∀ x, ρ.next x = Part.some (query (x.foldl step init))) ∧
      (∀ x, ρ.sel x = Part.some (select (x.foldl step init))) := by
  have hfold : Computable (fun x : List Bool => x.foldl step init) := by
    have h := Computable.list_foldl (l := fun x : List Bool => x)
      (g := fun _ : List Bool => init)
      (h := fun (_ : List Bool) (p : S × Bool) => step p.1 p.2)
      Computable.id (Computable.const init)
      (hstep.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
    exact h
  refine ⟨⟨fun x => Part.some (query (x.foldl step init)),
    fun x => Part.some (select (x.foldl step init)), ?_⟩, ⟨?_, ?_⟩, fun x => rfl, fun x => rfl⟩
  · intro x y hxy hne a ha b hb
    rw [Part.mem_some_iff] at ha hb
    subst ha hb
    exact hnr x y hxy hne
  · exact (hquery.comp hfold).partrec
  · exact (hselect.comp hfold).partrec

/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: if the rule `ρ` always
asks for the position `q x` after the history `x`, the revealed bits are obtained by appending
`w (q x)` to the previous history. -/
private lemma not_isMisesKLRandom_of_plainK_lt_revealed_succ (ρ : KLRule)
    (q : BitString → ℕ) (hq : ∀ x, ρ.next x = Part.some (q x)) (w : CantorSeq) (t : ℕ) :
    ρ.revealed w (t + 1) = ρ.revealed w t ++ [w (q (ρ.revealed w t))] := by
  have hdom : (ρ.next (ρ.revealed w t)).Dom := by
    rw [hq]
    exact trivial
  have hmem : q (ρ.revealed w t) ∈ ρ.next (ρ.revealed w t) := by
    rw [hq]
    exact Part.mem_some _
  rw [KLRule.revealed]
  simp only [hdom, ↓reduceDIte]
  rw [Part.get_eq_of_mem hmem hdom]

/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: no bit is revealed at
time `0`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_revealed_zero (ρ : KLRule) (w : CantorSeq) :
    ρ.revealed w 0 = [] := by
  rw [KLRule.revealed]

/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: a rule whose `next` is
total reveals exactly one bit per step. -/
private lemma not_isMisesKLRandom_of_plainK_lt_revealed_length (ρ : KLRule)
    (q : BitString → ℕ) (hq : ∀ x, ρ.next x = Part.some (q x)) (w : CantorSeq) (t : ℕ) :
    (ρ.revealed w t).length = t := by
  induction t with
  | zero => rw [not_isMisesKLRandom_of_plainK_lt_revealed_zero]; rfl
  | succ t ih =>
    rw [not_isMisesKLRandom_of_plainK_lt_revealed_succ ρ q hq, List.length_append, ih]
    rfl

/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: if `ρ.sel x` is always
the value `s x`, the set of strings of `ρ` is `{x | s x = true}`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_partialRuleSet_eq (ρ : KLRule)
    (s : BitString → Bool) (hs : ∀ x, ρ.sel x = Part.some (s x)) :
    partialRuleSet ρ.sel = {x | s x = true} := by
  ext x
  simp only [partialRuleSet, Set.mem_ofPred_eq, hs, Part.some_dom, implies_true, true_and,
    Part.mem_some_iff]
  exact eq_comm

/-- Step 8b' of the proof of `not_isMisesKLRandom_of_plainK_lt`: the selected output of a
rule with total `sel x = s x`, as the bits of the revealed string selected by `{x | s x = true}`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_outputChain_eq (ρ : KLRule)
    (s : BitString → Bool) (hs : ∀ x, ρ.sel x = Part.some (s x)) (w : CantorSeq) (t : ℕ) :
    ρ.outputChain w t = selectedBits {x | s x = true} (ρ.revealed w t) := by
  unfold KLRule.outputChain
  rw [not_isMisesKLRandom_of_plainK_lt_partialRuleSet_eq ρ s hs]

/-- The discrepancy of a string is at most its length. -/
private lemma not_isMisesKLRandom_of_plainK_lt_disc_le (u : BitString) :
    |(u.count true : ℝ) - u.count false| ≤ u.length := by
  have h : ((u.count true : ℝ) + u.count false) = u.length := by
    exact_mod_cast List.count_true_add_count_false u
  rw [abs_le]
  constructor <;>
    nlinarith [Nat.cast_nonneg (α := ℝ) (u.count true), Nat.cast_nonneg (α := ℝ) (u.count false)]

/-- Accounting for one successful stage: earlier selections (at most `m`) cannot destroy the
discrepancy of the `ε |x|` selected bits of the stage word, because `ε |x| > 4 (m + 1)`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_account (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (pre sx : BitString) (m xl N : ℕ) (hpre : pre.length ≤ m) (hsx : sx.length ≤ xl)
    (hdisc : ε * xl ≤ |(sx.count true : ℝ) - sx.count false|)
    (hbig : 4 * ((m : ℝ) + 1) < ε * xl) (hN : N ≤ m) :
    N ≤ (pre ++ sx).length ∧
      (ε / 4) * ((pre ++ sx).length : ℝ) ≤
        |((pre ++ sx).count true : ℝ) - (pre ++ sx).count false| := by
  have hc : ((pre ++ sx).count true : ℝ) - (pre ++ sx).count false =
      ((pre.count true : ℝ) - pre.count false) + ((sx.count true : ℝ) - sx.count false) := by
    simp only [List.count_append, Nat.cast_add]; ring
  have hpd := not_isMisesKLRandom_of_plainK_lt_disc_le pre
  have hsd := not_isMisesKLRandom_of_plainK_lt_disc_le sx
  have hlen : (((pre ++ sx).length : ℕ) : ℝ) = pre.length + sx.length := by simp
  have hprem : (pre.length : ℝ) ≤ m := by exact_mod_cast hpre
  have hsx' : (sx.length : ℝ) ≤ xl := by exact_mod_cast hsx
  have hNR : (N : ℝ) ≤ m := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ pre.length := Nat.cast_nonneg _
  have h1 : |(sx.count true : ℝ) - sx.count false| - |(pre.count true : ℝ) - pre.count false| ≤
      |((pre.count true : ℝ) - pre.count false) + ((sx.count true : ℝ) - sx.count false)| := by
    have := abs_sub_abs_le_abs_sub ((sx.count true : ℝ) - sx.count false)
      (-((pre.count true : ℝ) - pre.count false))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    exact this
  constructor
  · have : (N : ℝ) ≤ (((pre ++ sx).length : ℕ) : ℝ) := by
      rw [hlen]; nlinarith
    exact_mod_cast this
  · rw [hc, hlen]
    nlinarith

/-- Selecting can only shorten a string. -/
private lemma not_isMisesKLRandom_of_plainK_lt_selectedAux_length_le (R : Set BitString) :
    ∀ (x pre : BitString), (selectedAux R pre x).length ≤ x.length := by
  intro x
  induction x with
  | nil => intro pre; simp [selectedAux]
  | cons b rest ih =>
    intro pre
    simp only [selectedAux, List.length_append, List.length_cons]
    have h1 := ih (pre ++ [b])
    split_ifs <;> simp <;> omega

private lemma not_isMisesKLRandom_of_plainK_lt_selectedBits_length_le (R : Set BitString)
    (x : BitString) : (selectedBits R x).length ≤ x.length :=
  not_isMisesKLRandom_of_plainK_lt_selectedAux_length_le R x []

/-- Conclusion of a good stage: if the output chain at some time is the earlier output `pre`
(at most `m` bits) followed by the bits of the stage word `x` selected by `F D j`, and `x` is
longer than `4 (m + 1) / ε` with discrepancy at least `ε |x|`, then the chain is long and has
discrepancy at least `ε / 4` times its length. -/
private lemma not_isMisesKLRandom_of_plainK_lt_stage_conclusion (ε : ℚ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {M : ℕ} (F : List BitString → Fin M → BitString → Bool) (D : List BitString)
    (j : Fin M) (x pre : BitString) (m N : ℕ) (hpre : pre.length ≤ m) (hN : N ≤ m)
    (hθ : 4 * ((m : ℝ) + 1) / (ε : ℝ) < x.length)
    (hdisc : (ε : ℝ) * x.length ≤
      |((selectedBits {y | F D j y = true} x).count true : ℝ) -
        (selectedBits {y | F D j y = true} x).count false|) :
    N ≤ (pre ++ selectedBits {y | F D j y = true} x).length ∧
      ((ε : ℝ) / 4) * ((pre ++ selectedBits {y | F D j y = true} x).length : ℝ) ≤
        |((pre ++ selectedBits {y | F D j y = true} x).count true : ℝ) -
          (pre ++ selectedBits {y | F D j y = true} x).count false| := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hε1R : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have hbig : 4 * ((m : ℝ) + 1) < (ε : ℝ) * x.length := by
    have := (div_lt_iff₀ hεR).mp hθ
    linarith
  exact not_isMisesKLRandom_of_plainK_lt_account (ε : ℝ) hεR hε1R pre
    (selectedBits {y | F D j y = true} x) m x.length N hpre
    (not_isMisesKLRandom_of_plainK_lt_selectedBits_length_le _ _) hdisc hbig hN

/-- The segments `χ_B ↾ ℓ` increase for the prefix order. -/
private lemma not_isMisesKLRandom_of_plainK_lt_cp_prefix (B : Set ℕ) {ℓ ℓ' : ℕ}
    (h : ℓ ≤ ℓ') :
    not_isMisesKLRandom_of_plainK_lt_cp B ℓ <+:
      not_isMisesKLRandom_of_plainK_lt_cp B ℓ' := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_cp
  have : (List.range ℓ).map (fun n => decide (n ∈ B)) =
      ((List.range ℓ').map (fun n => decide (n ∈ B))).take ℓ := by
    rw [← List.map_take, List.take_range, min_eq_left h]
  rw [this]
  exact List.take_prefix _ _

/-- The tail of column `c` (`false` = the column `r`, `true` = the column `r + 2 ^ k` modulo
`2 ^ (k + 1)`) from the offset `m`. -/
private def not_isMisesKLRandom_of_plainK_lt_tail (w : CantorSeq) (k r : ℕ) (c : Bool)
    (m : ℕ) : CantorSeq :=
  fun i => not_isMisesKLRandom_of_plainK_lt_column w (k + 1) (r + if c then 2 ^ k else 0) (m + i)

/-- Discovery predicate of the canonical tick process: after `τ` ticks of a stage with global
tick base `g`, some prefix of the first `τ` bits of the tail of column `c` from `m`, longer than
`θ`, has been listed by `Dseq` from the first `g + τ` background bits. -/
private def not_isMisesKLRandom_of_plainK_lt_P (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (θ : ℝ) (c : Bool) (m g τ : ℕ) : Prop :=
  ∃ n : ℕ, θ < n ∧ n ≤ τ ∧
    cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r c m) n ∈
      Dseq (not_isMisesKLRandom_of_plainK_lt_cp
        (not_isMisesKLRandom_of_plainK_lt_background w k r) (g + τ))

open Classical in
/-- The least discovery tick. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_tauc (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (θ : ℝ) (c : Bool) (m g : ℕ) : ℕ :=
  if h : ∃ τ, not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g τ then Nat.find h else 0

/-- A discovery tick exists. -/
private lemma not_isMisesKLRandom_of_plainK_lt_P_exists (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (θ : ℝ) (c : Bool) (m g : ℕ) :
    ∃ τ, not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g τ := by
  obtain ⟨n, ℓ0, hn, h⟩ := hDhit c m ⌊θ⌋₊
  refine ⟨max n ℓ0, n, ?_, le_max_left _ _, ?_⟩
  · have h1 := Nat.lt_floor_add_one θ
    have h2 : (⌊θ⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
    linarith
  · exact h (g + max n ℓ0) (by omega)

private lemma not_isMisesKLRandom_of_plainK_lt_tauc_spec (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (θ : ℝ) (c : Bool) (m g : ℕ)
    (h : ∃ τ, not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g τ) :
    not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g
      (not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ c m g) := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_tauc
  rw [dite_eq_left h]
  exact Nat.find_spec h

private lemma not_isMisesKLRandom_of_plainK_lt_tauc_le (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (θ : ℝ) (c : Bool) (m g τ : ℕ)
    (hτ : not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g τ) :
    not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ c m g ≤ τ := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_tauc
  rw [dite_eq_left ⟨τ, hτ⟩]
  exact Nat.find_min' _ hτ

/-- A discovery tick is positive when the threshold is nonnegative. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tauc_pos (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (θ : ℝ) (hθ : 0 ≤ θ) (c : Bool) (m g : ℕ)
    (h : ∃ τ, not_isMisesKLRandom_of_plainK_lt_P w k r Dseq θ c m g τ) :
    0 < not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ c m g := by
  obtain ⟨n, hn, hnτ, _⟩ := not_isMisesKLRandom_of_plainK_lt_tauc_spec w k r Dseq θ c m g h
  have : (0 : ℝ) < n := lt_of_le_of_lt hθ hn
  have hn0 : 0 < n := by exact_mod_cast this
  omega

/-- The canonical stage offsets `(m^a, m^b, g)`: each stage advances column `c` by its own
discovery tick and the tick base by their sum, so every rule has the same stage boundaries. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_stage (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | s + 1 =>
    ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
        not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
          (4 * ((((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 : ℕ) : ℝ) + 1) /
            (ε : ℝ)) false (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2,
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 +
        not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
          (4 * ((((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 : ℕ) : ℝ) + 1) /
            (ε : ℝ)) true (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2,
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
        not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
          (4 * ((((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 : ℕ) : ℝ) + 1) /
            (ε : ℝ)) false (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
        not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
          (4 * ((((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 : ℕ) : ℝ) + 1) /
            (ε : ℝ)) true (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2)

/-- Right case of a stage: if the second column is discovered no later than the first one, the
list frozen at the first discovery contains a prefix of the second tail, longer than `θ` and not
longer than the second discovery tick. -/
private lemma not_isMisesKLRandom_of_plainK_lt_right_case (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString)
    (hDmono : ∀ σ σ' : List Bool, σ <+: σ' → ∀ u ∈ Dseq σ, u ∈ Dseq σ')
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (θ : ℝ) (f : Bool) (mf mq g : ℕ)
    (hle : not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ (!f) mq g ≤
      not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ f mf g) :
    ∃ x : BitString,
      x ∈ Dseq (not_isMisesKLRandom_of_plainK_lt_cp
        (not_isMisesKLRandom_of_plainK_lt_background w k r)
        (g + not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ f mf g)) ∧
      θ < x.length ∧
      x.length ≤ not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq θ (!f) mq g ∧
      x = cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f) mq) x.length := by
  obtain ⟨n, hθn, hnτ, hmem⟩ := not_isMisesKLRandom_of_plainK_lt_tauc_spec w k r Dseq θ
    (!f) mq g (not_isMisesKLRandom_of_plainK_lt_P_exists w k r Dseq hDhit θ (!f) mq g)
  refine ⟨cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f) mq) n, ?_, ?_, ?_,
      ?_⟩
  · exact hDmono _ _ (not_isMisesKLRandom_of_plainK_lt_cp_prefix _ (by omega)) _ hmem
  · simpa using hθn
  · simpa using hnτ
  · simp

/-- Threshold of stage `s`: `4 (g + 1) / ε` with `g = mₐ + m_b`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_theta (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) : ℝ :=
  4 * ((((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 : ℕ) : ℝ) + 1) / (ε : ℝ)

/-- Offset of column `f` at the start of stage `s`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_mcol (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (f : Bool) (s : ℕ) : ℕ :=
  if f then (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
  else (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1

/-- Discovery tick of column `f` in stage `s`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_tcol (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (f : Bool) (s : ℕ) : ℕ :=
  not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
    (not_isMisesKLRandom_of_plainK_lt_theta w k r Dseq ε s) f
    (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε f s)
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2

private lemma not_isMisesKLRandom_of_plainK_lt_stage_succ_g (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).2.2 =
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε false s +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε true s := rfl

private lemma not_isMisesKLRandom_of_plainK_lt_stage_succ_a (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).1 =
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε false s := rfl

private lemma not_isMisesKLRandom_of_plainK_lt_stage_succ_b (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).2.1 =
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε true s := rfl

/-- The tick base is the sum of the two offsets. -/
private lemma not_isMisesKLRandom_of_plainK_lt_stage_g_eq (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 =
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [not_isMisesKLRandom_of_plainK_lt_stage_succ_g,
      not_isMisesKLRandom_of_plainK_lt_stage_succ_a,
      not_isMisesKLRandom_of_plainK_lt_stage_succ_b, ih]
    omega

/-- Every discovery tick is positive. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tcol_pos (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (hε : 0 < ε)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (f : Bool) (s : ℕ) :
    0 < not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hθ : 0 ≤ not_isMisesKLRandom_of_plainK_lt_theta w k r Dseq ε s := by
    unfold not_isMisesKLRandom_of_plainK_lt_theta
    positivity
  exact not_isMisesKLRandom_of_plainK_lt_tauc_pos w k r Dseq _ hθ f _ _
    (not_isMisesKLRandom_of_plainK_lt_P_exists w k r Dseq hDhit _ f _ _)

/-- The tick base grows by at least two in every stage. -/
private lemma not_isMisesKLRandom_of_plainK_lt_stage_g_ge (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (hε : 0 < ε)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (s : ℕ) :
    2 * s ≤ (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 := by
  induction s with
  | zero => simp [not_isMisesKLRandom_of_plainK_lt_stage]
  | succ s ih =>
    rw [not_isMisesKLRandom_of_plainK_lt_stage_succ_g]
    have h1 := not_isMisesKLRandom_of_plainK_lt_tcol_pos w k r Dseq ε hε hDhit false s
    have h2 := not_isMisesKLRandom_of_plainK_lt_tcol_pos w k r Dseq ε hε hDhit true s
    omega

/-- The dynamic content of the scheduler, for a family of rules `R f j` (`f` = first column, `j` =
the
finite selector): in every stage `s`, after the `u`-th column answer of phase 2 (`u ≤ τ_q`), the
output
is an earlier output of length at most `g_s` followed by the bits of the first `u` bits of the
second tail
selected by `F D j`, where `D = Dseq (cp (g_s + τ_f))` is the list frozen at the end of phase 1. -/
private def not_isMisesKLRandom_of_plainK_lt_RunSpec (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (R : Bool → Fin M → KLRule) : Prop :=
  ∀ (f : Bool) (j : Fin M) (s u : ℕ),
    u ≤ not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s →
    ∃ (t : ℕ) (pre : BitString),
      pre.length ≤ (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 ∧
      (R f j).outputChain w t = pre ++ selectedBits
          {y | F (Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
            not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s))) j y = true}
        (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
          (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε (!f) s)) u)

/-- Assembly: a family of admissible rules `R f j` with the run description `RunSpec` gives the
conclusion of the scheduler. -/
private lemma not_isMisesKLRandom_of_plainK_lt_assembly
    (w : CantorSeq) (k r : ℕ) (β : ℚ)
    (Dseq : List Bool → List BitString)
    (hDmono : ∀ σ σ' : List Bool, σ <+: σ' → ∀ u ∈ Dseq σ, u ∈ Dseq σ')
    (hDkraft : ∀ ℓ : ℕ,
      ∑ x ∈ (Dseq (not_isMisesKLRandom_of_plainK_lt_cp
        (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ)).toFinset,
          (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (M : ℕ) (ε : ℚ) (F : List BitString → Fin M → BitString → Bool)
    (hM : 0 < M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlocal : ∀ D : List BitString,
      (∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length)) ≤ 1 →
      ∀ x ∈ D, ∃ j : Fin M,
        (ε : ℝ) * x.length ≤
          |((selectedBits {y | F D j y = true} x).count true : ℝ) -
            (selectedBits {y | F D j y = true} x).count false|)
    (R : Bool → Fin M → KLRule) (hR : ∀ f j, (R f j).IsAdmissible)
    (hrun : not_isMisesKLRandom_of_plainK_lt_RunSpec w k r Dseq ε F R) :
    ∃ R' : Fin (2 * M) → KLRule,
      (∀ j, (R' j).IsAdmissible) ∧ ∀ N : ℕ, ∃ j t,
        N ≤ ((R' j).outputChain w t).length ∧
        ((ε : ℝ) / 4) * ((R' j).outputChain w t).length ≤
          |(((R' j).outputChain w t).count true : ℝ) -
            ((R' j).outputChain w t).count false| := by
  classical
  let Rp : Fin (2 * M) → KLRule := fun i => R (decide (M ≤ (i : ℕ))) ⟨(i : ℕ) % M, Nat.mod_lt _ hM⟩
  have hidx : ∀ (f : Bool) (j : Fin M), ∃ i : Fin (2 * M), Rp i = R f j := by
    intro f j
    have hj : (j : ℕ) < M := j.2
    cases f
    · refine ⟨⟨(j : ℕ), by omega⟩, ?_⟩
      change R (decide (M ≤ (j : ℕ))) ⟨(j : ℕ) % M, Nat.mod_lt _ hM⟩ = R false j
      congr 1
      · simp [Nat.not_le.mpr hj]
      · exact Fin.ext (Nat.mod_eq_of_lt hj)
    · refine ⟨⟨(j : ℕ) + M, by omega⟩, ?_⟩
      change R (decide (M ≤ (j : ℕ) + M)) ⟨((j : ℕ) + M) % M, Nat.mod_lt _ hM⟩ = R true j
      congr 1
      · simp
      · exact Fin.ext (by simp [Nat.add_mod_right, Nat.mod_eq_of_lt hj])
  refine ⟨Rp, fun i => hR _ _, ?_⟩
  intro N
  -- the stage `N` has tick base `g ≥ N`
  have hg : N ≤ (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).2.2 := by
    have := not_isMisesKLRandom_of_plainK_lt_stage_g_ge w k r Dseq ε hε hDhit N
    omega
  -- the claim for a first column `f` that is discovered no earlier than the second one
  have claim : ∀ f : Bool,
      not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) N ≤
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f N →
      ∃ (j : Fin M) (t : ℕ),
        N ≤ ((R f j).outputChain w t).length ∧
        ((ε : ℝ) / 4) * ((R f j).outputChain w t).length ≤
          |(((R f j).outputChain w t).count true : ℝ) -
            ((R f j).outputChain w t).count false| := by
    intro f hle
    obtain ⟨x, hxD, hθx, hxτ, hxeq⟩ :=
      not_isMisesKLRandom_of_plainK_lt_right_case w k r Dseq hDmono hDhit
        (not_isMisesKLRandom_of_plainK_lt_theta w k r Dseq ε N) f
        (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε f N)
        (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε (!f) N)
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).2.2 hle
    obtain ⟨j, hj⟩ := hlocal _ (hDkraft _) x hxD
    obtain ⟨t, pre, hpre, hchain⟩ := hrun f j N x.length hxτ
    refine ⟨j, t, ?_⟩
    rw [hchain, ← hxeq]
    have hgeq := not_isMisesKLRandom_of_plainK_lt_stage_g_eq w k r Dseq ε N
    have hθ' : 4 * (((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).2.2 : ℝ) + 1) /
        (ε : ℝ) < x.length := by
      have h1 : (((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).1 +
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).2.1 : ℕ) : ℝ) =
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε N).2.2 : ℝ) := by
        rw [hgeq]
      unfold not_isMisesKLRandom_of_plainK_lt_theta at hθx
      rw [h1] at hθx
      exact hθx
    exact not_isMisesKLRandom_of_plainK_lt_stage_conclusion ε hε hε1 F _ j x pre _ N
      hpre hg hθ' hj
  rcases le_total (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε true N)
      (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε false N) with hle | hle
  · obtain ⟨j, t, h⟩ := claim false hle
    obtain ⟨i, hi⟩ := hidx false j
    exact ⟨i, t, by rw [hi]; exact h⟩
  · obtain ⟨j, t, h⟩ := claim true hle
    obtain ⟨i, hi⟩ := hidx true j
    exact ⟨i, t, by rw [hi]; exact h⟩

/-- Automaton state: `(sub, γ, cp, ca, cb, g, ph, bits, τf)`: `sub = true` iff the next query is a
column query; `γ` completed ticks; `cp` background knowledge; `ca, cb` bits read in each column;
`g` tick base of the stage; `ph` whether phase 2 has begun; `bits` bits read in the current
phase; `τf` length of phase 1. -/
private abbrev not_isMisesKLRandom_of_plainK_lt_St : Type :=
  Bool × ℕ × List Bool × ℕ × ℕ × ℕ × Bool × List Bool × ℕ

/-- The discovery test with the listed words `Dl` given: some `n ≤ |bits|` with
`4 (g + 1) b < n a` and `bits.take n ∈ Dl` (`ε = a / b`). -/
private def not_isMisesKLRandom_of_plainK_lt_hitCore (a b : ℕ)
    (p : ℕ × List Bool × List BitString) : Bool :=
  decide ((List.range (p.2.1.length + 1)).findIdx (fun n =>
      decide (4 * (p.1 + 1) * b < n * a) &&
        decide (p.2.2.findIdx (fun v => decide (v = p.2.1.take n)) < p.2.2.length)) <
    p.2.1.length + 1)

/-- Initial state. -/
private def not_isMisesKLRandom_of_plainK_lt_init (k r : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_St :=
  cond (decide (0 % 2 ^ k = r)) (true, 0, [false], 0, 0, 0, false, [], 0)
    (false, 0, [], 0, 0, 0, false, [], 0)

/-- The query position. -/
private def not_isMisesKLRandom_of_plainK_lt_query (k r : ℕ) (f : Bool)
    (s : not_isMisesKLRandom_of_plainK_lt_St) : ℕ :=
  cond s.1
    (cond (cond s.2.2.2.2.2.2.1 (!f) f)
      (2 ^ (k + 1) * s.2.2.2.2.1 + (r + 2 ^ k))
      (2 ^ (k + 1) * s.2.2.2.1 + r))
    s.2.1

/-- Whether the revealed bit is selected. -/
private def not_isMisesKLRandom_of_plainK_lt_select (Dseq : List Bool → List BitString)
    {M : ℕ} (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (s : not_isMisesKLRandom_of_plainK_lt_St) : Bool :=
  s.1 && s.2.2.2.2.2.2.1 &&
    F (Dseq (s.2.2.1.take (s.2.2.2.2.2.1 + s.2.2.2.2.2.2.2.2))) j s.2.2.2.2.2.2.2.1

/-- Transition after a column answer, given the outcome `hit` of the discovery test. -/
private def not_isMisesKLRandom_of_plainK_lt_colCore (k r : ℕ) (f : Bool)
    (x : not_isMisesKLRandom_of_plainK_lt_St × Bool × Bool) :
    not_isMisesKLRandom_of_plainK_lt_St :=
  (decide ((x.1.2.1 + 1) % 2 ^ k = r),
    x.1.2.1 + 1,
    cond (decide ((x.1.2.1 + 1) % 2 ^ k = r)) (x.1.2.2.1 ++ [false]) x.1.2.2.1,
    cond (cond x.1.2.2.2.2.2.2.1 (!f) f) x.1.2.2.2.1 (x.1.2.2.2.1 + 1),
    cond (cond x.1.2.2.2.2.2.2.1 (!f) f) (x.1.2.2.2.2.1 + 1) x.1.2.2.2.2.1,
    cond (x.1.2.2.2.2.2.2.1 && x.2.2) (x.1.2.1 + 1) x.1.2.2.2.2.2.1,
    cond x.1.2.2.2.2.2.2.1 (!x.2.2) x.2.2,
    cond x.2.2 [] (x.1.2.2.2.2.2.2.2.1 ++ [x.2.1]),
    cond x.1.2.2.2.2.2.2.1 (cond x.2.2 0 x.1.2.2.2.2.2.2.2.2)
      (cond x.2.2 (x.1.2.2.2.2.2.2.2.1 ++ [x.2.1]).length 0))

/-- Transition after a background answer. -/
private def not_isMisesKLRandom_of_plainK_lt_bgCore
    (x : not_isMisesKLRandom_of_plainK_lt_St × Bool) :
    not_isMisesKLRandom_of_plainK_lt_St :=
  (true, x.1.2.1, x.1.2.2.1 ++ [x.2], x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2.1,
    x.1.2.2.2.2.2.2.1, x.1.2.2.2.2.2.2.2.1, x.1.2.2.2.2.2.2.2.2)

/-- Transition. -/
private def not_isMisesKLRandom_of_plainK_lt_step (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool)
    (s : not_isMisesKLRandom_of_plainK_lt_St) (bit : Bool) :
    not_isMisesKLRandom_of_plainK_lt_St :=
  cond s.1
    (not_isMisesKLRandom_of_plainK_lt_colCore k r f
      (s, bit, not_isMisesKLRandom_of_plainK_lt_hitCore a b
        (s.2.2.2.2.2.1, s.2.2.2.2.2.2.2.1 ++ [bit],
          Dseq (s.2.2.1.take (s.2.2.2.2.2.1 + (s.2.2.2.2.2.2.2.1 ++ [bit]).length)))))
    (not_isMisesKLRandom_of_plainK_lt_bgCore (s, bit))

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_hitCore (a b : ℕ) :
    Primrec (not_isMisesKLRandom_of_plainK_lt_hitCore a b) := by
  unfold not_isMisesKLRandom_of_plainK_lt_hitCore
  have hbits : Primrec (fun p : ℕ × List Bool × List BitString => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hDl : Primrec (fun p : ℕ × List Bool × List BitString => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlen : Primrec (fun p : ℕ × List Bool × List BitString => p.2.1.length + 1) :=
    Primrec.nat_add.comp (Primrec.list_length.comp hbits) (Primrec.const 1)
  have hrange : Primrec (fun p : ℕ × List Bool × List BitString => List.range (p.2.1.length + 1)) :=
    Primrec.list_range.comp hlen
  have hinner : Primrec₂ (fun (q : (ℕ × List Bool × List BitString) × ℕ) (v : BitString) =>
      decide (v = q.1.2.1.take q.2)) := by
    have h1 : Primrec (fun z : ((ℕ × List Bool × List BitString) × ℕ) × BitString => z.2) :=
      Primrec.snd
    have h2 : Primrec (fun z : ((ℕ × List Bool × List BitString) × ℕ) × BitString =>
        z.1.1.2.1.take z.1.2) :=
      Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
          (hbits.comp (Primrec.fst.comp Primrec.fst))
    exact (PrimrecRel.decide Primrec.eq).comp h1 h2
  have hfind : Primrec₂ (fun (p : ℕ × List Bool × List BitString) (n : ℕ) =>
      decide (4 * (p.1 + 1) * b < n * a) &&
        decide (p.2.2.findIdx (fun v => decide (v = p.2.1.take n)) < p.2.2.length)) := by
    have hq1 : Primrec (fun z : (ℕ × List Bool × List BitString) × ℕ => z.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hn : Primrec (fun z : (ℕ × List Bool × List BitString) × ℕ => z.2) := Primrec.snd
    have hA : Primrec (fun z : (ℕ × List Bool × List BitString) × ℕ =>
        decide (4 * (z.1.1 + 1) * b < z.2 * a)) :=
      (PrimrecRel.decide Primrec.nat_lt).comp
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec.nat_add.comp hq1 (Primrec.const 1))) (Primrec.const b))
        (Primrec.nat_mul.comp hn (Primrec.const a))
    have hB : Primrec (fun z : (ℕ × List Bool × List BitString) × ℕ =>
        decide (z.1.2.2.findIdx (fun v => decide (v = z.1.2.1.take z.2)) < z.1.2.2.length)) :=
      (PrimrecRel.decide Primrec.nat_lt).comp
        (Primrec.list_findIdx (f := fun z : (ℕ × List Bool × List BitString) × ℕ => z.1.2.2)
          (p := fun z v => decide (v = z.1.2.1.take z.2)) (hDl.comp Primrec.fst) hinner)
        (Primrec.list_length.comp (hDl.comp Primrec.fst))
    exact Primrec.and.comp hA hB
  exact (PrimrecRel.decide Primrec.nat_lt).comp (Primrec.list_findIdx hrange hfind) hlen

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_colCore (k r : ℕ) (f : Bool) :
    Primrec (not_isMisesKLRandom_of_plainK_lt_colCore k r f) := by
  unfold not_isMisesKLRandom_of_plainK_lt_colCore
  have s1 : Primrec (fun x : not_isMisesKLRandom_of_plainK_lt_St × Bool × Bool => x.1) :=
    Primrec.fst
  have t1 := Primrec.snd.comp s1
  have t2 := Primrec.snd.comp t1
  have t3 := Primrec.snd.comp t2
  have t4 := Primrec.snd.comp t3
  have t5 := Primrec.snd.comp t4
  have t6 := Primrec.snd.comp t5
  have t7 := Primrec.snd.comp t6
  have hγ := Primrec.fst.comp t1
  have hcp := Primrec.fst.comp t2
  have hca := Primrec.fst.comp t3
  have hcb := Primrec.fst.comp t4
  have hg := Primrec.fst.comp t5
  have hph := Primrec.fst.comp t6
  have hbits := Primrec.fst.comp t7
  have hτ := Primrec.snd.comp t7
  have hbit : Primrec (fun x : not_isMisesKLRandom_of_plainK_lt_St × Bool × Bool => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hhit : Primrec (fun x : not_isMisesKLRandom_of_plainK_lt_St × Bool × Bool => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hγ1 := Primrec.nat_add.comp hγ (Primrec.const 1)
  have hskip := (PrimrecRel.decide Primrec.eq).comp
    (Primrec.nat_mod.comp hγ1 (Primrec.const (2 ^ k))) (Primrec.const r)
  have hc := Primrec.cond hph (Primrec.const (!f)) (Primrec.const f)
  have hbits1 := Primrec.list_concat.comp hbits hbit
  exact Primrec.pair hskip (Primrec.pair hγ1
    (Primrec.pair (Primrec.cond hskip (Primrec.list_concat.comp hcp (Primrec.const false)) hcp)
    (Primrec.pair (Primrec.cond hc hca (Primrec.nat_add.comp hca (Primrec.const 1)))
    (Primrec.pair (Primrec.cond hc (Primrec.nat_add.comp hcb (Primrec.const 1)) hcb)
    (Primrec.pair (Primrec.cond (Primrec.and.comp hph hhit) hγ1 hg)
    (Primrec.pair (Primrec.cond hph (Primrec.not.comp hhit) hhit)
    (Primrec.pair (Primrec.cond hhit (Primrec.const ([] : List Bool)) hbits1)
      (Primrec.cond hph (Primrec.cond hhit (Primrec.const 0) hτ)
        (Primrec.cond hhit (Primrec.list_length.comp hbits1) (Primrec.const 0))))))))))

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_bgCore :
    Primrec not_isMisesKLRandom_of_plainK_lt_bgCore := by
  unfold not_isMisesKLRandom_of_plainK_lt_bgCore
  have s1 : Primrec (fun x : not_isMisesKLRandom_of_plainK_lt_St × Bool => x.1) :=
    Primrec.fst
  have t1 := Primrec.snd.comp s1
  have t2 := Primrec.snd.comp t1
  have t3 := Primrec.snd.comp t2
  have t4 := Primrec.snd.comp t3
  have t5 := Primrec.snd.comp t4
  have t6 := Primrec.snd.comp t5
  have t7 := Primrec.snd.comp t6
  have hbit : Primrec (fun x : not_isMisesKLRandom_of_plainK_lt_St × Bool => x.2) :=
    Primrec.snd
  exact Primrec.pair (Primrec.const true) (Primrec.pair (Primrec.fst.comp t1)
    (Primrec.pair (Primrec.list_concat.comp (Primrec.fst.comp t2) hbit)
    (Primrec.pair (Primrec.fst.comp t3) (Primrec.pair (Primrec.fst.comp t4)
    (Primrec.pair (Primrec.fst.comp t5) (Primrec.pair (Primrec.fst.comp t6)
    (Primrec.pair (Primrec.fst.comp t7) (Primrec.snd.comp t7))))))))

private lemma not_isMisesKLRandom_of_plainK_lt_primrec_query (k r : ℕ) (f : Bool) :
    Primrec (not_isMisesKLRandom_of_plainK_lt_query k r f) := by
  unfold not_isMisesKLRandom_of_plainK_lt_query
  have u0 : Primrec (fun s : not_isMisesKLRandom_of_plainK_lt_St => s.2) := Primrec.snd
  have u1 := Primrec.snd.comp u0
  have u2 := Primrec.snd.comp u1
  have u3 := Primrec.snd.comp u2
  have u4 := Primrec.snd.comp u3
  have u5 := Primrec.snd.comp u4
  have hc := Primrec.cond (Primrec.fst.comp u5) (Primrec.const (!f)) (Primrec.const f)
  exact Primrec.cond Primrec.fst
    (Primrec.cond hc
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const (2 ^ (k + 1)))
        (Primrec.fst.comp u3)) (Primrec.const (r + 2 ^ k)))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const (2 ^ (k + 1)))
        (Primrec.fst.comp u2)) (Primrec.const r)))
    (Primrec.fst.comp u0)

private lemma not_isMisesKLRandom_of_plainK_lt_computable_step (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (hDc : Computable Dseq) (f : Bool) :
    Computable₂ (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) := by
  have u0 : Primrec (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool => p.1) :=
    Primrec.fst
  have v1 := Primrec.snd.comp u0
  have v2 := Primrec.snd.comp v1
  have v3 := Primrec.snd.comp v2
  have v4 := Primrec.snd.comp v3
  have v5 := Primrec.snd.comp v4
  have v6 := Primrec.snd.comp v5
  have v7 := Primrec.snd.comp v6
  have hcp := Primrec.fst.comp v2
  have hg := Primrec.fst.comp v5
  have hbits := Primrec.fst.comp v7
  have hbit : Primrec (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool => p.2) :=
    Primrec.snd
  have hbits1 := Primrec.list_concat.comp hbits hbit
  have hcpTake : Primrec (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool =>
      p.1.2.2.1.take (p.1.2.2.2.2.2.1 + (p.1.2.2.2.2.2.2.2.1 ++ [p.2]).length)) :=
    Primrec.list_take.comp (Primrec.nat_add.comp hg (Primrec.list_length.comp hbits1)) hcp
  have hDl := hDc.comp hcpTake.to_comp
  have hhit : Computable (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool =>
      not_isMisesKLRandom_of_plainK_lt_hitCore a b
        (p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1 ++ [p.2],
          Dseq (p.1.2.2.1.take (p.1.2.2.2.2.2.1 + (p.1.2.2.2.2.2.2.2.1 ++ [p.2]).length)))) :=
    (not_isMisesKLRandom_of_plainK_lt_primrec_hitCore a b).to_comp.comp
      (Computable.pair hg.to_comp (Computable.pair hbits1.to_comp hDl))
  have hcol : Computable (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool =>
      not_isMisesKLRandom_of_plainK_lt_colCore k r f
        (p.1, p.2, not_isMisesKLRandom_of_plainK_lt_hitCore a b
          (p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1 ++ [p.2],
            Dseq (p.1.2.2.1.take (p.1.2.2.2.2.2.1 + (p.1.2.2.2.2.2.2.2.1 ++ [p.2]).length))))) :=
    (not_isMisesKLRandom_of_plainK_lt_primrec_colCore k r f).to_comp.comp
      (Computable.pair Computable.fst (Computable.pair Computable.snd hhit))
  have hbg : Computable (fun p : not_isMisesKLRandom_of_plainK_lt_St × Bool =>
      not_isMisesKLRandom_of_plainK_lt_bgCore (p.1, p.2)) :=
    not_isMisesKLRandom_of_plainK_lt_primrec_bgCore.to_comp.comp Computable.id
  exact Computable.cond (Primrec.fst.comp Primrec.fst).to_comp hcol hbg

private lemma not_isMisesKLRandom_of_plainK_lt_computable_select
    (Dseq : List Bool → List BitString) (hDc : Computable Dseq) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool)
    (hF : Computable (fun p : (List BitString × Fin M) × BitString => F p.1.1 p.1.2 p.2))
    (j : Fin M) :
    Computable (not_isMisesKLRandom_of_plainK_lt_select Dseq F j) := by
  unfold not_isMisesKLRandom_of_plainK_lt_select
  have u0 : Primrec (fun s : not_isMisesKLRandom_of_plainK_lt_St => s.2) := Primrec.snd
  have u1 := Primrec.snd.comp u0
  have u2 := Primrec.snd.comp u1
  have u3 := Primrec.snd.comp u2
  have u4 := Primrec.snd.comp u3
  have u5 := Primrec.snd.comp u4
  have u6 := Primrec.snd.comp u5
  have u7 := Primrec.snd.comp u6
  have hcp := Primrec.fst.comp u1
  have hg := Primrec.fst.comp u4
  have hph := Primrec.fst.comp u5
  have hbits := Primrec.fst.comp u6
  have hτ := Primrec.snd.comp u6
  have hDl := hDc.comp (Primrec.list_take.comp (Primrec.nat_add.comp hg hτ) hcp).to_comp
  have hFj : Computable (fun s : not_isMisesKLRandom_of_plainK_lt_St =>
      F (Dseq (s.2.2.1.take (s.2.2.2.2.2.1 + s.2.2.2.2.2.2.2.2))) j s.2.2.2.2.2.2.2.1) :=
    hF.comp (Computable.pair (Computable.pair hDl (Computable.const j)) hbits.to_comp)
  have hsub : Primrec (fun s : not_isMisesKLRandom_of_plainK_lt_St => s.1) := Primrec.fst
  have h := Computable.cond (Primrec.and.comp hsub hph).to_comp hFj (Computable.const false)
  refine h.of_eq (fun s => ?_)
  cases h1 : (s.1 && s.2.2.2.2.2.2.1) <;> simp

/-- One step of the automaton: invariant of `sub`, monotonicity of the fronts, and the advance of
the
front that was just queried. -/
private lemma not_isMisesKLRandom_of_plainK_lt_step_facts (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool)
    (s : not_isMisesKLRandom_of_plainK_lt_St) (bit : Bool)
    (hI : s.1 = false → s.2.1 % 2 ^ k ≠ r) :
    ((not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).1 = false →
      (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.1 % 2 ^ k ≠ r) ∧
    s.2.1 + (if s.1 then 1 else 0) ≤
      (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.1 +
        (if (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).1 then 1 else 0) ∧
    s.2.2.2.1 ≤ (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.2.2.1 ∧
    s.2.2.2.2.1 ≤ (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.2.2.2.1 ∧
    (s.1 = false →
      (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.1 +
        (if (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).1 then 1 else 0) =
        s.2.1 + 1) ∧
    (s.1 = true → (cond s.2.2.2.2.2.2.1 (!f) f) = false →
      (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.2.2.1 =
        s.2.2.2.1 + 1) ∧
    (s.1 = true → (cond s.2.2.2.2.2.2.1 (!f) f) = true →
      (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit).2.2.2.2.1 =
        s.2.2.2.2.1 + 1) := by
  obtain ⟨sub, γ, cp, ca, cb, g, ph, bits, τf⟩ := s
  cases sub
  · simp [not_isMisesKLRandom_of_plainK_lt_step,
      not_isMisesKLRandom_of_plainK_lt_bgCore]
  · unfold not_isMisesKLRandom_of_plainK_lt_step
    simp only [Bool.cond_true]
    unfold not_isMisesKLRandom_of_plainK_lt_colCore
    generalize not_isMisesKLRandom_of_plainK_lt_hitCore a b
      (g, bits ++ [bit], Dseq (cp.take (g + (bits ++ [bit]).length))) = hit
    cases ph <;> cases hit <;> cases f <;> simp

private lemma not_isMisesKLRandom_of_plainK_lt_colpos_a (k r i : ℕ) (hr : r < 2 ^ k) :
    (2 ^ (k + 1) * i + r) % 2 ^ k = r := by
  have h : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  rw [h, mul_assoc, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hr

private lemma not_isMisesKLRandom_of_plainK_lt_colpos_b (k r i : ℕ) (hr : r < 2 ^ k) :
    (2 ^ (k + 1) * i + (r + 2 ^ k)) % 2 ^ k = r := by
  have h : 2 ^ (k + 1) * i + (r + 2 ^ k) = r + 2 ^ k * (2 * i + 1) := by
    rw [pow_succ]; ring
  rw [h, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hr

private lemma not_isMisesKLRandom_of_plainK_lt_colpos_ne (k r i j : ℕ) (hr : r < 2 ^ k) :
    2 ^ (k + 1) * i + r ≠ 2 ^ (k + 1) * j + (r + 2 ^ k) := by
  intro h
  have h1 : (2 ^ (k + 1) * i + r) % 2 ^ (k + 1) = r := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h2 : (2 ^ (k + 1) * j + (r + 2 ^ k)) % 2 ^ (k + 1) = r + 2 ^ k := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by rw [pow_succ]; omega)
  rw [h] at h1
  omega

/-- Invariant and monotonicity along a run of the automaton. -/
private lemma not_isMisesKLRandom_of_plainK_lt_foldl_facts (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) :
    ∀ (z : List Bool) (s : not_isMisesKLRandom_of_plainK_lt_St),
      (s.1 = false → s.2.1 % 2 ^ k ≠ r) →
      ((z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).1 = false →
        (z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).2.1 % 2 ^ k ≠ r) ∧
      s.2.1 + (if s.1 then 1 else 0) ≤
        (z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).2.1 +
          (if (z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).1
            then 1 else 0) ∧
      s.2.2.2.1 ≤
        (z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).2.2.2.1 ∧
      s.2.2.2.2.1 ≤
        (z.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f) s).2.2.2.2.1 := by
  intro z
  induction z with
  | nil => intro s hI; exact ⟨hI, le_rfl, le_rfl, le_rfl⟩
  | cons bit z ih =>
    intro s hI
    obtain ⟨h1, h2, h3, h4, -⟩ :=
      not_isMisesKLRandom_of_plainK_lt_step_facts k r a b Dseq f s bit hI
    obtain ⟨i1, i2, i3, i4⟩ := ih _ h1
    exact ⟨i1, le_trans h2 i2, le_trans h3 i3, le_trans h4 i4⟩

/-- The queries of the automaton never repeat along a chain of histories. -/
private lemma not_isMisesKLRandom_of_plainK_lt_hnr (k r a b : ℕ) (hr : r < 2 ^ k)
    (Dseq : List Bool → List BitString) (f : Bool) :
    ∀ x y : List Bool, x <+: y → x ≠ y →
      not_isMisesKLRandom_of_plainK_lt_query k r f
          (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
            (not_isMisesKLRandom_of_plainK_lt_init k r)) ≠
        not_isMisesKLRandom_of_plainK_lt_query k r f
          (y.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
            (not_isMisesKLRandom_of_plainK_lt_init k r)) := by
  intro x y hxy hne
  obtain ⟨z, rfl⟩ := hxy
  have hz : z ≠ [] := by
    rintro rfl
    exact hne (by simp)
  obtain ⟨bit, z', rfl⟩ := List.exists_cons_of_ne_nil hz
  rw [List.foldl_append, List.foldl_cons]
  have hIinit : (not_isMisesKLRandom_of_plainK_lt_init k r).1 = false →
      (not_isMisesKLRandom_of_plainK_lt_init k r).2.1 % 2 ^ k ≠ r := by
    unfold not_isMisesKLRandom_of_plainK_lt_init
    by_cases h : r = 0
    · subst h; simp
    · have h0 : ¬ ((0 : ℕ) = r) := fun e => h e.symm
      simp [h0]
  obtain ⟨hIs, -⟩ := not_isMisesKLRandom_of_plainK_lt_foldl_facts k r a b Dseq f x _ hIinit
  generalize x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
    (not_isMisesKLRandom_of_plainK_lt_init k r) = s at hIs ⊢
  obtain ⟨h1, h2, h3, h4, hadv, hca, hcb⟩ :=
    not_isMisesKLRandom_of_plainK_lt_step_facts k r a b Dseq f s bit hIs
  obtain ⟨i1, i2, i3, i4⟩ :=
    not_isMisesKLRandom_of_plainK_lt_foldl_facts k r a b Dseq f z' _ h1
  generalize z'.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
    (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f s bit) = s2 at i1 i2 i3 i4 ⊢
  unfold not_isMisesKLRandom_of_plainK_lt_query
  cases hs1 : s.1 <;> cases hs2 : s2.1
  · -- both background queries
    simp only [Bool.cond_false]
    have h5 := hadv hs1
    rw [hs2] at i2
    simp only [Bool.false_eq_true, ite_false] at i2
    omega
  · -- background query, then a column query
    simp only [Bool.cond_false, Bool.cond_true]
    intro h
    have hne' := hIs hs1
    cases hc : (cond s2.2.2.2.2.2.2.1 (!f) f) <;>
      simp only [hc, Bool.cond_false, Bool.cond_true] at h
    · exact hne' (h ▸ not_isMisesKLRandom_of_plainK_lt_colpos_a k r _ hr)
    · exact hne' (h ▸ not_isMisesKLRandom_of_plainK_lt_colpos_b k r _ hr)
  · -- column query, then a background query
    simp only [Bool.cond_false, Bool.cond_true]
    intro h
    have hne' := i1 hs2
    cases hc : (cond s.2.2.2.2.2.2.1 (!f) f) <;>
      simp only [hc, Bool.cond_false, Bool.cond_true] at h
    · exact hne' (h ▸ not_isMisesKLRandom_of_plainK_lt_colpos_a k r _ hr)
    · exact hne' (h ▸ not_isMisesKLRandom_of_plainK_lt_colpos_b k r _ hr)
  · -- two column queries
    simp only [Bool.cond_true]
    cases hc1 : (cond s.2.2.2.2.2.2.1 (!f) f) <;>
      cases hc2 : (cond s2.2.2.2.2.2.2.1 (!f) f) <;> simp only [Bool.cond_false, Bool.cond_true]
    · intro h
      have e := hca hs1 hc1
      have h' : 2 ^ (k + 1) * s.2.2.2.1 = 2 ^ (k + 1) * s2.2.2.2.1 := Nat.add_right_cancel h
      have := Nat.eq_of_mul_eq_mul_left (by positivity) h'
      omega
    · intro h
      exact not_isMisesKLRandom_of_plainK_lt_colpos_ne k r _ _ hr h
    · intro h
      exact not_isMisesKLRandom_of_plainK_lt_colpos_ne k r _ _ hr h.symm
    · intro h
      have e := hcb hs1 hc1
      have h' : 2 ^ (k + 1) * s.2.2.2.2.1 = 2 ^ (k + 1) * s2.2.2.2.2.1 :=
        Nat.add_right_cancel h
      have := Nat.eq_of_mul_eq_mul_left (by positivity) h'
      omega

/-! ### Dynamics of the automaton on the real sequence -/

/-- `χ_B ↾ ℓ` for the background of `w`. -/
private noncomputable abbrev not_isMisesKLRandom_of_plainK_lt_cpw (w : CantorSeq) (k r ℓ : ℕ)
    :
    List Bool :=
  not_isMisesKLRandom_of_plainK_lt_cp (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ

/-- The discovery test of the transition, as a function of the stored lists. -/
private def not_isMisesKLRandom_of_plainK_lt_hit (a b : ℕ)
    (Dseq : List Bool → List BitString) (g : ℕ) (cp bits : List Bool) : Bool :=
  not_isMisesKLRandom_of_plainK_lt_hitCore a b (g, bits, Dseq (cp.take (g + bits.length)))

/-- Which column is read: the first column `f` in phase 1, the other one in phase 2. -/
private def not_isMisesKLRandom_of_plainK_lt_colof (f ph : Bool) : Bool :=
  if ph then !f else f

/-- The bit of the column `c` that is read next. -/
private def not_isMisesKLRandom_of_plainK_lt_colbit (w : CantorSeq) (k r : ℕ) (c : Bool)
    (ca cb : ℕ) : Bool :=
  w (if c then 2 ^ (k + 1) * cb + (r + 2 ^ k) else 2 ^ (k + 1) * ca + r)

/-- A state at a tick boundary. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_TB (w : CantorSeq)
    (k r γ ca cb g : ℕ)
    (ph : Bool) (bits : List Bool) (τf : ℕ) : not_isMisesKLRandom_of_plainK_lt_St :=
  (decide (γ % 2 ^ k = r), γ,
    not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + if γ % 2 ^ k = r then 1 else 0),
    ca, cb, g, ph, bits, τf)

/-- The states of the run on `w`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_run (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) : ℕ → not_isMisesKLRandom_of_plainK_lt_St
  | 0 => not_isMisesKLRandom_of_plainK_lt_init k r
  | t + 1 =>
    not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f
      (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t)
      (w (not_isMisesKLRandom_of_plainK_lt_query k r f
        (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t)))

/-- The selected output of the run on `w`. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_outS (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) {M : ℕ} (F : List BitString → Fin M → BitString → Bool)
    (j : Fin M) (f : Bool) : ℕ → BitString
  | 0 => []
  | t + 1 =>
    not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t ++
      (if not_isMisesKLRandom_of_plainK_lt_select Dseq F j
          (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t) = true then
        [w (not_isMisesKLRandom_of_plainK_lt_query k r f
          (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t))]
      else [])

private lemma not_isMisesKLRandom_of_plainK_lt_cpw_succ_ne (w : CantorSeq) (k r γ : ℕ)
    (h : γ % 2 ^ k ≠ r) :
    not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1) =
      not_isMisesKLRandom_of_plainK_lt_cpw w k r γ ++ [w γ] := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_cpw not_isMisesKLRandom_of_plainK_lt_cp
  rw [List.range_succ, List.map_append]
  congr 1
  have hmem : γ ∈ not_isMisesKLRandom_of_plainK_lt_background w k r ↔ w γ = true := by
    simp [not_isMisesKLRandom_of_plainK_lt_background, h]
  by_cases hw : w γ = true
  · simp [hmem.mpr hw, hw]
  · have : γ ∉ not_isMisesKLRandom_of_plainK_lt_background w k r := fun hh => hw (hmem.mp hh)
    have hw' : w γ = false := by simpa using hw
    simp [this, hw']

private lemma not_isMisesKLRandom_of_plainK_lt_cpw_succ_eq (w : CantorSeq) (k r γ : ℕ)
    (h : γ % 2 ^ k = r) :
    not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1) =
      not_isMisesKLRandom_of_plainK_lt_cpw w k r γ ++ [false] := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_cpw not_isMisesKLRandom_of_plainK_lt_cp
  rw [List.range_succ, List.map_append]
  congr 1
  have : γ ∉ not_isMisesKLRandom_of_plainK_lt_background w k r := by
    intro hh
    exact hh.1 h
  simp [this]

/-- `cp.take n` is `cp` at `min n ℓ`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_cpw_take (w : CantorSeq) (k r ℓ n : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_cpw w k r ℓ).take n =
      not_isMisesKLRandom_of_plainK_lt_cpw w k r (min n ℓ) := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_cpw not_isMisesKLRandom_of_plainK_lt_cp
  rw [← List.map_take, List.take_range]

private lemma not_isMisesKLRandom_of_plainK_lt_cpw_length (w : CantorSeq) (k r ℓ : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_cpw w k r ℓ).length = ℓ := by
  classical
  unfold not_isMisesKLRandom_of_plainK_lt_cpw not_isMisesKLRandom_of_plainK_lt_cp
  simp

/-- Background query: from a state before the background query of tick `γ`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_bg_step (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) (t γ ca cb g : ℕ) (ph : Bool)
    (bits : List Bool) (τf : ℕ) (hne : γ % 2 ^ k ≠ r)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      (false, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r γ, ca, cb, g, ph, bits, τf)) :
    not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f (t + 1) =
      (true, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1), ca, cb, g, ph, bits,
        τf) := by
  rw [not_isMisesKLRandom_of_plainK_lt_run, h]
  simp only [not_isMisesKLRandom_of_plainK_lt_step,
      not_isMisesKLRandom_of_plainK_lt_query,
    not_isMisesKLRandom_of_plainK_lt_bgCore, Bool.cond_false]
  rw [not_isMisesKLRandom_of_plainK_lt_cpw_succ_ne w k r γ hne]

/-- Column query: from a state before the column query of tick `γ`. -/
private lemma not_isMisesKLRandom_of_plainK_lt_col_step (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) (t γ ca cb g : ℕ) (ph : Bool)
    (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      (true, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1), ca, cb, g, ph, bits,
        τf)) :
    not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f (t + 1) =
      not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1)
        (if not_isMisesKLRandom_of_plainK_lt_colof f ph then ca else ca + 1)
        (if not_isMisesKLRandom_of_plainK_lt_colof f ph then cb + 1 else cb)
        (if ph && not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
            (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
            (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
              (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]) then γ + 1 else g)
        (xor ph (not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
            (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
            (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
              (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb])))
        (if not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
            (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
            (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
              (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]) then []
          else bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
              (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb])
        (if ph then
            (if not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
              (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
              (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
                (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]) then 0 else τf)
          else
            (if not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
              (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
              (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
                (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]) then
              (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r
                (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]).length else 0)) := by
  rw [not_isMisesKLRandom_of_plainK_lt_run, h]
  simp only [not_isMisesKLRandom_of_plainK_lt_step,
      not_isMisesKLRandom_of_plainK_lt_query,
    not_isMisesKLRandom_of_plainK_lt_colCore, Bool.cond_true,
    not_isMisesKLRandom_of_plainK_lt_hit,
    not_isMisesKLRandom_of_plainK_lt_TB, not_isMisesKLRandom_of_plainK_lt_colof,
    not_isMisesKLRandom_of_plainK_lt_colbit]
  by_cases hp : ph = true <;> by_cases hc : (!f) = true <;> by_cases hf : f = true <;>
    by_cases hs : (γ + 1) % 2 ^ k = r <;>
    simp_all [not_isMisesKLRandom_of_plainK_lt_cpw_succ_eq]

/-- The discovery test, in terms of the existence of a prefix in the list. -/
private lemma not_isMisesKLRandom_of_plainK_lt_hit_iff (a b : ℕ)
    (Dseq : List Bool → List BitString) (g : ℕ) (cp bits : List Bool) :
    not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g cp bits = true ↔
      ∃ n : ℕ, n ≤ bits.length ∧ 4 * (g + 1) * b < n * a ∧
        bits.take n ∈ Dseq (cp.take (g + bits.length)) := by
  have hrange : ∀ (p : ℕ → Bool) (n : ℕ), (List.range n).findIdx p < n ↔ ∃ m, m < n ∧ p m = true :=
      by
    intro p n
    have h := List.findIdx_lt_length (p := p) (xs := List.range n)
    rw [List.length_range] at h
    simpa [List.mem_range] using h
  unfold not_isMisesKLRandom_of_plainK_lt_hit not_isMisesKLRandom_of_plainK_lt_hitCore
  dsimp only
  simp only [decide_eq_true_eq, hrange, Bool.and_eq_true, List.findIdx_lt_length,
    exists_eq_right]
  constructor <;> rintro ⟨n, hn, h1, h2⟩ <;> exact ⟨n, by omega, h1, h2⟩

/-- The state after a column answer, as a function of the state before it. -/
private noncomputable def not_isMisesKLRandom_of_plainK_lt_colNext (w : CantorSeq)
    (k r a b : ℕ) (Dseq : List Bool → List BitString) (f : Bool) (γ ca cb g : ℕ) (ph : Bool)
    (bits : List Bool) (τf : ℕ) : not_isMisesKLRandom_of_plainK_lt_St :=
  let bit := not_isMisesKLRandom_of_plainK_lt_colbit w k r
    (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb
  let hit := not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
    (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1)) (bits ++ [bit])
  not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1)
    (if not_isMisesKLRandom_of_plainK_lt_colof f ph then ca else ca + 1)
    (if not_isMisesKLRandom_of_plainK_lt_colof f ph then cb + 1 else cb)
    (if ph && hit then γ + 1 else g) (xor ph hit) (if hit then [] else bits ++ [bit])
    (if ph then (if hit then 0 else τf) else (if hit then (bits ++ [bit]).length else 0))

/-- One tick (one or two queries). -/
private lemma not_isMisesKLRandom_of_plainK_lt_tick (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t γ ca cb g : ℕ) (ph : Bool) (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g ph bits τf) :
    ∃ t', not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t' =
        not_isMisesKLRandom_of_plainK_lt_colNext w k r a b Dseq f γ ca cb g ph bits τf ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t' =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t ++
          (if not_isMisesKLRandom_of_plainK_lt_select Dseq F j
              (true, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1), ca, cb, g, ph,
                bits, τf) = true then
            [not_isMisesKLRandom_of_plainK_lt_colbit w k r
              (not_isMisesKLRandom_of_plainK_lt_colof f ph) ca cb]
          else []) := by
  by_cases hs : γ % 2 ^ k = r
  · have hTB : not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g ph bits τf =
        (true, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1), ca, cb, g, ph, bits,
          τf) := by
      simp [not_isMisesKLRandom_of_plainK_lt_TB, hs]
    rw [hTB] at h
    refine ⟨t + 1, not_isMisesKLRandom_of_plainK_lt_col_step w k r a b Dseq f t γ ca cb g
      ph bits τf h, ?_⟩
    rw [not_isMisesKLRandom_of_plainK_lt_outS, h]
    simp [not_isMisesKLRandom_of_plainK_lt_query,
      not_isMisesKLRandom_of_plainK_lt_colbit, not_isMisesKLRandom_of_plainK_lt_colof]
  · have hTB : not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g ph bits τf =
        (false, γ, not_isMisesKLRandom_of_plainK_lt_cpw w k r γ, ca, cb, g, ph, bits, τf) :=
            by
      simp [not_isMisesKLRandom_of_plainK_lt_TB, hs]
    rw [hTB] at h
    have h1 := not_isMisesKLRandom_of_plainK_lt_bg_step w k r a b Dseq f t γ ca cb g ph bits
      τf hs h
    refine ⟨t + 1 + 1, not_isMisesKLRandom_of_plainK_lt_col_step w k r a b Dseq f (t + 1) γ
      ca cb g ph bits τf h1, ?_⟩
    have hout1 : not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f (t + 1) =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t := by
      rw [not_isMisesKLRandom_of_plainK_lt_outS, h]
      simp [not_isMisesKLRandom_of_plainK_lt_select]
    have e : not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f (t + 1 + 1) =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f (t + 1) ++
          (if not_isMisesKLRandom_of_plainK_lt_select Dseq F j
              (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f (t + 1)) = true then
            [w (not_isMisesKLRandom_of_plainK_lt_query k r f
              (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f (t + 1)))]
          else []) := rfl
    rw [e, h1, hout1]
    simp [not_isMisesKLRandom_of_plainK_lt_query,
      not_isMisesKLRandom_of_plainK_lt_colbit, not_isMisesKLRandom_of_plainK_lt_colof]

/-- Tick of phase 1 without discovery. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tick1_nohit (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t γ ca cb g : ℕ) (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g false bits τf)
    (hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
      (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r f ca cb]) = false) :
    ∃ t', not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t' =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1) (if f then ca else ca + 1)
          (if f then cb + 1 else cb) g false
          (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r f ca cb]) 0 ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t' =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t := by
  obtain ⟨t', h1, h2⟩ := not_isMisesKLRandom_of_plainK_lt_tick w k r a b Dseq f F j t γ ca
    cb g false bits τf h
  refine ⟨t', ?_, ?_⟩
  · rw [h1]
    simp [not_isMisesKLRandom_of_plainK_lt_colNext,
      not_isMisesKLRandom_of_plainK_lt_colof, hh]
  · rw [h2]
    simp [not_isMisesKLRandom_of_plainK_lt_select]

/-- Tick of phase 1 with discovery: the phase ends. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tick1_hit (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t γ ca cb g : ℕ) (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g false bits τf)
    (hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
      (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r f ca cb]) = true) :
    ∃ t', not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t' =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1) (if f then ca else ca + 1)
          (if f then cb + 1 else cb) g true []
          (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r f ca cb]).length ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t' =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t := by
  obtain ⟨t', h1, h2⟩ := not_isMisesKLRandom_of_plainK_lt_tick w k r a b Dseq f F j t γ ca
    cb g false bits τf h
  refine ⟨t', ?_, ?_⟩
  · rw [h1]
    simp [not_isMisesKLRandom_of_plainK_lt_colNext,
      not_isMisesKLRandom_of_plainK_lt_colof, hh]
  · rw [h2]
    simp [not_isMisesKLRandom_of_plainK_lt_select]

/-- Tick of phase 2 without discovery. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tick2_nohit (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t γ ca cb g : ℕ) (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g true bits τf)
    (hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
      (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) ca cb]) = false) :
    ∃ t', not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t' =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1) (if !f then ca else ca + 1)
          (if !f then cb + 1 else cb) g true
          (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) ca cb]) τf ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t' =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t ++
          (if F (Dseq ((not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1)).take (g + τf)))
              j bits = true then
            [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) ca cb] else []) := by
  obtain ⟨t', h1, h2⟩ := not_isMisesKLRandom_of_plainK_lt_tick w k r a b Dseq f F j t γ ca
    cb g true bits τf h
  refine ⟨t', ?_, ?_⟩
  · rw [h1]
    simp [not_isMisesKLRandom_of_plainK_lt_colNext,
      not_isMisesKLRandom_of_plainK_lt_colof, hh]
  · rw [h2]
    simp [not_isMisesKLRandom_of_plainK_lt_select,
      not_isMisesKLRandom_of_plainK_lt_colof]

/-- Tick of phase 2 with discovery: the stage ends. -/
private lemma not_isMisesKLRandom_of_plainK_lt_tick2_hit (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t γ ca cb g : ℕ) (bits : List Bool) (τf : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ ca cb g true bits τf)
    (hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1))
      (bits ++ [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) ca cb]) = true) :
    ∃ t', not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t' =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ + 1) (if !f then ca else ca + 1)
          (if !f then cb + 1 else cb) (γ + 1) false [] 0 ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t' =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t ++
          (if F (Dseq ((not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ + 1)).take (g + τf)))
              j bits = true then
            [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) ca cb] else []) := by
  obtain ⟨t', h1, h2⟩ := not_isMisesKLRandom_of_plainK_lt_tick w k r a b Dseq f F j t γ ca
    cb g true bits τf h
  refine ⟨t', ?_, ?_⟩
  · rw [h1]
    simp [not_isMisesKLRandom_of_plainK_lt_colNext,
      not_isMisesKLRandom_of_plainK_lt_colof, hh]
  · rw [h2]
    simp [not_isMisesKLRandom_of_plainK_lt_select,
      not_isMisesKLRandom_of_plainK_lt_colof]

/-- `take n` of a prefix is the shorter prefix. -/
private lemma not_isMisesKLRandom_of_plainK_lt_cantorPrefix_take (u : CantorSeq)
    {n τ : ℕ} (h : n ≤ τ) : (cantorPrefix u τ).take n = cantorPrefix u n := by
  apply List.ext_getElem
  · simp [cantorPrefix_length, h]
  · intro i hi hj
    simp only [List.getElem_take, cantorPrefix_getElem]

/-- The bit read by column `c` is the next bit of the tail of `c` from the current offset. -/
private lemma not_isMisesKLRandom_of_plainK_lt_colbit_tail (w : CantorSeq) (k r : ℕ)
    (c : Bool) (ca cb m τ : ℕ) (h : (if c then cb else ca) = m + τ) :
    not_isMisesKLRandom_of_plainK_lt_colbit w k r c ca cb =
      not_isMisesKLRandom_of_plainK_lt_tail w k r c m τ := by
  cases c <;> simp_all [not_isMisesKLRandom_of_plainK_lt_colbit,
    not_isMisesKLRandom_of_plainK_lt_tail, not_isMisesKLRandom_of_plainK_lt_column]

/-- Number of selected bits is at most the number of completed ticks. -/
private lemma not_isMisesKLRandom_of_plainK_lt_out_le (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (t : ℕ) :
    (not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t).length ≤
      (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t).2.1 := by
  induction t with
  | zero =>
    simp [not_isMisesKLRandom_of_plainK_lt_outS]
  | succ t ih =>
    have e : not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f (t + 1) =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t ++
          (if not_isMisesKLRandom_of_plainK_lt_select Dseq F j
              (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t) = true then
            [w (not_isMisesKLRandom_of_plainK_lt_query k r f
              (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t))]
          else []) := rfl
    rw [e, not_isMisesKLRandom_of_plainK_lt_run]
    generalize not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t = s at ih ⊢
    obtain ⟨sub, γ, cp, ca, cb, g, ph, bits, τf⟩ := s
    cases sub
    · simpa [not_isMisesKLRandom_of_plainK_lt_select,
        not_isMisesKLRandom_of_plainK_lt_step,
        not_isMisesKLRandom_of_plainK_lt_bgCore] using ih
    · simp only [not_isMisesKLRandom_of_plainK_lt_step,
        not_isMisesKLRandom_of_plainK_lt_colCore,
        Bool.cond_true]
      simp only [List.length_append]
      split_ifs <;> simp at ih ⊢ <;> omega

/-- Phase 1 ticks without discovery. -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase1 (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t0 γ0 ca0 cb0 g : ℕ)
    (h0 : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t0 =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ0 ca0 cb0 g false [] 0) (T : ℕ)
    (hno : ∀ τ < T, not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + τ + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
        (if f then cb0 else ca0)) (τ + 1)) = false) :
    ∃ t, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ0 + T) (ca0 + if f then 0 else T)
          (cb0 + if f then T else 0) g false
          (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
            (if f then cb0 else ca0)) T) 0 ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t0 := by
  induction T with
  | zero => exact ⟨t0, by simpa [cantorPrefix] using h0, rfl⟩
  | succ T ih =>
    obtain ⟨t1, h1, o1⟩ := ih (fun τ hτ => hno τ (by omega))
    have hbit := not_isMisesKLRandom_of_plainK_lt_colbit_tail w k r f
      (ca0 + if f then 0 else T) (cb0 + if f then T else 0) (if f then cb0 else ca0) T
      (by cases f <;> simp)
    have hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
        (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
        (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
          (if f then cb0 else ca0)) T ++
          [not_isMisesKLRandom_of_plainK_lt_colbit w k r f (ca0 + if f then 0 else T)
            (cb0 + if f then T else 0)]) = false := by
      rw [hbit, ← cantorPrefix_succ]
      exact hno T (Nat.lt_succ_self T)
    obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_tick1_nohit w k r a b Dseq f F j
      t1 (γ0 + T) _ _ g _ 0 h1 hh
    refine ⟨t2, ?_, o2.trans o1⟩
    rw [h2, hbit, ← cantorPrefix_succ]
    cases f <;> simp [not_isMisesKLRandom_of_plainK_lt_TB, Nat.add_assoc]

/-- The last tick of phase 1 (the discovery tick). -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase1_end (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t0 γ0 ca0 cb0 g : ℕ)
    (h0 : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t0 =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ0 ca0 cb0 g false [] 0) (T : ℕ)
    (hno : ∀ τ < T, not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + τ + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
        (if f then cb0 else ca0)) (τ + 1)) = false)
    (hyes : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
        (if f then cb0 else ca0)) (T + 1)) = true) :
    ∃ t, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ0 + (T + 1))
          (ca0 + if f then 0 else (T + 1)) (cb0 + if f then (T + 1) else 0) g true []
          (T + 1) ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t0 := by
  obtain ⟨t1, h1, o1⟩ := not_isMisesKLRandom_of_plainK_lt_phase1 w k r a b Dseq f F j t0 γ0
    ca0 cb0 g h0 T hno
  have hbit := not_isMisesKLRandom_of_plainK_lt_colbit_tail w k r f
    (ca0 + if f then 0 else T) (cb0 + if f then T else 0) (if f then cb0 else ca0) T
    (by cases f <;> simp)
  have hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r f
        (if f then cb0 else ca0)) T ++
        [not_isMisesKLRandom_of_plainK_lt_colbit w k r f (ca0 + if f then 0 else T)
          (cb0 + if f then T else 0)]) = true := by
    rw [hbit, ← cantorPrefix_succ]
    exact hyes
  obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_tick1_hit w k r a b Dseq f F j
    t1 (γ0 + T) _ _ g _ 0 h1 hh
  refine ⟨t2, ?_, o2.trans o1⟩
  rw [h2, hbit]
  simp only [List.length_append, cantorPrefix_length, List.length_singleton]
  cases f <;> simp [not_isMisesKLRandom_of_plainK_lt_TB, Nat.add_assoc]

/-- Phase 2 ticks without discovery: the selected bits are those of the frozen selector. -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase2 (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t0 γ0 ca0 cb0 g τf : ℕ)
    (h0 : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t0 =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ0 ca0 cb0 g true [] τf)
    (hγ : γ0 = g + τf) (T : ℕ)
    (hno : ∀ τ < T, not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + τ + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
        (if !f then cb0 else ca0)) (τ + 1)) = false) :
    ∃ t, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ0 + T) (ca0 + if !f then 0 else T)
          (cb0 + if !f then T else 0) g true
          (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
            (if !f then cb0 else ca0)) T) τf ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t0 ++
          selectedBits {y | F (Dseq (not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf)))
              j y = true}
            (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
              (if !f then cb0 else ca0)) T) := by
  induction T with
  | zero => exact ⟨t0, by simpa [cantorPrefix] using h0,
              by simp [cantorPrefix, selectedBits, selectedAux]⟩
  | succ T ih =>
    obtain ⟨t1, h1, o1⟩ := ih (fun τ hτ => hno τ (by omega))
    have hbit := not_isMisesKLRandom_of_plainK_lt_colbit_tail w k r (!f)
      (ca0 + if !f then 0 else T) (cb0 + if !f then T else 0) (if !f then cb0 else ca0) T
      (by cases f <;> simp)
    have hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
        (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
        (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
          (if !f then cb0 else ca0)) T ++
          [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) (ca0 + if !f then 0 else T)
            (cb0 + if !f then T else 0)]) = false := by
      rw [hbit, ← cantorPrefix_succ]
      exact hno T (Nat.lt_succ_self T)
    obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_tick2_nohit w k r a b Dseq f F j
      t1 (γ0 + T) _ _ g _ τf h1 hh
    have htake : (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1)).take (g + τf) =
        not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf) := by
      rw [not_isMisesKLRandom_of_plainK_lt_cpw_take]
      congr 1
      omega
    refine ⟨t2, ?_, ?_⟩
    · rw [h2, hbit, ← cantorPrefix_succ]
      cases f <;> simp [not_isMisesKLRandom_of_plainK_lt_TB, Nat.add_assoc]
    · rw [o2, o1, htake, hbit, List.append_assoc]
      congr 1
      rw [cantorPrefix_succ, selectedBits_append_singleton]
      by_cases hF : F (Dseq (not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf))) j
          (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
            (if !f then cb0 else ca0)) T) = true
      · simp
      · simp

/-- The last tick of phase 2 (the discovery tick): the stage ends. -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase2_end (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M)
    (t0 γ0 ca0 cb0 g τf : ℕ)
    (h0 : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t0 =
      not_isMisesKLRandom_of_plainK_lt_TB w k r γ0 ca0 cb0 g true [] τf)
    (hγ : γ0 = g + τf) (T : ℕ)
    (hno : ∀ τ < T, not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + τ + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
        (if !f then cb0 else ca0)) (τ + 1)) = false)
    (hyes : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
        (if !f then cb0 else ca0)) (T + 1)) = true) :
    ∃ t, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
        not_isMisesKLRandom_of_plainK_lt_TB w k r (γ0 + (T + 1))
          (ca0 + if !f then 0 else (T + 1)) (cb0 + if !f then (T + 1) else 0) (γ0 + (T + 1))
          false [] 0 ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t0 ++
          selectedBits {y | F (Dseq (not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf)))
              j y = true}
            (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
              (if !f then cb0 else ca0)) (T + 1)) := by
  obtain ⟨t1, h1, o1⟩ := not_isMisesKLRandom_of_plainK_lt_phase2 w k r a b Dseq f F j t0 γ0
    ca0 cb0 g τf h0 hγ T hno
  have hbit := not_isMisesKLRandom_of_plainK_lt_colbit_tail w k r (!f)
    (ca0 + if !f then 0 else T) (cb0 + if !f then T else 0) (if !f then cb0 else ca0) T
    (by cases f <;> simp)
  have hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
        (if !f then cb0 else ca0)) T ++
        [not_isMisesKLRandom_of_plainK_lt_colbit w k r (!f) (ca0 + if !f then 0 else T)
          (cb0 + if !f then T else 0)]) = true := by
    rw [hbit, ← cantorPrefix_succ]
    exact hyes
  obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_tick2_hit w k r a b Dseq f F j
    t1 (γ0 + T) _ _ g _ τf h1 hh
  have htake : (not_isMisesKLRandom_of_plainK_lt_cpw w k r (γ0 + T + 1)).take (g + τf) =
      not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf) := by
    rw [not_isMisesKLRandom_of_plainK_lt_cpw_take]
    congr 1
    omega
  refine ⟨t2, ?_, ?_⟩
  · rw [h2]
    cases f <;> simp [not_isMisesKLRandom_of_plainK_lt_TB, Nat.add_assoc]
  · rw [o2, o1, htake, hbit, List.append_assoc]
    congr 1
    rw [cantorPrefix_succ, selectedBits_append_singleton]
    by_cases hF : F (Dseq (not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τf))) j
        (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
          (if !f then cb0 else ca0)) T) = true
    · simp
    · simp

/-- The automaton's discovery test is the mathematical discovery predicate of the canonical tick
process (`δ` extra background bits may be known). -/
private lemma not_isMisesKLRandom_of_plainK_lt_hit_iff_P (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (hε : 0 < ε) (a b : ℕ) (hb : 0 < b)
    (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (c : Bool) (m g τ δ : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_hit a b Dseq g
        (not_isMisesKLRandom_of_plainK_lt_cpw w k r (g + τ + δ))
        (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r c m) τ) = true ↔
      not_isMisesKLRandom_of_plainK_lt_P w k r Dseq (4 * ((g : ℝ) + 1) / (ε : ℝ)) c m g
        τ := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have key : ∀ n : ℕ, (4 * ((g : ℝ) + 1) / (ε : ℝ) < n) ↔ 4 * (g + 1) * b < n * a := by
    intro n
    rw [div_lt_iff₀ hεR, hεab, ← mul_div_assoc, lt_div_iff₀ hbR]
    constructor <;> intro h <;> exact_mod_cast h
  rw [not_isMisesKLRandom_of_plainK_lt_hit_iff, cantorPrefix_length,
    not_isMisesKLRandom_of_plainK_lt_cpw_take]
  have hmin : min (g + τ) (g + τ + δ) = g + τ := by omega
  rw [hmin]
  unfold not_isMisesKLRandom_of_plainK_lt_P
  constructor
  · rintro ⟨n, hn, h1, h2⟩
    refine ⟨n, (key n).mpr h1, hn, ?_⟩
    rwa [not_isMisesKLRandom_of_plainK_lt_cantorPrefix_take _ hn] at h2
  · rintro ⟨n, h1, hn, h2⟩
    refine ⟨n, hn, (key n).mp h1, ?_⟩
    rwa [not_isMisesKLRandom_of_plainK_lt_cantorPrefix_take _ hn]

/-- The initial state is the stage-0 tick-boundary state. -/
private lemma not_isMisesKLRandom_of_plainK_lt_init_eq (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) :
    not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f 0 =
      not_isMisesKLRandom_of_plainK_lt_TB w k r 0 0 0 0 false [] 0 := by
  have h0 : not_isMisesKLRandom_of_plainK_lt_cpw w k r 0 = [] := by
    classical
    simp [not_isMisesKLRandom_of_plainK_lt_cp]
  change not_isMisesKLRandom_of_plainK_lt_init k r = _
  unfold not_isMisesKLRandom_of_plainK_lt_init not_isMisesKLRandom_of_plainK_lt_TB
  by_cases h : 0 % 2 ^ k = r
  · have h1 := not_isMisesKLRandom_of_plainK_lt_cpw_succ_eq w k r 0 h
    simpa [h, h0] using h1.symm
  · have h' : ¬ (0 = r) := by simpa using h
    simp [h', h0]

/-- Link with the abstract run. -/
private lemma not_isMisesKLRandom_of_plainK_lt_link (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (ρ : KLRule)
    (hq : ∀ x, ρ.next x = Part.some (not_isMisesKLRandom_of_plainK_lt_query k r f
      (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
        (not_isMisesKLRandom_of_plainK_lt_init k r))))
    (hs : ∀ x, ρ.sel x = Part.some (not_isMisesKLRandom_of_plainK_lt_select Dseq F j
      (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
        (not_isMisesKLRandom_of_plainK_lt_init k r)))) (t : ℕ) :
    (ρ.revealed w t).foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
        (not_isMisesKLRandom_of_plainK_lt_init k r) =
      not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t ∧
    ρ.outputChain w t = not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t := by
  have ho : ∀ n, ρ.outputChain w n = selectedBits
      {x | not_isMisesKLRandom_of_plainK_lt_select
      Dseq F j (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r a b Dseq f)
        (not_isMisesKLRandom_of_plainK_lt_init k r)) = true} (ρ.revealed w n) :=
    fun n => not_isMisesKLRandom_of_plainK_lt_outputChain_eq ρ _ hs w n
  induction t with
  | zero =>
    rw [not_isMisesKLRandom_of_plainK_lt_revealed_zero]
    refine ⟨rfl, ?_⟩
    rw [ho 0, not_isMisesKLRandom_of_plainK_lt_revealed_zero]
    simp [not_isMisesKLRandom_of_plainK_lt_outS, selectedBits, selectedAux]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hrev := not_isMisesKLRandom_of_plainK_lt_revealed_succ ρ _ hq w t
    refine ⟨?_, ?_⟩
    · rw [hrev, List.foldl_append, ih1]
      simp only [List.foldl_cons, List.foldl_nil]
      rfl
    · rw [ho (t + 1), hrev, selectedBits_append_singleton, ← ho t, ih2, ih1]
      change _ = _ ++ (if not_isMisesKLRandom_of_plainK_lt_select Dseq F j
          (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t) = true then
            [w (not_isMisesKLRandom_of_plainK_lt_query k r f
              (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t))] else [])
      by_cases hsel : not_isMisesKLRandom_of_plainK_lt_select Dseq F j
          (not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t) = true
      · simp [hsel, ih1]
      · simp [hsel, ih1]

/-- The threshold of stage `s` in terms of the tick base. -/
private lemma not_isMisesKLRandom_of_plainK_lt_theta_eq (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (s : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_theta w k r Dseq ε s =
      4 * (((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 : ℝ) + 1) /
        (ε : ℝ) := by
  unfold not_isMisesKLRandom_of_plainK_lt_theta
  rw [not_isMisesKLRandom_of_plainK_lt_stage_g_eq]

/-- Before the discovery tick the test fails. -/
private lemma not_isMisesKLRandom_of_plainK_lt_hitF (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString) (ε : ℚ) (hε : 0 < ε) (a b : ℕ) (hb : 0 < b)
    (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (c : Bool) (s γ δ τ : ℕ)
    (he : γ = (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 + τ + δ)
    (hlt : τ < not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε c s) :
    not_isMisesKLRandom_of_plainK_lt_hit a b Dseq
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r γ)
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r c
        (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s)) τ) = false := by
  by_contra hne
  have hh : not_isMisesKLRandom_of_plainK_lt_hit a b Dseq
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r γ)
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r c
        (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s)) τ) = true := by
    simpa using hne
  subst he
  have hP := (not_isMisesKLRandom_of_plainK_lt_hit_iff_P w k r Dseq ε hε a b hb hεab c
    (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s) _ τ δ).mp hh
  rw [← not_isMisesKLRandom_of_plainK_lt_theta_eq] at hP
  have hle := not_isMisesKLRandom_of_plainK_lt_tauc_le w k r Dseq _ c _ _ τ hP
  exact absurd hlt (by unfold not_isMisesKLRandom_of_plainK_lt_tcol; omega)

/-- At the discovery tick the test succeeds. -/
private lemma not_isMisesKLRandom_of_plainK_lt_hitT (w : CantorSeq) (k r : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (ε : ℚ) (hε : 0 < ε) (a b : ℕ) (hb : 0 < b)
    (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (c : Bool) (s δ : ℕ) :
    not_isMisesKLRandom_of_plainK_lt_hit a b Dseq
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
      (not_isMisesKLRandom_of_plainK_lt_cpw w k r
        ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
          not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε c s + δ))
      (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r c
        (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s))
        (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε c s)) = true := by
  have hex := not_isMisesKLRandom_of_plainK_lt_P_exists w k r Dseq hDhit
    (not_isMisesKLRandom_of_plainK_lt_theta w k r Dseq ε s) c
    (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s)
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
  have hspec := not_isMisesKLRandom_of_plainK_lt_tauc_spec w k r Dseq _ c _ _ hex
  rw [not_isMisesKLRandom_of_plainK_lt_theta_eq] at hspec
  have htc : not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε c s =
      not_isMisesKLRandom_of_plainK_lt_tauc w k r Dseq
        (4 * (((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 : ℝ) + 1) /
          (ε : ℝ)) c (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε c s)
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 := by
    unfold not_isMisesKLRandom_of_plainK_lt_tcol
    rw [not_isMisesKLRandom_of_plainK_lt_theta_eq]
  rw [htc]
  exact (not_isMisesKLRandom_of_plainK_lt_hit_iff_P w k r Dseq ε hε a b hb hεab c _ _ _
      δ).mpr
    hspec

/-- Phase 1 of a stage, from the stage-start state. -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase1_run (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (ε : ℚ) (hε : 0 < ε) (hb : 0 < b) (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (s t : ℕ)
    (h : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 false [] 0) :
    ∃ t1, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t1 =
        not_isMisesKLRandom_of_plainK_lt_TB w k r
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
            not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            if f then 0 else not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 +
            if f then not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s else 0)
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 true []
          (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t1 =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t := by
  obtain ⟨T1, hT1⟩ : ∃ T, not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s = T + 1 :=
    ⟨not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s - 1, by
      have := not_isMisesKLRandom_of_plainK_lt_tcol_pos w k r Dseq ε hε hDhit f s
      omega⟩
  obtain ⟨t1, h1, o1⟩ := not_isMisesKLRandom_of_plainK_lt_phase1_end w k r a b Dseq f F j t
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
    (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 h T1
    (fun τ hτ => not_isMisesKLRandom_of_plainK_lt_hitF w k r Dseq ε hε a b hb hεab f s _ 0
      (τ + 1) (by omega) (by omega))
    (by
      have := not_isMisesKLRandom_of_plainK_lt_hitT w k r Dseq hDhit ε hε a b hb hεab f s 0
      rw [hT1, Nat.add_zero, ← Nat.add_assoc] at this
      exact this)
  refine ⟨t1, ?_, o1⟩
  rw [hT1]
  exact h1

/-- Phase 2 of a stage: the selected bits of the frozen selector, and the next stage start. -/
private lemma not_isMisesKLRandom_of_plainK_lt_phase2_run (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (ε : ℚ) (hε : 0 < ε) (hb : 0 < b) (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (s t1 u : ℕ)
    (hu : u ≤ not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s)
    (h1 : not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t1 =
        not_isMisesKLRandom_of_plainK_lt_TB w k r
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
            not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
            if f then 0 else not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 +
            if f then not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s else 0)
          (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 true []
          (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)) :
    ∃ t2, not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t2 =
        not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t1 ++
          selectedBits {y | F (Dseq (not_isMisesKLRandom_of_plainK_lt_cpw w k r
            ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
              not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s))) j y = true}
            (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
              (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε (!f) s)) u) ∧
      (u = not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s →
        ∃ g' ma' mb' : ℕ,
          g' = (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).2.2 ∧
          ma' = (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).1 ∧
          mb' = (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε (s + 1)).2.1 ∧
          not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t2 =
            not_isMisesKLRandom_of_plainK_lt_TB w k r g' ma' mb' g' false [] 0) := by
  have hm : (if (!f) = true then
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1 +
          (if f then not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s else 0)
      else (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1 +
          (if f then 0 else not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)) =
      not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε (!f) s := by
    cases f <;> simp [not_isMisesKLRandom_of_plainK_lt_mcol]
  rcases Nat.lt_or_ge u (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s) with
    hlt | hge
  · obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_phase2 w k r a b Dseq f F j t1
      ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) _ _
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
      (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) h1 rfl u
      (fun τ hτ => by
        rw [hm]
        exact not_isMisesKLRandom_of_plainK_lt_hitF w k r Dseq ε hε a b hb hεab (!f) s _
          (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) (τ + 1) (by omega)
          (by omega))
    refine ⟨t2, ?_, fun hh => absurd hh (by omega)⟩
    rw [o2, hm]
  · have hu' : u = not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s := by omega
    obtain ⟨T2, hT2⟩ : ∃ T, not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s =
        T + 1 :=
      ⟨not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s - 1, by
        have := not_isMisesKLRandom_of_plainK_lt_tcol_pos w k r Dseq ε hε hDhit (!f) s
        omega⟩
    obtain ⟨t2, h2, o2⟩ := not_isMisesKLRandom_of_plainK_lt_phase2_end w k r a b Dseq f F j
      t1 ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
        not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) _ _
      (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
      (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) h1 rfl T2
      (fun τ hτ => by
        rw [hm]
        exact not_isMisesKLRandom_of_plainK_lt_hitF w k r Dseq ε hε a b hb hεab (!f) s _
          (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s) (τ + 1) (by omega)
          (by omega))
      (by
        rw [hm]
        have := not_isMisesKLRandom_of_plainK_lt_hitT w k r Dseq hDhit ε hε a b hb hεab (!f)
          s (not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s)
        rw [hT2, Nat.add_right_comm _ (T2 + 1), ← Nat.add_assoc] at this
        exact this)
    refine ⟨t2, ?_, fun _ => ?_⟩
    · rw [o2, hm, hu', hT2]
    · refine ⟨_, _, _, ?_, ?_, ?_, h2⟩
      · rw [not_isMisesKLRandom_of_plainK_lt_stage_succ_g]
        cases f <;> simp at hT2 ⊢ <;> omega
      · rw [not_isMisesKLRandom_of_plainK_lt_stage_succ_a]
        cases f <;> simp at hT2 ⊢
        omega
      · rw [not_isMisesKLRandom_of_plainK_lt_stage_succ_b]
        cases f <;> simp at hT2 ⊢
        omega

/-- The tick-boundary state at the start of every stage. -/
private lemma not_isMisesKLRandom_of_plainK_lt_stage_start (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (ε : ℚ) (hε : 0 < ε) (hb : 0 < b) (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (s : ℕ) :
    ∃ t, not_isMisesKLRandom_of_plainK_lt_run w k r a b Dseq f t =
      not_isMisesKLRandom_of_plainK_lt_TB w k r
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).1
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.1
        (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 false [] 0 := by
  induction s with
  | zero =>
    exact ⟨0, by simpa [not_isMisesKLRandom_of_plainK_lt_stage] using
      not_isMisesKLRandom_of_plainK_lt_init_eq w k r a b Dseq f⟩
  | succ s ih =>
    obtain ⟨t, h⟩ := ih
    obtain ⟨t1, h1, _⟩ := not_isMisesKLRandom_of_plainK_lt_phase1_run w k r a b Dseq hDhit
      ε hε hb hεab f F j s t h
    obtain ⟨t2, _, h2⟩ := not_isMisesKLRandom_of_plainK_lt_phase2_run w k r a b Dseq hDhit
      ε hε hb hεab f F j s t1 _ le_rfl h1
    obtain ⟨g', ma', mb', hg, ha, hmb, hr⟩ := h2 rfl
    subst hg ha hmb
    exact ⟨t2, hr⟩

/-- The dynamics of the run, in terms of the abstract run and its output. -/
private lemma not_isMisesKLRandom_of_plainK_lt_runspec_core (w : CantorSeq) (k r a b : ℕ)
    (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (ε : ℚ) (hε : 0 < ε) (hb : 0 < b) (hεab : (ε : ℝ) = (a : ℝ) / (b : ℝ)) (f : Bool) {M : ℕ}
    (F : List BitString → Fin M → BitString → Bool) (j : Fin M) (s u : ℕ)
    (hu : u ≤ not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε (!f) s) :
    ∃ (t : ℕ) (pre : BitString),
      pre.length ≤ (not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 ∧
      not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f t = pre ++
        selectedBits {y | F (Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r)
          ((not_isMisesKLRandom_of_plainK_lt_stage w k r Dseq ε s).2.2 +
            not_isMisesKLRandom_of_plainK_lt_tcol w k r Dseq ε f s))) j y = true}
          (cantorPrefix (not_isMisesKLRandom_of_plainK_lt_tail w k r (!f)
            (not_isMisesKLRandom_of_plainK_lt_mcol w k r Dseq ε (!f) s)) u) := by
  obtain ⟨ts, hts⟩ := not_isMisesKLRandom_of_plainK_lt_stage_start w k r a b Dseq hDhit ε
    hε hb hεab f F j s
  obtain ⟨t1, h1, o1⟩ := not_isMisesKLRandom_of_plainK_lt_phase1_run w k r a b Dseq hDhit ε
    hε hb hεab f F j s ts hts
  obtain ⟨t2, o2, _⟩ := not_isMisesKLRandom_of_plainK_lt_phase2_run w k r a b Dseq hDhit ε
    hε hb hεab f F j s t1 u hu h1
  refine ⟨t2, not_isMisesKLRandom_of_plainK_lt_outS w k r a b Dseq F j f ts, ?_, ?_⟩
  · have hl := not_isMisesKLRandom_of_plainK_lt_out_le w k r a b Dseq f F j ts
    rw [hts] at hl
    simpa [not_isMisesKLRandom_of_plainK_lt_TB] using hl
  · rw [o2, o1]

/-- The dynamics of the automaton: the rules given by the automaton satisfy the run description
`RunSpec` (stage induction, then the two phases of each stage). -/
private lemma not_isMisesKLRandom_of_plainK_lt_runspec
    (w : CantorSeq) (k r : ℕ) (Dseq : List Bool → List BitString)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (M : ℕ) (ε : ℚ) (F : List BitString → Fin M → BitString → Bool) (hε : 0 < ε)
    (R : Bool → Fin M → KLRule)
    (hnext : ∀ (f : Bool) (j : Fin M) (x : List Bool), (R f j).next x =
      Part.some (not_isMisesKLRandom_of_plainK_lt_query k r f
        (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r ε.num.toNat ε.den Dseq f)
          (not_isMisesKLRandom_of_plainK_lt_init k r))))
    (hsel : ∀ (f : Bool) (j : Fin M) (x : List Bool), (R f j).sel x =
      Part.some (not_isMisesKLRandom_of_plainK_lt_select Dseq F j
        (x.foldl (not_isMisesKLRandom_of_plainK_lt_step k r ε.num.toNat ε.den Dseq f)
          (not_isMisesKLRandom_of_plainK_lt_init k r)))) :
    not_isMisesKLRandom_of_plainK_lt_RunSpec w k r Dseq ε F R := by
  intro f j s u hu
  have hnum : (0 : ℤ) ≤ ε.num := Rat.num_nonneg.mpr hε.le
  have hεab : (ε : ℝ) = ((ε.num.toNat : ℕ) : ℝ) / ((ε.den : ℕ) : ℝ) := by
    have h1 : ((ε.num.toNat : ℕ) : ℤ) = ε.num := Int.toNat_of_nonneg hnum
    have h2 : ((ε.num.toNat : ℕ) : ℝ) = (ε.num : ℝ) := by exact_mod_cast h1
    rw [h2, Rat.cast_def]
  obtain ⟨t, pre, hpre, hout⟩ := not_isMisesKLRandom_of_plainK_lt_runspec_core w k r
    ε.num.toNat ε.den Dseq hDhit ε hε ε.den_pos hεab f F j s u hu
  refine ⟨t, pre, hpre, ?_⟩
  rw [(not_isMisesKLRandom_of_plainK_lt_link w k r ε.num.toNat ε.den Dseq f F j (R f j)
    (hnext f j) (hsel f j) t).2]
  exact hout

/-- Step 8 of the proof of `not_isMisesKLRandom_of_plainK_lt`: the oracle-free scheduler
(canonical-tick construction with shared stage boundaries: an automaton on the list of revealed bits
gives the `2 * M` Kolmogorov-Loveland rules; `not_isMisesKLRandom_of_plainK_lt_runspec` describes
its run). -/
private lemma not_isMisesKLRandom_of_plainK_lt_dseq_scheduler
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) (β : ℚ)
    (Dseq : List Bool → List BitString) (hDc : Computable Dseq)
    (hDmono : ∀ σ σ' : List Bool, σ <+: σ' → ∀ u ∈ Dseq σ, u ∈ Dseq σ')
    (hDkraft : ∀ ℓ : ℕ,
      ∑ x ∈ (Dseq (not_isMisesKLRandom_of_plainK_lt_cp
        (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ)).toFinset,
          (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1)
    (hDhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n ℓ0 : ℕ, N < n ∧ ∀ ℓ ≥ ℓ0,
      cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n ∈
        Dseq (not_isMisesKLRandom_of_plainK_lt_cp
          (not_isMisesKLRandom_of_plainK_lt_background w k r) ℓ))
    (M : ℕ) (ε : ℚ) (F : List BitString → Fin M → BitString → Bool)
    (hM : 0 < M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : Computable (fun p : (List BitString × Fin M) × BitString => F p.1.1 p.1.2 p.2))
    (hlocal : ∀ D : List BitString,
      (∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length)) ≤ 1 →
      ∀ x ∈ D, ∃ j : Fin M,
        (ε : ℝ) * x.length ≤
          |((selectedBits {y | F D j y = true} x).count true : ℝ) -
            (selectedBits {y | F D j y = true} x).count false|) :
    ∃ R : Fin (2 * M) → KLRule,
      (∀ j, (R j).IsAdmissible) ∧ ∀ N : ℕ, ∃ j t,
        N ≤ ((R j).outputChain w t).length ∧
        ((ε : ℝ) / 4) * ((R j).outputChain w t).length ≤
          |(((R j).outputChain w t).count true : ℝ) -
            ((R j).outputChain w t).count false| := by
  -- the rule `(f, j)` of the automaton, with `next` and `sel` given by `query` and `select`
  choose R hRadm hRnext hRsel using fun (f : Bool) (j : Fin M) =>
    not_isMisesKLRandom_of_plainK_lt_rule_of_automaton
      (not_isMisesKLRandom_of_plainK_lt_init k r)
      (not_isMisesKLRandom_of_plainK_lt_step k r ε.num.toNat ε.den Dseq f)
      (not_isMisesKLRandom_of_plainK_lt_query k r f)
      (not_isMisesKLRandom_of_plainK_lt_select Dseq F j)
      (not_isMisesKLRandom_of_plainK_lt_computable_step k r ε.num.toNat ε.den Dseq hDc f)
      (not_isMisesKLRandom_of_plainK_lt_primrec_query k r f).to_comp
      (not_isMisesKLRandom_of_plainK_lt_computable_select Dseq hDc F hF j)
      (not_isMisesKLRandom_of_plainK_lt_hnr k r ε.num.toNat ε.den hr Dseq f)
  exact not_isMisesKLRandom_of_plainK_lt_assembly w k r β Dseq hDmono hDkraft hDhit M ε F
    hM hε hε1 hlocal R hRadm
    (not_isMisesKLRandom_of_plainK_lt_runspec w k r Dseq hDhit M ε F hε R
      (fun f j x => hRnext f j x) (fun f j x => hRsel f j x))

/-- Step 8 of the proof of `not_isMisesKLRandom_of_plainK_lt`:
run the two competing searches on disjoint dyadic columns, using only their
complementary bits as an oracle. At a stage starting at column offset `m`, ignore
words of length at most `4 * (m + 1) / ε`. Read one column until an enumerated tail-prefix is found,
then use each finite selector on the other column, giving `2 * M` rules.
The symmetric strategy handles the other ordering of the discovery times. Finish
both searches before the next stage, so the strategies share the same stage
boundaries. At least one of the rules has, during each stage, an output prefix whose
new discrepancy dominates all earlier selections. This yields arbitrarily long
output prefixes with discrepancy at least `ε / 4` times their length. The hypotheses
specify every property of the enumeration and the finite selectors used by this construction.
Background queries are implemented by revealing complementary bits and caching
answers; each rule selects only from its target column and never queries a position twice. -/
lemma not_isMisesKLRandom_of_plainK_lt_scheduler
    (w : CantorSeq) (k r : ℕ) (hr : r < 2 ^ k) (β : ℚ)
    (E : ℕ → Option BitString)
    (hE : ComputableIn
      {charOracle (not_isMisesKLRandom_of_plainK_lt_background w k r)} E)
    (hweight : ∀ D : Finset BitString, (∀ x ∈ D, ∃ t, E t = some x) →
      ∑ x ∈ D, (2 : ℝ) ^ (-(β : ℝ) * x.length) ≤ 1)
    (hhit : ∀ b : Bool, ∀ m N : ℕ, ∃ n t : ℕ, N < n ∧
      E t = some (cantorPrefix (fun i =>
        not_isMisesKLRandom_of_plainK_lt_column w (k + 1)
          (r + if b then 2 ^ k else 0) (m + i)) n))
    (M : ℕ) (ε : ℚ) (F : List BitString → Fin M → BitString → Bool)
    (hM : 0 < M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : Computable (fun p : (List BitString × Fin M) × BitString => F p.1.1 p.1.2 p.2))
    (hlocal : ∀ D : List BitString,
      (∑ x ∈ D.toFinset, (2 : ℝ) ^ (-(β : ℝ) * x.length)) ≤ 1 →
      ∀ x ∈ D, ∃ j : Fin M,
        (ε : ℝ) * x.length ≤
          |((selectedBits {y | F D j y = true} x).count true : ℝ) -
            (selectedBits {y | F D j y = true} x).count false|) :
    ∃ R : Fin (2 * M) → KLRule,
      (∀ j, (R j).IsAdmissible) ∧ ∀ N : ℕ, ∃ j t,
        N ≤ ((R j).outputChain w t).length ∧
        ((ε : ℝ) / 4) * ((R j).outputChain w t).length ≤
          |(((R j).outputChain w t).count true : ℝ) -
            ((R j).outputChain w t).count false| := by
  obtain ⟨Dseq, hDc, hDmono, hDsound, hDcomplete⟩ :=
    not_isMisesKLRandom_of_plainK_lt_use
      (not_isMisesKLRandom_of_plainK_lt_background w k r) E hE
  refine not_isMisesKLRandom_of_plainK_lt_dseq_scheduler w k r hr β Dseq hDc hDmono
    ?_ ?_ M ε F hM hε hε1 hF hlocal
  · intro ℓ
    exact hweight _ (fun x hx => hDsound ℓ x (List.mem_toFinset.mp hx))
  · intro b m N
    obtain ⟨n, t, hn, ht⟩ := hhit b m N
    obtain ⟨ℓ0, hℓ0⟩ := hDcomplete t _ ht
    exact ⟨n, ℓ0, hn, hℓ0⟩

end Kolmogorov.FrequencyGames
