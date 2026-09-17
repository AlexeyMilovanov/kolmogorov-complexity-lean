import KolmogorovMathlib.Prefix.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator.FreeList

/-!
# Computability and correctness of the online allocator

The Kraft–Chaitin allocator answers a stream of requests `(output, length)` by handing out
codewords online, keeping a free list of the still-unused nodes of the binary tree.  This
module proves the three properties the coding theorem needs of it:

* it is effective — `allocateOne_computable`, `allocatorState_computable` and
  `allocFun_computable` give computability of one allocation step, of the allocator state and
  of the allocation function, uniformly in the context;
* it is prefix-free — `allocFun_prefixFree`: codes handed out at two different stages are
  incomparable, via `alloc_descendant_freeNext`;
* it succeeds — `allocFun_success`: a request of length `l` is answered as long as the total
  requested Kraft weight stays within one.

The combinator proofs go through `allocatorState_eq_rec` and `allocFun_eq_bind`, which restate
the definitions in a shape the `Computable` combinators can be applied to.
-/

namespace Kolmogorov
namespace KraftChaitin
open scoped ENNReal

/-- `allocateOne` written as an `Option.map` over the fit search. -/
lemma allocateOne_eq_map (free : List BitString) (l : ℕ) :
    allocateOne free l = (free.findIdx? (fun v => decide (v.length ≤ l))).map
      (fun idx => ((splitNode free[idx]! l).1,
        free.take idx ++ (splitNode free[idx]! l).2.reverse ++ free.drop (idx + 1))) := by
  unfold allocateOne
  cases free.findIdx? (fun v => decide (v.length ≤ l)) <;> rfl

-- Treat the data functions opaquely from here on: their definitions have already
-- been characterized by the equational lemmas above, and keeping them reducible
-- makes the `Computable`/`Primrec` combinator unifications whnf-unfold these large
-- definitions, which is prohibitively slow.
attribute [local irreducible] splitNode allocateOne

/-- `allocateOne` is computable. -/
lemma allocateOne_computable :
    Computable (fun p : List BitString × ℕ => allocateOne p.1 p.2) := by
  apply Primrec.to_comp
  have hv : Primrec (fun a : (List BitString × ℕ) × ℕ => a.1.1[a.2]!) :=
    getElem!_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hnode : Primrec (fun a : (List BitString × ℕ) × ℕ => splitNode a.1.1[a.2]! a.1.2) :=
    splitNode_primrec.comp (Primrec.pair hv (Primrec.snd.comp Primrec.fst))
  have hg : Primrec₂ (fun (p : List BitString × ℕ) (idx : ℕ) =>
      ((splitNode p.1[idx]! p.2).1,
        p.1.take idx ++ (splitNode p.1[idx]! p.2).2.reverse ++ p.1.drop (idx + 1))) := by
    refine Primrec.pair (Primrec.fst.comp hnode) ?_
    exact Primrec.list_append.comp
      (Primrec.list_append.comp
        (take_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.list_reverse.comp (Primrec.snd.comp hnode)))
      (drop_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))
  exact (Primrec.option_map findIdx?_pred_primrec hg).of_eq
    (fun p => (allocateOne_eq_map p.1 p.2).symm)

/-- `allocatorState` rewritten as an explicit `Nat.rec` with a combinator-friendly step. -/
lemma allocatorState_eq_rec (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocatorState req n = Nat.rec (some [[]])
      (fun y IH => IH.bind (fun free =>
        ((req y).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free))) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have step_eq : ∀ X : Option (List BitString),
        (match X with
          | none => none
          | some free => match req k with
            | none => some free
            | some (_, l) => match allocateOne free l with
              | none => none
              | some (_, free') => some free')
        = X.bind (fun free =>
            ((req k).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free)) := by
      intro X
      cases X with
      | none => rfl
      | some free =>
        simp only [Option.bind_some]
        rcases hr : req k with _ | ⟨o, l⟩
        · rfl
        · simp only [Option.map_some]
          rcases allocateOne free l with _ | ⟨a, free'⟩ <;> rfl
    calc allocatorState req (k + 1)
        = (match allocatorState req k with
            | none => none
            | some free => match req k with
              | none => some free
              | some (_, l) => match allocateOne free l with
                | none => none
                | some (_, free') => some free') := by rfl
      _ = (allocatorState req k).bind (fun free =>
            ((req k).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD (some free)) :=
            step_eq _
      _ = _ := by rw [ih]

attribute [local irreducible] allocatorState

private lemma allocatorState_hinner_free_comp :
    Computable (fun (p : (((BitString × ℕ) × (ℕ × Option (List BitString))) ×
      List BitString) × (BitString × ℕ)) => p.1.2) :=
  Computable.snd.comp Computable.fst

private lemma allocatorState_hinner_length_comp :
    Computable (fun (p : (((BitString × ℕ) × (ℕ × Option (List BitString))) ×
      List BitString) × (BitString × ℕ)) => p.2.2) :=
  Computable.snd.comp Computable.snd

-- Extracted as a helper to isolate the slow `Primcodable` elaboration.
/-- Allocating one request out of the free list and keeping the updated free list is computable
in the allocator state and the request. -/
lemma allocatorState_hinner_computable :
    Computable₂
      (fun (d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString)
        (pr : BitString × ℕ) => (allocateOne d.2 pr.2).map Prod.snd) := by
  refine Computable.option_map ?_ (Computable.snd.comp Computable.snd).to₂
  exact @Computable.comp
    ((((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString) × (BitString × ℕ))
    (List BitString × ℕ)
    (Option (BitString × List BitString))
    inferInstance inferInstance inferInstance
    (fun (p : List BitString × ℕ) => allocateOne p.1 p.2)
    (fun p => (p.1.2, p.2.2))
    allocateOne_computable
    (allocatorState_hinner_free_comp.pair allocatorState_hinner_length_comp)

/-- One step of the allocator-state recursion — evaluate `req`, allocate from the free list and
keep the updated free list — is computable whenever `req` is. -/
lemma allocatorState_hstep_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable₂ (fun (p : BitString × ℕ) (q : ℕ × Option (List BitString)) =>
      q.2.bind (fun free =>
        ((req p.1 q.1).map (fun pr => (allocateOne free pr.2).map Prod.snd)).getD
          (some free))) := by
  have hreq : Computable
      (fun d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString =>
        req d.1.1.1 d.1.2.1) :=
    @Computable.comp (((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString)
      (BitString × ℕ) (Option (BitString × ℕ))
      inferInstance inferInstance inferInstance
      (fun p => req p.1 p.2)
      (fun d => (d.1.1.1, d.1.2.1))
      hcomp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
  have hg : Computable
      (fun d : ((BitString × ℕ) × (ℕ × Option (List BitString))) × List BitString =>
        ((req d.1.1.1 d.1.2.1).map
          (fun pr => (allocateOne d.2 pr.2).map Prod.snd)).getD (some d.2)) :=
    Computable.option_getD (Computable.option_map hreq allocatorState_hinner_computable)
      (Computable.option_some.comp Computable.snd)
  exact Computable.option_bind (Computable.snd.comp Computable.snd) hg

/-- The allocator state is computable uniformly in the context.

The `Nat.rec` step function is built by `Computable` combinators over a deeply
nested product of list types, whose `Primcodable` encoders make elaboration
unusually slow. -/
lemma allocatorState_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocatorState (req p.1) p.2) := by
  have hstep := allocatorState_hstep_computable req hcomp
  refine (Computable.nat_rec Computable.snd (Computable.const (some [[]])) hstep).of_eq ?_
  intro p
  exact (allocatorState_eq_rec (req p.1) p.2).symm

/-! ## The three top-level obligations -/

/-- `allocFun` rewritten as a bind over the allocator state. -/
lemma allocFun_eq_bind (req : ℕ → Option (BitString × ℕ)) (n : ℕ) :
    allocFun req n = (allocatorState req n).bind (fun free =>
      ((req n).map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none) := by
  unfold allocFun
  rcases allocatorState req n with _ | free
  · rfl
  · simp only [Option.bind_some]
    rcases req n with _ | ⟨o, l⟩
    · rfl
    · simp only [Option.map_some]
      rcases allocateOne free l with _ | ⟨a, free'⟩ <;> rfl

private lemma allocFun_hinner_free_comp :
    Computable (fun p : ((BitString × ℕ) × List BitString) × (BitString × ℕ) => p.1.2) :=
  Computable.snd.comp Computable.fst

private lemma allocFun_hinner_length_comp :
    Computable (fun p : ((BitString × ℕ) × List BitString) × (BitString × ℕ) => p.2.2) :=
  Computable.snd.comp Computable.snd

/-- Allocating one request out of the free list and keeping the allocated string is computable
in the allocator state and the request. -/
lemma allocFun_hinner_computable :
    Computable₂ (fun (e : (BitString × ℕ) × List BitString) (pr : BitString × ℕ) =>
        (allocateOne e.2 pr.2).map Prod.fst) := by
  refine Computable.option_map ?_ (Computable.fst.comp Computable.snd).to₂
  exact @Computable.comp
    (((BitString × ℕ) × List BitString) × (BitString × ℕ))
    (List BitString × ℕ)
    (Option (BitString × List BitString))
    inferInstance inferInstance inferInstance
    (fun p : List BitString × ℕ => allocateOne p.1 p.2)
    (fun p => (p.1.2, p.2.2))
    allocateOne_computable
    (allocFun_hinner_free_comp.pair allocFun_hinner_length_comp)

/-- One step of the allocation function — evaluate `req`, allocate from the free list and return
`none` when there is no request — is computable whenever `req` is. -/
lemma allocFun_hg_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable₂ (fun (p : BitString × ℕ) (free : List BitString) =>
      ((req p.1 p.2).map (fun pr => (allocateOne free pr.2).map Prod.fst)).getD none) := by
  have hreq : Computable (fun e : (BitString × ℕ) × List BitString => req e.1.1 e.1.2) :=
    hcomp.comp Computable.fst
  exact Computable.option_getD
    (Computable.option_map hreq allocFun_hinner_computable) (Computable.const none)

/-- The allocation function is computable uniformly in the context. -/
lemma allocFun_computable (req : BitString → ℕ → Option (BitString × ℕ))
    (hcomp : Computable (fun p : BitString × ℕ => req p.1 p.2)) :
    Computable (fun p : BitString × ℕ => allocFun (req p.1) p.2) := by
  have hg := allocFun_hg_computable req hcomp
  refine (Computable.option_bind (allocatorState_computable req hcomp) hg).of_eq ?_
  intro p
  exact (allocFun_eq_bind (req p.1) p.2).symm

/-
If step `n` produces a codeword, the state after step `n` exists.
-/
lemma allocFun_state_succ (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) : ∃ free', allocatorState req (n + 1) = some free' := by
  unfold allocFun at hn;
  unfold allocatorState; aesop;

/-
The codeword allocated at step `n` is prefix-incomparable to every node still
free after step `n`.
-/
lemma alloc_incomp_freeNext (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (cn : BitString)
    (hn : allocFun req n = some cn) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∀ w ∈ free', ¬ cn <+: w ∧ ¬ w <+: cn := by
  obtain ⟨free, hfree⟩ : ∃ free, allocatorState req n = some free := by
    cases h : allocatorState req n
    · simp_all +decide only [allocFun, reduceCtorEq]
    simp_all +decide only [allocFun, Option.some.injEq, exists_eq']
  unfold allocFun at hn;
  rcases h : req n with ( _ | ⟨ fst, l ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only
  rcases h' : allocateOne free l with ( _ | ⟨ allocated, snd ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq]
  have h_succ : allocatorState req (n + 1) = some snd := by
    simp only [allocatorState, hfree, h, h']
  have h_eq : free' = snd := Option.some.inj (hfree'.symm.trans h_succ)
  rw [h_eq]
  apply allocateOne_alloc_incomp_free' free l cn snd h'
    (allocatorState_prefixFree req n free hfree)
    (allocatorState_descLengths req n free hfree)

/-
Descendant monotonicity of the free list: a node free at a later step has a
prefix among the nodes free at an earlier step.
-/
lemma allocatorState_descendant_mono (req : ℕ → Option (BitString × ℕ)) (k k' : ℕ) (hk : k ≤ k')
    (F F' : List BitString) (h : allocatorState req k = some F)
    (h' : allocatorState req k' = some F') :
    ∀ w ∈ F', ∃ u ∈ F, u <+: w := by
  induction hk generalizing F F' with
  | refl =>
      intro w hw
      have hFF' : F = F' := by
        simpa [h] using h'
      subst F'
      exact ⟨w, hw, List.prefix_refl w⟩
  | step hkm ih =>
      rename_i m
      unfold allocatorState at h'
      cases hG : allocatorState req m with
      | none =>
          rw [hG] at h'
          cases h'
      | some G =>
          cases hreq : req m with
          | none =>
              have hGF' : G = F' := by
                simpa [hG, hreq] using h'
              subst F'
              exact ih F G h hG
          | some pr =>
              rcases pr with ⟨a, l⟩
              cases halloc : allocateOne G l with
              | none =>
                  simp only [hG, hreq, halloc, reduceCtorEq] at h'
              | some out =>
                  rcases out with ⟨a', free'⟩
                  have hfree' : free' = F' := by
                    simpa [hG, hreq, halloc] using h'
                  subst F'
                  intro w hw
                  obtain ⟨u, hu, huw⟩ := allocateOne_free_descendant G l a' free' halloc w hw
                  obtain ⟨v, hv, hvu⟩ := ih F G h hG u hu
                  exact ⟨v, hv, List.IsPrefix.trans hvu huw⟩

/-
The codeword allocated at step `m` is a descendant of some node free at step `m`.
-/
lemma allocFun_descendant_state (req : ℕ → Option (BitString × ℕ)) (m : ℕ) (cm : BitString)
    (hm : allocFun req m = some cm) :
    ∃ Fm, allocatorState req m = some Fm ∧ ∃ u ∈ Fm, u <+: cm := by
  unfold allocFun at hm;
  rcases h : allocatorState req m with (_ | Fm)
  · simp_all +decide only [reduceCtorEq]
  rcases h' : req m with (_ | ⟨fst, l⟩)
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq, exists_eq_left']
  rcases h'' : allocateOne Fm l with ( _ | ⟨ allocated, snd ⟩ )
  · simp_all +decide only [reduceCtorEq]
  simp_all +decide only [Option.some.injEq]
  exact allocateOne_allocated_descendant Fm l cm snd h''

/-- For `m > n`, the codeword allocated at step `m` has a prefix among the nodes
free after step `n`. -/
lemma alloc_descendant_freeNext (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cm : BitString)
    (hnm : n < m) (hm : allocFun req m = some cm) (free' : List BitString)
    (hfree' : allocatorState req (n + 1) = some free') :
    ∃ w ∈ free', w <+: cm := by
  obtain ⟨Fm, hFm, u, hu, hupre⟩ := allocFun_descendant_state req m cm hm
  obtain ⟨w, hw, hwpre⟩ := allocatorState_descendant_mono req (n + 1) m hnm free' Fm hfree' hFm u hu
  exact ⟨w, hw, hwpre.trans hupre⟩

/-- Two codes handed out at different stages are incomparable: the allocator is prefix-free. -/
lemma allocFun_prefixFree (req : ℕ → Option (BitString × ℕ)) (n m : ℕ) (cn cm : BitString)
    (hn : allocFun req n = some cn) (hm : allocFun req m = some cm) (hneq : n ≠ m) :
    ¬ List.IsPrefix cn cm := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req n cn hn
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req n m cm hlt hm free' hfree'
    obtain ⟨h1, h2⟩ := alloc_incomp_freeNext req n cn hn free' hfree' w hw
    exact not_prefix_of_descendant hwpre h1 h2
  · exact absurd heq hneq
  · obtain ⟨free', hfree'⟩ := allocFun_state_succ req m cm hm
    obtain ⟨w, hw, hwpre⟩ := alloc_descendant_freeNext req m n cn hgt hn free' hfree'
    obtain ⟨_, h2⟩ := alloc_incomp_freeNext req m cm hm free' hfree' w hw
    exact fun hcontra => h2 (hwpre.trans hcontra)

/-- A request of length `l` is answered whenever the total requested weight stays within the
Kraft bound. -/
lemma allocFun_success (req : ℕ → Option (BitString × ℕ)) (n : ℕ) (o : BitString) (l : ℕ)
    (hreq : req n = some (o, l))
    (hweight : (∑' i, match req i with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1) :
    ∃ c, allocFun req n = some c ∧ c.length = l := by
  -- Reduce the inline Kraft sum to `reqMass`.
  have hw : (∑' i, reqMass req i) ≤ 1 := by
    refine le_trans (le_of_eq ?_) hweight
    exact tsum_congr (fun i => rfl)
  -- The state exists at step `n`.
  obtain ⟨free, hstate⟩ : ∃ free, allocatorState req n = some free := by
    have := allocatorState_isSome req n hw
    exact Option.isSome_iff_exists.mp this
  have hd : DescLengths free := allocatorState_descLengths req n free hstate
  have hmass : freeMass free + usedMass req n = 1 := allocatorState_mass req n free hstate
  -- Serviceability: the free mass is at least `2^{-l}`.
  have hreqn : reqMass req n = (2 : ℝ≥0∞)⁻¹ ^ l := by simp only [reqMass, hreq]
  have hpartial : usedMass req n + (2 : ℝ≥0∞)⁻¹ ^ l ≤ 1 := by
    have hsucc : usedMass req (n + 1) ≤ ∑' i, reqMass req i := usedMass_le_tsum req (n + 1)
    have hstep : usedMass req (n + 1) = usedMass req n + reqMass req n := by
      simp only [usedMass, Finset.sum_range_succ]
    rw [hstep, hreqn] at hsucc
    exact le_trans hsucc hw
  have hmassge : (2 : ℝ≥0∞)⁻¹ ^ l ≤ freeMass free := by
    by_contra hlt
    push Not at hlt
    have : freeMass free + usedMass req n < (2 : ℝ≥0∞)⁻¹ ^ l + usedMass req n :=
      ENNReal.add_lt_add_right (by
        have : usedMass req n ≤ 1 := le_trans (usedMass_le_tsum req n) hw
        exact ne_top_of_le_ne_top (by norm_num) this) hlt
    rw [hmass, add_comm ((2 : ℝ≥0∞)⁻¹ ^ l)] at this
    exact absurd hpartial (not_le.mpr this)
  obtain ⟨v, hv, hvl⟩ := exists_fit_of_mass_ge free l hd hmassge
  -- Allocation succeeds, with the requested length.
  obtain ⟨a, free', halloc⟩ : ∃ a free', allocateOne free l = some (a, free') := by
    have := allocateOne_isSome_of_exists free l ⟨v, hv, hvl⟩
    obtain ⟨⟨a, free'⟩, h⟩ := Option.isSome_iff_exists.mp this
    exact ⟨a, free', h⟩
  refine ⟨a, ?_, allocateOne_length free l a free' halloc⟩
  simp only [allocFun, hstate, hreq, halloc]

end KraftChaitin
end Kolmogorov
