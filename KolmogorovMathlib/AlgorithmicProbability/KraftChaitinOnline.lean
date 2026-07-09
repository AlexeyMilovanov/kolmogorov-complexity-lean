/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore

/-!
# Online Kraft-Chaitin Allocator
-/

namespace Kolmogorov

open scoped ENNReal

/-- A request stream is a computable sequence of requested lengths.
`req n = some l` means the `n`-th request is for a prefix-free code of length `l`.
`req n = none` means no request at step `n`. -/
def IsComputableRequestStream (req : ℕ → Option ℕ) : Prop :=
  Computable req

/-- The total Kraft weight of a request stream. -/
noncomputable def requestKraftWeight (req : ℕ → Option ℕ) : ℝ≥0∞ :=
  ∑' n, match req n with
    | some l => (2 : ℝ≥0∞)⁻¹ ^ l
    | none => 0

/-- Online Prefix-Free Code Allocator.
Given a computable request stream whose total Kraft weight is `≤ 1`,
there is a computable allocator `alloc : ℕ → Option BitString` that assigns
a disjoint prefix-free code to each valid request, matching the requested length. -/
theorem exists_online_prefixFree_of_kraft_le_one (req : ℕ → Option ℕ)
    (hcomp : IsComputableRequestStream req)
    (hweight : requestKraftWeight req ≤ 1) :
    ∃ alloc : ℕ → Option BitString,
      Computable alloc ∧
      (∀ n l, req n = some l → ∃ c, alloc n = some c ∧ c.length = l) ∧
      (∀ n, req n = none → alloc n = none) ∧
      (∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m → ¬ List.IsPrefix cn cm) := by
  let famReq : BitString → ℕ → Option (BitString × ℕ) :=
    fun _ n ↦ (req n).map (fun l ↦ ([], l))
  have hfamComp : Computable (fun p : BitString × ℕ ↦ famReq p.1 p.2) := by
    have hmap : Computable (fun n : ℕ ↦ (req n).map (fun l ↦ (([] : BitString), l))) := by
      have hpair : Computable₂ (fun (n : ℕ) (l : ℕ) ↦ (([] : BitString), l)) :=
        (Computable.const []).pair Computable.snd
      exact Computable.option_map hcomp hpair
    exact hmap.comp Computable.snd
  have hfamWeight :
      ∀ ctx : BitString,
        (∑' n, match famReq ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0) ≤ 1 := by
    intro ctx
    convert hweight using 1
    congr 1
    ext n
    simp [famReq]
    cases req n <;> rfl
  obtain ⟨famAlloc, hfamAllocComp, hfamAllocLen, hfamPrefix⟩ :=
    exists_online_prefixFree_family famReq hfamComp hfamWeight
  let alloc : ℕ → Option BitString := fun n ↦
    match req n with
    | some _ => famAlloc [] n
    | none => none
  have hallocComp : Computable alloc := by
    have hbranchSome : Computable₂ (fun (n : ℕ) (val : ℕ) ↦ famAlloc [] n) :=
      hfamAllocComp.comp ((Computable.const []).pair Computable.fst)
    have hbranchNone : Computable (fun _ : ℕ ↦ (none : Option BitString)) :=
      Computable.const none
    exact (Computable.option_casesOn hcomp hbranchNone hbranchSome).of_eq
      (fun n ↦ by
        dsimp [alloc]
        cases req n <;> rfl)
  refine ⟨alloc, hallocComp, ?_, ?_, ?_⟩
  · intro n l hreq
    obtain ⟨c, hc, hlen⟩ := hfamAllocLen [] n [] l (by simp [famReq, hreq])
    exact ⟨c, by simpa [alloc, hreq] using hc, hlen⟩
  · intro n hreq
    simp [alloc, hreq]
  · intro n m cn cm hn hm hnm
    by_cases hnreq : req n = none
    · simp [alloc, hnreq] at hn
    by_cases hmreq : req m = none
    · simp [alloc, hmreq] at hm
    obtain ⟨ln, hreqn⟩ := Option.ne_none_iff_exists'.mp hnreq
    obtain ⟨lm, hreqm⟩ := Option.ne_none_iff_exists'.mp hmreq
    exact hfamPrefix [] n m cn cm
      (by simpa [alloc, hreqn] using hn)
      (by simpa [alloc, hreqm] using hm)
      hnm

end Kolmogorov
