/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace

/-!
# Polynomial-space bounds for the game evaluator (`P^R_tt ⊆ PSPACE`, machine part)

The game evaluator of `AFG/Expspace.lean` works in space polynomial in the input length, the
clock and the size of the query set; the exponential bound of `gameValue_mem_EXPSPACE` comes only
from the a priori bound `2 ^ (clock + 1)` on the number of possible queries.  This file

* proves the closure properties of `PSPACE` under finite modifications and `PSPACE ⊆ EXPSPACE`;
* transfers stack programs that are polynomially space bounded outside a finite set to `PSPACE`;
* re-derives the space bounds of the query enumeration, of the preparation of the game data and
  of the evaluation program parametrically in a bound `BB` on the codes of duplicate-free lists of
  possible queries (`*_gen`), and specialises them to a bound `Q` on the size of the query set
  (`*_poly`), for the same programs;
* shows that the evaluator runs in space polynomial in `|x| + clock e |x| + |querySet|`
  (`exists_gameProg_poly`), and concludes that the value of the game is in `PSPACE` when the query
  set has at most `clock e |x| + 1` (or polynomially many) elements outside a finite set of inputs
  (`gameValue_mem_PSPACE`, `gameValue_mem_PSPACE_of_poly`, `gameValue_mem_PSPACE_of_family`).
-/

namespace Kolmogorov.RandomStrings

/-! ### `PSPACE`: finite modifications and inclusion in `EXPSPACE` -/

/-- Changing a set at a single string does not leave `PSPACE`: the machine `modOTM` compares the
input with the hardwired string `z` (extra space `|z| + 1` cells). -/
theorem PSPACE_modify_one (A A' : Set BitString) (hA : A ∈ PSPACE) (z : BitString)
    (h : ∀ x, x ≠ z → (x ∈ A' ↔ x ∈ A)) : A' ∈ PSPACE := by
  classical
  obtain ⟨M, p, hM, hAM⟩ := hA
  refine ⟨modOTM M z (decide (z ∈ A')), p + Polynomial.C (z.length + 1), fun x => ?_,
    fun x => ?_⟩
  · obtain ⟨t, ht, hcard⟩ := hM x
    obtain ⟨u, hu, hcu, -⟩ := modOTM_spec M z (decide (z ∈ A')) x t ht
    refine ⟨u, hu, hcu.trans ?_⟩
    rw [Polynomial.eval_add, Polynomial.eval_C]
    omega
  · obtain ⟨t, ht, -⟩ := hM x
    obtain ⟨u, -, -, hacc⟩ := modOTM_spec M z (decide (z ∈ A')) x t ht
    rw [hacc]
    by_cases hxz : x = z
    · subst hxz; simp
    · rw [ite_eq_right hxz, h x hxz, hAM x]

/-- Finite modifications do not leave `PSPACE`. -/
theorem PSPACE_of_eventually_eq (A B : Set BitString) (hB : B ∈ PSPACE) (Z : Finset BitString)
    (h : ∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) : A ∈ PSPACE := by
  classical
  induction Z using Finset.induction_on generalizing A with
  | empty =>
    have hAB : A = B := Set.ext fun x => h x (Finset.notMem_empty x)
    rw [hAB]; exact hB
  | @insert z Z hz ih =>
    let A' : Set BitString := {x | if x = z then x ∈ B else x ∈ A}
    have hA' : A' ∈ PSPACE := ih A' fun x hx => by
      by_cases hxz : x = z
      · simp [A', hxz]
      · simp only [A', Set.mem_ofPred_eq, ite_eq_right hxz]
        exact h x (by simp [hxz, hx])
    exact PSPACE_modify_one A' A hA' z fun x hxz => by simp [A', hxz]

/-- `PSPACE_of_eventually_eq` with the arguments in the order of the closure hypothesis of the
general theorem. -/
theorem PSPACE_of_eventually_eq' (A B : Set BitString) (Z : Finset BitString) (hB : B ∈ PSPACE)
    (h : ∀ x, x ∉ Z → (x ∈ A ↔ x ∈ B)) : A ∈ PSPACE :=
  PSPACE_of_eventually_eq A B hB Z h

/-- `P^∅ ⊆ PSPACE`: a polynomially clocked machine scans at most `p(n) + 1` cells. -/
theorem polyTimeOracle_empty_subset_PSPACE : PolyTimeOracle ∅ ⊆ PSPACE := by
  rintro A ⟨M, p, hp, hA⟩
  refine ⟨M, p + 1, fun x => ?_, hA⟩
  obtain ⟨t, ht, hh⟩ := hp x
  refine ⟨t, hh, (visited_card_le M ∅ x t).trans ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_one]
  omega

/-- `PSPACE ⊆ EXPSPACE`. -/
theorem PSPACE_subset_EXPSPACE : PSPACE ⊆ EXPSPACE := by
  rintro A ⟨M, p, hM, hA⟩
  refine ⟨M, p, fun x => ?_, hA⟩
  obtain ⟨t, ht, hc⟩ := hM x
  exact ⟨t, ht, hc.trans Nat.lt_two_pow_self.le⟩

/-! ### Stack programs in polynomial space -/

/-- A stack program that halts on every input, in space `p(|x|)` outside a finite set `Z` of
inputs, decides a set in `PSPACE` (simulation `Prog.exists_sim`; on the finitely many inputs of
`Z` the simulation uses a bounded number of cells, absorbed in the constant term). -/
theorem Prog.lang_mem_PSPACE (P : Prog) (p : Polynomial ℕ) (Z : Finset BitString)
    (hhalt : ∀ x : BitString, ∃ t, P.Halted (P.run x t))
    (hsp : ∀ x : BitString, x ∉ Z → ∃ t, P.Halted (P.run x t) ∧
      ∀ s ≤ t, (P.run x s).space ≤ p.eval x.length) :
    P.Lang ∈ PSPACE := by
  classical
  obtain ⟨M, C, hM⟩ := P.exists_sim
  have hS : ∀ x : BitString, ∃ t S, P.Halted (P.run x t) ∧ ∀ s ≤ t, (P.run x s).space ≤ S := by
    intro x
    obtain ⟨t, ht⟩ := hhalt x
    exact ⟨t, (Finset.range (t + 1)).sup fun s => (P.run x s).space, ht, fun s hs =>
      Finset.le_sup (f := fun s => (P.run x s).space) (Finset.mem_range.2 (by omega))⟩
  choose tf Sf htf hSf using hS
  set D : ℕ := Z.sup fun x => C * (Sf x + 1) with hD
  refine ⟨M, Polynomial.C C * (p + 1) + Polynomial.C D, fun x => ?_, fun x => ?_⟩
  · have hev : (Polynomial.C C * (p + 1) + Polynomial.C D).eval x.length =
        C * (p.eval x.length + 1) + D := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
    rw [hev]
    by_cases hx : x ∈ Z
    · obtain ⟨u, hu, hcard, -⟩ := hM x (tf x) (Sf x) (htf x) (hSf x)
      refine ⟨u, hu, hcard.trans ?_⟩
      have : C * (Sf x + 1) ≤ D := Finset.le_sup (f := fun x => C * (Sf x + 1)) hx
      exact this.trans (Nat.le_add_left _ _)
    · obtain ⟨t, ht, hsp'⟩ := hsp x hx
      obtain ⟨u, hu, hcard, -⟩ := hM x t _ ht hsp'
      exact ⟨u, hu, hcard.trans (Nat.le_add_right _ _)⟩
  · obtain ⟨u, -, -, hacc⟩ := hM x (tf x) (Sf x) (htf x) (hSf x)
    rw [P.mem_lang_iff_of_halted x (tf x) (htf x), hacc]

/-! ### Parametric space bounds: the query enumeration -/

/-- The hypothesis of the parametric bounds: every duplicate-free list of possible queries of
`(c, e)` on `x` has a code of length at most `BB`. -/
def QBound (c : OTMCode) (e : ℕ) (x : BitString) (BB : ℕ) : Prop :=
  ∀ Lo : List BitString, Lo.Nodup → (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
    (Stacks.encList Lo).length ≤ BB

/-- A bound on the size of the query set gives a bound on the codes of duplicate-free lists of
possible queries: at most `Q` strings, each of length `≤ T`, hence of code length `≤ 2T + 1`. -/
theorem qBound_of_card (c : OTMCode) (e : ℕ) (x : BitString) (Q : ℕ)
    (hQ : (querySet c.toOTM x (clock e x.length)).card ≤ Q) :
    QBound c e x (Q * (2 * clock e x.length + 1)) := by
  classical
  intro Lo hnd hLo
  have hT : ∀ z ∈ Lo, z.length ≤ clock e x.length := fun z hz =>
    length_le_of_mem_queryAll _ x _ z (hLo z hz)
  have h1 : Lo.length ≤ Q := by
    have hsub : Lo.toFinset ⊆ querySet c.toOTM x (clock e x.length) := by
      intro z hz
      rw [mem_querySet_iff_queryAll]
      exact hLo z (List.mem_toFinset.1 hz)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at this
    omega
  calc (Stacks.encList Lo).length ≤ Lo.length * (2 * clock e x.length + 1) :=
        QEnum.length_encList_le _ Lo hT
    _ ≤ Q * (2 * clock e x.length + 1) := Nat.mul_le_mul_right _ h1

/-- The a priori exponential bound (as in `exists_queryEnumStmt`): every input has some `BB`. -/
theorem qBound_exp (c : OTMCode) (e : ℕ) (x : BitString) :
    QBound c e x ((2 ^ (clock e x.length + 1)) ^ 2) := fun Lo hnd hLo =>
  QEnum.length_encList_le_sq c.toOTM x (clock e x.length) _ le_rfl Lo hnd hLo

/-- Arithmetic: the parameter `n + T + Q (2T + 1) + 1` is at most `3 (n + T + Q + 1) ^ 2`. -/
theorem qparam_le (n T Q : ℕ) : n + T + Q * (2 * T + 1) + 1 ≤ 3 * (n + T + Q + 1) ^ 2 := by
  nlinarith

/-- **Enumeration of the query set, parametric space bound.**  The statement of
`exists_queryEnumStmt` (the same program `QEnum.qeStmt`) runs within space
`K · (|x| + clock e |x| + BB + 1) ^ 2` whenever `BB` bounds the codes of all duplicate-free lists of
possible queries.  The exponential bound of `exists_queryEnumStmt` is the case
`BB = (2 ^ (clock e |x| + 1)) ^ 2` (`qBound_exp`). -/
theorem exists_queryEnumStmt_gen (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (inp out : Fin k) (K : ℕ), inp ≠ out ∧
      ∀ (x : BitString) (BB : ℕ), QBound c e x BB →
        ∃ L : List BitString, L.Nodup ∧
        (∀ z, z ∈ L ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
        Exec s (Function.update (fun _ => []) inp x)
          (Function.update (Function.update (fun _ => []) inp x) out (Stacks.encList L))
          (K * (x.length + clock e x.length + BB + 1) ^ 2) := by
  obtain ⟨sSel, KS, hSel⟩ := QEnum.exists_selStmt
  obtain ⟨sZero, KZ, hZero⟩ := QEnum.exists_zeroStmt
  obtain ⟨sMerge, KM, hMerge⟩ := QEnum.exists_mergeStmt
  obtain ⟨sSim, CS, hSim⟩ := QEnum.exists_recSimStmt c e
  refine ⟨28, QEnum.qeStmt sZero sSel sSim sMerge, 0, 1,
    8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM + 2 * KZ, by decide, fun x BB hB => ?_⟩
  set K0 := 8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM + 2 * KZ with hK0
  set a := x.length + clock e x.length + BB + 1 with ha
  have h1a : 1 ≤ a := by omega
  have hG : ∀ (Lo Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln ++ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length →
      QEnum.stepBound e KS CS KM x Lo Ln l ≤ K0 * a ^ 2 := by
    intro Lo Ln l hnd hall hl
    have he := hB (Ln ++ Lo) hnd hall
    rw [QEnum.encList_append, List.length_append] at he
    have := QEnum.stepBound_le e KS CS KM x Lo Ln l a (by omega) (by omega) (by omega) hl h1a
    calc QEnum.stepBound e KS CS KM x Lo Ln l ≤
          (8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM) * a ^ 2 := this
      _ ≤ K0 * a ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have hGz : ∀ Lo : List BitString, Lo.Nodup →
      (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      KZ * ((Stacks.encList Lo).length + 1) + (QEnum.stR x Lo false).space ≤ K0 * a ^ 2 := by
    intro Lo hnd hLo
    have he := hB Lo hnd hLo
    rw [QEnum.stR_space]
    have ha2 : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) _
    have hKZ : KZ * ((Stacks.encList Lo).length + 1) ≤ 2 * (KZ * a ^ 2) := by
      calc KZ * ((Stacks.encList Lo).length + 1) ≤ KZ * (2 * a ^ 2) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (KZ * a ^ 2) := by ring
    have hR : K0 * a ^ 2 = 8 * a ^ 2 + 16 * (CS * a ^ 2) +
        3 * (KS * a ^ 2) + 16 * (KM * CS * a ^ 2) + 2 * (KM * a ^ 2) +
        2 * (KZ * a ^ 2) := by rw [hK0]; ring
    rw [hR]
    omega
  exact QEnum.exec_qe hZero hSel hSim hMerge x (K0 * a ^ 2) BB hG hGz hB

/-! ### Parametric space bounds: preparation and evaluation -/

/-- **Preparation of the game data, parametric space bound.**  The statement of
`exists_prepStmt` (the same program: the query enumeration, two filterings against hardwired
lists, and the costs and budget) runs within space `C · (|x| + clock e |x| + BB + 1) ^ 2`, and the
prepared data have size within the same bound, whenever `BB` bounds the codes of all
duplicate-free lists of possible queries (`QBound`).  The proof is the one of `exists_prepStmt`
with the query enumeration bound of `exists_queryEnumStmt_gen` and with `|encList LQ| ≤ BB`. -/
theorem exists_prepStmt_gen (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 6 ≤ k ∧ ∀ (x : BitString) (BB : ℕ), QBound c e x BB →
      ∃ (LX LR cs : List BitString) (eb : BitString) (N W : ℕ),
      LX.Nodup ∧ LX.toFinset = querySet c.toOTM x (clock e x.length) \ Y ∧
      (∀ z, z ∈ LR ↔ z ∈ querySet c.toOTM x (clock e x.length) ∧ z.length ≤ T.fn z) ∧
      (∀ z ∈ LX, z.length - 1 ≤ N ∧ T.fn z ≤ N) ∧ m ≤ N ∧
      cs.length = LX.length ∧ (∀ b ∈ cs, b.length = W) ∧ eb.length = W ∧
      (∀ i < LX.length, binVal (cs.getD i []) =
        costNum N (T.fn (LX.getD i [])) (LX.getD i []).length) ∧
      binVal eb = 2 ^ (N - m) ∧
      binVal eb + (LX.map fun z => costNum N (T.fn z) z.length).sum < 2 ^ W ∧
      x.length + clock e x.length + (Stacks.encList LX).length +
          (Stacks.encList cs).length +
        eb.length + (Stacks.encList LR).length + 1 ≤
          C * (x.length + clock e x.length + BB + 1) ^ 2 ∧
      Exec s (Stacks.input k x)
        (Stacks.layout k [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR])
        (C * (x.length + clock e x.length + BB + 1) ^ 2) := by
  classical
  obtain ⟨kq, sq, inp, out, Cq, hio, hq⟩ := exists_queryEnumStmt_gen c e
  obtain ⟨k₂, s₂, C₂, hk₂, hfil⟩ := exists_filterNotMemStmt
  obtain ⟨kc, sc, Cc, hkc, hcost⟩ := exists_costStmt T m
  let K := 7 + kq + k₂ + kc
  let fq : Fin kq → Fin K := fun i => if i = inp then ⟨0, by omega⟩ else if i = out then
    ⟨5, by omega⟩ else ⟨7 + i.val, by omega⟩
  let g₁ : Fin k₂ → Fin K := fun i =>
    ⟨place3 5 6 1 (7 + kq) i.val, place3_lt (by omega) (by omega) (by omega) (by omega) i.isLt⟩
  let g₂ : Fin k₂ → Fin K := fun i =>
    ⟨place3 5 6 4 (7 + kq) i.val, place3_lt (by omega) (by omega) (by omega) (by omega) i.isLt⟩
  let fc : Fin kc → Fin K := fun i =>
    ⟨place3 1 2 3 (7 + kq + k₂) i.val, place3_lt (by omega) (by omega) (by omega) (by omega) i.isLt⟩
  have hfq : Function.Injective fq := by
    intro a b h
    simp only [fq] at h
    split_ifs at h <;> simp_all [Fin.ext_iff] <;> omega
  have hg₁ : Function.Injective g₁ := fun a b h => Fin.ext
    (place3_injective (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (congrArg Fin.val h))
  have hg₂ : Function.Injective g₂ := fun a b h => Fin.ext
    (place3_injective (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (congrArg Fin.val h))
  have hfc : Function.Injective fc := fun a b h => Fin.ext
    (place3_injective (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (congrArg Fin.val h))
  set LY : List BitString := Y.toList with hLY
  set LZ : List BitString := (T.dom.filter fun z => T.value z < z.length).toList with hLZ
  set D := 8 + (Stacks.encList LY).length + (Stacks.encList LZ).length +
    C₂ * ((Stacks.encList LY).length + (Stacks.encList LZ).length + 4) + 4 * Cc with hD
  refine ⟨K, Stmt.seqs [sq.rename fq, Stmt.pushList ⟨6, by omega⟩ (Stacks.encList LY),
    s₂.rename g₁, Stmt.clear ⟨6, by omega⟩, Stmt.pushList ⟨6, by omega⟩ (Stacks.encList LZ),
    s₂.rename g₂, Stmt.clear ⟨6, by omega⟩, Stmt.clear ⟨5, by omega⟩, sc.rename fc],
    D + Cq, by omega, fun x BB hB => ?_⟩
  obtain ⟨LQ, hQnd, hQ, hexq⟩ := hq x BB hB
  obtain ⟨cs, eb, N, W, hN, hm, hcs, hW, heb, hcost', hE, hov, hexc⟩ :=
    hcost (LQ.filter fun z => decide (z ∉ LY))
  -- step 1: enumerate the queries onto stack 5
  set τ₀ := Stacks.input K x with hτ₀
  have hc₁ : (fun r => τ₀ (fq r)) = Function.update (fun _ => []) inp x := by
    funext r
    by_cases h1 : r = inp
    · subst h1; simp [fq, hτ₀, Stacks.input]
    · by_cases h2 : r = out
      · subst h2; simp [fq, h1, hτ₀, Stacks.input]
      · simp [fq, h1, h2, hτ₀, Stacks.input]
  rw [← hc₁] at hexq
  have e₁ := Exec.call hfq hexq
  have hfqo : fq out = ⟨5, by omega⟩ := by simp [fq, Ne.symm hio]
  rw [hfqo] at e₁
  set τ₁ := Function.update τ₀ ⟨5, by omega⟩ (Stacks.encList LQ) with hτ₁
  -- step 2: the hardwired list `Y`
  have e₂ := Stmt.exec_pushList (⟨6, by omega⟩ : Fin K) (Stacks.encList LY) τ₁
  rw [show τ₁ ⟨6, by omega⟩ = [] by simp [hτ₁, hτ₀, Stacks.input], List.append_nil] at e₂
  set τ₂ := Function.update τ₁ ⟨6, by omega⟩ (Stacks.encList LY) with hτ₂
  -- step 3: the board `LX = LQ \ Y` onto stack 1
  have h₃ := hfil LQ LY
  have hc₃ : (fun r => τ₂ (g₁ r)) = Stacks.layout k₂ [Stacks.encList LQ, Stacks.encList LY] := by
    funext r
    obtain ⟨n, hn⟩ := r
    rcases n with _ | _ | _ | n <;>
      simp only [hτ₂, hτ₁, hτ₀, place3, ↓reduceIte, ne_eq, Fin.mk.injEq, Nat.reduceEqDiff,
        not_false_eq_true, Function.update_of_ne, Function.update_self, Stacks.layout,
        List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Order.lt_two_iff, zero_le, getElem?_pos, List.getElem_cons_zero, Option.getD_some, g₁,
        one_ne_zero, Std.le_refl, List.getElem_cons_succ, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
        OfNat.one_ne_ofNat, Stacks.input, lt_self_iff_false, getElem?_neg, Option.getD_none,
        Nat.add_eq_zero_iff, and_false, and_self, Nat.add_eq_right, Function.update_apply,
        false_and, add_le_iff_nonpos_left, nonpos_iff_eq_zero]
    all_goals (split_ifs <;> first | rfl | omega)
  rw [Stacks.layout_three _ _ _ (by omega), ← hc₃] at h₃
  have e₃ := Exec.call hg₁ h₃
  set τ₃ := Function.update τ₂ (g₁ ⟨2, by omega⟩)
    (Stacks.encList (LQ.filter fun z => decide (z ∉ LY))) with hτ₃
  -- step 4: clear stack 6
  have e₄ := Stmt.exec_clear (⟨6, by omega⟩ : Fin K) _ τ₃ rfl
  set τ₄ := Function.update τ₃ ⟨6, by omega⟩ [] with hτ₄
  -- step 5: the hardwired list of the non-random table entries
  have e₅ := Stmt.exec_pushList (⟨6, by omega⟩ : Fin K) (Stacks.encList LZ) τ₄
  rw [show τ₄ ⟨6, by omega⟩ = [] from Function.update_self _ _ _, List.append_nil] at e₅
  set τ₅ := Function.update τ₄ ⟨6, by omega⟩ (Stacks.encList LZ) with hτ₅
  -- step 6: the random queries `LR = LQ \ LZ` onto stack 4
  have h₆ := hfil LQ LZ
  have hc₆ : (fun r => τ₅ (g₂ r)) = Stacks.layout k₂ [Stacks.encList LQ, Stacks.encList LZ] := by
    funext r
    obtain ⟨n, hn⟩ := r
    rcases n with _ | _ | _ | n <;>
      simp only [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, place3, OfNat.ofNat_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, decide_not, Function.update_idem, ne_eq, Fin.mk.injEq, Nat.reduceEqDiff,
        not_false_eq_true, Function.update_of_ne, Function.update_self, Stacks.layout,
        List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Order.lt_two_iff, zero_le, getElem?_pos, List.getElem_cons_zero, Option.getD_some, g₁, g₂,
        one_ne_zero, Std.le_refl, List.getElem_cons_succ, Stacks.input, lt_self_iff_false,
        getElem?_neg, Option.getD_none, Nat.add_eq_zero_iff, and_false, and_self, Nat.add_eq_right,
        Function.update_apply, false_and, add_le_iff_nonpos_left, nonpos_iff_eq_zero]
    all_goals (split_ifs <;> first | rfl | omega)
  rw [Stacks.layout_three _ _ _ (by omega), ← hc₆] at h₆
  have e₆ := Exec.call hg₂ h₆
  set τ₆ := Function.update τ₅ (g₂ ⟨2, by omega⟩)
    (Stacks.encList (LQ.filter fun z => decide (z ∉ LZ))) with hτ₆
  -- steps 7, 8: clear stacks 6 and 5
  have e₇ := Stmt.exec_clear (⟨6, by omega⟩ : Fin K) _ τ₆ rfl
  set τ₇ := Function.update τ₆ ⟨6, by omega⟩ [] with hτ₇
  have e₈ := Stmt.exec_clear (⟨5, by omega⟩ : Fin K) _ τ₇ rfl
  set τ₈ := Function.update τ₇ ⟨5, by omega⟩ [] with hτ₈
  -- step 9: costs and budget onto stacks 2 and 3
  have hc₉ : (fun r => τ₈ (fc r)) =
      Stacks.layout kc [Stacks.encList (LQ.filter fun z => decide (z ∉ LY))] := by
    funext r
    obtain ⟨n, hn⟩ := r
    rcases n with _ | _ | _ | n <;>
      simp only [hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, place3, OfNat.ofNat_ne_zero,
        ↓reduceIte, OfNat.ofNat_ne_one, decide_not, Function.update_idem, ne_eq, Fin.mk.injEq,
        OfNat.one_ne_ofNat, not_false_eq_true, Function.update_of_ne, Function.update_self,
        Stacks.layout, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add,
        Order.lt_one_iff, getElem?_pos, List.getElem_cons_zero, Option.getD_some, g₁, g₂, fc,
        one_ne_zero, Nat.reduceEqDiff, Stacks.input, lt_self_iff_false, getElem?_neg,
        Option.getD_none, Nat.reduceAdd, Nat.add_eq_zero_iff, and_false,
        and_self, Nat.add_eq_right, Function.update_apply, false_and, ite_eq_left_iff]
    all_goals (intros; split_ifs <;> first | rfl | omega)
  rw [Stacks.layout_three' _ _ _ (by omega) (by omega), ← hc₉] at hexc
  have e₉ := Exec.call2 hfc hexc
  set τ₉ := Function.update (Function.update τ₈ (fc ⟨1, by omega⟩) (Stacks.encList cs))
    (fc ⟨2, by omega⟩) eb with hτ₉
  -- space bookkeeping
  set a := x.length + clock e x.length + BB + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have haa : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsp₀ : Stacks.space τ₀ = x.length := by
    rw [hτ₀, Stacks.input_eq_layout, Stacks.space_layout _ (by simp; omega)]; simp
  have hsp₁ : Stacks.space τ₁ = Stacks.space τ₀ + (Stacks.encList LQ).length :=
    Stacks.space_update_nil _ _ _ (by simp [hτ₀, Stacks.input])
  have s₁ := e₁.space_le.2
  have s₂ := e₂.space_le.2
  have s₃ := e₃.space_le.2
  have s₄ := e₄.space_le.2
  have s₅ := e₅.space_le.2
  have s₆ := e₆.space_le.2
  have s₇ := e₇.space_le.2
  have s₈ := e₈.space_le.2
  have s₉ := e₉.space_le.2
  have hLX := Stacks.length_encList_filter_le LQ (fun z => decide (z ∉ LY))
  have hLR := Stacks.length_encList_filter_le LQ (fun z => decide (z ∉ LZ))
  have hLQB : (Stacks.encList LQ).length ≤ BB := hB LQ hQnd fun z hz => (hQ z).1 hz
  have hLQ : (Stacks.encList LQ).length ≤ a := by omega
  have hτ₈1 : τ₈ (fc ⟨1, by omega⟩) = [] := by
    simp [fc, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, g₁, g₂]
  have hτ₈2 : τ₈ (fc ⟨2, by omega⟩) = [] := by
    simp [fc, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, g₁, g₂]
  have hsp₉ : Stacks.space τ₉ = Stacks.space τ₈ + (Stacks.encList cs).length + eb.length := by
    rw [hτ₉, Stacks.space_update_nil _ _ _ (by
        rw [Function.update_of_ne (hfc.ne (by simp [Fin.ext_iff]))]; exact hτ₈2),
      Stacks.space_update_nil _ _ _ hτ₈1]
  -- all bounds are below `TOTAL ≤ (D + Cq) · a ^ 2`
  have hT2 : Cq * a ^ 2 + Stacks.space τ₀ + (Stacks.encList LY).length +
      (Stacks.encList LZ).length +
      C₂ * ((Stacks.encList LQ).length + (Stacks.encList LY).length + 1) +
      C₂ * ((Stacks.encList LQ).length + (Stacks.encList LZ).length + 1) +
      Cc * ((Stacks.encList (LQ.filter fun z => decide (z ∉ LY))).length + 1) ^ 2 + 3 * a ≤
      (D + Cq) * a ^ 2 := by
    have i1 : C₂ * ((Stacks.encList LQ).length + (Stacks.encList LY).length + 1) ≤
        C₂ * (((Stacks.encList LY).length + 2) * a) :=
      Nat.mul_le_mul_left _ (aux_lin_le _ _ _ ha1 hLQ)
    have i2 : C₂ * ((Stacks.encList LQ).length + (Stacks.encList LZ).length + 1) ≤
        C₂ * (((Stacks.encList LZ).length + 2) * a) :=
      Nat.mul_le_mul_left _ (aux_lin_le _ _ _ ha1 hLQ)
    have i3 : Cc * ((Stacks.encList (LQ.filter fun z => decide (z ∉ LY))).length + 1) ^ 2 ≤
        Cc * (4 * a ^ 2) :=
      Nat.mul_le_mul_left _ (aux_sq_le _ _ (hLX.trans hLQ) ha1)
    have i4 : (Stacks.encList LY).length ≤ (Stacks.encList LY).length * a ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have i5 : (Stacks.encList LZ).length ≤ (Stacks.encList LZ).length * a ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have i6 : C₂ * (((Stacks.encList LY).length + 2) * a) ≤
        C₂ * (((Stacks.encList LY).length + 2) * a ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ haa)
    have i7 : C₂ * (((Stacks.encList LZ).length + 2) * a) ≤
        C₂ * (((Stacks.encList LZ).length + 2) * a ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ haa)
    have i9 : Stacks.space τ₀ ≤ a ^ 2 := by rw [hsp₀]; omega
    rw [hD]
    linarith
  have hfin : ∀ t, t ≤ (D + Cq) * a ^ 2 → t ≤ (D + Cq) * a ^ 2 := fun t ht => ht
  refine ⟨LQ.filter fun z => decide (z ∉ LY), LQ.filter fun z => decide (z ∉ LZ), cs, eb, N, W,
    hQnd.filter _, ?_, ?_, hN, hm, hcs, hW, heb, hcost', hE, hov, ?_, ?_⟩
  · ext z
    simp [hLY, hQ, mem_querySet_iff_queryAll]
  · intro z
    simp only [List.mem_filter, hLZ, Finset.mem_toList, Finset.mem_filter, decide_eq_true_eq,
      hQ, mem_querySet_iff_queryAll]
    unfold Table.fn
    split_ifs with hd <;> simp [hd]
    omega
  · have := hfin _ hT2
    omega
  · refine Stmt.exec_of_eq (.seq (e₁.mono (hfin _ (by omega))) (.seq (e₂.mono (hfin _ (by omega)))
      (.seq (e₃.mono (hfin _ (by omega))) (.seq (e₄.mono (hfin _ (by omega)))
      (.seq (e₅.mono (hfin _ (by omega))) (.seq (e₆.mono (hfin _ (by omega)))
      (.seq (e₇.mono (hfin _ (by omega))) (.seq (e₈.mono (hfin _ (by omega)))
      (.seq (e₉.mono (hfin _ (by omega))) (.skip (hfin _ (by omega)))))))))))) ?_
    funext j
    obtain ⟨n, hn⟩ := j
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;>
      simp [hτ₉, fc, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, g₁, g₂,
        Stacks.layout]

/-- **The evaluation program, parametric space bound.**  The statement of `exists_evalStmt`
(the same program: preparation followed by the depth-first evaluation) runs within space
`C · (|x| + clock e |x| + BB + 1) ^ 4` whenever `BB` bounds the codes of all duplicate-free lists
of possible queries (`QBound`), and leaves the value of the game on its output stack. -/
theorem exists_evalStmt_gen (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (out : Fin k) (C : ℕ), ∀ (x : BitString) (BB : ℕ), QBound c e x BB →
      ∃ σ' : Stacks k,
      Exec s (Stacks.input k x) σ' (C * (x.length + clock e x.length + BB + 1) ^ 4) ∧
      ((σ' out).head? = some true ↔
        gameValB (querySet c.toOTM x (clock e x.length) \ Y)
          (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
          (2 ^ (gameN e T m x.length - m))
          (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
            (querySet c.toOTM x (clock e x.length) \ Y)).outcome = true) := by
  classical
  obtain ⟨k₁, s₁, C₁, hk₁, hprep⟩ := exists_prepStmt_gen c e T m Y
  obtain ⟨k₂, s₂, C₂, hk₂, hgame⟩ := exists_gameStmt c e
  have h₁ : k₁ ≤ max k₁ k₂ := le_max_left _ _
  have h₂ : k₂ ≤ max k₁ k₂ := le_max_right _ _
  refine ⟨max k₁ k₂, .seq (s₁.rename (Fin.castLE h₁)) (s₂.rename (Fin.castLE h₂)),
    ⟨5, by omega⟩, C₁ + C₂ * C₁ ^ 2, fun x BB hB => ?_⟩
  obtain ⟨LX, LR, cs, eb, N, W, hnd, hLX, hLR, hN, hm, hcs, hW, heb, hcost, hE, hov, hsize,
    hex₁⟩ := hprep x BB hB
  set a := x.length + clock e x.length + BB + 1 with ha
  have ha1 : 1 ≤ a := by omega
  -- the game statement on the prepared data
  have hex₂ := hgame x LX LR cs eb W (fun z => costNum N (T.fn z) z.length) hnd hcs hW heb hcost hov
  -- inline both
  rw [Stacks.input_eq_layout, ← Stacks.layout_castLE h₁] at hex₁
  have r₁ := Exec.rename_of_comp (Fin.castLE_injective h₁) hex₁
  rw [Stacks.extend_castLE_layout h₁ _ _ (by simp; omega) (by simp; omega),
    Stacks.rest_castLE_layout h₁ _ (by simp; omega), Nat.add_zero] at r₁
  rw [← Stacks.layout_castLE h₂] at hex₂
  have r₂ := Exec.rename_of_comp (Fin.castLE_injective h₂) hex₂
  rw [Stacks.extend_castLE_layout h₂ _ _ (by simp; omega) (by simp; omega),
    Stacks.rest_castLE_layout h₂ _ (by simp; omega), Nat.add_zero] at r₂
  rw [← Stacks.input_eq_layout] at r₁
  refine ⟨_, ((Exec.seq_max r₁ r₂).mono ?_), ?_⟩
  · have ha24 : a ^ 2 ≤ a ^ 4 := Nat.pow_le_pow_right ha1 (by norm_num)
    refine max_le ?_ ?_
    · calc C₁ * a ^ 2 ≤ C₁ * a ^ 4 := Nat.mul_le_mul_left _ ha24
        _ ≤ (C₁ + C₂ * C₁ ^ 2) * a ^ 4 := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    · calc C₂ * _ ≤ C₂ * (C₁ * a ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
        _ = C₂ * C₁ ^ 2 * a ^ 4 := by ring
        _ ≤ (C₁ + C₂ * C₁ ^ 2) * a ^ 4 := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · -- the output bit
    have hout : (Stacks.layout (max k₁ k₂) [x, Stacks.encList LX, Stacks.encList cs, eb,
        Stacks.encList LR, [gameValB LX.toFinset (fun z => costNum N (T.fn z) z.length) (binVal eb)
          (fun S => decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x))]]) ⟨5, by omega⟩ =
        [gameValB LX.toFinset (fun z => costNum N (T.fn z) z.length) (binVal eb)
          (fun S => decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x))] := rfl
    rw [hout, List.head?_cons, Option.some_inj, hLX, hE]
    have hfun : (fun S => decide (ClockedAccepts c e {z | z ∈ LR ∧ z ∉ S} x)) =
(gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (clock e x.length) \ Y)).outcome := by
      funext S
      change decide _ = decide _
      rw [decide_eq_decide]
      refine clockedAccepts_iff_of_agree c e _ _ x fun z hz => ?_
      simp only [Set.mem_ofPred_eq, oracleOf, hLR]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hz, h.1⟩, h.2⟩⟩
    rw [hfun, gameValB_gameOf_of_le c e T m x _ N (fun z hz => hN z (by
      rw [← hLX] at hz; exact List.mem_toFinset.1 hz)) hm, gameValB_gameOf]

/-! ### Specialisations: the exponential bound for every input, the polynomial bound for small
query sets

The programs of `exists_queryEnumStmt_gen`, `exists_prepStmt_gen` and `exists_evalStmt_gen` are the
programs of `exists_queryEnumStmt`, `exists_prepStmt` and `exists_evalStmt`.  The statements below
record, for one and the same program, the exponential bound of the original statements (from the
a priori bound `qBound_exp`) on every input and a polynomial bound in `|x| + clock e |x| + Q` on the
inputs whose query set has at most `Q` elements (from `qBound_of_card`). -/

/-- Arithmetic for the polynomial specialisation. -/
theorem qparam_pow_le (n T Q d : ℕ) :
    (n + T + Q * (2 * T + 1) + 1) ^ d ≤ 3 ^ d * (n + T + Q + 1) ^ (2 * d) := by
  calc (n + T + Q * (2 * T + 1) + 1) ^ d ≤ (3 * (n + T + Q + 1) ^ 2) ^ d :=
        Nat.pow_le_pow_left (qparam_le n T Q) d
    _ = 3 ^ d * (n + T + Q + 1) ^ (2 * d) := by rw [mul_pow, ← pow_mul]

/-- Arithmetic for the exponential specialisation. -/
theorem qparam_exp_le (K d n T : ℕ) :
    K * (n + T + (2 ^ (T + 1)) ^ 2 + 1) ^ d ≤ 2 ^ ((K + 3 * d) * (T + n + 1)) := by
  have ha1 : 1 ≤ T + n + 1 := by omega
  have h1 : n + T + 1 ≤ 2 ^ (T + n + 1) :=
    le_trans (by omega) (Nat.lt_two_pow_self (n := T + n + 1)).le
  have h2 : (2 ^ (T + 1)) ^ 2 ≤ 2 ^ (2 * (T + n + 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (T + n + 1) ≤ 2 ^ (2 * (T + n + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ≤ 2 ^ (T + n + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (T + n + 1) := Nat.pow_le_pow_right (by norm_num) ha1
  have h4 : n + T + (2 ^ (T + 1)) ^ 2 + 1 ≤ 2 ^ (3 * (T + n + 1)) := by
    have e3 : 2 ^ (3 * (T + n + 1)) = 2 ^ (2 * (T + n + 1)) * 2 ^ (T + n + 1) := by
      rw [← pow_add]; congr 1; ring
    have h6 := Nat.mul_le_mul_left (2 ^ (2 * (T + n + 1))) h5
    rw [e3]; omega
  have hK : K ≤ 2 ^ (K * (T + n + 1)) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  calc K * (n + T + (2 ^ (T + 1)) ^ 2 + 1) ^ d ≤
        2 ^ (K * (T + n + 1)) * (2 ^ (3 * (T + n + 1))) ^ d :=
        Nat.mul_le_mul hK (Nat.pow_le_pow_left h4 d)
    _ = 2 ^ ((K + 3 * d) * (T + n + 1)) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- **Enumeration of the query set in polynomial space.**  One program (the query enumeration
`QEnum.qeStmt` of `exists_queryEnumStmt`) runs on every input within the exponential space bound of
`exists_queryEnumStmt`, and within space `K · (|x| + clock e |x| + Q + 1) ^ 4` whenever the query
set has at most `Q` elements. -/
theorem exists_queryEnumStmt_poly (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (inp out : Fin k) (C K : ℕ), inp ≠ out ∧
      (∀ x : BitString, ∃ L : List BitString, L.Nodup ∧
        (∀ z, z ∈ L ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
        Exec s (Function.update (fun _ => []) inp x)
          (Function.update (Function.update (fun _ => []) inp x) out (Stacks.encList L))
          (2 ^ (C * (clock e x.length + x.length + 1)))) ∧
      ∀ (x : BitString) (Q : ℕ), (querySet c.toOTM x (clock e x.length)).card ≤ Q →
        ∃ L : List BitString, L.Nodup ∧
        (∀ z, z ∈ L ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
        Exec s (Function.update (fun _ => []) inp x)
          (Function.update (Function.update (fun _ => []) inp x) out (Stacks.encList L))
          (K * (x.length + clock e x.length + Q + 1) ^ 4) := by
  obtain ⟨k, s, inp, out, K, hio, hq⟩ := exists_queryEnumStmt_gen c e
  refine ⟨k, s, inp, out, K + 3 * 2, 3 ^ 2 * K, hio, fun x => ?_, fun x Q hQ => ?_⟩
  · obtain ⟨L, hnd, hmem, hex⟩ := hq x _ (qBound_exp c e x)
    exact ⟨L, hnd, hmem, hex.mono (qparam_exp_le K 2 x.length (clock e x.length))⟩
  · obtain ⟨L, hnd, hmem, hex⟩ := hq x _ (qBound_of_card c e x Q hQ)
    refine ⟨L, hnd, hmem, hex.mono ?_⟩
    calc K * (x.length + clock e x.length + Q * (2 * clock e x.length + 1) + 1) ^ 2
        ≤ K * (3 ^ 2 * (x.length + clock e x.length + Q + 1) ^ (2 * 2)) :=
          Nat.mul_le_mul_left _ (qparam_pow_le _ _ _ 2)
      _ = 3 ^ 2 * K * (x.length + clock e x.length + Q + 1) ^ 4 := by ring

/-- The contract of the preparation statement of `exists_prepStmt` at the space bound `B`: the
prepared game data (board `LX`, random possible queries `LR`, costs `cs`, budget `eb` at
precision `N` and width `W`) have total size `≤ B`, and the statement produces them within
space `B`. -/
def PrepContract (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) {k : ℕ}
    (s : Stmt k) (x : BitString) (B : ℕ) : Prop :=
  ∃ (LX LR cs : List BitString) (eb : BitString) (N W : ℕ),
    LX.Nodup ∧ LX.toFinset = querySet c.toOTM x (clock e x.length) \ Y ∧
    (∀ z, z ∈ LR ↔ z ∈ querySet c.toOTM x (clock e x.length) ∧ z.length ≤ T.fn z) ∧
    (∀ z ∈ LX, z.length - 1 ≤ N ∧ T.fn z ≤ N) ∧ m ≤ N ∧
    cs.length = LX.length ∧ (∀ b ∈ cs, b.length = W) ∧ eb.length = W ∧
    (∀ i < LX.length, binVal (cs.getD i []) =
      costNum N (T.fn (LX.getD i [])) (LX.getD i []).length) ∧
    binVal eb = 2 ^ (N - m) ∧
    binVal eb + (LX.map fun z => costNum N (T.fn z) z.length).sum < 2 ^ W ∧
    x.length + clock e x.length + (Stacks.encList LX).length + (Stacks.encList cs).length +
      eb.length + (Stacks.encList LR).length + 1 ≤ B ∧
    Exec s (Stacks.input k x)
      (Stacks.layout k [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR]) B

/-- The contract of the preparation statement is monotone in the space bound. -/
theorem PrepContract.mono {c : OTMCode} {e : ℕ} {T : Table} {m : ℕ} {Y : Finset BitString} {k : ℕ}
    {s : Stmt k} {x : BitString} {B B' : ℕ} (h : PrepContract c e T m Y s x B) (hB : B ≤ B') :
    PrepContract c e T m Y s x B' := by
  obtain ⟨LX, LR, cs, eb, N, W, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨LX, LR, cs, eb, N, W, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12.trans hB,
    h13.mono hB⟩

/-- **Preparation of the game data in polynomial space.**  One program (that of
`exists_prepStmt`) satisfies the contract of `exists_prepStmt` with the exponential bound on every
input, and with the bound `K · (|x| + clock e |x| + Q + 1) ^ 4` whenever the query set has at most
`Q` elements. -/
theorem exists_prepStmt_poly (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (C K : ℕ), 6 ≤ k ∧
      (∀ x : BitString, PrepContract c e T m Y s x (2 ^ (C * (clock e x.length + x.length + 1)))) ∧
      ∀ (x : BitString) (Q : ℕ), (querySet c.toOTM x (clock e x.length)).card ≤ Q →
        PrepContract c e T m Y s x (K * (x.length + clock e x.length + Q + 1) ^ 4) := by
  obtain ⟨k, s, K, hk, hprep⟩ := exists_prepStmt_gen c e T m Y
  refine ⟨k, s, K + 3 * 2, 3 ^ 2 * K, hk, fun x => ?_, fun x Q hQ => ?_⟩
  · exact PrepContract.mono (hprep x _ (qBound_exp c e x))
      (qparam_exp_le K 2 x.length (clock e x.length))
  · refine PrepContract.mono (hprep x _ (qBound_of_card c e x Q hQ)) ?_
    calc K * (x.length + clock e x.length + Q * (2 * clock e x.length + 1) + 1) ^ 2
        ≤ K * (3 ^ 2 * (x.length + clock e x.length + Q + 1) ^ (2 * 2)) :=
          Nat.mul_le_mul_left _ (qparam_pow_le _ _ _ 2)
      _ = 3 ^ 2 * K * (x.length + clock e x.length + Q + 1) ^ 4 := by ring

/-- **The evaluation program in polynomial space.**  One program (that of `exists_evalStmt`)
leaves the value of the game on its output stack, within the exponential space bound of
`exists_evalStmt` on every input, and within space `K · (|x| + clock e |x| + Q + 1) ^ 8` whenever
the query set has at most `Q` elements. -/
theorem exists_evalStmt_poly (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (out : Fin k) (C K : ℕ),
      (∀ x : BitString, ∃ σ' : Stacks k,
        Exec s (Stacks.input k x) σ' (2 ^ (C * (clock e x.length + x.length + 1))) ∧
        ((σ' out).head? = some true ↔
          gameValB (querySet c.toOTM x (clock e x.length) \ Y)
            (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
            (2 ^ (gameN e T m x.length - m))
            (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
              (querySet c.toOTM x (clock e x.length) \ Y)).outcome = true)) ∧
      ∀ (x : BitString) (Q : ℕ), (querySet c.toOTM x (clock e x.length)).card ≤ Q →
        ∃ σ' : Stacks k,
        Exec s (Stacks.input k x) σ' (K * (x.length + clock e x.length + Q + 1) ^ 8) ∧
        ((σ' out).head? = some true ↔
          gameValB (querySet c.toOTM x (clock e x.length) \ Y)
            (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
            (2 ^ (gameN e T m x.length - m))
            (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
              (querySet c.toOTM x (clock e x.length) \ Y)).outcome = true) := by
  obtain ⟨k, s, out, K, hs⟩ := exists_evalStmt_gen c e T m Y
  refine ⟨k, s, out, K + 3 * 4, 3 ^ 4 * K, fun x => ?_, fun x Q hQ => ?_⟩
  · obtain ⟨σ', hex, hout⟩ := hs x _ (qBound_exp c e x)
    exact ⟨σ', hex.mono (qparam_exp_le K 4 x.length (clock e x.length)), hout⟩
  · obtain ⟨σ', hex, hout⟩ := hs x _ (qBound_of_card c e x Q hQ)
    refine ⟨σ', hex.mono ?_, hout⟩
    calc K * (x.length + clock e x.length + Q * (2 * clock e x.length + 1) + 1) ^ 4
        ≤ K * (3 ^ 4 * (x.length + clock e x.length + Q + 1) ^ (2 * 4)) :=
          Nat.mul_le_mul_left _ (qparam_pow_le _ _ _ 4)
      _ = 3 ^ 4 * K * (x.length + clock e x.length + Q + 1) ^ 8 := by ring

/-! ### The game-evaluation program in polynomial space -/

/-- **The game-evaluation program with parametric space bound.**  One stack program (the program
of `exists_gameProg`) decides the value of the game; on every input `x` it halts within space
`C · (|x| + clock e |x| + BB + 1) ^ 4` for every bound `BB` on the codes of duplicate-free lists
of possible queries (`QBound`).  With `qBound_exp` it halts on every input. -/
theorem exists_gameProg_gen (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (P : Prog) (C : ℕ), (∀ x : BitString, x ∈ P.Lang ↔ val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clock e x.length) \ Y)) = true) ∧
      ∀ (x : BitString) (BB : ℕ), QBound c e x BB →
        ∃ t, P.Halted (P.run x t) ∧
          ∀ u ≤ t, (P.run x u).space ≤ C * (x.length + clock e x.length + BB + 1) ^ 4 := by
  obtain ⟨k, s, out, C, hs⟩ := exists_evalStmt_gen c e T m Y
  refine ⟨s.toProg out, C, fun x => ?_, fun x BB hB => ?_⟩
  · obtain ⟨σ', hσ', hout⟩ := hs x _ (qBound_exp c e x)
    obtain ⟨t, ht, -, hacc⟩ := s.toProg_spec out x σ' _ hσ'
    rw [Prog.mem_lang_iff_of_halted _ x t ht, hacc, hout, gameValB_gameOf]
  · obtain ⟨σ', hσ', -⟩ := hs x BB hB
    obtain ⟨t, ht, hsp, -⟩ := s.toProg_spec out x σ' _ hσ'
    exact ⟨t, ht, hsp⟩

/-- **The game-evaluation program runs in space polynomial in `|x| + clock e |x| + |querySet|`.**
The only exponential ingredient of `gameValue_mem_EXPSPACE` is the a priori bound
`|querySet| ≤ 2 ^ (clock e |x| + 1)` (`QEnum.length_le_of_nodup`). -/
theorem exists_gameProg_poly (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (P : Prog) (K : ℕ), (∀ x : BitString, x ∈ P.Lang ↔ val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
        (querySet c.toOTM x (clock e x.length) \ Y)) = true) ∧
      ∀ x : BitString, ∃ t, P.Halted (P.run x t) ∧ ∀ u ≤ t, (P.run x u).space ≤
K * (x.length + clock e x.length +
          (querySet c.toOTM x (clock e x.length)).card + 1) ^ 8 := by
  obtain ⟨P, C, hlang, hsp⟩ := exists_gameProg_gen c e T m Y
  refine ⟨P, 3 ^ 4 * C, hlang, fun x => ?_⟩
  obtain ⟨t, ht, hs⟩ := hsp x _ (qBound_of_card c e x _ le_rfl)
  refine ⟨t, ht, fun u hu => (hs u hu).trans ?_⟩
  calc C * (x.length + clock e x.length +
        (querySet c.toOTM x (clock e x.length)).card * (2 * clock e x.length + 1) + 1) ^ 4
      ≤ C * (3 ^ 4 * (x.length + clock e x.length +
          (querySet c.toOTM x (clock e x.length)).card + 1) ^ (2 * 4)) :=
        Nat.mul_le_mul_left _ (qparam_pow_le _ _ _ 4)
    _ = 3 ^ 4 * C * (x.length + clock e x.length +
          (querySet c.toOTM x (clock e x.length)).card + 1) ^ 8 := by ring

/-- **Claim 4, polynomial-space case, general form.**  If outside a finite set `Z` of inputs
the clocked machine `(c, e)` has at most `q(|x|)` possible queries for a polynomial `q`, then the
set of inputs on which the YES player wins the game is in `PSPACE`. -/
theorem gameValue_mem_PSPACE_of_poly (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ)
    (Y : Finset BitString)
    (Z : Finset BitString) (q : Polynomial ℕ)
    (hsmall : ∀ x, x ∉ Z →
        (querySet c.toOTM x (clock e x.length)).card ≤ q.eval x.length) :
    {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ PSPACE := by
  obtain ⟨P, C, hlang, hsp⟩ := exists_gameProg_gen c e T m Y
  have hset : P.Lang = {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} := Set.ext fun x => hlang x
  rw [← hset]
  let p : Polynomial ℕ := Polynomial.C C * (Polynomial.X + (Polynomial.X ^ e + Polynomial.C e) +
      q * (2 * (Polynomial.X ^ e + Polynomial.C e) + 1) + 1) ^ 4
  have hpev : ∀ n : ℕ,
      p.eval n = C * (n + clock e n + q.eval n * (2 * clock e n + 1) + 1) ^ 4 := by
    intro n
    simp [p, clock]
  refine Prog.lang_mem_PSPACE P p Z (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨t, ht, -⟩ := hsp x _ (qBound_exp c e x)
    exact ⟨t, ht⟩
  · obtain ⟨t, ht, hs⟩ := hsp x _ (qBound_of_card c e x _ (hsmall x hx))
    refine ⟨t, ht, fun u hu => ?_⟩
    rw [hpev]
    exact hs u hu

/-- **Claim 4, polynomial-space case.**  If outside a finite set `Z` of inputs the clocked
machine `(c, e)` has at most `clock e |x| + 1` possible queries (e.g. a non-adaptive machine),
then the set of inputs on which the YES player wins the game is in `PSPACE`. -/
theorem gameValue_mem_PSPACE (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString)
    (Z : Finset BitString)
    (hsmall : ∀ x, x ∉ Z → (querySet c.toOTM x (clock e x.length)).card ≤ clock e x.length + 1) :
    {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
      (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ PSPACE :=
  gameValue_mem_PSPACE_of_poly c e T m Y Z (Polynomial.X ^ e + Polynomial.C e + 1) fun x hx => by
    simpa [clock] using hsmall x hx

/-- The hypothesis `hgame` of the general theorem for the class `PSPACE`, for any family of
machines whose membership property `Φ` bounds the query set by `clock e |x| + 1` (e.g. the
non-adaptive machines). -/
theorem gameValue_mem_PSPACE_of_family (Φ : OTMCode → ℕ → BitString → Prop)
    (hΦ : ∀ c e x, Φ c e x →
      (querySet c.toOTM x (clock e x.length)).card ≤ clock e x.length + 1) :
    ∀ (c : OTMCode) (e : ℕ) (Z : Finset BitString), (∀ x, x ∉ Z → Φ c e x) →
      ∀ (T : Table) (m : ℕ) (Y : Finset BitString),
        {x : BitString | val (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
          (querySet c.toOTM x (clock e x.length) \ Y)) = true} ∈ PSPACE :=
  fun c e Z hZ T m Y => gameValue_mem_PSPACE c e T m Y Z fun x hx => hΦ c e x (hZ x hx)

end Kolmogorov.RandomStrings
