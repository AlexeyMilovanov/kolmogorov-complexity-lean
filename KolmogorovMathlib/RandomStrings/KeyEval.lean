/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.KeyEval.Table
import KolmogorovMathlib.RandomStrings.KeyEval.Plumbing

/-!
# The value-iteration driver of the EXP evaluator

The evaluator computes `valKC (allBits L) dec X P out c E F` (`KeyCodes.lean`, `KeySlots.lean`)
by layered value iteration: a table with one bit per triple `(κ, y, n)` (a key code of `L` bits
and two scores `< 2 ^ W`) holds the current layer; one layer step replaces it by `stepKC` of the
old table, and the answer is read off the last layer (`valKC_eq_of_layer`).

This file fixes the **table representation** and proves the **semantic half of the driver**:
* the table is a bit string of length `2 ^ (L + (W + W))`; the entry of `(κ, y, n)` is at the
  position `binVal (κ ++ bitsOf W y ++ bitsOf W n)` (`idxStr`, `tabRead`): the index string is the
  key code followed by the two scores, least significant bit first, so a counter over all bit
  strings of length `L + 2W` (`Stmt.incr`) enumerates exactly the triples;
* the layer step `tabNext` (entry `i` is the step function at the decoded triple of `i`) and its
  read-back `tabRead_tabNext`, the first layer `tabInit` (`tabRead_tabInit`), the iteration
  `tabIter`;
* versions of `stepKC_congr`/`layer_eq_yesKC`/`valKC_eq_of_layer` that only need agreement on the
  codes of the list (`stepKC_congr_mem`, `layer_eq_yesKC_mem`, `valKC_eq_of_layer_mem`: the
  table is only meaningful on key codes of length `L`);
* **`valKC_eq_tabIter`**: for `E < 2 ^ W`, `valKC (allBits L) …` is the read-off of the `F`-th
  table iterate; **`valKCLang_eq_tabIter`** instantiates it to the evaluator target `valKCLang`.

The program half (statements on stacks, `Exec`/`ExecLe` specifications of the table walk, the
layer loop and the main loop, parametrised by the key routines) is developed in `KeyEval.Table`
(the table and its loops) and `KeyEval.Plumbing` (the plumbing routines); this module contains
the self-cleaning budget test and the driver's logic in the program's terms.
-/

namespace Kolmogorov.RandomStrings

namespace KeyEval

/-! ### A self-cleaning budget test -/

/-- A budget test (self-cleaning): with `bitsOf W y` on `f 0` and `bitsOf W E` on `f 2`, run the
cost routine on the keys on `K`, `K'` (result `bitsOf W num` on `f 1`), add and compare by the
inlined `scoreStmt`, and clear the sum on `f 3`: the bit `[y + num ≤ E]` is left on `f 4`. -/
def costTest {k : ℕ} (K K' A A' t : Fin k) (f : Fin 9 → Fin k) (s : Stmt k) : Stmt k :=
  .seq (callPair K K' A A' t s) (.seq (scoreStmt.rename f) (Stmt.clear (f 3)))

/-- The stack layout of the cost test: the key stacks `K`, `K'`, the argument stacks `A`, `A'`,
the guard `t` and the input stack `I` are separated as `execLe_callPair` requires, `f` is
injective, the result stack `f 1` avoids `A` and `A'`, and `A`, `A'` lie below `kR`, the first
scratch stack of the pair routine. -/
structure CostFrame {k : ℕ} (K K' A A' t I : Fin k) (f : Fin 9 → Fin k) (kR : ℕ) : Prop where
  /-- The nine stacks `f 0, …, f 8` are distinct. -/
  hf : Function.Injective f
  /-- The first key stack `K` is not the first argument stack `A`. -/
  hKA : K ≠ A
  /-- The first key stack `K` is not the guard `t`. -/
  hKt : K ≠ t
  /-- The first argument stack `A` is not the guard `t`. -/
  hAt : A ≠ t
  /-- The second key stack `K'` is not the second argument stack `A'`. -/
  hK'A' : K' ≠ A'
  /-- The second key stack `K'` is not the guard `t`. -/
  hK't : K' ≠ t
  /-- The second argument stack `A'` is not the guard `t`. -/
  hA't : A' ≠ t
  /-- The second key stack `K'` is not the first argument stack `A`. -/
  hK'A : K' ≠ A
  /-- The two argument stacks `A` and `A'` are distinct. -/
  hAA' : A ≠ A'
  /-- The input stack `I` is not the first argument stack `A`. -/
  hIA : I ≠ A
  /-- The input stack `I` is not the second argument stack `A'`. -/
  hIA' : I ≠ A'
  /-- The result stack `f 1` is not the first argument stack `A`. -/
  hFA : f 1 ≠ A
  /-- The result stack `f 1` is not the second argument stack `A'`. -/
  hFA' : f 1 ≠ A'
  /-- The first argument stack `A` is not a scratch stack (it lies below `kR`). -/
  hAk : A.val < kR
  /-- The second argument stack `A'` is not a scratch stack (it lies below `kR`). -/
  hA'k : A'.val < kR

/-- The entry state of the cost test: the input `x` is on `I`, the argument stacks `A`, `A'`, the
guard `t` and the stacks `f 1`, `f 3`, …, `f 7` are empty, the keys on `K`, `K'` have `L` bits,
`bitsOf W y` is on `f 0` and `bitsOf W E` on `f 2`, every scratch stack (from `kR` on) is empty,
and `y ≤ E`, `num (σ K) (σ K') ≤ E + 1` and `2 * E + 2 ≤ 2 ^ W`. -/
structure CostEntry {k : ℕ} (σ : Stacks k) (K K' A A' t I : Fin k) (f : Fin 9 → Fin k)
    (num : BitString → BitString → ℕ) (x : BitString) (L W kR y E : ℕ) : Prop where
  /-- The input stack `I` holds `x`. -/
  hI : σ I = x
  /-- The first argument stack `A` is empty. -/
  hA : σ A = []
  /-- The second argument stack `A'` is empty. -/
  hA' : σ A' = []
  /-- The guard `t` is empty. -/
  ht : σ t = []
  /-- The key on `K` has `L` bits. -/
  hK : (σ K).length = L
  /-- The key on `K'` has `L` bits. -/
  hK' : (σ K').length = L
  /-- Every scratch stack (from `kR` on) is empty. -/
  hw : ∀ j : Fin k, kR ≤ j.val → σ j = []
  /-- The stack `f 0` holds the score `y` in `W` bits. -/
  h0 : σ (f 0) = bitsOf W y
  /-- The result stack `f 1` of the cost routine is empty. -/
  h1 : σ (f 1) = []
  /-- The stack `f 2` holds the budget `E` in `W` bits. -/
  h2 : σ (f 2) = bitsOf W E
  /-- The sum stack `f 3` is empty. -/
  h3 : σ (f 3) = []
  /-- The bit stack `f 4` is empty. -/
  h4 : σ (f 4) = []
  /-- The first work stack `f 5` of the score step is empty. -/
  h5 : σ (f 5) = []
  /-- The second work stack `f 6` of the score step is empty. -/
  h6 : σ (f 6) = []
  /-- The third work stack `f 7` of the score step is empty. -/
  h7 : σ (f 7) = []
  /-- The score `y` is within the budget `E`. -/
  hy : y ≤ E
  /-- The number `num (σ K) (σ K')` computed by the cost routine is at most `E + 1`. -/
  hnum : num (σ K) (σ K') ≤ E + 1
  /-- The sum of a score and a saturated cost fits in `W` bits. -/
  hE : 2 * E + 2 ≤ 2 ^ W

/-- **The budget test.** In the layout `CostFrame` and from the entry state `CostEntry`
(`bitsOf W y` on `f 0`, `bitsOf W E` on `f 2`, the keys on `K`, `K'`), `costTest` leaves the bit
`decide (y + num (σ K) (σ K') ≤ E)` on `f 4` and changes no other stack, within the stated space
and step budget. -/
theorem execLe_costTest {k : ℕ} {K K' A A' t I : Fin k} {f : Fin 9 → Fin k}
    {s : Stmt k} {x : BitString} {L W kR B : ℕ} {num : BitString → BitString → ℕ}
    (hF : CostFrame K K' A A' t I f kR) (hs : PairNumRoutine s x L W kR I A A' (f 1) B num)
    {σ : Stacks k} {y E : ℕ} (hσ : CostEntry σ K K' A A' t I f num x L W kR y E) :
    ExecLe (costTest K K' A A' t f s) σ
      (Function.update σ (f 4) [decide (y + num (σ K) (σ K') ≤ E)])
      (σ.space + L + L + B + 3 * W + 2)
      (13 * (σ.space + L) + 2 + (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1)))) +
        (scoreStmt.budget (σ.space + L + L + B + 3 * W + 2) + (3 * W + 1))) := by
  obtain ⟨hf, hKA, hKt, hAt, hK'A', hK't, hA't, hK'A, hAA', hIA, hIA', hFA, hFA', hAk,
    hA'k⟩ := hF
  obtain ⟨hI, hA, hA', ht, hK, hK', hw, h0, h1, h2, h3, h4, h5, h6, h7, hy, hnum, hE⟩ := hσ
  have e1 := execLe_callPair hKA hKt hAt hK'A' hK't hA't hK'A hAA' hIA hIA' hFA hFA'
    hs.pair hAk hA'k hI hA hA' ht h1 hK hK' hw
  have sp1 := e1.toExec.space_le.2
  set σ1 := Function.update σ (f 1) (bitsOf W (num (σ K) (σ K'))) with hσ1
  have hne : ∀ i j : Fin 9, i ≠ j → f i ≠ f j := fun i j h e => h (hf e)
  have g0 : σ1 (f 0) = bitsOf W y := by
    rw [hσ1, Function.update_of_ne (hne 0 1 (by decide)), h0]
  have g1 : σ1 (f 1) = bitsOf W (num (σ K) (σ K')) := by rw [hσ1, Function.update_self]
  have g2 : σ1 (f 2) = bitsOf W E := by
    rw [hσ1, Function.update_of_ne (hne 2 1 (by decide)), h2]
  have gj : ∀ j : Fin 9, j ≠ 1 → σ (f j) = [] → σ1 (f j) = [] := fun j hj h => by
    rw [hσ1, Function.update_of_ne (hne j 1 hj), h]
  have hyW : y < 2 ^ W := by omega
  have hnW : num (σ K) (σ K') < 2 ^ W := by omega
  have hEW : E < 2 ^ W := by omega
  have e2 := execLe_scoreK_budget hf g0 g1 g2 (gj 3 (by decide) h3) (gj 4 (by decide) h4)
    (gj 5 (by decide) h5) (gj 6 (by decide) h6) (gj 7 (by decide) h7)
    (by rw [length_bitsOf, length_bitsOf]) (by rw [length_bitsOf, length_bitsOf])
    (by rw [binVal_bitsOf_of_lt hyW, binVal_bitsOf_of_lt hnW, length_bitsOf]; omega)
  rw [length_bitsOf, binVal_bitsOf_of_lt hyW, binVal_bitsOf_of_lt hnW,
    binVal_bitsOf_of_lt hEW] at e2
  have sp2 := e2.toExec.space_le.2
  set σ2 := Function.update (Function.update (Function.update σ1 (f 1) []) (f 3)
    (addBits false (bitsOf W y) (bitsOf W (num (σ K) (σ K'))))) (f 4)
    [decide (y + num (σ K) (σ K') ≤ E)] with hσ2
  have h23 : σ2 (f 3) = addBits false (bitsOf W y) (bitsOf W (num (σ K) (σ K'))) := by
    rw [hσ2, Function.update_of_ne (hne 3 4 (by decide)), Function.update_self]
  have e3 := Stmt.execT_clear (f 3) _ σ2 h23
  rw [length_addBits false _ _ (by rw [length_bitsOf, length_bitsOf]), length_bitsOf] at e3
  have hfin : Function.update σ2 (f 3) [] =
      Function.update σ (f 4) [decide (y + num (σ K) (σ K') ≤ E)] := by
    funext r
    by_cases r4 : r = f 4
    · subst r4
      rw [Function.update_of_ne (hne 4 3 (by decide)), hσ2, Function.update_self,
        Function.update_self]
    · rw [Function.update_of_ne r4]
      by_cases r3 : r = f 3
      · subst r3; rw [Function.update_self, h3]
      · rw [Function.update_of_ne r3, hσ2, Function.update_of_ne r4, Function.update_of_ne r3]
        by_cases r1 : r = f 1
        · subst r1; rw [Function.update_self, h1]
        · rw [Function.update_of_ne r1, hσ1, Function.update_of_ne r1]
  rw [hfin] at e3
  have hS1 : Stacks.space σ1 + 3 * W + 2 ≤ σ.space + L + L + B + 3 * W + 2 := by omega
  have e2' := (e2.mono hS1).mono_time (budget_mono scoreStmt hS1)
  exact (e1.mono (by omega)).seq (e2'.seq ((ExecLe.of_execT e3).mono (by omega)))

/-- A self-cleaning comparison test: `G := [y ≤ E]` from `bitsOf W y` on `Y` and `bitsOf W E` on
`Eb` (both kept), through the empty work stacks `T1`, `T2`, `t` (the guard of the layer body). -/
def leTest {k : ℕ} (Y Eb T1 T2 t G : Fin k) : Stmt k :=
  .seq (Stmt.copy Y T1 t) (.seq (Stmt.copy Eb T2 t) (Stmt.cmpInto T1 T2 G))

/-- **The comparison test.** With `bitsOf W y` on `Y`, `bitsOf W E` on `Eb` (both kept) and the
stacks `T1`, `T2`, `t`, `G` empty, `leTest` leaves the bit `decide (y ≤ E)` on `G` and changes no
other stack, within space `σ.space + 2 * W + 1` and `40 * (σ.space + 2 * W + 1)` steps. -/
theorem execLe_leTest {k : ℕ} {Y Eb T1 T2 t G : Fin k} (hYT1 : Y ≠ T1) (hYt : Y ≠ t)
    (hT1t : T1 ≠ t) (hEbT2 : Eb ≠ T2) (hEbt : Eb ≠ t) (hT2t : T2 ≠ t) (hT1T2 : T1 ≠ T2)
    (hT1G : T1 ≠ G) (hT2G : T2 ≠ G) (hEbT1 : Eb ≠ T1) (htG : t ≠ G)
    {σ : Stacks k} {W y E : ℕ} (hY : σ Y = bitsOf W y) (hEb : σ Eb = bitsOf W E)
    (h1 : σ T1 = []) (h2 : σ T2 = []) (ht : σ t = []) (hG : σ G = []) (hy : y < 2 ^ W)
    (hE : E < 2 ^ W) :
    ExecLe (leTest Y Eb T1 T2 t G) σ (Function.update σ G [decide (y ≤ E)])
      (σ.space + 2 * W + 1) (40 * (σ.space + 2 * W + 1)) := by
  have e1 := Stmt.execLe_copy_budget hYT1 hYt hT1t ht (σ := σ)
  rw [hY, h1, List.append_nil, length_bitsOf] at e1
  have sp1 := e1.toExec.space_le.2
  set σ1 := Function.update σ T1 (bitsOf W y) with hσ1
  have g1t : σ1 t = [] := by rw [hσ1, Function.update_of_ne hT1t.symm, ht]
  have e2 := Stmt.execLe_copy_budget hEbT2 hEbt hT2t g1t
  have g1Eb : σ1 Eb = bitsOf W E := by rw [hσ1, Function.update_of_ne hEbT1, hEb]
  have g1T2 : σ1 T2 = [] := by rw [hσ1, Function.update_of_ne hT1T2.symm, h2]
  rw [g1Eb, g1T2, List.append_nil, length_bitsOf] at e2
  have sp2 := e2.toExec.space_le.2
  set σ2 := Function.update σ1 T2 (bitsOf W E) with hσ2
  have g2T1 : σ2 T1 = bitsOf W y := by
    rw [hσ2, Function.update_of_ne hT1T2, hσ1, Function.update_self]
  have g2T2 : σ2 T2 = bitsOf W E := by rw [hσ2, Function.update_self]
  have g2G : σ2 G = [] := by
    rw [hσ2, Function.update_of_ne hT2G.symm, hσ1, Function.update_of_ne hT1G.symm, hG]
  have e3 := Stmt.execLe_cmpInto hT1T2 hT1G hT2G (by rw [length_bitsOf, length_bitsOf]) g2T1 g2T2
    g2G
  have hb : cmpBits true (bitsOf W y) (bitsOf W E) = decide (y ≤ E) := by
    rw [Bool.eq_iff_iff, cmpBits_true_iff _ _ (by rw [length_bitsOf, length_bitsOf]),
      binVal_bitsOf_of_lt hy, binVal_bitsOf_of_lt hE, decide_eq_true_iff]
  rw [hb] at e3
  have hfin : Function.update (Function.update (Function.update σ2 T1 []) T2 []) G
      [decide (y ≤ E)] = Function.update σ G [decide (y ≤ E)] := by
    funext r
    by_cases rG : r = G
    · subst rG; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne rG, Function.update_of_ne rG]
      by_cases r2 : r = T2
      · subst r2; rw [Function.update_self, h2]
      · rw [Function.update_of_ne r2]
        by_cases r1 : r = T1
        · subst r1; rw [Function.update_self, h1]
        · rw [Function.update_of_ne r1, hσ2, Function.update_of_ne r2, hσ1,
            Function.update_of_ne r1]
  rw [hfin] at e3
  exact ((e1.mono (by omega)).seq ((e2.mono (by omega)).seq (e3.mono (by omega)))).mono_time
    (by omega)

/-- Look up the index string `ρ ++ yb ++ nb` (on `g 0`, `g 1`, `g 2`, kept) in the list table on
`h 1`: join it on `g 3 = h 0`, `tabLookup` into `h 2`, clear `h 0`. -/
def lookupJoin {k : ℕ} (g h : Fin 9 → Fin k) : Stmt k :=
  .seq (joinStmt.rename g) (.seq (tabLookup h) (Stmt.clear (h 0)))

/-- The entry state of the table lookup: the join target `g 3` and its work stack `g 4` are
empty, the stack `h 1` holds the list table `Ls` and the stacks `h 2, …, h 8` are empty. -/
structure LookupEntry {k : ℕ} (σ : Stacks k) (g h : Fin 9 → Fin k) (Ls : List BitString) :
    Prop where
  /-- The join target `g 3` is empty. -/
  hg3 : σ (g 3) = []
  /-- The work stack `g 4` of the join is empty. -/
  hg4 : σ (g 4) = []
  /-- The stack `h 1` holds the list table `Ls`. -/
  hT : σ (h 1) = Stacks.encList Ls
  /-- The bit stack `h 2` is empty. -/
  hG : σ (h 2) = []
  /-- The first work stack `h 3` of the table lookup is empty. -/
  hw3 : σ (h 3) = []
  /-- The second work stack `h 4` of the table lookup is empty. -/
  hw4 : σ (h 4) = []
  /-- The third work stack `h 5` of the table lookup is empty. -/
  hw5 : σ (h 5) = []
  /-- The fourth work stack `h 6` of the table lookup is empty. -/
  hw6 : σ (h 6) = []
  /-- The fifth work stack `h 7` of the table lookup is empty. -/
  hw7 : σ (h 7) = []
  /-- The sixth work stack `h 8` of the table lookup is empty. -/
  hw8 : σ (h 8) = []

/-- **The lookup step.** From the entry state `LookupEntry` (the list table `Ls` on `h 1`),
`lookupJoin g h` leaves the bit `decide (σ (g 0) ++ σ (g 1) ++ σ (g 2) ∈ Ls)` on `h 2` and
changes no other stack, within the stated space and step budget. -/
theorem execLe_lookupJoin {k : ℕ} {g h : Fin 9 → Fin k} (hg : Function.Injective g)
    (hh : Function.Injective h) (hgh : h 0 = g 3) {σ : Stacks k} {Ls : List BitString}
    (hL : LookupEntry σ g h Ls) :
    ExecLe (lookupJoin g h) σ
      (Function.update σ (h 2) [decide (σ (g 0) ++ σ (g 1) ++ σ (g 2) ∈ Ls)])
      (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2)
      (joinStmt.budget (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length) +
        (57 * (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
          (Stacks.encList Ls).length + 2) * (σ.space + (σ (g 0)).length + (σ (g 1)).length +
          (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
          29 * (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
            (Stacks.encList Ls).length + 2) + 3) +
        (3 * ((σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length) + 1)) := by
  obtain ⟨h3, h4, hT, hG, hw3, hw4, hw5, hw6, hw7, hw8⟩ := hL
  have hne : ∀ i j : Fin 9, i ≠ j → h i ≠ h j := fun i j hij e => hij (hh e)
  have e1 := execLe_joinK_budget hg h3 h4
  have sp1 := e1.toExec.space_le.2
  set idx := σ (g 0) ++ σ (g 1) ++ σ (g 2) with hidx
  set σ1 := Function.update σ (g 3) idx with hσ1
  have g1 : ∀ j : Fin 9, j ≠ 0 → σ1 (h j) = σ (h j) := fun j hj => by
    rw [hσ1, Function.update_of_ne (by rw [← hgh]; exact hne j 0 hj)]
  have e2 := exec_tabLookup hh (τ := σ1) (Ls := Ls) (by rw [g1 1 (by decide), hT])
    (by rw [g1 2 (by decide), hG]) (by rw [g1 3 (by decide), hw3]) (by rw [g1 4 (by decide), hw4])
    (by rw [g1 5 (by decide), hw5]) (by rw [g1 6 (by decide), hw6]) (by rw [g1 7 (by decide), hw7])
    (by rw [g1 8 (by decide), hw8])
  have h10 : σ1 (h 0) = idx := by rw [hσ1, hgh, Function.update_self]
  rw [h10] at e2
  have sp2 := e2.toExec.space_le.2
  set σ2 := Function.update σ1 (h 2) [decide (idx ∈ Ls)] with hσ2
  have h20 : σ2 (h 0) = idx := by rw [hσ2, Function.update_of_ne (hne 0 2 (by decide)), h10]
  have e3 := Stmt.execT_clear (h 0) _ σ2 h20
  have hfin : Function.update σ2 (h 0) [] = Function.update σ (h 2) [decide (idx ∈ Ls)] := by
    funext r
    by_cases r0 : r = h 0
    · subst r0
      rw [Function.update_self, Function.update_of_ne (hne 0 2 (by decide)), hgh, h3]
    · rw [Function.update_of_ne r0, hσ2]
      by_cases r2 : r = h 2
      · subst r2; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne r2, Function.update_of_ne r2, hσ1,
          Function.update_of_ne (by rw [← hgh]; exact r0)]
  rw [hfin] at e3
  have hidxl : idx.length = (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length := by
    rw [hidx, List.length_append, List.length_append]
  rw [hidxl] at e3
  have hsp1 : Stacks.space σ1 ≤ σ.space + (σ (g 0)).length + (σ (g 1)).length +
      (σ (g 2)).length := sp1
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 57 (Nat.add_le_add_right
    (Nat.add_le_add_right hsp1 (Stacks.encList Ls).length) 2))
    (Nat.add_le_add_right (Nat.add_le_add_right hsp1 (Stacks.encList Ls).length) 2)
  have e2' : ExecLe (tabLookup h) σ1 σ2
      (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2)
      (57 * (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
          (Stacks.encList Ls).length + 2) * (σ.space + (σ (g 0)).length + (σ (g 1)).length +
          (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
          29 * (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
            (Stacks.encList Ls).length + 2) + 3) :=
    (e2.mono (by omega)).mono_time (by omega)
  have e3' : ExecLe (Stmt.clear (h 0)) σ2 (Function.update σ (h 2) [decide (idx ∈ Ls)])
      (σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2)
      (3 * ((σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length) + 1) :=
    (ExecLe.of_execT e3).mono (by omega)
  have e1' := e1.mono (show σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length ≤
    σ.space + (σ (g 0)).length + (σ (g 1)).length + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2 by omega)
  exact (e1'.seq (e2'.seq e3')).mono_time (by omega)

/-- Adding the `W`-bit encodings of `a` and `b` (least significant bit first, carry in `false`)
gives the `W`-bit encoding of `a + b`, provided that `a + b < 2 ^ W`. -/
theorem addBits_bitsOf {W a b : ℕ} (h : a + b < 2 ^ W) :
    addBits false (bitsOf W a) (bitsOf W b) = bitsOf W (a + b) := by
  have hl : (bitsOf W a).length = (bitsOf W b).length := by rw [length_bitsOf, length_bitsOf]
  rw [← bitsOf_binVal (addBits false (bitsOf W a) (bitsOf W b)), length_addBits false _ _ hl,
    length_bitsOf, binVal_addBits_of_lt _ _ hl (by
      rw [length_bitsOf, binVal_bitsOf_of_lt (by omega), binVal_bitsOf_of_lt (by omega)]; exact h),
    binVal_bitsOf_of_lt (by omega), binVal_bitsOf_of_lt (by omega)]

/-- The lookup test of the layer body (self-cleaning): run the cost routine on the keys on `K`,
`K'` (to `f 1`), add `bitsOf W y` (on `f 0`) by the inlined `scoreStmt` (sum on `f 3 = g 1`),
clear its bit on `f 4`, look up `σ (g 0) ++ bitsOf W (y + num) ++ σ (g 2)` in the table on `h 1`
(`lookupJoin`, bit on `h 2`), clear the sum. -/
def sumLookup {k : ℕ} (K K' A A' t : Fin k) (f g h : Fin 9 → Fin k) (s : Stmt k) : Stmt k :=
  .seq (callPair K K' A A' t s) (.seq (scoreStmt.rename f) (.seq (Stmt.clear (f 4))
    (.seq (lookupJoin g h) (Stmt.clear (f 3)))))

/-- The stack layout of the lookup phase of `sumLookup`: `g` and `h` are injective, the joined
index string is built on `g 3 = h 0`, the sum of the score and the cost lies on `g 1 = f 3`, and
no stack of `h` is the sum stack `f 3`. -/
structure JoinFrame {k : ℕ} (f g h : Fin 9 → Fin k) : Prop where
  /-- The nine stacks `g 0, …, g 8` are distinct. -/
  hg : Function.Injective g
  /-- The nine stacks `h 0, …, h 8` are distinct. -/
  hh : Function.Injective h
  /-- The table lookup reads the joined index string, `h 0 = g 3`. -/
  hgh : h 0 = g 3
  /-- The middle part of the index string is the sum stack, `g 1 = f 3`. -/
  hgf : g 1 = f 3
  /-- No stack `h j` of the table lookup is the sum stack `f 3`. -/
  hhf : ∀ j : Fin 9, h j ≠ f 3

/-- **The lookup test.** In the layouts `CostFrame` and `JoinFrame` and from the entry states
`CostEntry` and `LookupEntry`, `sumLookup` leaves the bit
`decide (σ (g 0) ++ bitsOf W (y + num (σ K) (σ K')) ++ σ (g 2) ∈ Ls)` on `h 2` and changes no
other stack, within the stated space and step budget. -/
theorem execLe_sumLookup {k : ℕ} {K K' A A' t I : Fin k} {f g h : Fin 9 → Fin k}
    {s : Stmt k} {x : BitString} {L W kR B : ℕ} {num : BitString → BitString → ℕ}
    (hF : CostFrame K K' A A' t I f kR) (hJ : JoinFrame f g h)
    (hs : PairNumRoutine s x L W kR I A A' (f 1) B num)
    {σ : Stacks k} {y E : ℕ} {Ls : List BitString}
    (hσ : CostEntry σ K K' A A' t I f num x L W kR y E) (hL : LookupEntry σ g h Ls) :
    ExecLe (sumLookup K K' A A' t f g h s) σ
      (Function.update σ (h 2)
        [decide (σ (g 0) ++ bitsOf W (y + num (σ K) (σ K')) ++ σ (g 2) ∈ Ls)])
      (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2)
      (13 * (σ.space + L) + 2 + (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1)))) +
        (scoreStmt.budget (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
          (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
          (4 + (joinStmt.budget (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
            (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
            (57 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
              (σ (g 2)).length + (Stacks.encList Ls).length + 2) *
              (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
              (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
              29 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
              (σ (g 2)).length + (Stacks.encList Ls).length + 2) + 3) +
            (3 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
              (σ (g 2)).length + (Stacks.encList Ls).length + 2) + 1) + (3 * W + 1))))) := by
  obtain ⟨hf, hKA, hKt, hAt, hK'A', hK't, hA't, hK'A, hAA', hIA, hIA', hFA, hFA', hAk,
    hA'k⟩ := hF
  obtain ⟨hI, hA, hA', ht, hK, hK', hw, h0, h1, h2, h3, h4, h5, h6, h7, hy, hnum, hE⟩ := hσ
  obtain ⟨hg, hh, hgh, hgf, hhf⟩ := hJ
  obtain ⟨hg3, hg4, hT, hG, hw3, hw4, hw5, hw6, hw7, hw8⟩ := hL
  generalize hSdef : σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
    (σ (g 2)).length + (Stacks.encList Ls).length + 2 = S
  have hne : ∀ i j : Fin 9, i ≠ j → f i ≠ f j := fun i j hij e => hij (hf e)
  have e1 := execLe_callPair hKA hKt hAt hK'A' hK't hA't hK'A hAA' hIA hIA' hFA hFA'
    hs.pair hAk hA'k hI hA hA' ht h1 hK hK' hw
  have sp1 := e1.toExec.space_le.2
  set c' := num (σ K) (σ K') with hc'
  set σ1 := Function.update σ (f 1) (bitsOf W c') with hσ1
  have g0 : σ1 (f 0) = bitsOf W y := by
    rw [hσ1, Function.update_of_ne (hne 0 1 (by decide)), h0]
  have g1 : σ1 (f 1) = bitsOf W c' := by rw [hσ1, Function.update_self]
  have g2 : σ1 (f 2) = bitsOf W E := by
    rw [hσ1, Function.update_of_ne (hne 2 1 (by decide)), h2]
  have gj : ∀ j : Fin 9, j ≠ 1 → σ (f j) = [] → σ1 (f j) = [] := fun j hj hz => by
    rw [hσ1, Function.update_of_ne (hne j 1 hj), hz]
  have hyW : y < 2 ^ W := by omega
  have hnW : c' < 2 ^ W := by omega
  have e2 := execLe_scoreK_budget hf g0 g1 g2 (gj 3 (by decide) h3) (gj 4 (by decide) h4)
    (gj 5 (by decide) h5) (gj 6 (by decide) h6) (gj 7 (by decide) h7)
    (by rw [length_bitsOf, length_bitsOf]) (by rw [length_bitsOf, length_bitsOf])
    (by rw [binVal_bitsOf_of_lt hyW, binVal_bitsOf_of_lt hnW, length_bitsOf]; omega)
  rw [length_bitsOf, addBits_bitsOf (by omega)] at e2
  have sp2 := e2.toExec.space_le.2
  set σ2 := Function.update (Function.update (Function.update σ1 (f 1) []) (f 3)
    (bitsOf W (y + c'))) (f 4) [decide (binVal (bitsOf W y) + binVal (bitsOf W c') ≤
      binVal (bitsOf W E))] with hσ2
  have h24 : σ2 (f 4) = [decide (binVal (bitsOf W y) + binVal (bitsOf W c') ≤
      binVal (bitsOf W E))] := by rw [hσ2, Function.update_self]
  have e3 := Stmt.execT_clear (f 4) _ σ2 h24
  have sp3 := e3.toExec.space_le
  set σ3 := Function.update σ (f 3) (bitsOf W (y + c')) with hσ3
  have h3eq : Function.update σ2 (f 4) [] = σ3 := by
    funext r
    by_cases r4 : r = f 4
    · subst r4; rw [Function.update_self, hσ3, Function.update_of_ne (hne 4 3 (by decide)), h4]
    · rw [Function.update_of_ne r4, hσ2, Function.update_of_ne r4, hσ3]
      by_cases r3 : r = f 3
      · subst r3; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne r3, Function.update_of_ne r3]
        by_cases r1 : r = f 1
        · subst r1; rw [Function.update_self, h1]
        · rw [Function.update_of_ne r1, hσ1, Function.update_of_ne r1]
  rw [h3eq] at e3
  have hσ3g : ∀ r, r ≠ f 3 → σ3 r = σ r := fun r hr => by
    rw [hσ3, Function.update_of_ne hr]
  have hf3g3 : g 3 ≠ f 3 := by rw [← hgf]; exact fun e => by have := hg e; omega
  have hf3g4 : g 4 ≠ f 3 := by rw [← hgf]; exact fun e => by have := hg e; omega
  have hf3g0 : g 0 ≠ f 3 := by rw [← hgf]; exact fun e => by have := hg e; omega
  have hf3g2 : g 2 ≠ f 3 := by rw [← hgf]; exact fun e => by have := hg e; omega
  have e4 := execLe_lookupJoin hg hh hgh (σ := σ3) (Ls := Ls)
    ⟨by rw [hσ3g _ hf3g3, hg3], by rw [hσ3g _ hf3g4, hg4], by rw [hσ3g _ (hhf 1), hT],
      by rw [hσ3g _ (hhf 2), hG], by rw [hσ3g _ (hhf 3), hw3], by rw [hσ3g _ (hhf 4), hw4],
      by rw [hσ3g _ (hhf 5), hw5], by rw [hσ3g _ (hhf 6), hw6], by rw [hσ3g _ (hhf 7), hw7],
      by rw [hσ3g _ (hhf 8), hw8]⟩
  rw [hσ3g _ hf3g0, hσ3g _ hf3g2, hgf, hσ3, Function.update_self] at e4
  have sp3' : Stacks.space (Function.update σ (f 3) (bitsOf W (y + c'))) ≤ Stacks.space σ2 := by
    have := e3.toExec.space_le.2; rwa [hσ3] at this
  rw [length_bitsOf] at e4
  have sp4 := e4.toExec.space_le.2
  set b := decide (σ (g 0) ++ bitsOf W (y + c') ++ σ (g 2) ∈ Ls) with hb
  set σ4 := Function.update (Function.update σ (f 3) (bitsOf W (y + c'))) (h 2) [b] with hσ4
  have h43 : σ4 (f 3) = bitsOf W (y + c') := by
    rw [hσ4, Function.update_of_ne (hhf 2).symm, Function.update_self]
  have e5 := Stmt.execT_clear (f 3) _ σ4 h43
  have hfin : Function.update σ4 (f 3) [] = Function.update σ (h 2) [b] := by
    funext r
    by_cases r3 : r = f 3
    · subst r3; rw [Function.update_self, Function.update_of_ne (hhf 2).symm, h3]
    · rw [Function.update_of_ne r3, hσ4]
      by_cases r2 : r = h 2
      · subst r2; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne r2, Function.update_of_ne r2, Function.update_of_ne r3]
  rw [hfin] at e5
  have hS3 : Stacks.space (Function.update σ (f 3) (bitsOf W (y + c'))) +
      (σ (g 0)).length + W + (σ (g 2)).length ≤ S := by omega
  have hS3' : Stacks.space (Function.update σ (f 3) (bitsOf W (y + c'))) +
      (σ (g 0)).length + W + (σ (g 2)).length + (Stacks.encList Ls).length + 2 ≤ S := by
    omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 57 hS3') hS3'
  have hS1 : Stacks.space σ1 + 3 * W + 2 ≤ S := by omega
  have e2' := (e2.mono hS1).mono_time (budget_mono scoreStmt hS1)
  have e3' := ((ExecLe.of_execT e3).mono (show Stacks.space σ2 ≤ S by omega)).mono_time
    (show 3 * [decide (binVal (bitsOf W y) + binVal (bitsOf W c') ≤ binVal (bitsOf W E))].length
      + 1 ≤ 4 by simp)
  have e4' := (e4.mono hS3').mono_time
    (show _ ≤ joinStmt.budget S + (57 * S * S + 29 * S + 3) + (3 * S + 1) by
      have := budget_mono joinStmt hS3
      omega)
  have e5' := ((ExecLe.of_execT e5).mono e4'.toExec.space_le.2).mono_time
    (show 3 * (bitsOf W (y + c')).length + 1 ≤ 3 * W + 1 by rw [length_bitsOf])
  exact ((e1.mono (by omega)).seq (e2'.seq (e3'.seq (e4'.seq e5')))).mono_time (by omega)

/-- The inner body of the layer (the test `goodBit` for the reply `ρ` on `R` to `κ'` on `K'`):
`y ≤ E`, then the move, then the budget, then the lookup, short-circuited, bit on `f 4`. -/
def goodBody {k : ℕ} (K' R A A' t T1 T2 : Fin k) (f g h : Fin 9 → Fin k)
    (sMove sCost : Stmt k) : Stmt k :=
  andBit (f 4) (leTest (f 0) (f 2) T1 T2 t (f 4))
    (andBit (f 4) (callPairBit K' R A A' t (f 1) (f 4) sMove)
      (andBit (f 4) (costTest K' R A A' t f sCost) (sumLookup K' R A A' t f g h sCost)))

/-- **The inner body of the layer.** From a state as in `CostEntry` and `LookupEntry` (for the
keys on `K'` and `R`), except that `y ≤ E` is not assumed, `goodBody` leaves on `f 4` the
short-circuited conjunction of `y ≤ E`, the move bit `mv (σ K') (σ R)`, the budget test
`y + num (σ K') (σ R) ≤ E` and the table lookup of
`σ (g 0) ++ bitsOf W (y + num (σ K') (σ R)) ++ σ (g 2)`, and changes no other stack, within the
stated space and step budget. -/
theorem execLe_goodBody {k : ℕ} {K' R A A' t T1 T2 I : Fin k} {f g h : Fin 9 → Fin k}
    (hf : Function.Injective f) (hg : Function.Injective g) (hh : Function.Injective h)
    (hgh : h 0 = g 3) (hgf : g 1 = f 3) (hhf : ∀ j : Fin 9, h j ≠ f 3) (hh2 : h 2 = f 4)
    (hYT1 : f 0 ≠ T1) (hYt : f 0 ≠ t) (hT1t : T1 ≠ t) (hEbT2 : f 2 ≠ T2) (hEbt : f 2 ≠ t)
    (hT2t : T2 ≠ t) (hT1T2 : T1 ≠ T2) (hT1G : T1 ≠ f 4) (hT2G : T2 ≠ f 4)
    (hEbT1 : f 2 ≠ T1) (htG : t ≠ f 4)
    (hKA : K' ≠ A) (hKt : K' ≠ t) (hAt : A ≠ t) (hK'A' : R ≠ A')
    (hK't : R ≠ t) (hA't : A' ≠ t) (hK'A : R ≠ A) (hAA' : A ≠ A') (hIA : I ≠ A)
    (hIA' : I ≠ A') (hFA : f 1 ≠ A) (hFA' : f 1 ≠ A')
    {sMove sCost : Stmt k} {x : BitString} {L W kR B : ℕ} {mv : BitString → BitString → Bool}
    {num : BitString → BitString → ℕ}
    (hsM : PairBitRoutine sMove x L kR I A A' (f 1) B mv)
    (hsC : PairNumRoutine sCost x L W kR I A A' (f 1) B num) (hAk : A.val < kR)
    (hA'k : A'.val < kR)
    {σ : Stacks k} {y E : ℕ} {Ls : List BitString} (hI : σ I = x) (hA : σ A = [])
    (hA' : σ A' = [])
    (ht : σ t = []) (hK : (σ K').length = L) (hK' : (σ R).length = L)
    (hw : ∀ j : Fin k, kR ≤ j.val → σ j = [])
    (h0 : σ (f 0) = bitsOf W y) (h1 : σ (f 1) = []) (h2 : σ (f 2) = bitsOf W E)
    (h3 : σ (f 3) = []) (h4 : σ (f 4) = []) (h5 : σ (f 5) = []) (h6 : σ (f 6) = [])
    (h7 : σ (f 7) = []) (hT1 : σ T1 = []) (hT2 : σ T2 = []) (hyW : y < 2 ^ W)
    (hnum : num (σ K') (σ R) ≤ E + 1) (hE : 2 * E + 2 ≤ 2 ^ W)
    (hg3 : σ (g 3) = []) (hg4 : σ (g 4) = []) (hT : σ (h 1) = Stacks.encList Ls)
    (hw3 : σ (h 3) = []) (hw4 : σ (h 4) = []) (hw5 : σ (h 5) = [])
    (hw6 : σ (h 6) = []) (hw7 : σ (h 7) = []) (hw8 : σ (h 8) = []) :
    ExecLe (goodBody K' R A A' t T1 T2 f g h sMove sCost) σ
      (Function.update σ (f 4) [decide (y ≤ E) && (mv (σ K') (σ R) &&
        (decide (y + num (σ K') (σ R) ≤ E) &&
          decide (σ (g 0) ++ bitsOf W (y + num (σ K') (σ R)) ++ σ (g 2) ∈ Ls)))])
      (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W + (σ (g 2)).length +
        (Stacks.encList Ls).length + 2)
      (40 * (σ.space + 2 * W + 1) +
        ((13 * (σ.space + L) + 2 +
          (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))) + 4) +
        ((13 * (σ.space + L) + 2 +
          (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))) +
          (scoreStmt.budget (σ.space + L + L + B + 3 * W + 2) + (3 * W + 1))) +
        ((13 * (σ.space + L) + 2 +
          (13 * (σ.space + L + L) + 2 + (B + (3 * L + 1 + (3 * L + 1))))) +
          (scoreStmt.budget (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
            (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
            (4 + (joinStmt.budget (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
              (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
              (57 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
                (σ (g 2)).length + (Stacks.encList Ls).length + 2) *
                (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
                (σ (g 2)).length + (Stacks.encList Ls).length + 2) +
                29 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
                (σ (g 2)).length + (Stacks.encList Ls).length + 2) + 3) +
              (3 * (σ.space + L + L + B + 3 * W + 2 + (σ (g 0)).length + W +
                (σ (g 2)).length + (Stacks.encList Ls).length + 2) + 1) +
              (3 * W + 1))))) + 9) := by
  have hF : CostFrame K' R A A' t I f kR :=
    ⟨hf, hKA, hKt, hAt, hK'A', hK't, hA't, hK'A, hAA', hIA, hIA', hFA, hFA', hAk, hA'k⟩
  have hne : ∀ i j : Fin 9, i ≠ j → f i ≠ f j := fun i j hij e => hij (hf e)
  have hEW : E < 2 ^ W := by omega
  have e1 := execLe_leTest hYT1 hYt hT1t hEbT2 hEbt hT2t hT1T2 hT1G hT2G hEbT1 htG h0 h2 hT1 hT2
    ht h4 hyW hEW
  by_cases hy : y ≤ E
  · have hσ : CostEntry σ K' R A A' t I f num x L W kR y E :=
      ⟨hI, hA, hA', ht, hK, hK', hw, h0, h1, h2, h3, h4, h5, h6, h7, hy, hnum, hE⟩
    have e4 := execLe_sumLookup hF ⟨hg, hh, hgh, hgf, hhf⟩ hsC hσ
      ⟨hg3, hg4, hT, by rw [hh2, h4], hw3, hw4, hw5, hw6, hw7, hw8⟩
    rw [hh2] at e4
    have e3 := execLe_costTest hF hsC hσ
    have e2 := execLe_callPairBit hKA hKt hAt hK'A' hK't hA't hK'A hAA' hIA hIA' hFA hFA'
      (hne 1 4 (by decide)) hsM hAk hA'k hI hA hA' ht h1 h4 hK hK' hw
    have a3 := execLe_andBit h4 (e3.mono (by omega)) (fun _ => e4)
    have a2 := execLe_andBit h4 (e2.mono (by omega)) (fun _ => a3)
    exact (execLe_andBit h4 (e1.mono (by omega)) (fun _ => a2)).mono_time (by omega)
  · exact (execLe_andBit (τ₂ := 0) h4 (e1.mono (by omega))
      (fun hb => absurd hb (by simp [hy]))).mono_time (by omega)

end KeyEval

/-- Saturating the move cost at `E + 1` does not change the budget tests of `stepKC`. -/
theorem le_min_sat_iff (a b E : ℕ) : a + min b (E + 1) ≤ E ↔ a + b ≤ E := by
  constructor
  · intro h; rcases le_total b (E + 1) with h' | h'
    · rw [min_eq_left h'] at h; exact h
    · rw [min_eq_right h'] at h; omega
  · intro h; rw [min_eq_left (by omega)]; exact h

/-- The layer step with saturated move costs `min (costN …) (E + 1)` — what the program
computes from `sCost` (`stepKCsat_eq`: the same as `stepKC`). -/
def stepKCsat {α : Type} (codes : List α) (dec : α → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E : ℕ)
    (g : α → ℕ → ℕ → Bool) (κ : α) (y n : ℕ) : Bool :=
  out (dec κ) && codes.all fun κ' =>
    !(decide (KeyMoveRaw X P (dec κ) (dec κ')) && !decide (dec κ' ⊆ dec κ) &&
        decide (n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E)) ||
      codes.any fun ρ => decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
        decide (y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E) &&
        g ρ (y + min (costN c (dec κ') (dec ρ)) (E + 1))
          (n + min (costN c (dec κ) (dec κ')) (E + 1))

/-- **Saturation does not change the layer step**: `stepKCsat`, which caps the move costs at
`E + 1`, computes the same bit as `stepKC`. -/
theorem stepKCsat_eq {α : Type} (codes : List α) (dec : α → Finset BitString)
    (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E : ℕ)
    (g : α → ℕ → ℕ → Bool) (κ : α) (y n : ℕ) :
    stepKCsat codes dec X P out c E g κ y n = stepKC codes dec X P out c E g κ y n := by
  unfold stepKCsat stepKC
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun κ' _ => ?_
  by_cases h2 : n + costN c (dec κ) (dec κ') ≤ E
  · rw [min_eq_left (show costN c (dec κ) (dec κ') ≤ E + 1 by omega)]
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    refine or_congr_right (exists_congr fun ρ => and_congr_right fun _ => ?_)
    by_cases h1 : y + costN c (dec κ') (dec ρ) ≤ E
    · rw [min_eq_left (show costN c (dec κ') (dec ρ) ≤ E + 1 by omega)]
    · have h1' : ¬ y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E := by
        rw [le_min_sat_iff]; exact h1
      simp [h1, h1']
  · have h2' : ¬ n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E := by
      rw [le_min_sat_iff]; exact h2
    simp [h2, h2']

open KeyEval in
/-- **The read-off in the program's terms**: the root move is the move from the zero code
(`decK_bitsOf_zero`) and its cost is the saturated cost `min (costN …) (E + 1)` that `sCost`
writes; with these, the read-off of a last layer `tabF` (agreeing with `yesKC … F` on codes
and scores `≤ E`) is `valKC` over the slot codes. -/
theorem valKC_eq_readoff_sat (L' n : ℕ) (X : Finset BitString)
    (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E F : ℕ)
    (tabF : BitString → ℕ → ℕ → Bool)
    (h : ∀ κ ∈ allBits (n * (2 * L' + 1)), ∀ y m, y ≤ E → m ≤ E →
      tabF κ y m = yesKC (allBits (n * (2 * L' + 1))) (decK L' n) X P out c E F κ y m) :
    valKC (allBits (n * (2 * L' + 1))) (decK L' n) X P out c E F =
      (allBits (n * (2 * L' + 1))).any fun κ =>
        decide (KeyMoveRaw X P (decK L' n (bitsOf (n * (2 * L' + 1)) 0)) (decK L' n κ)) &&
        decide (min (costN c (decK L' n (bitsOf (n * (2 * L' + 1)) 0)) (decK L' n κ)) (E + 1)
          ≤ E) &&
        tabF κ (min (costN c (decK L' n (bitsOf (n * (2 * L' + 1)) 0)) (decK L' n κ)) (E + 1))
          0 := by
  rw [valKC_eq_of_layer_mem _ _ _ _ _ _ _ F tabF h, decK_bitsOf_zero]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  refine exists_congr fun κ => and_congr_right fun _ => ?_
  by_cases hc : costN c ∅ (decK L' n κ) ≤ E
  · rw [min_eq_left (by omega)]
  · have h1 : ¬ min (costN c ∅ (decK L' n κ)) (E + 1) ≤ E := by
      rw [← Nat.zero_add (min _ _), le_min_sat_iff]; simpa using hc
    simp [hc, h1]

open KeyEval in
/-- **The value iteration over the table computes `valKC`**: with scores in `W` bits and
`E < 2 ^ W`, the value of the key game over all codes of `L` bits is the read-off of the `F`-th
table iterate (`tabIter` with the step `stepKC` and the first layer `out ∘ dec`). -/
theorem valKC_eq_tabIter (L W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E F : ℕ)
    (hE : E < 2 ^ W) :
    valKC (allBits L) dec X P out c E F = (allBits L).any fun κ =>
      decide (KeyMoveRaw X P ∅ (dec κ)) && decide (costN c ∅ (dec κ) ≤ E) &&
        tabRead W (tabIter L W (stepKC (allBits L) dec X P out c E) (fun κ => out (dec κ)) F)
          κ (costN c ∅ (dec κ)) 0 := by
  apply valKC_eq_of_layer_mem
  refine layer_eq_yesKC_mem (allBits L) dec X P out c E
    (fun f κ y n => tabRead W (tabIter L W (stepKC (allBits L) dec X P out c E)
      (fun κ => out (dec κ)) f) κ y n) ?_ ?_ F
  · intro κ hκ y n hy hn
    exact tabRead_tabInit _ ((mem_allBits L κ).1 hκ) (hy.trans_lt hE) (hn.trans_lt hE)
  · intro f κ hκ y n hy hn
    exact tabRead_tabNext _ _ ((mem_allBits L κ).1 hκ) (hy.trans_lt hE) (hn.trans_lt hE)

open KeyEval in
/-- The evaluator target `valKCLang` as the read-off of the table iteration, with the key codes
of `L = clock (2 clock + 1)` bits, the budget `E = 2 ^ (gameN - m)` and scores of
`W = gameN - m + 1` bits. -/
theorem valKCLang_eq_tabIter (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    valKCLang c e T m Y = {x | ((allBits (clock e x.length * (2 * clock e x.length + 1))).any
      fun κ =>
        decide (KeyMoveRaw (querySet c.toOTM x (clock e x.length) \ Y)
          (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length)) ∅
          (decK (clock e x.length) (clock e x.length) κ)) &&
        decide (costN (fun z => costNum (gameN e T m x.length) (T.fn z) z.length) ∅
          (decK (clock e x.length) (clock e x.length) κ) ≤ 2 ^ (gameN e T m x.length - m)) &&
        tabRead (gameN e T m x.length - m + 1)
          (tabIter (clock e x.length * (2 * clock e x.length + 1))
            (gameN e T m x.length - m + 1)
            (stepKC (allBits (clock e x.length * (2 * clock e x.length + 1)))
              (decK (clock e x.length) (clock e x.length))
              (querySet c.toOTM x (clock e x.length) \ Y)
              (fun S => queries c.toOTM (oracleOf T.fn S) x (clock e x.length))
              (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
                (querySet c.toOTM x (clock e x.length) \ Y)).outcome
              (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
              (2 ^ (gameN e T m x.length - m)))
            (fun κ => (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
                (querySet c.toOTM x (clock e x.length) \ Y)).outcome
              (decK (clock e x.length) (clock e x.length) κ))
            (2 ^ (clock e x.length + 1)))
          κ (costN (fun z => costNum (gameN e T m x.length) (T.fn z) z.length) ∅
            (decK (clock e x.length) (clock e x.length) κ)) 0) = true} := by
  ext x
  change _ = true ↔ _ = true
  rw [valKC_eq_tabIter _ (gameN e T m x.length - m + 1)]
  rw [pow_succ]
  have := Nat.one_le_two_pow (n := gameN e T m x.length - m)
  omega

/-! ### The driver's logic in the program's terms

The bit a layer program computes per index string (`layerBit`: outcome, `any` over the replies,
inner `any` with the lookup of the index string in the old list table) is `stepKC` of the old
list table (`stepKC_readL_eq_layerBit`); the main loop's invariant on list tables
(`readL_inv_zero`, `readL_inv_succ`); the read-off as a lookup in the last list table
(`valKC_eq_readoff_list`). -/

section DriverLogic

open KeyEval
/-- The bit the layer program computes for the index triple `(κ, y, n)`, in the program's terms:
the outcome bit, then the `any` loop over the opponent's replies `κ'` of the `bad` test, whose
inner `any` loop over `ρ` looks up the index string `ρ ++ bitsOf W (y + c') ++ bitsOf W (n + c)`
in the old list table (costs saturated at `E + 1`, as `sCost` writes them). -/
def layerBit (L W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E : ℕ) (Lold : List BitString)
    (κ : BitString) (y n : ℕ) :
    Bool :=
  out (dec κ) && !((allBits L).any fun κ' =>
    decide (KeyMoveRaw X P (dec κ) (dec κ')) && !decide (dec κ' ⊆ dec κ) &&
      decide (n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E) &&
      !((allBits L).any fun ρ =>
        decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
          decide (y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E) &&
          decide (ρ ++ bitsOf W (y + min (costN c (dec κ') (dec ρ)) (E + 1)) ++
            bitsOf W (n + min (costN c (dec κ) (dec κ')) (E + 1)) ∈ Lold)))

/-- **The layer bit in the program's terms is `stepKC`** of the old list table. -/
theorem stepKC_readL_eq_layerBit (L W : ℕ) (dec : BitString → Finset BitString)
    (X : Finset BitString)
    (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E : ℕ)
    (Lold : List BitString) (κ : BitString) (y n : ℕ) :
    stepKC (allBits L) dec X P out c E (readL W Lold) κ y n =
      layerBit L W dec X P out c E Lold κ y n := by
  rw [← stepKCsat_eq]
  unfold stepKCsat layerBit readL idxStr
  congr 1
  rw [List.all_eq_not_any_not]
  congr 2
  funext κ'
  cases decide (KeyMoveRaw X P (dec κ) (dec κ')) <;>
    cases decide (dec κ' ⊆ dec κ) <;>
    cases decide (n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E) <;> simp

/-- **The main loop's invariant, first layer**: a list table holding, among the index strings,
exactly those whose key has outcome `true` agrees with `yesKC … 0` on keys and scores `≤ E`. -/
theorem readL_inv_zero (L W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E : ℕ)
    (hE : E < 2 ^ W) (Ls : List BitString)
    (h0 : ∀ s : BitString, s.length = L + W + W →
      (s ∈ Ls ↔ out (dec (strKey L s)) = true)) :
    ∀ κ ∈ allBits L, ∀ y n, y ≤ E → n ≤ E →
      readL W Ls κ y n = yesKC (allBits L) dec X P out c E 0 κ y n := by
  apply layer_inv_zero
  intro κ hκ y n hy hn
  exact readL_init (fun κ => out (dec κ)) Ls h0 ((mem_allBits L κ).1 hκ) (hy.trans_lt hE)
    (hn.trans_lt hE)

/-- **The main loop's invariant, one layer**: if the old list table agrees with `yesKC … j` and
the new one holds exactly the index strings with `stepKC` of the old one `true`, the new one
agrees with `yesKC … (j + 1)`. -/
theorem readL_inv_succ (L W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString) (out : Finset BitString → Bool)
    (c : BitString → ℕ) (E j : ℕ)
    (hE : E < 2 ^ W) (Lold Lnew : List BitString)
    (hold : ∀ κ ∈ allBits L, ∀ y n, y ≤ E → n ≤ E →
      readL W Lold κ y n = yesKC (allBits L) dec X P out c E j κ y n)
    (hnew : ∀ s : BitString, s.length = L + W + W → (s ∈ Lnew ↔
      stepKC (allBits L) dec X P out c E (readL W Lold) (strKey L s) (strY L W s)
        (strN L W s) = true)) :
    ∀ κ ∈ allBits L, ∀ y n, y ≤ E → n ≤ E →
      readL W Lnew κ y n = yesKC (allBits L) dec X P out c E (j + 1) κ y n := by
  apply layer_inv_succ _ _ _ _ _ _ _ _ _ _ hold
  intro κ hκ y n hy hn
  exact readL_step _ Lold Lnew hnew ((mem_allBits L κ).1 hκ) (hy.trans_lt hE) (hn.trans_lt hE)

/-- **The read-off in the program's terms** (list table): if the last list table agrees with
`yesKC … F` on keys and scores `≤ E`, then `valKC` over the slot codes is the `any` loop over
the codes `κ` of the root move from the zero code, its saturated cost, and the lookup of the
index string `κ ++ bitsOf W cost ++ bitsOf W 0`. -/
theorem valKC_eq_readoff_list (L' n W : ℕ) (X : Finset BitString)
    (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E F : ℕ) (Ls : List BitString)
    (h : ∀ κ ∈ allBits (n * (2 * L' + 1)), ∀ y m, y ≤ E → m ≤ E →
      readL W Ls κ y m = yesKC (allBits (n * (2 * L' + 1))) (decK L' n) X P out c E F κ y m) :
    valKC (allBits (n * (2 * L' + 1))) (decK L' n) X P out c E F =
      (allBits (n * (2 * L' + 1))).any fun κ =>
        decide (KeyMoveRaw X P (decK L' n (bitsOf (n * (2 * L' + 1)) 0)) (decK L' n κ)) &&
        decide (min (costN c (decK L' n (bitsOf (n * (2 * L' + 1)) 0)) (decK L' n κ)) (E + 1)
          ≤ E) &&
        decide (κ ++ bitsOf W (min (costN c (decK L' n (bitsOf (n * (2 * L' + 1)) 0))
          (decK L' n κ)) (E + 1)) ++ bitsOf W 0 ∈ Ls) :=
  valKC_eq_readoff_sat L' n X P out c E F (readL W Ls) h

/-- The inner test of the layer body, right-nested as `andBit` chains compute it: guard
`y ≤ E` (so that `y + cost` does not overflow `W` bits), the move `κ' → ρ`, the budget test,
the lookup of `ρ ++ bitsOf W (y + c') ++ nb` in the old list table (`nb` = the bits of
`n + c`). -/
def goodBit (W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString)
    (c : BitString → ℕ) (E : ℕ) (Lold : List BitString) (κ' : BitString) (y : ℕ)
    (nb : BitString) (ρ : BitString) : Bool :=
  decide (y ≤ E) && (decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
    (decide (y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E) &&
      decide (ρ ++ bitsOf W (y + min (costN c (dec κ') (dec ρ)) (E + 1)) ++ nb ∈ Lold)))

/-- The middle test of the layer body (a reply `κ'` of the opponent that wins against `κ`),
right-nested, with the guard `n ≤ E`. -/
def badBit (L W : ℕ) (dec : BitString → Finset BitString) (X : Finset BitString)
    (P : Finset BitString → Finset BitString)
    (c : BitString → ℕ) (E : ℕ) (Lold : List BitString) (κ : BitString) (y n : ℕ)
    (κ' : BitString) : Bool :=
  decide (n ≤ E) && (decide (KeyMoveRaw X P (dec κ) (dec κ')) &&
    (!decide (dec κ' ⊆ dec κ) && (decide (n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E) &&
      !((allBits L).any (goodBit W dec X P c E Lold κ' y
        (bitsOf W (n + min (costN c (dec κ) (dec κ')) (E + 1))))))))

/-- **The guarded, right-nested layer bit equals `layerBit`** (hence `stepKC` of the old list
table, `stepKC_readL_eq_layerBit`). -/
theorem layerBit_eq_guarded (L W : ℕ) (dec : BitString → Finset BitString)
    (X : Finset BitString) (P : Finset BitString → Finset BitString)
    (out : Finset BitString → Bool) (c : BitString → ℕ) (E : ℕ)
    (Lold : List BitString) (κ : BitString) (y n : ℕ) :
    layerBit L W dec X P out c E Lold κ y n =
      (out (dec κ) && !((allBits L).any (badBit L W dec X P c E Lold κ y n))) := by
  unfold layerBit
  congr 3
  funext κ'
  unfold badBit goodBit
  by_cases hn : n ≤ E
  · have hg : ∀ ρ, (decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
        decide (y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E) &&
        decide (ρ ++ bitsOf W (y + min (costN c (dec κ') (dec ρ)) (E + 1)) ++
          bitsOf W (n + min (costN c (dec κ) (dec κ')) (E + 1)) ∈ Lold)) =
        (decide (y ≤ E) && (decide (KeyMoveRaw X P (dec κ') (dec ρ)) &&
          (decide (y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E) &&
            decide (ρ ++ bitsOf W (y + min (costN c (dec κ') (dec ρ)) (E + 1)) ++
              bitsOf W (n + min (costN c (dec κ) (dec κ')) (E + 1)) ∈ Lold)))) := by
      intro ρ
      by_cases hy : y ≤ E
      · simp [hy, Bool.and_assoc]
      · have : ¬ y + min (costN c (dec κ') (dec ρ)) (E + 1) ≤ E := by omega
        simp [hy, this]
    simp only [hg, hn, decide_true, Bool.true_and, Bool.and_assoc]
  · have : ¬ n + min (costN c (dec κ) (dec κ')) (E + 1) ≤ E := by omega
    simp [hn, this]

end DriverLogic

end Kolmogorov.RandomStrings
