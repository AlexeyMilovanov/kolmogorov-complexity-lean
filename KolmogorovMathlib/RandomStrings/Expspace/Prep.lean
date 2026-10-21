/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.Cost

/-!
# Preparing and evaluating the game

The preparation statement `exists_prepStmt` (the query list, the filtered lists, the costs and
the budget, each procedure inlined along injective placements) and the evaluation statement
`exists_evalStmt`, which combines it with `exists_gameStmt`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-- A linear bound used in space calculations. -/
theorem aux_lin_le (q y l : ℕ) (hq : 1 ≤ q) (hl : l ≤ q) : l + y + 1 ≤ (y + 2) * q := by
  nlinarith

/-- A quadratic bound used in space calculations. -/
theorem aux_sq_le (q l : ℕ) (hl : l ≤ q) (hq : 1 ≤ q) : (l + 1) ^ 2 ≤ 4 * q ^ 2 := by
  nlinarith

/-- **Preparation of the game data.**  From the input `x` (stack `0`) a statement
computes, on stacks `1`–`4` (all other stacks empty at the end, `x` kept on stack `0`):
* `encList LX`: the board `X = querySet \ Y` as a duplicate-free list;
* `encList cs`: the cost numerators `costNum N (T.fn z) |z|` of the strings `z` of `LX`, in the
  same order, as bit strings of a common width `W`, at a precision `N` bounding `|z| - 1`,
  `T.fn z` (`z ∈ LX`) and `m` (e.g. `N = 2 |encList LX| + 6 + m + max T.value`);
* `eb`: the budget numerator `2 ^ (N - m)`, of width `W`;
* `encList LR`: the possible queries that are random for `T.fn` (`|z| ≤ T.fn z`);
with no overflow in width `W`, all data of size `2 ^ O(clock e |x| + |x|)`, within space
`2 ^ (C · (clock e |x| + |x| + 1))`.
Proof: the query list `LQ` by `exists_queryEnumStmt`, then `LX = LQ.filter (· ∉ Y)` and
`LR = LQ.filter (· ∉ Z)` (`Z` the hardwired table entries with `T.value z < |z|`) by
`exists_filterNotMemStmt` against hardwired codes (`Stmt.pushList`), then the costs and the
budget by `exists_costStmt`; each procedure inlined by `Exec.call`/`Exec.call2` along
injective placements (`place3`), the space bounded by `2 ^ (C · (clock + |x| + 1))` through the
size of `LQ` (`pow_mul_sq_le`). -/
theorem exists_prepStmt (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (C : ℕ), 6 ≤ k ∧ ∀ x : BitString,
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
        eb.length + (Stacks.encList LR).length + 1 ≤ 2 ^ (C * (clock e x.length + x.length + 1)) ∧
      Exec s (Stacks.input k x)
        (Stacks.layout k [x, Stacks.encList LX, Stacks.encList cs, eb, Stacks.encList LR])
        (2 ^ (C * (clock e x.length + x.length + 1))) := by
  classical
  obtain ⟨kq, sq, inp, out, Cq, hio, hq⟩ := exists_queryEnumStmt c e
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
    D + 2 * (Cq + 1) + 1, by omega, fun x => ?_⟩
  obtain ⟨LQ, hQnd, hQ, hexq⟩ := hq x
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
      simp [g₁, place3, hτ₂, hτ₁, hτ₀, Stacks.input, Stacks.layout, Function.update_apply]
    all_goals split_ifs <;> try rfl
    all_goals omega
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
      simp [g₂, g₁, place3, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, Stacks.layout,
        Function.update_apply]
    all_goals split_ifs <;> try rfl
    all_goals omega
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
      simp [fc, g₂, g₁, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input,
        Stacks.layout, Function.update_apply]
    all_goals split_ifs <;> try simp
    all_goals omega
  rw [Stacks.layout_three' _ _ _ (by omega) (by omega), ← hc₉] at hexc
  have e₉ := Exec.call2 hfc hexc
  set τ₉ := Function.update (Function.update τ₈ (fc ⟨1, by omega⟩) (Stacks.encList cs))
    (fc ⟨2, by omega⟩) eb with hτ₉
  -- space bookkeeping
  set a := clock e x.length + x.length + 1 with ha
  set Q := 2 ^ ((Cq + 1) * a) with hQdef
  have ha1 : 1 ≤ a := by omega
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQq : 2 ^ (Cq * a) ≤ Q := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have haQ : a ≤ Q := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hQQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) _
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
  have hLQ : (Stacks.encList LQ).length ≤ Q := by omega
  have hτ₈1 : τ₈ (fc ⟨1, by omega⟩) = [] := by
    simp [fc, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, g₁, g₂]
  have hτ₈2 : τ₈ (fc ⟨2, by omega⟩) = [] := by
    simp [fc, place3, hτ₈, hτ₇, hτ₆, hτ₅, hτ₄, hτ₃, hτ₂, hτ₁, hτ₀, Stacks.input, g₁, g₂]
  have hsp₉ : Stacks.space τ₉ = Stacks.space τ₈ + (Stacks.encList cs).length + eb.length := by
    rw [hτ₉, Stacks.space_update_nil _ _ _ (by
        rw [Function.update_of_ne (hfc.ne (by simp [Fin.ext_iff]))]; exact hτ₈2),
      Stacks.space_update_nil _ _ _ hτ₈1]
  -- all bounds are below `TOTAL ≤ D · Q ^ 2`
  have hT2 : 2 ^ (Cq * a) + Stacks.space τ₀ + (Stacks.encList LY).length +
      (Stacks.encList LZ).length +
      C₂ * ((Stacks.encList LQ).length + (Stacks.encList LY).length + 1) +
      C₂ * ((Stacks.encList LQ).length + (Stacks.encList LZ).length + 1) +
      Cc * ((Stacks.encList (LQ.filter fun z => decide (z ∉ LY))).length + 1) ^ 2 + 3 * Q ≤
      D * Q ^ 2 := by
    have i1 : C₂ * ((Stacks.encList LQ).length + (Stacks.encList LY).length + 1) ≤
        C₂ * (((Stacks.encList LY).length + 2) * Q) :=
      Nat.mul_le_mul_left _ (aux_lin_le _ _ _ hQ1 hLQ)
    have i2 : C₂ * ((Stacks.encList LQ).length + (Stacks.encList LZ).length + 1) ≤
        C₂ * (((Stacks.encList LZ).length + 2) * Q) :=
      Nat.mul_le_mul_left _ (aux_lin_le _ _ _ hQ1 hLQ)
    have i3 : Cc * ((Stacks.encList (LQ.filter fun z => decide (z ∉ LY))).length + 1) ^ 2 ≤
        Cc * (4 * Q ^ 2) :=
      Nat.mul_le_mul_left _ (aux_sq_le _ _ (hLX.trans hLQ) hQ1)
    have i4 : (Stacks.encList LY).length ≤ (Stacks.encList LY).length * Q ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have i5 : (Stacks.encList LZ).length ≤ (Stacks.encList LZ).length * Q ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have i6 : C₂ * (((Stacks.encList LY).length + 2) * Q) ≤
        C₂ * (((Stacks.encList LY).length + 2) * Q ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQQ)
    have i7 : C₂ * (((Stacks.encList LZ).length + 2) * Q) ≤
        C₂ * (((Stacks.encList LZ).length + 2) * Q ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQQ)
    have i8 : 2 ^ (Cq * a) ≤ Q ^ 2 := hQq.trans hQQ
    have i9 : Stacks.space τ₀ ≤ Q ^ 2 := by rw [hsp₀]; omega
    rw [hD]
    linarith
  have hfin : ∀ t, t ≤ D * Q ^ 2 → t ≤ 2 ^ ((D + 2 * (Cq + 1) + 1) * a) := fun t ht =>
    ht.trans (pow_mul_sq_le (Cq + 1) D a ha1)
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

/-- **The evaluation program.**  For the data of `exists_gameProg` there is a statement which, on
input `x` (stack `0`), leaves on its output stack the bit `gameValB X cost E out` for
`X = querySet c.toOTM x (clock e |x|) \ Y`, `cost z = costNum (gameN …) (T.fn z) |z|`,
`E = 2 ^ (gameN … - m)` and the outcomes of the game, within space
`2 ^ (C · (clock e |x| + |x| + 1))`.
Proof: the preparation statement `exists_prepStmt` followed by the evaluation statement
`exists_gameStmt`, both inlined by `Fin.castLE` into `max k₁ k₂` stacks (their work stacks may
overlap: each leaves them empty); the outcomes `{z ∈ LR | z ∉ S}` agree with `oracleOf T.fn S`
on the query set (`clockedAccepts_iff_of_agree`). -/
theorem exists_evalStmt (c : OTMCode) (e : ℕ) (T : Table) (m : ℕ) (Y : Finset BitString) :
    ∃ (k : ℕ) (s : Stmt k) (out : Fin k) (C : ℕ), ∀ x : BitString, ∃ σ' : Stacks k,
      Exec s (Stacks.input k x) σ' (2 ^ (C * (clock e x.length + x.length + 1))) ∧
      ((σ' out).head? = some true ↔
        gameValB (querySet c.toOTM x (clock e x.length) \ Y)
          (fun z => costNum (gameN e T m x.length) (T.fn z) z.length)
          (2 ^ (gameN e T m x.length - m))
          (gameOf c e x T.fn ((2 : ℝ)⁻¹ ^ m)
            (querySet c.toOTM x (clock e x.length) \ Y)).outcome = true) := by
  classical
  obtain ⟨k₁, s₁, C₁, hk₁, hprep⟩ := exists_prepStmt c e T m Y
  obtain ⟨k₂, s₂, C₂, hk₂, hgame⟩ := exists_gameStmt c e
  have h₁ : k₁ ≤ max k₁ k₂ := le_max_left _ _
  have h₂ : k₂ ≤ max k₁ k₂ := le_max_right _ _
  refine ⟨max k₁ k₂, .seq (s₁.rename (Fin.castLE h₁)) (s₂.rename (Fin.castLE h₂)),
    ⟨5, by omega⟩, C₂ + 2 * C₁ + 1, fun x => ?_⟩
  obtain ⟨LX, LR, cs, eb, N, W, hnd, hLX, hLR, hN, hm, hcs, hW, heb, hcost, hE, hov, hsize,
    hex₁⟩ := hprep x
  set a := clock e x.length + x.length + 1 with ha
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
  · refine max_le (Nat.pow_le_pow_right (by norm_num) (by nlinarith)) ?_
    calc C₂ * _ ≤ C₂ * (2 ^ (C₁ * a)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
      _ ≤ 2 ^ ((C₂ + 2 * C₁ + 1) * a) := pow_mul_sq_le C₁ C₂ a ha1
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

end Kolmogorov.RandomStrings
