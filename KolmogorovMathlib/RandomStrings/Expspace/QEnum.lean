/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.QEnumParts

/-!
# The enumeration of the query set

The fixpoint statement `QEnum.qeStmt` assembled from the four sub-contracts, its pure lemmas,
the inlining of the sub-contracts, the space arithmetic, and the main contract
`exists_queryEnumStmt`: the duplicate-free list of all queries of the clocked machine on `x` is
computed in space `2 ^ O(clock + |x|)`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace QEnum

/-! ### The enumeration of the query set from the four sub-contracts -/

/-- The contract of the selection statement. -/
def SelSpec (s : Stmt 12) (K : ℕ) : Prop := ∀ (Us : List BitString) (v : BitString),
    Exec s (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
      (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Us)) 1 v)
        2 (Stacks.encList (sel v Us)))
      (K * ((Stacks.encList Us).length + v.length + 1))

/-- The contract of the zero-mask statement. -/
def ZeroSpec (s : Stmt 3) (K : ℕ) : Prop := ∀ l : BitString,
    Exec s (Function.update (fun _ => []) 0 l)
      (Function.update (Function.update (fun _ => []) 0 l) 1 (List.replicate l.length false))
      (K * (l.length + 1))

/-- The contract of the merge statement. -/
def MergeSpec (s : Stmt 16) (K : ℕ) : Prop := ∀ (Q Lo Ln : List BitString),
    Exec s (Function.update (Function.update (Function.update (fun _ => []) 0 (Stacks.encList Q))
        1 (Stacks.encList Lo)) 2 (Stacks.encList Ln))
      (Function.update (Function.update (fun _ => []) 1 (Stacks.encList Lo)) 2
        (Stacks.encList (mergeL Lo Q Ln)))
      (K * ((Stacks.encList Q).length + (Stacks.encList Lo).length +
        (Stacks.encList Ln).length + 1))

/-- The contract of the recording simulation. -/
def SimSpec (c : OTMCode) (e : ℕ) (s : Stmt 21) (C : ℕ) : Prop :=
  ∀ (x : BitString) (L : List BitString),
    ∃ Q : List BitString,
      (∀ z, z ∈ Q ↔ z ∈ queries c.toOTM {z | z ∈ L} x (clock e x.length)) ∧
      Exec s (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L))
        (Function.update (Function.update (Function.update (fun _ => []) 0 x) 1
          (Stacks.encList L)) 16 (Stacks.encList Q))
        (C * (x.length + clock e x.length + (Stacks.encList L).length + 1) ^ 2)

/-- "The top of the stack is the bit `false`". -/
def isFalse (o : Option Bool) : Bool := o == some false

/-- Stack maps of the inlined procedures (`28` stacks: `0` input, `1` known queries, `2` new
queries, `3` changed flag, `4` mask counter, `5` done flag, `6` oracle code, `7` record,
`8` carry, `9` temporary, `10`–`27` shared work stacks). -/
def fSel : Fin 12 → Fin 28 := ![1, 4, 6, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The stack renaming `fZero` embeds the zero-mask statement into the enumeration. -/
def fZero : Fin 3 → Fin 28 := ![1, 4, 10]

/-- The stack renaming `fMerge` embeds the merge statement into the enumeration. -/
def fMerge : Fin 16 → Fin 28 :=
  ![7, 1, 2, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-- The stack renaming `fSim` embeds the recording simulation into the enumeration. -/
def fSim : Fin 21 → Fin 28 :=
  ![0, 6, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 7, 24, 25, 26, 27]

/-- The stack renaming `fSel` for the selection statement is injective. -/
theorem fSel_inj : Function.Injective fSel := by decide

/-- The stack renaming `fZero` for the zero-mask statement is injective. -/
theorem fZero_inj : Function.Injective fZero := by decide

/-- The stack renaming `fMerge` for the merge statement is injective. -/
theorem fMerge_inj : Function.Injective fMerge := by decide

/-- The stack renaming `fSim` for the recording simulation is injective. -/
theorem fSim_inj : Function.Injective fSim := by decide

/-- One mask: select the oracle, simulate with recording, merge the record, increment. -/
def counterBody (sSel : Stmt 12) (sSim : Stmt 21) (sMerge : Stmt 16) : Stmt 28 :=
  Stmt.seqs [sSel.rename fSel, sSim.rename fSim, sMerge.rename fMerge, Stmt.clear 6,
    Stmt.incr 4 9 8, Stmt.caseBit 8 fun g => .seq (.pop 8) (if g then Stmt.setFlag 5 else .skip)]

/-- One round: all masks over the known queries. -/
def roundStmt (sZero : Stmt 3) (sSel : Stmt 12) (sSim : Stmt 21) (sMerge : Stmt 16) : Stmt 28 :=
  Stmt.seqs [Stmt.clearFlag 3, sZero.rename fZero, .push 5 false,
    .loop 5 isFalse (counterBody sSel sSim sMerge), Stmt.clear 4, .pop 5,
    .ite 2 Option.isSome (Stmt.setFlag 3) .skip, Stmt.moveAll 2 9, Stmt.moveAll 9 1]

/-- The enumeration: rounds until nothing new is found. -/
def qeStmt (sZero : Stmt 3) (sSel : Stmt 12) (sSim : Stmt 21) (sMerge : Stmt 16) : Stmt 28 :=
  Stmt.seqs [.push 3 true, .loop 3 Stmt.isTrue (roundStmt sZero sSel sSim sMerge), .pop 3]

/-- Stacks during the mask loop. -/
def stC (x : BitString) (Lo Ln : List BitString) (l : BitString) (d : Bool) : Stacks 28 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => []) 0 x) 1 (Stacks.encList Lo)) 2 (Stacks.encList Ln)) 3 [false])
      4 l) 5 [d]

/-- Stacks between rounds. -/
def stR (x : BitString) (Lo : List BitString) (f : Bool) : Stacks 28 :=
  Function.update (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList Lo)) 3
    [f]

/-! #### Pure lemmas -/

/-- Bit strings of equal length with equal `binVal` values are equal. -/
theorem binVal_inj : ∀ {l m : BitString}, l.length = m.length → binVal l = binVal m → l = m
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l, b :: m, hl, hb => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [binVal] at hb
    cases a <;> cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at hb
    · rw [binVal_inj hl (by omega)]
    · omega
    · omega
    · rw [binVal_inj hl (by omega)]

/-- Appending a `true` bit adds the next power of two to the binary value. -/
theorem binVal_tag (z : BitString) : binVal (z ++ [true]) = binVal z + 2 ^ z.length := by
  rw [binVal_append]; simp [binVal]

/-- The binary value of a string with a final `true` bit uniquely determines the string. -/
theorem tag_inj {z w : BitString} (h : binVal (z ++ [true]) = binVal (w ++ [true])) : z = w := by
  rw [binVal_tag, binVal_tag] at h
  have hz := binVal_lt z
  have hw := binVal_lt w
  have hl : z.length = w.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : 2 ^ (z.length + 1) ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this; omega
    · have : 2 ^ (w.length + 1) ≤ 2 ^ z.length := Nat.pow_le_pow_right (by norm_num) hlt
      rw [pow_succ] at this; omega
  exact binVal_inj hl (by rw [hl] at h; omega)

/-- A duplicate-free list of strings of length at most `T` has at most `2 ^ (T + 1)` elements. -/
theorem length_le_of_nodup (T : ℕ) (L : List BitString) (hL : L.Nodup)
    (hT : ∀ z ∈ L, z.length ≤ T) :
    L.length ≤ 2 ^ (T + 1) := by
  classical
  have hinj : Set.InjOn (fun z : BitString => binVal (z ++ [true])) {z | z ∈ L} :=
    fun z _ w _ h => tag_inj h
  have hnd : (L.map fun z : BitString => binVal (z ++ [true])).Nodup :=
    hL.map_on fun z hz w hw h => tag_inj h
  have hsub : (L.map fun z : BitString => binVal (z ++ [true])).toFinset ⊆
      Finset.range (2 ^ (T + 1)) := by
    intro n hn
    simp only [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨z, hz, rfl⟩ := hn
    rw [Finset.mem_range, binVal_tag]
    have h1 := binVal_lt z
    have h2 : 2 ^ (z.length + 1) ≤ 2 ^ (T + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := hT z hz; omega)
    rw [pow_succ] at h2; omega
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at this
  exact this

/-- `Stacks.encList` of a concatenated list is the concatenation of the encodings. -/
theorem encList_append (L L' : List BitString) :
    Stacks.encList (L ++ L') = Stacks.encList L ++ Stacks.encList L' := by
  simp [Stacks.encList]

/-- `Stacks.encList L` is empty exactly when the original list `L` is empty. -/
theorem encList_eq_nil (L : List BitString) : Stacks.encList L = [] ↔ L = [] := by
  cases L with
  | nil => simp [Stacks.encList]
  | cons z L => simp [encList_cons, Stacks.encStr]

/-- `Stacks.encList` uses at most `2 * T + 1` bits per string of length at most `T`. -/
theorem length_encList_le (T : ℕ) : ∀ L : List BitString,
    (∀ z ∈ L, z.length ≤ T) →
    (Stacks.encList L).length ≤ L.length * (2 * T + 1)
  | [], _ => by simp [Stacks.encList]
  | z :: L, h => by
    have h1 := length_encList_le T L (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have h2 := h z List.mem_cons_self
    rw [encList_cons, List.length_append, Stacks.length_encStr, List.length_cons]
    have : (L.length + 1) * (2 * T + 1) = L.length * (2 * T + 1) + (2 * T + 1) := by ring
    omega

/-- The list `sel v Us` selected by a mask is a sublist of `Us`. -/
theorem sel_sublist : ∀ (v : BitString) (Us : List BitString),
    List.Sublist (sel v Us) Us
  | [], Us => by cases Us <;> simp [sel]
  | _ :: _, [] => by simp [sel]
  | b :: v, z :: Us => by
    simp only [sel]
    split
    · exact (sel_sublist v Us).cons_cons z
    · exact (sel_sublist v Us).cons z

/-- The mask of an oracle on a list. -/
noncomputable def mask (B : Set BitString) (Lo : List BitString) : BitString :=
  Lo.map fun w => @decide (w ∈ B) (Classical.propDecidable _)

/-- Membership in a masked selection is equivalent to membership in both the list and oracle set. -/
theorem mem_sel_mask (B : Set BitString) (z : BitString) : ∀ (Lo : List BitString)
    (pad : BitString),
    z ∈ sel (mask B Lo ++ pad) Lo ↔ z ∈ Lo ∧ z ∈ B
  | [], pad => by cases pad <;> simp [sel, mask]
  | w :: Lo, pad => by
    have ih := mem_sel_mask B z Lo pad
    simp only [mask, List.map_cons, List.cons_append] at ih ⊢
    simp only [sel]
    by_cases hw : w ∈ B
    · simp only [hw, decide_true, ite_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩) <;> simp_all
      · rintro ⟨rfl | h1, h2⟩ <;> simp_all
    · simp only [hw, decide_false, Bool.false_eq_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact absurd h2 hw
        · exact ⟨h1, h2⟩

/-- The mask `mask B Lo` has the same length as the list `Lo`. -/
theorem length_mask (B : Set BitString) (Lo : List BitString) :
    (mask B Lo).length = Lo.length := by
  simp [mask]

/-- **Fixpoint.**  If no mask over `Lo` produces a query outside `Lo`, then every possible query
is in `Lo`. -/
theorem queryAll_subset_of_fix (M : OTM) (x : BitString) (T : ℕ) (Lo : List BitString) (W : ℕ)
    (hW : Lo.length ≤ W)
    (hfix : ∀ v : BitString, v.length = W → ∀ z ∈ queries M {z | z ∈ sel v Lo} x T, z ∈ Lo) :
    ∀ z ∈ queryAll M x T, z ∈ Lo := by
  rintro z ⟨B, hz⟩
  set v := mask B Lo ++ List.replicate (W - Lo.length) false with hv
  have hvl : v.length = W := by simp [hv, length_mask]; omega
  set B' : Set BitString := {z | z ∈ sel v Lo} with hB'
  have hagree : ∀ w ∈ Lo, (w ∈ B ↔ w ∈ B') := by
    intro w hw
    change w ∈ B ↔ w ∈ sel v Lo
    rw [hv, mem_sel_mask]; exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have claim : ∀ t ≤ T, run M B x t = run M B' x t ∧
      ∀ s < t, ∀ w, askedAt M (run M B x s) = some w → w ∈ Lo := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rfl, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
    | succ t ih =>
      intro ht
      obtain ⟨hrun, hprev⟩ := ih (by omega)
      have hask : ∀ w, askedAt M (run M B x t) = some w → w ∈ Lo := by
        intro w hw
        rw [hrun] at hw
        exact hfix v hvl w ((mem_queries M B' x T w).2 ⟨t, by omega, hw⟩)
      refine ⟨?_, ?_⟩
      · change step M B (run M B x t) = step M B' (run M B' x t)
        rw [← hrun]
        exact step_eq_of_agree M B B' _ fun w hw => hagree w (hask w hw)
      · intro s hs w hw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
        · exact hprev s h w hw
        · subst h; exact hask w hw
  obtain ⟨s, hs, hw⟩ := (mem_queries M B x T z).1 hz
  exact (claim T le_rfl).2 s hs z hw

/-- Membership in `mergeL Lo Q Ln` is membership in `Ln` or a new query from `Q`. -/
theorem mem_mergeL (Lo : List BitString) (z : BitString) : ∀ (Q Ln : List BitString),
    z ∈ mergeL Lo Q Ln ↔ z ∈ Ln ∨ (z ∈ Q ∧ z ∉ Lo)
  | [], Ln => by simp [mergeL]
  | q :: Q, Ln => by
    rw [mergeL, mem_mergeL Lo z Q]
    by_cases hq : q ∈ Lo ∨ q ∈ Ln
    · rw [ite_eq_left hq]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 h1 with rfl | h1
          · rcases hq with hq | hq
            · exact absurd hq h2
            · exact Or.inl hq
          · exact Or.inr ⟨h1, h2⟩
    · rw [ite_eq_right hq]
      simp only [not_or] at hq
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨Or.inl rfl, hq.1⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨h1, h2⟩

/-- `mergeL` preserves duplicate-freeness when `Ln ++ Lo` is duplicate-free. -/
theorem nodup_mergeL (Lo : List BitString) : ∀ (Q Ln : List BitString), (Ln ++ Lo).Nodup →
    (mergeL Lo Q Ln ++ Lo).Nodup
  | [], Ln, h => by simpa [mergeL] using h
  | q :: Q, Ln, h => by
    rw [mergeL]
    apply nodup_mergeL Lo Q
    split_ifs with hq
    · exact h
    · simp only [not_or] at hq
      rw [List.cons_append, List.nodup_cons]
      exact ⟨by simp [hq.1, hq.2], h⟩

/-! #### Inlining -/

/-- An injectively renamed statement runs with its original space bound plus the initial
space of the larger stack configuration, preserving stacks outside the renaming. -/
theorem exec_call {k K : ℕ} {f : Fin k → Fin K} (hf : Function.Injective f) {s : Stmt k}
    {σ σ' : Stacks k} {S : ℕ} (h : Exec s σ σ' S) {τ τ' : Stacks K}
    (hin : ∀ r, τ (f r) = σ r) (hout : ∀ r, τ' (f r) = σ' r)
    (hfr : ∀ j, j ∉ Finset.univ.image f → τ' j = τ j) :
    Exec (s.rename f) τ τ' (S + τ.space) := by
  classical
  have hv : (fun r => τ (f r)) = σ := funext hin
  have h1 := Exec.rename_of_comp hf (σ' := σ') (τ := τ) (by rw [hv]; exact h)
  have e : Function.extend f σ' τ = τ' := by
    funext j
    by_cases hj : ∃ r, f r = j
    · obtain ⟨r, rfl⟩ := hj; rw [hf.extend_apply, hout]
    · rw [Function.extend_apply' _ _ _ hj, hfr j (by simpa using hj)]
  have hr : Stacks.rest f τ ≤ τ.space := by
    have := Stacks.space_extend hf (fun r => τ (f r)) τ
    rw [Stacks.extend_comp_self hf] at this; omega
  rw [e] at h1
  exact h1.mono (by omega)

/-- The length of every stack `σ r` is bounded by the total space `σ.space`. -/
theorem length_le_space {k : ℕ} (σ : Stacks k) (r : Fin k) : (σ r).length ≤ σ.space :=
  Finset.single_le_sum (f := fun r => (σ r).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ r)

/-- The length of `Stacks.encList` is monotone under the sublist relation. -/
theorem length_encList_sublist {L' L : List BitString} (h : L'.Sublist L) :
    (Stacks.encList L').length ≤ (Stacks.encList L).length := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => rw [encList_cons, List.length_append]; omega
  | cons_cons a _ ih =>
    rw [encList_cons, encList_cons, List.length_append, List.length_append]
    omega

/-- The total space of `stC` is the sum of its encoded data and control stacks. -/
theorem stC_space (x : BitString) (Lo Ln : List BitString) (l : BitString) (d : Bool) :
    (stC x Lo Ln l d).space = x.length + (Stacks.encList Lo).length +
      (Stacks.encList Ln).length + l.length + 2 := by
  simp [Stacks.space, stC, Fin.sum_univ_succ, Function.update_apply]
  omega

/-- The total space of `stR` is the input, query list, and flag lengths. -/
theorem stR_space (x : BitString) (Lo : List BitString) (f : Bool) :
    (stR x Lo f).space = x.length + (Stacks.encList Lo).length + 1 := by
  simp [Stacks.space, stR, Fin.sum_univ_succ, Function.update_apply]
  omega

/-- The carry transition clears stack `8` and copies its bit to the done flag on stack `5`. -/
theorem exec_carryStep (g : Bool) (x : BitString) (Lo Ln : List BitString) (l : BitString) (G : ℕ)
    (hsp : Stacks.space (Function.update (Function.update (stC x Lo Ln l false) 4
      (incBits l)) 8 [g]) ≤ G) :
    Exec (Stmt.caseBit 8 fun g => .seq (.pop 8) (if g then Stmt.setFlag 5 else .skip))
      (Function.update (Function.update (stC x Lo Ln l false) 4 (incBits l)) 8 [g])
      (Function.update (Function.update (Function.update (Function.update
        (stC x Lo Ln l false) 4 (incBits l)) 8 [g]) 8 []) 5 [g]) G := by
  generalize hσ : Function.update (Function.update (stC x Lo Ln l false) 4 (incBits l)) 8 [g] =
    σ at hsp ⊢
  have h8 : σ 8 = [g] := by rw [← hσ]; rfl
  have h5 : σ 5 = [false] := by rw [← hσ]; rfl
  rw [Stmt.exec_caseBit (b := g) (l := []) h8]
  have p := Exec.pop (r := 8) (σ := σ) (S := G) hsp
  rw [h8] at p
  have hsp' := p.space_le.2
  refine .seq p ?_
  have h5' : (Function.update σ 8 ([g] : BitString).tail) 5 = [false] := by
    rw [Function.update_of_ne (by decide)]; exact h5
  cases g
  · refine Stmt.exec_of_eq (Exec.skip hsp') ?_
    funext j
    by_cases hj : j = 5
    · subst hj; rw [Function.update_self]; exact h5'
    · rw [Function.update_of_ne hj]; rfl
  · exact (Stmt.exec_setFlag h5').mono hsp'

/-- The counter body records queries for a selected mask, merges them into `Ln`, increments
the mask, and stays within `G` under the displayed bound. -/
theorem exec_counterBody {c : OTMCode} {e : ℕ} {sSel : Stmt 12} {sSim : Stmt 21}
    {sMerge : Stmt 16} {KS CS KM : ℕ} (hSel : SelSpec sSel KS) (hSim : SimSpec c e sSim CS)
    (hMerge : MergeSpec sMerge KM) (x : BitString) (Lo Ln : List BitString) (l : BitString) (G : ℕ)
    (hG : (stC x Lo Ln l false).space + (Stacks.encList Lo).length +
      CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 +
      KS * ((Stacks.encList Lo).length + l.length + 1) +
      KM * (CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 +
        (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1) + 2 ≤ G) :
    ∃ Q : List BitString,
      (∀ z, z ∈ Q ↔ z ∈ queries c.toOTM {z | z ∈ sel l Lo} x (clock e x.length)) ∧
      Exec (counterBody sSel sSim sMerge) (stC x Lo Ln l false)
        (stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l)) G := by
  have e1 := exec_call fSel_inj (hSel Lo l) (τ := stC x Lo Ln l false)
    (τ' := Function.update (stC x Lo Ln l false) 6 (Stacks.encList (sel l Lo)))
    (by intro r; fin_cases r <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd (by decide) hj)
  obtain ⟨Q, hQ, hS⟩ := hSim x (sel l Lo)
  have e2 := exec_call fSim_inj hS
    (τ := Function.update (stC x Lo Ln l false) 6 (Stacks.encList (sel l Lo)))
    (τ' := Function.update (Function.update (stC x Lo Ln l false) 6
      (Stacks.encList (sel l Lo))) 7 (Stacks.encList Q))
    (by intro r; fin_cases r <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd (by decide) hj)
  have e3 := exec_call fMerge_inj (hMerge Q Lo Ln)
    (τ := Function.update (Function.update (stC x Lo Ln l false) 6
      (Stacks.encList (sel l Lo))) 7 (Stacks.encList Q))
    (τ' := Function.update (stC x Lo (mergeL Lo Q Ln) l false) 6 (Stacks.encList (sel l Lo)))
    (by intro r; fin_cases r <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro j hj; fin_cases j <;> first | rfl | exact absurd (by decide) hj)
  have e4 := Stmt.exec_clear 6 _ (Function.update (stC x Lo (mergeL Lo Q Ln) l false) 6
    (Stacks.encList (sel l Lo))) rfl
  have h4 : Function.update (Function.update (stC x Lo (mergeL Lo Q Ln) l false) 6
      (Stacks.encList (sel l Lo))) 6 [] = stC x Lo (mergeL Lo Q Ln) l false := by
    funext j; fin_cases j <;> rfl
  rw [h4] at e4
  have e5 := Stmt.exec_incr (A := (4 : Fin 28)) (t := 9) (C := 8) (by decide) (by decide)
    (by decide) (σ := stC x Lo (mergeL Lo Q Ln) l false) rfl rfl
  have h5 : (stC x Lo (mergeL Lo Q Ln) l false) 4 = l := rfl
  rw [h5] at e5
  have e6 := exec_carryStep (incCarry l) x Lo (mergeL Lo Q Ln) l G
  have h6 : Function.update (Function.update (Function.update (Function.update
      (stC x Lo (mergeL Lo Q Ln) l false) 4 (incBits l)) 8 [incCarry l]) 8 []) 5
        [incCarry l] = stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l) := by
    funext j; fin_cases j <;> rfl
  rw [h6] at e6
  -- space bookkeeping
  have hsel := length_encList_sublist (sel_sublist l Lo)
  have hQl : (Stacks.encList Q).length ≤
      CS * (x.length + clock e x.length + (Stacks.encList (sel l Lo)).length + 1) ^ 2 :=
    (length_le_space _ 16).trans hS.space_le.2
  have hmono : CS * (x.length + clock e x.length + (Stacks.encList (sel l Lo)).length + 1) ^ 2 ≤
      CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have sp1 : Stacks.space (Function.update (stC x Lo Ln l false) 6 (Stacks.encList (sel l Lo))) =
      (stC x Lo Ln l false).space + (Stacks.encList (sel l Lo)).length := by
    have := Stacks.space_update (stC x Lo Ln l false) 6 (Stacks.encList (sel l Lo))
    have h0 : (stC x Lo Ln l false) 6 = [] := rfl
    rw [h0] at this; simpa using this
  have sp2 : Stacks.space (Function.update (Function.update (stC x Lo Ln l false) 6
      (Stacks.encList (sel l Lo))) 7 (Stacks.encList Q)) =
      (stC x Lo Ln l false).space + (Stacks.encList (sel l Lo)).length +
        (Stacks.encList Q).length := by
    have := Stacks.space_update (Function.update (stC x Lo Ln l false) 6
      (Stacks.encList (sel l Lo))) 7 (Stacks.encList Q)
    have h0 : (Function.update (stC x Lo Ln l false) 6 (Stacks.encList (sel l Lo))) 7 = [] := rfl
    rw [h0, sp1] at this; simpa using this
  have hKM : KM * ((Stacks.encList Q).length + (Stacks.encList Lo).length +
      (Stacks.encList Ln).length + 1) ≤
      KM * (CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 +
        (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have s3 := e3.space_le.2
  have s4 := e4.space_le.2
  have s5 := e5.space_le.2
  refine ⟨Q, hQ, ?_⟩
  refine .seq (e1.mono (by omega)) (.seq (e2.mono (by omega)) (.seq (e3.mono (by omega))
    (.seq (e4.mono (by omega)) (.seq (e5.mono (by omega)) (.seq (e6 (by omega))
      (.skip (by have := (e6 (by omega)).space_le.2; omega)))))))

/-- The bound needed for one mask step. -/
def stepBound (e : ℕ) (KS CS KM : ℕ) (x : BitString) (Lo Ln : List BitString) (l : BitString) : ℕ :=
  (stC x Lo Ln l false).space + (Stacks.encList Lo).length +
    CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 +
    KS * ((Stacks.encList Lo).length + l.length + 1) +
    KM * (CS * (x.length + clock e x.length + (Stacks.encList Lo).length + 1) ^ 2 +
      (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1) + 2

/-- A mask-loop state `stC` fits within the bound allocated to its step. -/
theorem stC_space_le_stepBound (e : ℕ) (KS CS KM : ℕ) (x : BitString) (Lo Ln : List BitString)
    (l : BitString) (d : Bool) : (stC x Lo Ln l d).space ≤ stepBound e KS CS KM x Lo Ln l := by
  unfold stepBound; rw [stC_space, stC_space]; omega

/-- **The mask loop**: all masks of width `|encList Lo|` are processed. -/
theorem exec_counterLoop {c : OTMCode} {e : ℕ} {sSel : Stmt 12} {sSim : Stmt 21}
    {sMerge : Stmt 16} {KS CS KM : ℕ} (hSel : SelSpec sSel KS) (hSim : SimSpec c e sSim CS)
    (hMerge : MergeSpec sMerge KM) (x : BitString) (Lo : List BitString) (G : ℕ) (hnd : Lo.Nodup)
    (hG : ∀ (Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length → stepBound e KS CS KM x Lo Ln l ≤ G) :
    ∃ Ln l, (Ln ++ Lo).Nodup ∧ (∀ z ∈ Ln, z ∈ queryAll c.toOTM x (clock e x.length)) ∧
      (∀ v : BitString, v.length = (Stacks.encList Lo).length →
        ∀ z ∈ queries c.toOTM {z | z ∈ sel v Lo} x (clock e x.length), z ∈ Lo ∨ z ∈ Ln) ∧
      Exec (.loop 5 isFalse (counterBody sSel sSim sMerge))
        (stC x Lo [] (List.replicate (Stacks.encList Lo).length false) false)
        (stC x Lo Ln l true) G := by
  set W := (Stacks.encList Lo).length with hW
  set T := clock e x.length with hT
  let I : Stacks 28 → Prop := fun σ => ∃ Ln l d, σ = stC x Lo Ln l d ∧ l.length = W ∧
    (Ln ++ Lo).Nodup ∧ (∀ z ∈ Ln, z ∈ queryAll c.toOTM x T) ∧
    (∀ v : BitString, v.length = W → (d = true ∨ binVal v < binVal l) →
      ∀ z ∈ queries c.toOTM {z | z ∈ sel v Lo} x T, z ∈ Lo ∨ z ∈ Ln)
  have hstep : ∀ σ, I σ → isFalse (σ 5).head? = true →
      ∃ σ', Exec (counterBody sSel sSim sMerge) σ σ' G ∧ I σ' ∧
        (fun σ : Stacks 28 => if σ 5 = [true] then 0 else 2 ^ W - binVal (σ 4) + 1) σ' <
        (fun σ : Stacks 28 => if σ 5 = [true] then 0 else 2 ^ W - binVal (σ 4) + 1) σ := by
    rintro σ ⟨Ln, l, d, rfl, hl, hnd', hq, hcov⟩ hc
    have hd : d = false := by
      have : (stC x Lo Ln l d) 5 = [d] := rfl
      rw [this] at hc; cases d <;> simp_all [isFalse]
    subst hd
    obtain ⟨Q, hQ, hex⟩ := exec_counterBody hSel hSim hMerge x Lo Ln l G (hG Ln l hnd' hq hl)
    have hinc := binVal_incBits l
    have hlt := binVal_lt l
    rw [hl] at hinc hlt
    refine ⟨_, hex, ⟨mergeL Lo Q Ln, incBits l, incCarry l, rfl, by rw [length_incBits]; exact hl,
      nodup_mergeL Lo Q Ln hnd', ?_, ?_⟩, ?_⟩
    · intro z hz
      rcases (mem_mergeL Lo z Q Ln).1 hz with h | ⟨h, -⟩
      · exact hq z h
      · exact ⟨_, (hQ z).1 h⟩
    · intro v hv hvd z hz
      by_cases hlt' : binVal v < binVal l
      · rcases hcov v hv (Or.inr hlt') z hz with h | h
        · exact Or.inl h
        · exact Or.inr ((mem_mergeL Lo z Q Ln).2 (Or.inl h))
      · have hvlt := binVal_lt v
        rw [hv] at hvlt
        have heq : binVal v = binVal l := by
          rcases hvd with h | h
          · rw [h] at hinc; simp at hinc; omega
          · cases hcar : incCarry l
            · rw [hcar] at hinc; simp at hinc; omega
            · rw [hcar] at hinc; simp at hinc; omega
        have hvl : v = l := binVal_inj (by rw [hv, hl]) heq
        subst hvl
        by_cases hzLo : z ∈ Lo
        · exact Or.inl hzLo
        · exact Or.inr ((mem_mergeL Lo z Q Ln).2 (Or.inr ⟨(hQ z).2 hz, hzLo⟩))
    · change (if (stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l)) 5 = [true] then 0
          else 2 ^ W - binVal ((stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l)) 4) + 1) <
        (if (stC x Lo Ln l false) 5 = [true] then 0
          else 2 ^ W - binVal ((stC x Lo Ln l false) 4) + 1)
      have h1 : (stC x Lo Ln l false) 5 = [false] := rfl
      have h2 : (stC x Lo Ln l false) 4 = l := rfl
      have h3 : (stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l)) 5 = [incCarry l] := rfl
      have h4 : (stC x Lo (mergeL Lo Q Ln) (incBits l) (incCarry l)) 4 = incBits l := rfl
      rw [h1, h2, h3, h4]
      cases hcar : incCarry l
      · rw [hcar] at hinc; simp at hinc ⊢; omega
      · simp
  have hexit : ∀ σ, I σ → σ.space ≤ G := by
    rintro σ ⟨Ln, l, d, rfl, hl, hnd', hq, -⟩
    exact (stC_space_le_stepBound e KS CS KM x Lo Ln l d).trans (hG Ln l hnd' hq hl)
  have hI0 : I (stC x Lo [] (List.replicate W false) false) := by
    refine ⟨[], List.replicate W false, false, rfl, by simp, by simpa using hnd, by simp, ?_⟩
    intro v _ hvd
    rcases hvd with h | h
    · exact absurd h (by simp)
    · rw [binVal_replicate_false] at h; exact absurd h (Nat.not_lt_zero _)
  obtain ⟨σ', hex, ⟨Ln, l, d, rfl, hl, hnd', hq, hcov⟩, hc⟩ :=
    Exec.loop_of_variant I _ G hstep hexit _ hI0
  have hd : d = true := by
    have : (stC x Lo Ln l d) 5 = [d] := rfl
    rw [this] at hc; cases d <;> simp_all [isFalse]
  subst hd
  exact ⟨Ln, l, hnd', hq, fun v hv => hcov v hv (Or.inl rfl), hex⟩

/-- Overwriting stack 3 of `stR x Lo true` with `[false]` gives `stR x Lo false`. -/
private lemma exec_round_h1 (x : BitString) (Lo : List BitString) (j : Fin 28) :
    Function.update (stR x Lo true) 3 [false] j = stR x Lo false j := by
  match j with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨n+28, h⟩ => exact absurd h (by omega)

/-- Overwriting stack 4 of `stR x Lo false` with the zero mask changes no stack outside the image
of `fZero`. -/
private lemma exec_round_h2c (x : BitString) (Lo : List BitString) (j : Fin 28)
    (hj : j ∉ Finset.image fZero Finset.univ) :
    Function.update (stR x Lo false) 4
      (List.replicate (Stacks.encList Lo).length false) j = stR x Lo false j := by
  have h_neq : j ≠ 4 := by
    intro h_eq
    subst h_eq
    exact hj (Finset.mem_image_of_mem fZero (Finset.mem_univ (1 : Fin 3)))
  simp [Function.update, h_neq]

private lemma exec_round_h3 (x : BitString) (Lo : List BitString) (j : Fin 28) :
    Function.update (Function.update (stR x Lo false) 4
      (List.replicate (Stacks.encList Lo).length false)) 5 (false :: (Function.update
      (stR x Lo false) 4 (List.replicate (Stacks.encList Lo).length false)) 5) j =
      stC x Lo [] (List.replicate (Stacks.encList Lo).length false) false j := by
  match j with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨n+28, h⟩ => exact absurd h (by omega)

/-- Clearing stack 4 and popping stack 5 of `stC x Lo Ln l true` gives `stR x Lo false` with
`Stacks.encList Ln` in stack 2. -/
private lemma exec_round_h6 (x : BitString) (Lo Ln : List BitString) (l : BitString) (j : Fin 28) :
    Function.update (Function.update (stC x Lo Ln l true) 4 []) 5
      ((Function.update (stC x Lo Ln l true) 4 []) 5).tail j =
      Function.update (stR x Lo false) 2 (Stacks.encList Ln) j := by
  match j with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨n+28, h⟩ => exact absurd h (by omega)

/-- Moving stack 2 of `stR x Lo f`, holding `Stacks.encList Ln`, through stack 9 onto stack 1
gives `stR x (Ln ++ Lo) f`. -/
private lemma exec_round_h9 (x : BitString) (Lo Ln : List BitString) (f : Bool) (j : Fin 28) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 2 [])
      9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
        (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 9 [])
      1 (((Function.update (Function.update (Function.update (stR x Lo f) 2 (Stacks.encList Ln))
        2 []) 9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
          (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 9).reverse ++
        (Function.update (Function.update (Function.update (stR x Lo f) 2 (Stacks.encList Ln))
          2 []) 9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
            (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 1) j =
      stR x (Ln ++ Lo) f j := by
  have a1 : (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 2 = Stacks.encList Ln := rfl
  have a2 : (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9 = [] := rfl
  rw [a1, a2, List.append_nil]
  have a3 : (Function.update (Function.update (Function.update (stR x Lo f) 2
      (Stacks.encList Ln)) 2 []) 9 (Stacks.encList Ln).reverse) 9 =
      (Stacks.encList Ln).reverse := rfl
  have a4 : (Function.update (Function.update (Function.update (stR x Lo f) 2
      (Stacks.encList Ln)) 2 []) 9 (Stacks.encList Ln).reverse) 1 = Stacks.encList Lo := rfl
  rw [a3, a4, List.reverse_reverse, ← encList_append]
  match j with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨n+28, h⟩ => exact absurd h (by omega)

/-- Setting stack 3 to `[true]` in `stR x Lo false` with `Stacks.encList Ln` in stack 2 gives
`stR x Lo true` with the same stack 2. -/
private lemma exec_round_h_setFlag (x : BitString) (Lo Ln : List BitString) (j : Fin 28) :
    Function.update (Function.update (stR x Lo false) 2 (Stacks.encList Ln)) 3 [true] j =
      Function.update (stR x Lo true) 2 (Stacks.encList Ln) j := by
  match j with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl
  | ⟨10, _⟩ => rfl | ⟨11, _⟩ => rfl | ⟨12, _⟩ => rfl | ⟨13, _⟩ => rfl | ⟨14, _⟩ => rfl
  | ⟨15, _⟩ => rfl | ⟨16, _⟩ => rfl | ⟨17, _⟩ => rfl | ⟨18, _⟩ => rfl | ⟨19, _⟩ => rfl
  | ⟨20, _⟩ => rfl | ⟨21, _⟩ => rfl | ⟨22, _⟩ => rfl | ⟨23, _⟩ => rfl | ⟨24, _⟩ => rfl
  | ⟨25, _⟩ => rfl | ⟨26, _⟩ => rfl | ⟨27, _⟩ => rfl
  | ⟨n+28, h⟩ => exact absurd h (by omega)

/-- **One round**: process all masks over `Lo`, then append the new queries. -/
theorem exec_round {c : OTMCode} {e : ℕ} {sZero : Stmt 3} {sSel : Stmt 12} {sSim : Stmt 21}
    {sMerge : Stmt 16} {KZ KS CS KM : ℕ} (hZero : ZeroSpec sZero KZ) (hSel : SelSpec sSel KS)
    (hSim : SimSpec c e sSim CS) (hMerge : MergeSpec sMerge KM) (x : BitString)
    (Lo : List BitString)
    (G : ℕ) (hnd : Lo.Nodup)
    (hG : ∀ (Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length → stepBound e KS CS KM x Lo Ln l ≤ G)
    (hGz : KZ * ((Stacks.encList Lo).length + 1) + (stR x Lo false).space ≤ G) :
    ∃ Ln f, (f = false ↔ Ln = []) ∧ (Ln ++ Lo).Nodup ∧
      (∀ z ∈ Ln, z ∈ queryAll c.toOTM x (clock e x.length)) ∧
      (∀ v : BitString, v.length = (Stacks.encList Lo).length →
        ∀ z ∈ queries c.toOTM {z | z ∈ sel v Lo} x (clock e x.length), z ∈ Lo ∨ z ∈ Ln) ∧
      Exec (roundStmt sZero sSel sSim sMerge) (stR x Lo true) (stR x (Ln ++ Lo) f) G := by
  have e1 := Stmt.exec_clearFlag (F := (3 : Fin 28)) (σ := stR x Lo true) (f := true) rfl
  have h1 : Function.update (stR x Lo true) 3 [false] = stR x Lo false :=
    funext (exec_round_h1 x Lo)
  rw [h1] at e1
  have e2 := exec_call fZero_inj (hZero (Stacks.encList Lo)) (τ := stR x Lo false)
    (τ' := Function.update (stR x Lo false) 4 (List.replicate (Stacks.encList Lo).length false))
    (by intro ⟨val, isLt⟩; match val with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | n+3 => exact absurd isLt (by omega))
    (by intro ⟨val, isLt⟩; match val with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | n+3 => exact absurd isLt (by omega))
    (exec_round_h2c x Lo)
  have hW0 := hG [] (List.replicate (Stacks.encList Lo).length false) (by simpa using hnd)
    (by simp) (by simp)
  have hs0 := stC_space_le_stepBound e KS CS KM x Lo []
    (List.replicate (Stacks.encList Lo).length false) false
  have e3 := Exec.push (r := (5 : Fin 28)) (b := false)
    (σ := Function.update (stR x Lo false) 4 (List.replicate (Stacks.encList Lo).length false))
    (S := G) (by
      have := stC_space x Lo [] (List.replicate (Stacks.encList Lo).length false) false
      have h' : Stacks.space (Function.update (stR x Lo false) 4
          (List.replicate (Stacks.encList Lo).length false)) =
          (stR x Lo false).space + (Stacks.encList Lo).length := by
        have := Stacks.space_update (stR x Lo false) 4
          (List.replicate (Stacks.encList Lo).length false)
        have h0 : (stR x Lo false) 4 = [] := rfl
        rw [h0] at this; simpa using this
      rw [h', stR_space]; rw [stC_space] at hs0
      simp only [List.length_replicate, encList_nil, List.length_nil] at hs0; omega)
  have h3 : Function.update (Function.update (stR x Lo false) 4
      (List.replicate (Stacks.encList Lo).length false)) 5 (false :: (Function.update
        (stR x Lo false) 4 (List.replicate (Stacks.encList Lo).length false)) 5) =
      stC x Lo [] (List.replicate (Stacks.encList Lo).length false) false :=
    funext (exec_round_h3 x Lo)
  rw [h3] at e3
  obtain ⟨Ln, l, hnd', hq, hcov, e4⟩ := exec_counterLoop hSel hSim hMerge x Lo G hnd hG
  have s4 := e4.space_le.2
  have e5 := Stmt.exec_clear 4 _ (stC x Lo Ln l true) rfl
  have e6 := Exec.pop (r := (5 : Fin 28)) (σ := Function.update (stC x Lo Ln l true) 4 [])
    (S := G) (e5.space_le.2.trans s4)
  have h6 : Function.update (Function.update (stC x Lo Ln l true) 4 []) 5
      ((Function.update (stC x Lo Ln l true) 4 []) 5).tail =
      Function.update (stR x Lo false) 2 (Stacks.encList Ln) :=
    funext (exec_round_h6 x Lo Ln l)
  rw [h6] at e6
  have s6 := e6.space_le.2
  -- the changed flag
  obtain ⟨f, hf, e7⟩ : ∃ f : Bool, (f = false ↔ Ln = []) ∧
      Exec (.ite 2 Option.isSome (Stmt.setFlag 3) .skip)
        (Function.update (stR x Lo false) 2 (Stacks.encList Ln))
        (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) G := by
    by_cases hL : Ln = []
    · refine ⟨false, by simp [hL], .iteF ?_ (.skip s6)⟩
      change Option.isSome (Stacks.encList Ln).head? = false
      rw [(encList_eq_nil Ln).2 hL]; rfl
    · refine ⟨true, by simp [hL], .iteT ?_ ?_⟩
      · change Option.isSome (Stacks.encList Ln).head? = true
        cases h : Stacks.encList Ln with
        | nil => exact absurd ((encList_eq_nil Ln).1 h) hL
        | cons b t => rfl
      · have := Stmt.exec_setFlag (F := (3 : Fin 28))
          (σ := Function.update (stR x Lo false) 2 (Stacks.encList Ln)) (f := false) rfl
        refine Stmt.exec_of_eq (this.mono s6) ?_
        funext j; exact (exec_round_h_setFlag x Lo Ln j)
  have s7 := e7.space_le.2
  have e8 := Stmt.exec_moveAll (by decide : (2 : Fin 28) ≠ 9) _
    (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) rfl
  have e9 := Stmt.exec_moveAll (by decide : (9 : Fin 28) ≠ 1) _
    (Function.update (Function.update (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 2 [])
      9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
        (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) rfl
  have h9 : Function.update (Function.update (Function.update (Function.update
      (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 2 [])
      9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
        (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 9 [])
      1 (((Function.update (Function.update (Function.update (stR x Lo f) 2 (Stacks.encList Ln))
        2 []) 9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
          (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 9).reverse ++
        (Function.update (Function.update (Function.update (stR x Lo f) 2 (Stacks.encList Ln))
          2 []) 9 ((Function.update (stR x Lo f) 2 (Stacks.encList Ln) 2).reverse ++
            (Function.update (stR x Lo f) 2 (Stacks.encList Ln)) 9)) 1) =
      stR x (Ln ++ Lo) f := funext (exec_round_h9 x Lo Ln f)
  rw [h9] at e9
  have s8 := e8.space_le.2
  refine ⟨Ln, f, hf, hnd', hq, hcov, ?_⟩
  have hGz' : (stR x Lo false).space ≤ G := by omega
  exact .seq (e1.mono (by rw [stR_space] at hGz' ⊢; omega)) (.seq (e2.mono (by omega))
    (.seq e3 (.seq e4 (.seq (e5.mono s4) (.seq e6 (.seq e7 (.seq (e8.mono s7)
      (.seq (e9.mono (s8.trans s7)) (.skip ((e9.space_le.2.trans s8).trans s7))))))))))

/-- Every input string contributes at least one bit to its `Stacks.encList` encoding. -/
theorem length_le_length_encList : ∀ L : List BitString, L.length ≤ (Stacks.encList L).length
  | [] => le_rfl
  | z :: L => by
    have := length_le_length_encList L
    rw [encList_cons, List.length_append, Stacks.length_encStr, List.length_cons]; omega

/-- Bounds for one mask step, one zero-mask execution, and the encoded query lists. -/
def RoundBounds (c : OTMCode) (e KZ KS CS KM : ℕ) (x : BitString) (G BB : ℕ) : Prop :=
  (∀ (Lo Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln ++ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length → stepBound e KS CS KM x Lo Ln l ≤ G) ∧
  (∀ Lo : List BitString, Lo.Nodup →
      (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      KZ * ((Stacks.encList Lo).length + 1) + (stR x Lo false).space ≤ G) ∧
  (∀ Lo : List BitString, Lo.Nodup →
      (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      (Stacks.encList Lo).length ≤ BB)

/-- **The rounds loop**: rounds until a round finds nothing new. -/
theorem exec_rounds {c : OTMCode} {e : ℕ} {sZero : Stmt 3} {sSel : Stmt 12} {sSim : Stmt 21}
    {sMerge : Stmt 16} {KZ KS CS KM : ℕ} (hZero : ZeroSpec sZero KZ) (hSel : SelSpec sSel KS)
    (hSim : SimSpec c e sSim CS) (hMerge : MergeSpec sMerge KM) (x : BitString) (G BB : ℕ)
    (hBounds : RoundBounds c e KZ KS CS KM x G BB) :
    ∃ Lo : List BitString, Lo.Nodup ∧ (∀ z, z ∈ Lo ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
      Exec (.loop 3 Stmt.isTrue (roundStmt sZero sSel sSim sMerge)) (stR x [] true)
        (stR x Lo false) G := by
  rcases hBounds with ⟨hG, hGz, hB⟩
  set T := clock e x.length with hT
  let J : Stacks 28 → Prop := fun σ => ∃ Lo f, σ = stR x Lo f ∧ Lo.Nodup ∧
    (∀ z ∈ Lo, z ∈ queryAll c.toOTM x T) ∧
    (f = false → ∀ v : BitString, v.length = (Stacks.encList Lo).length →
      ∀ z ∈ queries c.toOTM {z | z ∈ sel v Lo} x T, z ∈ Lo)
  let μ : Stacks 28 → ℕ := fun σ => 2 * (BB - (σ 1).length) + (if σ 3 = [true] then 1 else 0)
  have hstep : ∀ σ, J σ → Stmt.isTrue (σ 3).head? = true →
      ∃ σ', Exec (roundStmt sZero sSel sSim sMerge) σ σ' G ∧ J σ' ∧ μ σ' < μ σ := by
    rintro σ ⟨Lo, f, rfl, hnd, hLo, -⟩ hc
    have hf : f = true := by
      have : (stR x Lo f) 3 = [f] := rfl
      rw [this] at hc; cases f <;> simp_all [Stmt.isTrue]
    subst hf
    obtain ⟨Ln, f', hf', hnd', hLn, hcov, hex⟩ := exec_round hZero hSel hSim hMerge x Lo G hnd
      (fun Ln l h1 h2 h3 => hG Lo Ln l h1 (fun z hz => by
        rcases List.mem_append.1 hz with h | h
        · exact h2 z h
        · exact hLo z h) h3) (hGz Lo hnd hLo)
    have hall : ∀ z ∈ Ln ++ Lo, z ∈ queryAll c.toOTM x T := fun z hz => by
      rcases List.mem_append.1 hz with h | h
      · exact hLn z h
      · exact hLo z h
    refine ⟨_, hex, ⟨Ln ++ Lo, f', rfl, hnd', hall, ?_⟩, ?_⟩
    · intro hf0 v hv z hz
      have hLn0 : Ln = [] := hf'.1 hf0
      subst hLn0
      simp only [List.nil_append] at hv ⊢
      rcases hcov v hv z hz with h | h
      · exact h
      · simp at h
    · have hBB := hB (Ln ++ Lo) hnd' hall
      change 2 * (BB - ((stR x (Ln ++ Lo) f') 1).length) +
          (if (stR x (Ln ++ Lo) f') 3 = [true] then 1 else 0) <
        2 * (BB - ((stR x Lo true) 1).length) + (if (stR x Lo true) 3 = [true] then 1 else 0)
      have a1 : (stR x (Ln ++ Lo) f') 1 = Stacks.encList (Ln ++ Lo) := rfl
      have a2 : (stR x (Ln ++ Lo) f') 3 = [f'] := rfl
      have a3 : (stR x Lo true) 1 = Stacks.encList Lo := rfl
      have a4 : (stR x Lo true) 3 = [true] := rfl
      rw [a1, a2, a3, a4, ite_eq_left rfl]
      rw [encList_append, List.length_append] at hBB ⊢
      by_cases hL : Ln = []
      · have hf0 : f' = false := hf'.2 hL
        subst hL; subst hf0
        simp [encList_nil]
      · have hne : (Stacks.encList Ln).length ≥ 1 := by
          have := length_le_length_encList Ln
          have : Ln.length ≥ 1 := by
            cases Ln with
            | nil => exact absurd rfl hL
            | cons _ _ => simp
          omega
        cases f' <;> simp <;> omega
  have hexit : ∀ σ, J σ → σ.space ≤ G := by
    rintro σ ⟨Lo, f, rfl, hnd, hLo, -⟩
    have := hGz Lo hnd hLo
    rw [stR_space] at this ⊢; omega
  have hJ0 : J (stR x [] true) := ⟨[], true, rfl, List.nodup_nil, by simp, by simp⟩
  obtain ⟨σ', hex, ⟨Lo, f, rfl, hnd, hLo, hfix⟩, hc⟩ :=
    Exec.loop_of_variant J μ G hstep hexit _ hJ0
  have hf : f = false := by
    have : (stR x Lo f) 3 = [f] := rfl
    rw [this] at hc; cases f <;> simp_all [Stmt.isTrue]
  subst hf
  refine ⟨Lo, hnd, fun z => ⟨fun hz => hLo z hz, fun hz => ?_⟩, hex⟩
  exact queryAll_subset_of_fix c.toOTM x T Lo (Stacks.encList Lo).length
    (length_le_length_encList Lo) (hfix rfl) z hz

/-- The enumeration from the initial stacks. -/
theorem exec_qe {c : OTMCode} {e : ℕ} {sZero : Stmt 3} {sSel : Stmt 12} {sSim : Stmt 21}
    {sMerge : Stmt 16} {KZ KS CS KM : ℕ} (hZero : ZeroSpec sZero KZ) (hSel : SelSpec sSel KS)
    (hSim : SimSpec c e sSim CS) (hMerge : MergeSpec sMerge KM) (x : BitString) (G BB : ℕ)
    (hG : ∀ (Lo Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln ++ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length → stepBound e KS CS KM x Lo Ln l ≤ G)
    (hGz : ∀ Lo : List BitString, Lo.Nodup → (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      KZ * ((Stacks.encList Lo).length + 1) + (stR x Lo false).space ≤ G)
    (hB : ∀ Lo : List BitString, Lo.Nodup → (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      (Stacks.encList Lo).length ≤ BB) :
    ∃ L : List BitString, L.Nodup ∧ (∀ z, z ∈ L ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
      Exec (qeStmt sZero sSel sSim sMerge) (Function.update (fun _ => []) 0 x)
        (Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList L)) G := by
  obtain ⟨Lo, hnd, hmem, hex⟩ :=
    exec_rounds hZero hSel hSim hMerge x G BB ⟨hG, hGz, hB⟩
  have h0 := hGz [] List.nodup_nil (by simp)
  rw [stR_space] at h0
  have e1 := Exec.push (r := (3 : Fin 28)) (b := true) (σ := Function.update (fun _ => []) 0 x)
    (S := G) (by
      have : Stacks.space (Function.update (fun _ : Fin 28 => ([] : BitString)) 0 x) =
          x.length := by
        simp [Stacks.space, Fin.sum_univ_succ, Function.update_apply]
      rw [this]; simp only [encList_nil, List.length_nil] at h0; omega)
  have h1 : Function.update (Function.update (fun _ : Fin 28 => ([] : BitString)) 0 x) 3
      (true :: (Function.update (fun _ : Fin 28 => ([] : BitString)) 0 x) 3) = stR x [] true := by
    funext j; fin_cases j <;> rfl
  rw [h1] at e1
  have e2 := Exec.pop (r := (3 : Fin 28)) (σ := stR x Lo false) (S := G) hex.space_le.2
  have h2 : Function.update (stR x Lo false) 3 ((stR x Lo false) 3).tail =
      Function.update (Function.update (fun _ => []) 0 x) 1 (Stacks.encList Lo) := by
    funext j; fin_cases j <;> rfl
  rw [h2] at e2
  exact ⟨Lo, hnd, hmem, .seq e1 (.seq hex (.seq e2 (.skip e2.space_le.2)))⟩

/-! #### Space arithmetic -/

/-- The one-step bound `stepBound` is quadratic in a common bound on all input lengths. -/
theorem stepBound_le (e KS CS KM : ℕ) (x : BitString) (Lo Ln : List BitString)
    (l : BitString) (a : ℕ)
    (hx : x.length ≤ a) (hT : clock e x.length ≤ a)
    (he : (Stacks.encList Lo).length + (Stacks.encList Ln).length ≤ a)
    (hl : l.length = (Stacks.encList Lo).length) (ha : 1 ≤ a) :
    stepBound e KS CS KM x Lo Ln l ≤
      (8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM) * a ^ 2 := by
  unfold stepBound
  rw [stC_space]
  set P0 := x.length + clock e x.length + (Stacks.encList Lo).length + 1 with hP0
  have h1 : P0 ≤ 4 * a := by omega
  have h2 : P0 ^ 2 ≤ 16 * a ^ 2 := by
    calc P0 ^ 2 ≤ (4 * a) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 16 * a ^ 2 := by ring
  have hP : CS * P0 ^ 2 ≤ 16 * (CS * a ^ 2) := by
    calc CS * P0 ^ 2 ≤ CS * (16 * a ^ 2) := Nat.mul_le_mul_left _ h2
      _ = 16 * (CS * a ^ 2) := by ring
  have ha2 : a ≤ a ^ 2 := by nlinarith
  have hKS : KS * ((Stacks.encList Lo).length + l.length + 1) ≤ 3 * (KS * a ^ 2) := by
    calc KS * ((Stacks.encList Lo).length + l.length + 1) ≤ KS * (3 * a ^ 2) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (KS * a ^ 2) := by ring
  have hKM : KM * (CS * P0 ^ 2 + (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1) ≤
      16 * (KM * (CS * a ^ 2)) + 2 * (KM * a ^ 2) := by
    calc KM * (CS * P0 ^ 2 + (Stacks.encList Lo).length + (Stacks.encList Ln).length + 1) ≤
          KM * (16 * (CS * a ^ 2) + 2 * a ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 16 * (KM * (CS * a ^ 2)) + 2 * (KM * a ^ 2) := by ring
  have hR : (8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM) * a ^ 2 =
      8 * a ^ 2 + 16 * (CS * a ^ 2) + 3 * (KS * a ^ 2) + 16 * (KM * (CS * a ^ 2)) +
        2 * (KM * a ^ 2) := by ring
  rw [hR]
  omega

/-- The linear bound `2 * T + 1` is strictly smaller than `2 ^ (T + 1)`. -/
theorem two_mul_add_one_lt (T : ℕ) : 2 * T + 1 < 2 ^ (T + 1) := by
  have := @Nat.lt_two_pow_self T
  rw [pow_succ]; omega

/-- The code of a duplicate-free list of possible queries is short. -/
theorem length_encList_le_sq (M : OTM) (x : BitString) (T n : ℕ) (hn : T + 1 ≤ n)
    (Lo : List BitString)
    (hnd : Lo.Nodup) (hLo : ∀ z ∈ Lo, z ∈ queryAll M x T) :
    (Stacks.encList Lo).length ≤ (2 ^ n) ^ 2 := by
  have hT : ∀ z ∈ Lo, z.length ≤ T := fun z hz => length_le_of_mem_queryAll M x T z (hLo z hz)
  have h1 := length_le_of_nodup T Lo hnd hT
  have h2 := length_encList_le T Lo hT
  have h3 : 2 ^ (T + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 := two_mul_add_one_lt T
  calc (Stacks.encList Lo).length ≤ Lo.length * (2 * T + 1) := h2
    _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (h1.trans h3) (by omega)
    _ = (2 ^ n) ^ 2 := by ring

end QEnum

/-- **Enumeration of the query set.**  For every clocked code `(c, e)` there are a
statement `s` over `k` stacks, two distinct stacks `inp`, `out` and a constant `C` such that,
started with `x` on `inp` and all other stacks empty, `s` terminates with `x` on `inp`, the code
`Stacks.encList L` of a duplicate-free list `L` enumerating exactly
`queryAll c.toOTM x (clock e |x|)`
on `out`, and all other stacks empty, within space `2 ^ (C · (clock e |x| + |x| + 1))`.

Construction (`QEnum.qeStmt`, a fixpoint over subsets of the queries found so far; all runs use
list oracles): the known queries `Lo` start empty; a round enumerates, with a binary counter, every
mask `v` of width `|encList Lo|`, runs the recording simulation (`QEnum.exists_recSimStmt`) with the
oracle `sel v Lo` and merges the new recorded queries into a list `Ln` (`QEnum.exists_mergeStmt`),
then appends `Ln` to `Lo`; rounds repeat until a round finds nothing new.  Soundness: every recorded
query is in `queryAll`; completeness at the fixpoint: `QEnum.queryAll_subset_of_fix`; termination
and space: `QEnum.length_le_of_nodup` (at most `2 ^ (T + 1)` strings of length `≤ T`). -/
theorem exists_queryEnumStmt (c : OTMCode) (e : ℕ) :
    ∃ (k : ℕ) (s : Stmt k) (inp out : Fin k) (C : ℕ), inp ≠ out ∧
      ∀ x : BitString, ∃ L : List BitString, L.Nodup ∧
        (∀ z, z ∈ L ↔ z ∈ queryAll c.toOTM x (clock e x.length)) ∧
        Exec s (Function.update (fun _ => []) inp x)
          (Function.update (Function.update (fun _ => []) inp x) out (Stacks.encList L))
          (2 ^ (C * (clock e x.length + x.length + 1))) := by
  obtain ⟨sSel, KS, hSel⟩ := QEnum.exists_selStmt
  obtain ⟨sZero, KZ, hZero⟩ := QEnum.exists_zeroStmt
  obtain ⟨sMerge, KM, hMerge⟩ := QEnum.exists_mergeStmt
  obtain ⟨sSim, CS, hSim⟩ := QEnum.exists_recSimStmt c e
  refine ⟨28, QEnum.qeStmt sZero sSel sSim sMerge, 0, 1,
    (8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM + 2 * KZ) + 4, by decide, fun x => ?_⟩
  set K0 := 8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM + 2 * KZ with hK0
  set n := clock e x.length + x.length + 1 with hn
  set A := 2 ^ n with hA
  have hA2 : 2 ≤ A := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxA : x.length ≤ A ^ 2 := by
    have h1 := @Nat.lt_two_pow_self x.length
    have h2 : 2 ^ x.length ≤ A := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hTA : clock e x.length ≤ A ^ 2 := by
    have h1 := @Nat.lt_two_pow_self (clock e x.length)
    have h2 : 2 ^ clock e x.length ≤ A := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have h1A : 1 ≤ A ^ 2 := by nlinarith
  have hB : ∀ Lo : List BitString, Lo.Nodup →
      (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      (Stacks.encList Lo).length ≤ A ^ 2 := fun Lo hnd hLo =>
    QEnum.length_encList_le_sq c.toOTM x (clock e x.length) n (by omega) Lo hnd hLo
  have hG : ∀ (Lo Ln : List BitString) (l : BitString), (Ln ++ Lo).Nodup →
      (∀ z ∈ Ln ++ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      l.length = (Stacks.encList Lo).length →
      QEnum.stepBound e KS CS KM x Lo Ln l ≤ K0 * (A ^ 2) ^ 2 := by
    intro Lo Ln l hnd hall hl
    have he := hB (Ln ++ Lo) hnd hall
    rw [QEnum.encList_append, List.length_append] at he
    have := QEnum.stepBound_le e KS CS KM x Lo Ln l (A ^ 2) hxA hTA (by omega) hl h1A
    calc QEnum.stepBound e KS CS KM x Lo Ln l ≤
          (8 + 16 * CS + 3 * KS + 16 * (KM * CS) + 2 * KM) * (A ^ 2) ^ 2 := this
      _ ≤ K0 * (A ^ 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have hGz : ∀ Lo : List BitString, Lo.Nodup →
      (∀ z ∈ Lo, z ∈ queryAll c.toOTM x (clock e x.length)) →
      KZ * ((Stacks.encList Lo).length + 1) + (QEnum.stR x Lo false).space ≤ K0 * (A ^ 2) ^ 2 := by
    intro Lo hnd hLo
    have he := hB Lo hnd hLo
    rw [QEnum.stR_space]
    have ha2 : A ^ 2 ≤ (A ^ 2) ^ 2 := by nlinarith
    have hKZ : KZ * ((Stacks.encList Lo).length + 1) ≤ 2 * (KZ * (A ^ 2) ^ 2) := by
      calc KZ * ((Stacks.encList Lo).length + 1) ≤ KZ * (2 * (A ^ 2) ^ 2) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (KZ * (A ^ 2) ^ 2) := by ring
    have hR : K0 * (A ^ 2) ^ 2 = 8 * (A ^ 2) ^ 2 + 16 * (CS * (A ^ 2) ^ 2) +
        3 * (KS * (A ^ 2) ^ 2) + 16 * (KM * CS * (A ^ 2) ^ 2) + 2 * (KM * (A ^ 2) ^ 2) +
        2 * (KZ * (A ^ 2) ^ 2) := by rw [hK0]; ring
    rw [hR]
    omega
  obtain ⟨L, hnd, hmem, hex⟩ := QEnum.exec_qe hZero hSel hSim hMerge x (K0 * (A ^ 2) ^ 2) (A ^ 2)
    hG hGz hB
  refine ⟨L, hnd, hmem, hex.mono ?_⟩
  rw [mul_comm (K0 + 4) n, pow_mul]
  have hK : K0 ≤ A ^ K0 :=
    (@Nat.lt_two_pow_self K0).le.trans (Nat.pow_le_pow_left hA2 K0)
  calc K0 * (A ^ 2) ^ 2 ≤ A ^ K0 * (A ^ 2) ^ 2 := Nat.mul_le_mul_right _ hK
    _ = A ^ (K0 + 4) := by ring

end Kolmogorov.RandomStrings
