/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSMachine

/-!
# The depth-first search from the root

The run of `DFS.mstep` from the root frame: the scan of the NO moves by the binary counter and
the final theorems `DFS.mstep_root_no_moves` and `DFS.mstep_root`, which relate the machine's
answer to `DFS.gameV`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- Once an initial YES answer succeeds, the root's mode-2 scan finds no legal NO move and
returns true.  Induct over the bit counter `v'`; `isSub` can hold against the all-true root only
at the all-true vector, where the strict-inequality test rejects equality, and the following
increment carries.  `length_incBits` and `frameOK_root` establish `Good` along the scan. -/
private theorem binVal_lt_two_pow (v : BitString) : binVal v < 2 ^ v.length := by
  induction v with
  | nil => simp [binVal]
  | cons b v ih =>
    simp [binVal]
    cases b <;> simp <;> omega

private theorem binVal_replicate_true (m : ℕ) : binVal (List.replicate m true) + 1 = 2 ^ m := by
  induction m with
  | zero => simp [binVal]
  | succ m ih =>
    simp [List.replicate_succ, binVal]
    have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

private theorem incCarry_not_all_true (v : BitString) (m : ℕ) (h : v.length = m)
    (hne : v ≠ List.replicate m true) :
  incCarry v = false := by
  subst h
  induction v with
  | nil =>
    have h1 : ([] : List Bool) = List.replicate 0 true := rfl
    contradiction
  | cons b v ih =>
    cases b
    · simp [incCarry]
    · simp [List.replicate_succ] at hne
      simp [incCarry, ih hne]

private theorem incCarry_replicate_true_all (m : ℕ) : incCarry (List.replicate m true) = true := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, incCarry, ih]

private theorem isSub_all_true_not (v : BitString) (m : ℕ) (h : v.length = m)
    (hne : v ≠ List.replicate m true) :
  isSub (List.replicate m true) v = false := by
  have H_isSub_all_true : isSub (List.replicate m true) v = true ↔ v = List.replicate m true := by
    clear hne
    subst h
    induction v with
    | nil => simp [isSub]
    | cons b v ih =>
      cases b <;> simp [pv_isSub_cons, ih, List.replicate_succ]
  cases hsub : isSub (List.replicate m true) v
  · rfl
  · rw [hsub] at H_isSub_all_true
    have := H_isSub_all_true.mp rfl
    contradiction

private theorem isSub_all_true_true (v : BitString) (m : ℕ) (h : v.length = m)
    (heq : v = List.replicate m true) :
  isSub (List.replicate m true) v = true := by
  subst heq
  clear h
  induction m with
  | zero => simp [isSub]
  | succ m ih =>
    simp [List.replicate_succ, pv_isSub_cons, ih]

private theorem mstep_root_loop (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool)
    (r : BitString) (hr : r.length = m) (v' : BitString) (hv' : v'.length = m) :
    GoodRun m cv E out (2, { root m with r := r, v' := v' } :: []) (6, []) := by
  have H_bound : binVal v' < 2 ^ m := by
    have h_lt := binVal_lt_two_pow v'
    rw [hv'] at h_lt
    exact h_lt
  induction hv_val : 2 ^ m - 1 - binVal v' generalizing v' with
  | zero =>
    have h_eq_bin : binVal v' = 2 ^ m - 1 := by omega
    have h_v_all_true : v' = List.replicate m true := by
      cases h_eq : (v' == List.replicate m true)
      · exfalso
        have hne : v' ≠ List.replicate m true :=
            by intro contra; rw [contra] at h_eq; simp only [BEq.rfl, Bool.true_eq_false] at h_eq
        have h_carry : incCarry v' = false := incCarry_not_all_true v' m hv' hne
        have h_bin_val := binVal_incBits v'
        rw [h_carry] at h_bin_val
        simp only [Bool.toNat_false, mul_zero, add_zero] at h_bin_val
        have h_len_inc : (incBits v').length = m := by rw [length_incBits, hv']
        have h_lt_2 := binVal_lt_two_pow (incBits v')
        rw [h_len_inc] at h_lt_2
        have h_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have hz : binVal (incBits v') = binVal v' + 1 := by exact h_bin_val
        have hzz : binVal v' + 1 = 2 ^ m := by omega
        rw [hzz] at hz
        revert h_lt_2 hz
        generalize 2 ^ m = P
        intro h1 h2
        omega
      · simp only [beq_iff_eq] at h_eq; exact h_eq
    cases h_carry : incCarry v'
    · exfalso
      have h_carry_true : incCarry (List.replicate m true) = true := incCarry_replicate_true_all m
      rw [h_v_all_true, h_carry_true] at h_carry
      contradiction
    · have h_step : mstep m cv E out (2, { root m with r := r, v' := v' } :: []) = (6, []) := by
        simp [mstep, h_carry]
      refine ⟨1, ?_, ?_⟩
      · exact h_step
      · intro t ht
        cases t with
        | zero =>
          have h_eval : (mstep m cv E out)^[0] (2, { root m with r := r, v' := v' } :: []) =
              (2, { root m with r := r, v' := v' } :: []) := rfl
          rw [h_eval]
          have h1 : (2 : ℕ) ≤ 6 := by decide
          have h2 : ({ root m with r := r, v' := v' } :: [] : List Frame).length ≤ m + 2 := by
            have : ({ root m with r := r, v' := v' } :: [] : List Frame).length = 1 := rfl
            rw [this]
            omega
          exact ⟨h1, h2, fun G hG => by
            have h_or : G = { root m with r := r, v' := v' } ∨ G ∈ ([] : List Frame) :=
                List.mem_cons.mp hG
            cases h_or with
            | inl h_eq =>
              subst h_eq
              have hOK := frameOK_root m E
              exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, hv'.le, hr.le⟩
            | inr h_bot => contradiction⟩
        | succ t =>
          cases t with
          | zero =>
            have h_eval : (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' } :: []) =
                (6, []) := h_step
            rw [h_eval]
            have h1 : (6 : ℕ) ≤ 6 := by decide
            have h2 : ([] : List Frame).length ≤ m + 2 := by
              have : ([] : List Frame).length = 0 := rfl
              rw [this]
              omega
            exact ⟨h1, h2, fun G hG => by contradiction⟩
          | succ t => omega
  | succ d ih =>
    have h_carry : incCarry v' = false := by
      cases h : incCarry v'
      · rfl
      · exfalso
        have h1 := binVal_incBits v'
        rw [h] at h1
        simp only [Bool.toNat_true, mul_one] at h1
        have h_len : v'.length = m := hv'
        rw [h_len] at h1
        have H_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have hz : binVal v' = 2 ^ m - 1 := by
          have hz2 : binVal (incBits v') = 2 ^ m := by omega
          have hz3 : binVal v' + 1 = 2 ^ m := by omega
          omega
        omega
    have h_step : mstep m cv E out (2, { root m with r := r, v' := v' } :: []) =
        (1, { root m with r := r, v' := incBits v' } :: []) := by
      simp [mstep, h_carry]
    cases h_eq_all_true : (incBits v' == List.replicate m true)
    · have hne : incBits v' ≠ List.replicate m true := by
        intro c; rw [c] at h_eq_all_true; simp only [BEq.rfl, Bool.true_eq_false] at h_eq_all_true
      have h_step2 : mstep m cv E out (1, { root m with r := r, v' := incBits v' } :: []) =
          (2, { root m with r := r, v' := incBits v' } :: []) := by
        have h_sub : isSub (root m).v (incBits v') = false := by
          have H_root_v : (root m).v = List.replicate m true := rfl
          rw [H_root_v]
          apply isSub_all_true_not (incBits v') m
          · rw [length_incBits, hv']
          · exact hne
        have h_v_eq : (root m).v = List.replicate m true := rfl
        have H1 : ((root m).v == incBits v') = false := by
          cases heq : ((root m).v == incBits v')
          · rfl
          · have h_eq_true := heq
            have h_eq : (root m).v = incBits v' := beq_iff_eq.mp h_eq_true
            have h_not : (root m).v ≠ incBits v' := by
              intro hc; rw [h_v_eq] at hc; exact hne hc.symm
            contradiction
        simp [mstep, h_sub, H1]
      have h_good_run_2 : GoodRun m cv E out (2, { root m with r := r, v' := incBits v' } ::
          []) (6, []) := by
        apply ih (incBits v')
        · rw [length_incBits, hv']
        · have h_bin_val := binVal_incBits v'
          rw [h_carry] at h_bin_val
          simp only [Bool.toNat_false, mul_zero, add_zero] at h_bin_val
          have h_lt := binVal_lt_two_pow (incBits v')
          have h_len_inc : (incBits v').length = m := by rw [length_incBits, hv']
          rw [h_len_inc] at h_lt
          exact h_lt
        · have h_bin_val := binVal_incBits v'
          rw [h_carry] at h_bin_val
          simp at h_bin_val
          omega
      have h_good_run_start : GoodRun m cv E out (2, { root m with r := r, v' := v' } :: [])
          (2, { root m with r := r, v' := incBits v' } :: []) := by
        refine ⟨2, ?_, ?_⟩
        · have step_0_to_1: (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' } :: []) =
            (1, { root m with r := r, v' := incBits v' } :: []) := by
            simp [h_step]
          have step_1_to_2: (mstep m cv E out)^[2] (2, { root m with r := r, v' := v' } :: []) =
              (2, { root m with r := r, v' := incBits v' } :: []) := by
            change mstep m cv E out ((mstep m cv E out)^[1] (2, { root m with r := r, v' :=
                v' } :: [])) = _
            rw [step_0_to_1, h_step2]
          exact step_1_to_2
        · intro t ht
          cases t with
          | zero =>
            have h_eval : (mstep m cv E out)^[0] (2, { root m with r := r, v' := v' } :: []) =
                (2, { root m with r := r, v' := v' } :: []) := rfl
            rw [h_eval]
            have h1 : (2 : ℕ) ≤ 6 := by decide
            have h2 : ({ root m with r := r, v' := v' } :: [] : List Frame).length ≤ m + 2 := by
              have : ({ root m with r := r, v' := v' } :: [] : List Frame).length = 1 := rfl
              rw [this]
              omega
            exact ⟨h1, h2, fun G hG => by
              have h_or : G = { root m with r := r, v' := v' } ∨ G ∈ ([] : List Frame) :=
                  List.mem_cons.mp hG
              cases h_or with
              | inl h_eq =>
                subst h_eq
                have hOK := frameOK_root m E
                exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, hv'.le, hr.le⟩
              | inr h_bot => contradiction⟩
          | succ t =>
            cases t with
            | zero =>
              have h_eval : (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' } :: []) =
                  (1, { root m with r := r, v' := incBits v' } :: []) := by
                simp [h_step]
              rw [h_eval]
              have h1 : (1 : ℕ) ≤ 6 := by decide
              have h2 : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length ≤
                  m + 2 := by
                have : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length =
                    1 := rfl
                rw [this]
                omega
              exact ⟨h1, h2, fun G hG => by
                have h_or : G = { root m with r := r, v' := incBits v' } ∨
                    G ∈ ([] : List Frame) := List.mem_cons.mp hG
                cases h_or with
                | inl h_eq =>
                  subst h_eq
                  have hOK := frameOK_root m E
                  have h_len_inc : (incBits v').length ≤ m := by rw [length_incBits, hv']
                  exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, h_len_inc, hr.le⟩
                | inr h_bot => contradiction⟩
            | succ t =>
              cases t with
              | zero =>
                have step_0_to_1: (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' }
                    :: []) = (1, { root m with r := r, v' := incBits v' } :: []) := by
                  simp [h_step]
                have h_eval: (mstep m cv E out)^[2] (2, { root m with r := r, v' := v' } ::
                    []) = (2, { root m with r := r, v' := incBits v' } :: []) := by
                  change mstep m cv E out ((mstep m cv E out)^[1] (2, { root m with r := r, v' :=
                      v' } :: [])) = _
                  rw [step_0_to_1, h_step2]
                rw [h_eval]
                have h1 : (2 : ℕ) ≤ 6 := by decide
                have h2 : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length
                    ≤ m + 2 := by
                  have : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length =
                      1 := rfl
                  rw [this]
                  omega
                exact ⟨h1, h2, fun G hG => by
                  have h_or : G = { root m with r := r, v' := incBits v' } ∨
                      G ∈ ([] : List Frame) := List.mem_cons.mp hG
                  cases h_or with
                  | inl h_eq =>
                    subst h_eq
                    have hOK := frameOK_root m E
                    have h_len_inc : (incBits v').length ≤ m := by rw [length_incBits, hv']
                    exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, h_len_inc, hr.le⟩
                  | inr h_bot => contradiction⟩
              | succ t => omega
      exact goodRun_trans m cv E out h_good_run_start h_good_run_2
    · simp only [beq_iff_eq] at h_eq_all_true
      have h_sub : isSub (root m).v (incBits v') = true := by
        have H_root_v : (root m).v = List.replicate m true := rfl
        rw [H_root_v]
        apply isSub_all_true_true (incBits v') m
        · rw [length_incBits, hv']
        · exact h_eq_all_true
      have h_step2 : mstep m cv E out (1, { root m with r := r, v' := incBits v' } :: []) =
          (2, { root m with r := r, v' := incBits v' } :: []) := by
        have H_root_v : (root m).v = List.replicate m true := rfl
        have h_v_eq_v' : (root m).v = incBits v' := by rw [H_root_v, h_eq_all_true]
        have H_bool : ((root m).v == incBits v') = true := beq_iff_eq.mpr h_v_eq_v'
        have H_not : (!((root m).v == incBits v')) = false := by
          rw [H_bool]
          rfl
        simp [mstep, h_sub, H_not]
      have h_good_run_2 : GoodRun m cv E out (2, { root m with r := r, v' := incBits v' } ::
          []) (6, []) := by
        apply ih (incBits v')
        · rw [length_incBits, hv']
        · have h_bin_val := binVal_incBits v'
          rw [h_carry] at h_bin_val
          simp at h_bin_val
          have h_lt := binVal_lt_two_pow (incBits v')
          have h_len_inc : (incBits v').length = m := by rw [length_incBits, hv']
          rw [h_len_inc] at h_lt
          exact h_lt
        · have h_bin_val := binVal_incBits v'
          rw [h_carry] at h_bin_val
          simp at h_bin_val
          omega
      have h_good_run_start : GoodRun m cv E out (2, { root m with r := r, v' := v' } :: [])
          (2, { root m with r := r, v' := incBits v' } :: []) := by
        refine ⟨2, ?_, ?_⟩
        · have step_0_to_1: (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' } :: []) =
            (1, { root m with r := r, v' := incBits v' } :: []) := by
            simp [h_step]
          have step_1_to_2: (mstep m cv E out)^[2] (2, { root m with r := r, v' := v' } :: []) =
              (2, { root m with r := r, v' := incBits v' } :: []) := by
            change mstep m cv E out ((mstep m cv E out)^[1] (2, { root m with r := r, v' :=
                v' } :: [])) = _
            rw [step_0_to_1, h_step2]
          exact step_1_to_2
        · intro t ht
          cases t with
          | zero =>
            have h_eval : (mstep m cv E out)^[0] (2, { root m with r := r, v' := v' } :: []) =
                (2, { root m with r := r, v' := v' } :: []) := rfl
            rw [h_eval]
            have h1 : (2 : ℕ) ≤ 6 := by decide
            have h2 : ({ root m with r := r, v' := v' } :: [] : List Frame).length ≤ m + 2 := by
              have : ({ root m with r := r, v' := v' } :: [] : List Frame).length = 1 := rfl
              rw [this]
              omega
            exact ⟨h1, h2, fun G hG => by
              have h_or : G = { root m with r := r, v' := v' } ∨ G ∈ ([] : List Frame) :=
                  List.mem_cons.mp hG
              cases h_or with
              | inl h_eq =>
                subst h_eq
                have hOK := frameOK_root m E
                exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, hv'.le, hr.le⟩
              | inr h_bot => contradiction⟩
          | succ t =>
            cases t with
            | zero =>
              have h_eval : (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' } :: []) =
                  (1, { root m with r := r, v' := incBits v' } :: []) := by
                simp [h_step]
              rw [h_eval]
              have h1 : (1 : ℕ) ≤ 6 := by decide
              have h2 : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length ≤
                  m + 2 := by
                have : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length =
                    1 := rfl
                rw [this]
                omega
              exact ⟨h1, h2, fun G hG => by
                have h_or : G = { root m with r := r, v' := incBits v' } ∨
                    G ∈ ([] : List Frame) := List.mem_cons.mp hG
                cases h_or with
                | inl h_eq =>
                  subst h_eq
                  have hOK := frameOK_root m E
                  have h_len_inc : (incBits v').length ≤ m := by rw [length_incBits, hv']
                  exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, h_len_inc, hr.le⟩
                | inr h_bot => contradiction⟩
            | succ t =>
              cases t with
              | zero =>
                have step_0_to_1: (mstep m cv E out)^[1] (2, { root m with r := r, v' := v' }
                    :: []) = (1, { root m with r := r, v' := incBits v' } :: []) := by
                  simp [h_step]
                have h_eval: (mstep m cv E out)^[2] (2, { root m with r := r, v' := v' } ::
                    []) = (2, { root m with r := r, v' := incBits v' } :: []) := by
                  change mstep m cv E out ((mstep m cv E out)^[1] (2, { root m with r := r, v' :=
                      v' } :: [])) = _
                  rw [step_0_to_1, h_step2]
                rw [h_eval]
                have h1 : (2 : ℕ) ≤ 6 := by decide
                have h2 : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length
                    ≤ m + 2 := by
                  have : ({ root m with r := r, v' := incBits v' } :: [] : List Frame).length =
                      1 := rfl
                  rw [this]
                  omega
                exact ⟨h1, h2, fun G hG => by
                  have h_or : G = { root m with r := r, v' := incBits v' } ∨
                      G ∈ ([] : List Frame) := List.mem_cons.mp hG
                  cases h_or with
                  | inl h_eq =>
                    subst h_eq
                    have hOK := frameOK_root m E
                    have h_len_inc : (incBits v').length ≤ m := by rw [length_incBits, hv']
                    exact ⟨hOK.1, hOK.2.1, hOK.2.2.1, hOK.2.2.2.1, h_len_inc, hr.le⟩
                  | inr h_bot => contradiction⟩
              | succ t => omega
      exact goodRun_trans m cv E out h_good_run_start h_good_run_2

/-- **The machine answers for the root frame when no legal NO moves exist.**
This theorem establishes that from the root frame, after a mode-2 scan finds no legal NO move
and its internal bit counter overflows, the machine halts in the YES-answer state `6`.
-/
theorem mstep_root_no_moves (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool)
    (r : BitString) (hr : r.length = m) :
    GoodRun m cv E out (2, { root m with r := r } :: []) (6, []) := by
  have hv_root_len : ((root m).v').length = m := by
    have : (root m).v' = List.replicate m false := rfl
    rw [this, List.length_replicate]
  exact mstep_root_loop m cv E out r hr (root m).v' hv_root_len

/-- **Sub-contract (pure): the machine computes the game value** (remaining).  The hypothesis
`hcv` (moving from the root position to the empty position costs nothing) holds for the costs
`costV` of the application (`costV_replicate_true_false`). -/
theorem mstep_root (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    (hcv : cv (List.replicate m true) (List.replicate m false) = 0) :
    ∃ t, (mstep m cv E out)^[t] (3, [root m]) = (if gameV m cv E out then 6 else 5, []) ∧
      ∀ t' ≤ t, Good m E ((mstep m cv E out)^[t'] (3, [root m])) := by
  have hrec : ∀ (C : Frame) (L : List Frame), C.f = m → FrameOK m E C →
      (∀ G ∈ L, FrameOK m E G) → L.length + m ≤ m + 1 →
      GoodRun m cv E out (0, C :: L)
        (if safeV m cv E out m C.v C.y C.n then 6 else 5, L) := by
    intro C L hf hC hL hd
    simpa [hf] using mstep_eval_frame m cv E out C L hC hL (by simpa [hf] using hd)
  have hphase := mstep_answer_phase m cv E out m (root m) [] hrec rfl
    (frameOK_root m E) (by simp) (by simp [root]) (by simp [root, hcv])
  simp only at hphase
  rw [show { root m with r := List.replicate m false } = root m by rfl] at hphase
  cases hgame : gameV m cv E out with
  | false =>
    have hn : ¬ ∃ r : BitString, r.length = m ∧ isSub (root m).v' r = true ∧
        (root m).y + cv (root m).v' r ≤ E ∧
        safeV m cv E out m r ((root m).y + cv (root m).v' r)
          ((root m).n + cv (root m).v (root m).v') = true := by
      intro hex
      have := (root_answer_iff_gameV m cv E out hcv).1 hex
      simp [hgame] at this
    obtain ⟨t, ht, hgood⟩ := hphase.2 hn
    exact ⟨t, by simpa [hgame] using ht, hgood⟩
  | true =>
    have hex : ∃ r : BitString, r.length = m ∧ isSub (root m).v' r = true ∧
        (root m).y + cv (root m).v' r ≤ E ∧
        safeV m cv E out m r ((root m).y + cv (root m).v' r)
          ((root m).n + cv (root m).v (root m).v') = true :=
      (root_answer_iff_gameV m cv E out hcv).2 hgame
    obtain ⟨r, hr, hrun⟩ := hphase.1 hex
    have htail := mstep_root_no_moves m cv E out r hr.1
    obtain ⟨t, ht, hgood⟩ := goodRun_trans m cv E out hrun htail
    exact ⟨t, by simpa [hgame] using ht, hgood⟩

end DFS
end Kolmogorov.RandomStrings
