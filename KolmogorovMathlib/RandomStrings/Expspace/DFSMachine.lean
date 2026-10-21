/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSGame

/-!
# The depth-first search as a machine on frames

The frames of the search (`DFS.Frame`), the one-step machine `DFS.mstep`, the invariants
`DFS.FrameOK`, `DFS.Good` and `DFS.GoodRun`, and the phase lemmas `DFS.mstep_answer_phase`,
`DFS.mstep_no_phase` and `DFS.mstep_eval_frame` describing one frame's evaluation.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- A frame of the search: the position `v`, the scores `y` (YES) and `n` (NO), the fuel `f`, the
NO move `v'` and the YES answer `r` under examination. -/
structure Frame where
  v : BitString
  y : ℕ
  n : ℕ
  f : ℕ
  v' : BitString
  r : BitString

/-- The six strings coding a frame. -/
def Frame.fields (W : ℕ) (F : Frame) : List BitString :=
  [F.v, numBits W F.y, numBits W F.n, List.replicate F.f true, F.v', F.r]

/-- Mode `0` after the outcome `b` of the position of the top frame. -/
def enterStep (m : ℕ) (b : Bool) (F : Frame) (K : List Frame) : ℕ × List Frame :=
  if b then (if F.f = 0 then (6, K) else (1, { F with v' := List.replicate m false } :: K))
  else (5, K)

/-- One step of the search machine: modes `0` enter a frame, `1` check the NO move, `2` next NO
move, `3` check the YES answer, `4` next YES answer, `5`/`6` return `false`/`true` to the frame
below (with no frame below the machine has halted). -/
def mstep (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool) :
    ℕ × List Frame → ℕ × List Frame
  | (0, F :: K) => enterStep m (out F.v) F K
  | (1, F :: K) => if isSub F.v F.v' && !(F.v == F.v') && decide (F.n + cv F.v F.v' ≤ E) then
      (3, { F with r := List.replicate m false } :: K) else (2, F :: K)
  | (2, F :: K) => if incCarry F.v' then (6, K) else (1, { F with v' := incBits F.v' } :: K)
  | (3, F :: K) => if isSub F.v' F.r && decide (F.y + cv F.v' F.r ≤ E) then
      (0, ⟨F.r, F.y + cv F.v' F.r, F.n + cv F.v F.v', F.f - 1, [], []⟩ :: F :: K)
    else (4, F :: K)
  | (4, F :: K) => if incCarry F.r then (5, K) else (3, { F with r := incBits F.r } :: K)
  | (5, F :: K) => (4, F :: K)
  | (6, F :: K) => (2, F :: K)
  | s => s

/-- The root frame: its NO moves are never legal (`v` is full), its YES answers are the first
moves of `gameValB`. -/
def root (m : ℕ) : Frame :=
  ⟨List.replicate m true, 0, 0, m + 1, List.replicate m false, List.replicate m false⟩

/-- Bounds on a frame. -/
def FrameOK (m E : ℕ) (F : Frame) : Prop :=
  F.v.length = m ∧ F.y ≤ E ∧ F.n ≤ E ∧ F.f ≤ m + 1 ∧ F.v'.length ≤ m ∧ F.r.length ≤ m

/-- Bounds on a state of the machine. -/
def Good (m E : ℕ) (st : ℕ × List Frame) : Prop :=
  st.1 ≤ 6 ∧ st.2.length ≤ m + 2 ∧ ∀ F ∈ st.2, FrameOK m E F

/-- Moving to the empty position costs nothing: no bit is newly set. -/
theorem costV_replicate_true_false (c : List ℕ) (m : ℕ) :
    costV c (List.replicate m true) (List.replicate m false) = 0 := by
  induction c generalizing m with
  | nil => simp [costV]
  | cons a c ih =>
    cases m with
    | zero => simp [costV]
    | succ m =>
      rw [List.replicate_succ, List.replicate_succ, pv_costV_cons, ih]
      rfl

/-- A finite run of the search machine whose states, including both endpoints, satisfy `Good`.
This packages the two conclusions which have to be threaded through each of the enumeration
phases below. -/
def GoodRun (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    (s z : ℕ × List Frame) : Prop :=
  ∃ t, (mstep m cv E out)^[t] s = z ∧
    ∀ t' ≤ t, Good m E ((mstep m cv E out)^[t'] s)

/-- Good runs compose.  Unpack the two witnesses, use `Function.iterate_add_apply`, and split an
index below their sum according as it lies in the first run or in the translated second run;
`omega` handles the index arithmetic. -/
theorem goodRun_trans (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    {s u z : ℕ × List Frame} :
    GoodRun m cv E out s u → GoodRun m cv E out u z → GoodRun m cv E out s z := by
  rintro ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩
  refine ⟨b + a, ?_, ?_⟩
  · rw [Function.iterate_add_apply, ha, hb]
  · intro i hi
    by_cases hia : i ≤ a
    · exact hga i hia
    · obtain ⟨j, rfl⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
      rw [Nat.add_comm a j, Function.iterate_add_apply, ha]
      exact hgb j (by omega)

/-- The root frame satisfies all syntactic bounds.  Unfold `root` and `FrameOK`; list lengths are
`List.length_replicate`, and all remaining goals are elementary inequalities. -/
theorem frameOK_root (m E : ℕ) : FrameOK m E (root m) := by
  simp [FrameOK, root]

/-- Every width-`m` vector contains the all-false vector.  Induct simultaneously over `m` and the
vector, using its length hypothesis to rule out the mismatched cases, then unfold one layer of
`isSub`. -/
theorem isSub_replicate_false_left (m : ℕ) (r : BitString) (hr : r.length = m) :
    isSub (List.replicate m false) r = true := by
  induction m generalizing r with
  | zero =>
    cases r with
    | nil => rfl
    | cons b r => simp at hr
  | succ m ih =>
    cases r with
    | nil => simp at hr
    | cons b r =>
      simp only [List.length_cons, Nat.succ.injEq] at hr
      rw [List.replicate_succ, pv_isSub_cons, ih r hr]
      simp

/-- At the root, the semantic condition tested by the mode-3 answer enumeration is exactly
`gameV`.  Unfold `root` and `gameV`, use `isSub_replicate_false_left`, and rewrite the accumulated
NO cost with `hcv`; simplification then removes the zero additions. -/
theorem root_answer_iff_gameV (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool)
    (hcv : cv (List.replicate m true) (List.replicate m false) = 0) :
    (∃ r : BitString, r.length = m ∧ isSub (root m).v' r = true ∧
      (root m).y + cv (root m).v' r ≤ E ∧
      safeV m cv E out m r ((root m).y + cv (root m).v' r)
        ((root m).n + cv (root m).v (root m).v') = true) ↔
      gameV m cv E out = true := by
  dsimp [root, gameV]
  simp only [hcv, add_zero, zero_add, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, _, h1, h2⟩
    exact ⟨r, hr, h1, h2⟩
  · rintro ⟨r, hr, h1, h2⟩
    exact ⟨r, hr, isSub_replicate_false_left m r hr, h1, h2⟩

/-- Mode `3` enumerates all candidate YES answers for the current NO move.  Prove this by
induction on the remaining binary values from `F.r`, using `binVal_incBits`; on a legal candidate,
apply `hrec` to the child frame, and continue in mode `4` exactly when that recursive call is
false.  Length preservation follows from `length_incBits`, while the displayed depth bound makes
every child stack satisfy the recursive contract. The current NO move must satisfy `hNo`
to bound the child's NO score; the callers obtain this from the legal-move test or root cost. -/
theorem mstep_answer_phase (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    (f : ℕ) (F : Frame) (K : List Frame)
    (hrec : ∀ (C : Frame) (L : List Frame), C.f = f → FrameOK m E C →
      (∀ G ∈ L, FrameOK m E G) → L.length + f ≤ m + 1 →
      GoodRun m cv E out (0, C :: L)
        (if safeV m cv E out f C.v C.y C.n then 6 else 5, L))
    (hf : F.f = f + 1) (hF : FrameOK m E F) (hK : ∀ G ∈ K, FrameOK m E G)
    (hdepth : K.length + F.f ≤ m + 1) (hNo : F.n + cv F.v F.v' ≤ E) :
    let Answer := fun r : BitString => r.length = m ∧ isSub F.v' r = true ∧
      F.y + cv F.v' r ≤ E ∧
      safeV m cv E out f r (F.y + cv F.v' r) (F.n + cv F.v F.v') = true
    ((∃ r, Answer r) → ∃ r, Answer r ∧
      GoodRun m cv E out (3, { F with r := List.replicate m false } :: K)
        (2, { F with r := r } :: K)) ∧
    ((¬ ∃ r, Answer r) →
      GoodRun m cv E out (3, { F with r := List.replicate m false } :: K) (5, K)) := by
  classical
  let Answer := fun r : BitString => r.length = m ∧ isSub F.v' r = true ∧
    F.y + cv F.v' r ≤ E ∧
    safeV m cv E out f r (F.y + cv F.v' r) (F.n + cv F.v F.v') = true
  let Tail := fun q : BitString => ∃ r, binVal q ≤ binVal r ∧ Answer r
  change ((∃ r, Answer r) → ∃ r, Answer r ∧
      GoodRun m cv E out (3, { F with r := List.replicate m false } :: K)
        (2, { F with r := r } :: K)) ∧
    ((¬ ∃ r, Answer r) →
      GoodRun m cv E out (3, { F with r := List.replicate m false } :: K) (5, K))
  have hklen : K.length ≤ m := by omega
  have hframe (q : BitString) (hq : q.length ≤ m) : FrameOK m E { F with r := q } := by
    rcases hF with ⟨hv, hy, hn, hfuel, hv', _⟩
    exact ⟨hv, hy, hn, hfuel, hv', hq⟩
  have hstack (G : Frame) (hG : FrameOK m E G) (mode : ℕ) (hmode : mode ≤ 6) :
      Good m E (mode, G :: K) := by
    refine ⟨hmode, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro H hH
      simp only [List.mem_cons] at hH
      rcases hH with rfl | hH
      · exact hG
      · exact hK H hH
  have hreturn (mode : ℕ) (hmode : mode ≤ 6) : Good m E (mode, K) := by
    refine ⟨hmode, ?_, hK⟩
    change K.length ≤ m + 2
    omega
  have run_step (s z : ℕ × List Frame) (hs : Good m E s) (hz : Good m E z)
      (hst : mstep m cv E out s = z) : GoodRun m cv E out s z := by
    refine ⟨1, ?_, ?_⟩
    · simpa using hst
    · intro i hi
      interval_cases i
      · exact hs
      · simpa [Function.iterate_succ_apply, hst] using hz
  have run_start {s z : ℕ × List Frame} (hrun : GoodRun m cv E out s z) : Good m E s := by
    rcases hrun with ⟨t, _, hgood⟩
    simpa using hgood 0 (Nat.zero_le t)
  have aux (q : BitString) (hq : q.length = m) :
      (Tail q → ∃ r, Answer r ∧
        GoodRun m cv E out (3, { F with r := q } :: K) (2, { F with r := r } :: K)) ∧
      (¬ Tail q → GoodRun m cv E out (3, { F with r := q } :: K) (5, K)) := by
    generalize hd : 2 ^ m - binVal q = d
    induction d using Nat.strong_induction_on generalizing q with
    | h d ih =>
      let Fq : Frame := { F with r := q }
      have hFq : FrameOK m E Fq := by
        simpa [Fq] using hframe q (Nat.le_of_eq hq)
      have hqval : binVal q < 2 ^ m := by
        simpa [hq] using binVal_lt q
      have hcontinue (hnot : ¬ Answer q)
          (hto4 : GoodRun m cv E out (3, Fq :: K) (4, Fq :: K)) :
          (Tail q → ∃ r, Answer r ∧
            GoodRun m cv E out (3, Fq :: K) (2, { F with r := r } :: K)) ∧
          (¬ Tail q → GoodRun m cv E out (3, Fq :: K) (5, K)) := by
        cases hcar : incCarry q with
        | false =>
          have hincLen : (incBits q).length = m := by rw [length_incBits, hq]
          have hincVal : binVal (incBits q) = binVal q + 1 := by
            have hv := binVal_incBits q
            simp [hcar] at hv
            omega
          have hdec : 2 ^ m - binVal (incBits q) < d := by
            calc
              2 ^ m - binVal (incBits q) < 2 ^ m - binVal q :=
                Nat.sub_lt_sub_left hqval (by omega)
              _ = d := hd
          have hFinc : FrameOK m E { F with r := incBits q } :=
            hframe (incBits q) (Nat.le_of_eq hincLen)
          have hto3 : GoodRun m cv E out (4, Fq :: K)
              (3, { F with r := incBits q } :: K) := by
            apply run_step _ _ (hstack Fq hFq 4 (by omega))
              (hstack _ hFinc 3 (by omega))
            simp [mstep, Fq, hcar]
          constructor
          · rintro ⟨r, hqr, hr⟩
            have hne : binVal q ≠ binVal r := by
              intro heq
              have hEq : q = r := QEnum.binVal_inj (by rw [hq, hr.1]) heq
              apply hnot
              simpa [hEq] using hr
            have hnext : Tail (incBits q) := ⟨r, by omega, hr⟩
            obtain ⟨r, hr, htail⟩ :=
              (ih (2 ^ m - binVal (incBits q)) hdec (incBits q) hincLen rfl).1 hnext
            exact ⟨r, hr, goodRun_trans m cv E out
              (goodRun_trans m cv E out hto4 hto3) htail⟩
          · intro hn
            have hnnext : ¬ Tail (incBits q) := by
              rintro ⟨r, hir, hr⟩
              apply hn
              exact ⟨r, by omega, hr⟩
            have htail :=
              (ih (2 ^ m - binVal (incBits q)) hdec (incBits q) hincLen rfl).2 hnnext
            exact goodRun_trans m cv E out (goodRun_trans m cv E out hto4 hto3) htail
        | true =>
          have hto5 : GoodRun m cv E out (4, Fq :: K) (5, K) := by
            apply run_step _ _ (hstack Fq hFq 4 (by omega)) (hreturn 5 (by omega))
            simp [mstep, Fq, hcar]
          constructor
          · rintro ⟨r, hqr, hr⟩
            have hrval : binVal r < 2 ^ m := by
              simpa [hr.1] using binVal_lt r
            have hcarry := binVal_incBits q
            simp [hcar, hq] at hcarry
            have heqval : binVal q = binVal r := by omega
            have heq : q = r := QEnum.binVal_inj (by rw [hq, hr.1]) heqval
            exact False.elim (hnot (by simpa [heq] using hr))
          · intro _
            exact goodRun_trans m cv E out hto4 hto5
      by_cases htest :
          (isSub F.v' q && decide (F.y + cv F.v' q ≤ E)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
        rcases htest with ⟨hsub, hcost⟩
        let C : Frame :=
          ⟨q, F.y + cv F.v' q, F.n + cv F.v F.v', F.f - 1, [], []⟩
        have hCf : C.f = f := by simp [C, hf]
        have hC : FrameOK m E C := by
          rcases hF with ⟨_, _, _, hfuel, _, _⟩
          exact ⟨hq, hcost, hNo, by simp [C, hf]; omega, by simp [C], by simp [C]⟩
        have hL : ∀ G ∈ Fq :: K, FrameOK m E G := by
          intro G hG
          simp only [List.mem_cons] at hG
          rcases hG with rfl | hG
          · exact hFq
          · exact hK G hG
        have hchild := hrec C (Fq :: K) hCf hC hL (by simp [hf] at hdepth ⊢; omega)
        have hto0 : GoodRun m cv E out (3, Fq :: K) (0, C :: Fq :: K) := by
          apply run_step _ _ (hstack Fq hFq 3 (by omega)) (run_start hchild)
          simp [mstep, Fq, C, hsub, hcost]
        by_cases hsafe : safeV m cv E out f q (F.y + cv F.v' q)
            (F.n + cv F.v F.v') = true
        · have hans : Answer q := ⟨hq, hsub, hcost, hsafe⟩
          have hchild' : GoodRun m cv E out (0, C :: Fq :: K) (6, Fq :: K) := by
            simpa [C, Fq, hsafe] using hchild
          have hto2 : GoodRun m cv E out (6, Fq :: K) (2, Fq :: K) := by
            apply run_step _ _ (hstack Fq hFq 6 (by omega)) (hstack Fq hFq 2 (by omega))
            simp [mstep]
          have hrun : GoodRun m cv E out (3, Fq :: K) (2, Fq :: K) :=
            goodRun_trans m cv E out
              (goodRun_trans m cv E out hto0 hchild') hto2
          constructor
          · intro _
            exact ⟨q, hans, by simpa [Fq] using hrun⟩
          · intro hn
            exact False.elim (hn ⟨q, by omega, hans⟩)
        · have hsafe' : safeV m cv E out f q (F.y + cv F.v' q)
              (F.n + cv F.v F.v') = false := by
            cases h : safeV m cv E out f q (F.y + cv F.v' q)
                (F.n + cv F.v F.v')
            · rfl
            · exact False.elim (hsafe h)
          have hnot : ¬ Answer q := by
            intro ha
            exact Bool.noConfusion (hsafe'.symm.trans ha.2.2.2)
          have hchild' : GoodRun m cv E out (0, C :: Fq :: K) (5, Fq :: K) := by
            simpa [C, Fq, hsafe'] using hchild
          have hto4' : GoodRun m cv E out (5, Fq :: K) (4, Fq :: K) := by
            apply run_step _ _ (hstack Fq hFq 5 (by omega)) (hstack Fq hFq 4 (by omega))
            simp [mstep]
          have hto4 := goodRun_trans m cv E out
            (goodRun_trans m cv E out hto0 hchild') hto4'
          exact hcontinue hnot hto4
      · have hnot : ¬ Answer q := by
          intro ha
          apply htest
          simp [ha.2.1, ha.2.2.1]
        have hto4 : GoodRun m cv E out (3, Fq :: K) (4, Fq :: K) := by
          apply run_step _ _ (hstack Fq hFq 3 (by omega)) (hstack Fq hFq 4 (by omega))
          simp [mstep, Fq, htest]
        exact hcontinue hnot hto4
  have haux := aux (List.replicate m false) (by simp)
  constructor
  · intro hex
    apply haux.1
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, by simp [binVal_replicate_false], hr⟩
  · intro hn
    apply haux.2
    rintro ⟨r, _, hr⟩
    exact hn ⟨r, hr⟩

/-- A single machine transition between good states is a good run. -/
private theorem goodRun_step (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool)
    (s z : ℕ × List Frame) (hs : Good m E s) (hz : Good m E z)
    (hstep : mstep m cv E out s = z) : GoodRun m cv E out s z := by
  refine ⟨1, ?_, ?_⟩
  · simpa using hstep
  · intro i hi
    interval_cases i
    · exact hs
    · simpa [Function.iterate_succ_apply, hstep] using hz

/-- Bundled hypotheses for `mstep_no_phase_aux`.
This structure collects the recursive hypothesis for fuel `f` children,
the index condition `F.f = f + 1`, the well-formedness of the current
frame `F` and stack `K`, and the stack depth bound. -/
structure MStepNoPhaseAuxHyp (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool) (f : ℕ) (F : Frame) (K : List Frame) : Prop where
  /-- The recursive step hypothesis. -/
  hrec : ∀ (C : Frame) (L : List Frame), C.f = f → FrameOK m E C →
    (∀ G ∈ L, FrameOK m E G) → L.length + f ≤ m + 1 →
    GoodRun m cv E out (0, C :: L)
      (if safeV m cv E out f C.v C.y C.n then 6 else 5, L)
  /-- The current frame's phase index. -/
  hf : F.f = f + 1
  /-- The current frame is well-formed. -/
  hF : FrameOK m E F
  /-- The stack is well-formed. -/
  hK : ∀ G ∈ K, FrameOK m E G
  /-- The stack depth is bounded. -/
  hdepth : K.length + F.f ≤ m + 1

/-- The mode-1/mode-2 loop, started at `List.replicate m false`.  The two conclusions
correspond to whether every legal vector at or after the start vector has an answer. -/
private theorem mstep_no_phase_aux (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool) (f : ℕ) (F : Frame) (K : List Frame)
    (H : MStepNoPhaseAuxHyp m cv E out f F K)
    (curr : BitString) (hcurr : curr.length ≤ m) :
    let Legal := fun u : BitString => isSub F.v u = true ∧ F.v ≠ u ∧ F.n + cv F.v u ≤ E
    let Answer := fun u r : BitString => r.length = m ∧ isSub u r = true ∧
      F.y + cv u r ≤ E ∧ safeV m cv E out f r (F.y + cv u r)
        (F.n + cv F.v u) = true
    let All := fun w : BitString => ∀ u : BitString, u.length = m → binVal w ≤ binVal u →
      Legal u → ∃ r, Answer u r
    (All (List.replicate m false) → GoodRun m cv E out
      (1, { F with v' := List.replicate m false, r := curr } :: K) (6, K)) ∧
    (¬ All (List.replicate m false) → GoodRun m cv E out
      (1, { F with v' := List.replicate m false, r := curr } :: K) (5, K)) := by
  obtain ⟨hrec, hf, hF, hK, hdepth⟩ := H
  suffices key : ∀ v' curr : BitString, v'.length = m → curr.length ≤ m →
      let Legal := fun u : BitString => isSub F.v u = true ∧ F.v ≠ u ∧ F.n + cv F.v u ≤ E
      let Answer := fun u r : BitString => r.length = m ∧ isSub u r = true ∧
        F.y + cv u r ≤ E ∧ safeV m cv E out f r (F.y + cv u r) (F.n + cv F.v u) = true
      let All := fun w : BitString => ∀ u : BitString, u.length = m → binVal w ≤ binVal u →
        Legal u → ∃ r, Answer u r
      (All v' → GoodRun m cv E out (1, { F with v' := v', r := curr } :: K) (6, K)) ∧
      (¬ All v' → GoodRun m cv E out (1, { F with v' := v', r := curr } :: K) (5, K)) by
    exact key (List.replicate m false) curr (by simp) hcurr
  intro v' curr hv' hcurr
  let Legal := fun u : BitString => isSub F.v u = true ∧ F.v ≠ u ∧ F.n + cv F.v u ≤ E
  let Answer := fun u r : BitString => r.length = m ∧ isSub u r = true ∧
    F.y + cv u r ≤ E ∧ safeV m cv E out f r (F.y + cv u r) (F.n + cv F.v u) = true
  let All := fun w : BitString => ∀ u : BitString, u.length = m → binVal w ≤ binVal u →
    Legal u → ∃ r, Answer u r
  have hframe (w q : BitString) (hw : w.length ≤ m) (hq : q.length ≤ m) :
      FrameOK m E { F with v' := w, r := q } := by
    rcases hF with ⟨hv, hy, hn, hfuel, _, _⟩
    exact ⟨hv, hy, hn, hfuel, hw, hq⟩
  have hklen : K.length ≤ m := by omega
  have hstack (G : Frame) (hG : FrameOK m E G) (mode : ℕ) (hmode : mode ≤ 6) :
      Good m E (mode, G :: K) := by
    refine ⟨hmode, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro H hH
      simp only [List.mem_cons] at hH
      rcases hH with rfl | hH
      · exact hG
      · exact hK H hH
  have hreturn (mode : ℕ) (hmode : mode ≤ 6) : Good m E (mode, K) := by
    exact ⟨hmode, Nat.le_add_right_of_le hklen, hK⟩
  generalize hd : 2 ^ m - binVal v' = d
  induction d using Nat.strong_induction_on generalizing v' curr with
  | h d ih =>
    have hvlt := binVal_lt v'
    have hvltm : binVal v' < 2 ^ m := by simpa [hv'] using hvlt
    have hstartF := hframe v' curr (by omega) hcurr
    have hstart := hstack _ hstartF 1 (by omega)
    by_cases htest :
        (isSub F.v v' && !(F.v == v') && decide (F.n + cv F.v v' ≤ E)) = true
    · have hlegal : Legal v' := by
        dsimp [Legal]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
        rcases htest with ⟨⟨hsub, hne⟩, hcost⟩
        refine ⟨hsub, ?_, hcost⟩
        intro heq
        subst v'
        simp at hne
      let Fc : Frame := { F with v' := v', r := curr }
      have hFc : FrameOK m E Fc := hstartF
      have hfalse : (List.replicate m false).length ≤ m := by simp
      have hphaseF : FrameOK m E { Fc with r := List.replicate m false } := by
        simpa [Fc] using hframe v' (List.replicate m false) (by omega) hfalse
      have hto3 : GoodRun m cv E out (1, Fc :: K)
          (3, { Fc with r := List.replicate m false } :: K) := by
        apply goodRun_step m cv E out _ _ hstart (hstack _ hphaseF 3 (by omega))
        simp [mstep, Fc, htest]
      have hphase := mstep_answer_phase m cv E out f Fc K hrec
        (by simpa [Fc] using hf) hFc hK (by simpa [Fc] using hdepth)
        (by simpa [Fc] using hlegal.2.2)
      dsimp only at hphase
      have hphase_yes : (∃ r, Answer v' r) → ∃ r, Answer v' r ∧
          GoodRun m cv E out (3, { Fc with r := List.replicate m false } :: K)
            (2, { Fc with r := r } :: K) := by
        intro hex
        have hex' : ∃ r : BitString, r.length = m ∧ isSub Fc.v' r = true ∧
            Fc.y + cv Fc.v' r ≤ E ∧ safeV m cv E out f r (Fc.y + cv Fc.v' r)
              (Fc.n + cv Fc.v Fc.v') = true := by
          simpa [Answer, Fc] using hex
        obtain ⟨r, hr, hrun⟩ := hphase.1 hex'
        refine ⟨r, ?_, hrun⟩
        simpa [Answer, Fc] using hr
      have hphase_no : (¬ ∃ r, Answer v' r) →
          GoodRun m cv E out (3, { Fc with r := List.replicate m false } :: K) (5, K) := by
        intro hno
        apply hphase.2
        simpa [Answer, Fc] using hno
      constructor
      · intro hall
        have hex : ∃ r, Answer v' r := hall v' hv' (by omega) hlegal
        obtain ⟨r, hr, hanswer⟩ := hphase_yes hex
        have hrlen : r.length ≤ m := by rcases hr with ⟨hr, _⟩; omega
        have hstate2 : Good m E (2, { Fc with r := r } :: K) := by
          apply hstack _ _ 2 (by omega)
          simpa [Fc] using hframe v' r (by omega) hrlen
        cases hcar : incCarry v'
        · have hincLen : (incBits v').length = m := by rw [length_incBits, hv']
          have hincVal : binVal (incBits v') = binVal v' + 1 := by
            have h := binVal_incBits v'
            simp [hcar] at h
            omega
          have hdec : 2 ^ m - binVal (incBits v') < d := by
            calc
              2 ^ m - binVal (incBits v') < 2 ^ m - binVal v' :=
                Nat.sub_lt_sub_left hvltm (by omega)
              _ = d := hd
          have hnext : All (incBits v') := by
            intro u hu hge hleg
            exact hall u hu (by omega) hleg
          have hstate1 : Good m E
              (1, { Fc with v' := incBits v', r := r } :: K) := by
            apply hstack _ _ 1 (by omega)
            simpa [Fc] using hframe (incBits v') r (Nat.le_of_eq hincLen) hrlen
          have hto1 : GoodRun m cv E out (2, { Fc with r := r } :: K)
              (1, { Fc with v' := incBits v', r := r } :: K) := by
            apply goodRun_step m cv E out _ _ hstate2 hstate1
            simp [mstep, Fc, hcar]
          have htail := (ih (2 ^ m - binVal (incBits v')) hdec
            (incBits v') r hincLen hrlen rfl).1 hnext
          exact goodRun_trans m cv E out
            (goodRun_trans m cv E out (goodRun_trans m cv E out hto3 hanswer) hto1) htail
        · have hto6 : GoodRun m cv E out (2, { Fc with r := r } :: K) (6, K) := by
            apply goodRun_step m cv E out _ _ hstate2 (hreturn 6 (by omega))
            simp [mstep, Fc, hcar]
          exact goodRun_trans m cv E out (goodRun_trans m cv E out hto3 hanswer) hto6
      · intro hnall
        by_cases hex : ∃ r, Answer v' r
        · obtain ⟨r, hr, hanswer⟩ := hphase_yes hex
          have hrlen : r.length ≤ m := by rcases hr with ⟨hr, _⟩; omega
          have hstate2 : Good m E (2, { Fc with r := r } :: K) := by
            apply hstack _ _ 2 (by omega)
            simpa [Fc] using hframe v' r (by omega) hrlen
          cases hcar : incCarry v'
          · have hincLen : (incBits v').length = m := by rw [length_incBits, hv']
            have hincVal : binVal (incBits v') = binVal v' + 1 := by
              have h := binVal_incBits v'
              simp [hcar] at h
              omega
            have hdec : 2 ^ m - binVal (incBits v') < d := by
              calc
                2 ^ m - binVal (incBits v') < 2 ^ m - binVal v' :=
                  Nat.sub_lt_sub_left hvltm (by omega)
                _ = d := hd
            have hnnext : ¬ All (incBits v') := by
              intro hnext
              apply hnall
              intro u hu hge hleg
              by_cases heq : binVal u = binVal v'
              · have huv : u = v' := QEnum.binVal_inj (by omega) heq
                simpa [huv] using hex
              · exact hnext u hu (by omega) hleg
            have hstate1 : Good m E
                (1, { Fc with v' := incBits v', r := r } :: K) := by
              apply hstack _ _ 1 (by omega)
              simpa [Fc] using hframe (incBits v') r (Nat.le_of_eq hincLen) hrlen
            have hto1 : GoodRun m cv E out (2, { Fc with r := r } :: K)
                (1, { Fc with v' := incBits v', r := r } :: K) := by
              apply goodRun_step m cv E out _ _ hstate2 hstate1
              simp [mstep, Fc, hcar]
            have htail := (ih (2 ^ m - binVal (incBits v')) hdec
              (incBits v') r hincLen hrlen rfl).2 hnnext
            exact goodRun_trans m cv E out
              (goodRun_trans m cv E out (goodRun_trans m cv E out hto3 hanswer) hto1) htail
          · exfalso
            apply hnall
            intro u hu hge hleg
            have hval := binVal_lt u
            have hvalm : binVal u < 2 ^ m := by simpa [hu] using hval
            have hcarry := binVal_incBits v'
            simp [hcar, hv'] at hcarry
            have heq : binVal u = binVal v' := by omega
            have huv : u = v' := QEnum.binVal_inj (by omega) heq
            simpa [huv] using hex
        · exact goodRun_trans m cv E out hto3 (hphase_no hex)
    · have hnlegal : ¬ Legal v' := by
        intro hlegal
        apply htest
        rcases hlegal with ⟨hsub, hne, hcost⟩
        simp [hsub, hne, hcost]
      let Fc : Frame := { F with v' := v', r := curr }
      have hstate2 : Good m E (2, Fc :: K) := hstack _ hstartF 2 (by omega)
      have hto2 : GoodRun m cv E out (1, Fc :: K) (2, Fc :: K) := by
        apply goodRun_step m cv E out _ _ hstart hstate2
        simp [mstep, Fc, htest]
      cases hcar : incCarry v'
      · have hincLen : (incBits v').length = m := by rw [length_incBits, hv']
        have hincVal : binVal (incBits v') = binVal v' + 1 := by
          have h := binVal_incBits v'
          simp [hcar] at h
          omega
        have hdec : 2 ^ m - binVal (incBits v') < d := by
          calc
            2 ^ m - binVal (incBits v') < 2 ^ m - binVal v' :=
              Nat.sub_lt_sub_left hvltm (by omega)
            _ = d := hd
        have hstate1 : Good m E
            (1, { Fc with v' := incBits v' } :: K) := by
          apply hstack _ _ 1 (by omega)
          simpa [Fc] using hframe (incBits v') curr (Nat.le_of_eq hincLen) hcurr
        have hto1 : GoodRun m cv E out (2, Fc :: K)
            (1, { Fc with v' := incBits v' } :: K) := by
          apply goodRun_step m cv E out _ _ hstate2 hstate1
          simp [mstep, Fc, hcar]
        constructor
        · intro hall
          have hnext : All (incBits v') := by
            intro u hu hge hleg
            exact hall u hu (by omega) hleg
          have htail := (ih (2 ^ m - binVal (incBits v')) hdec
            (incBits v') curr hincLen hcurr rfl).1 hnext
          exact goodRun_trans m cv E out (goodRun_trans m cv E out hto2 hto1) htail
        · intro hnall
          have hnnext : ¬ All (incBits v') := by
            intro hnext
            apply hnall
            intro u hu hge hleg
            by_cases heq : binVal u = binVal v'
            · have huv : u = v' := QEnum.binVal_inj (by omega) heq
              exact False.elim (hnlegal (huv ▸ hleg))
            · exact hnext u hu (by omega) hleg
          have htail := (ih (2 ^ m - binVal (incBits v')) hdec
            (incBits v') curr hincLen hcurr rfl).2 hnnext
          exact goodRun_trans m cv E out (goodRun_trans m cv E out hto2 hto1) htail
      · have hto6 : GoodRun m cv E out (2, Fc :: K) (6, K) := by
          apply goodRun_step m cv E out _ _ hstate2 (hreturn 6 (by omega))
          simp [mstep, Fc, hcar]
        constructor
        · intro _
          exact goodRun_trans m cv E out hto2 hto6
        · intro hnall
          exfalso
          apply hnall
          intro u hu hge hleg
          have hval := binVal_lt u
          have hvalm : binVal u < 2 ^ m := by simpa [hu] using hval
          have hcarry := binVal_incBits v'
          simp [hcar, hv'] at hcarry
          have heq : binVal u = binVal v' := by omega
          have huv : u = v' := QEnum.binVal_inj (by omega) heq
          exact False.elim (hnlegal (huv ▸ hleg))

/-- Modes `1` and `2` enumerate the NO moves of a positive-fuel frame, calling the mode-3 phase
for each legal move.  Induct over the binary enumeration starting at the all-false vector and use
`mstep_answer_phase`; the recursive premise supplies precisely the smaller-fuel child calls.
After the carry, the universal clause in the definition of `safeV` determines whether the run
returns in mode `6` or mode `5`. -/
theorem mstep_no_phase (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    (f : ℕ) (F : Frame) (K : List Frame)
    (hrec : ∀ (C : Frame) (L : List Frame), C.f = f → FrameOK m E C →
      (∀ G ∈ L, FrameOK m E G) → L.length + f ≤ m + 1 →
      GoodRun m cv E out (0, C :: L)
        (if safeV m cv E out f C.v C.y C.n then 6 else 5, L))
    (hf : F.f = f + 1) (hout : out F.v = true) (hF : FrameOK m E F)
    (hK : ∀ G ∈ K, FrameOK m E G) (hdepth : K.length + F.f ≤ m + 1) :
    GoodRun m cv E out (1, { F with v' := List.replicate m false } :: K)
      (if safeV m cv E out (f + 1) F.v F.y F.n then 6 else 5, K) := by
  classical
  let Legal := fun u : BitString => isSub F.v u = true ∧ F.v ≠ u ∧ F.n + cv F.v u ≤ E
  let Answer := fun u r : BitString => r.length = m ∧ isSub u r = true ∧
    F.y + cv u r ≤ E ∧ safeV m cv E out f r (F.y + cv u r)
      (F.n + cv F.v u) = true
  let All := fun w : BitString => ∀ u : BitString, u.length = m → binVal w ≤ binVal u →
    Legal u → ∃ r, Answer u r
  have hrlen : F.r.length ≤ m := hF.2.2.2.2.2
  have haux := mstep_no_phase_aux m cv E out f F K ⟨hrec, hf, hF, hK, hdepth⟩
    F.r hrlen
  change (All (List.replicate m false) → GoodRun m cv E out
      (1, { F with v' := List.replicate m false, r := F.r } :: K) (6, K)) ∧
    (¬ All (List.replicate m false) → GoodRun m cv E out
      (1, { F with v' := List.replicate m false, r := F.r } :: K) (5, K)) at haux
  have hall_iff : All (List.replicate m false) ↔
      safeV m cv E out (f + 1) F.v F.y F.n = true := by
    rw [show safeV m cv E out (f + 1) F.v F.y F.n =
      (out F.v && decide (∀ u : BitString, u.length = m → isSub F.v u = true →
        F.v ≠ u → F.n + cv F.v u ≤ E → ∃ r : BitString, r.length = m ∧
          isSub u r = true ∧ F.y + cv u r ≤ E ∧
          safeV m cv E out f r (F.y + cv u r) (F.n + cv F.v u) = true)) from rfl]
    rw [hout]
    simp only [Bool.true_and, decide_eq_true_eq]
    constructor
    · intro hall u hu hsub hne hcost
      exact hall u hu (by simp [binVal_replicate_false]) ⟨hsub, hne, hcost⟩
    · intro hall u hu _ hlegal
      exact hall u hu hlegal.1 hlegal.2.1 hlegal.2.2
  by_cases hs : safeV m cv E out (f + 1) F.v F.y F.n = true
  · simpa [hs] using haux.1 (hall_iff.2 hs)
  · have hs0 : safeV m cv E out (f + 1) F.v F.y F.n = false :=
      Bool.eq_false_of_not_eq_true hs
    simpa [hs0] using haux.2 (fun hall => hs (hall_iff.1 hall))

/-- Entering any bounded frame computes its `safeV` value.  Prove the theorem by induction on
`F.f`: the zero case is one unfolding of `enterStep`, and the successor case first splits on
`out F.v` and then applies `mstep_no_phase` with the induction hypothesis.  The invariant
`K.length + F.f ≤ m + 1` is exactly what bounds the stack after pushing a child. -/
theorem mstep_eval_frame (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool)
    (F : Frame) (K : List Frame) (hF : FrameOK m E F)
    (hK : ∀ G ∈ K, FrameOK m E G) (hdepth : K.length + F.f ≤ m + 1) :
    GoodRun m cv E out (0, F :: K)
      (if safeV m cv E out F.f F.v F.y F.n then 6 else 5, K) := by
  induction f_val : F.f generalizing F K with
  | zero =>
    have h_safeV : safeV m cv E out 0 F.v F.y F.n = out F.v := rfl
    have h_enterStep : mstep m cv E out (0, F :: K) = (if out F.v then 6 else 5, K) := by
      simp [mstep, enterStep, f_val]
      split <;> rfl
    have H_good : Good m E (0, F :: K) :=
      ⟨by simp, by simp; omega, List.forall_mem_cons.2 ⟨hF, hK⟩⟩
    have H_good2 : Good m E (if out F.v then 6 else 5, K) := by
      split
      · exact ⟨by simp, by simp; omega, hK⟩
      · exact ⟨by simp, by simp; omega, hK⟩
    have h_safeV_f : safeV m cv E out F.f F.v F.y F.n = out F.v := by rw [f_val, h_safeV]
    have H_final : GoodRun m cv E out (0, F :: K) (if out F.v = true then 6 else 5, K) := by
      refine ⟨1, ?_, ?_⟩
      · exact h_enterStep
      · intro t ht
        cases t with
        | zero => exact H_good
        | succ t =>
          cases t
          · have : (mstep m cv E out)^[1] (0, F :: K) = (if out F.v = true then 6 else 5, K) :=
              h_enterStep
            rw [this]
            exact H_good2
          · omega
    have htarget : (if out F.v = true then 6 else 5, K) =
        (if safeV m cv E out F.f F.v F.y F.n = true then 6 else 5, K) := by rw [h_safeV_f]
    exact htarget ▸ H_final
  | succ f ih =>
    open Classical in
    have h_safeV : safeV m cv E out (f + 1) F.v F.y F.n =
      (out F.v && decide (∀ v' : BitString, v'.length = m → isSub F.v v' = true →
        F.v ≠ v' → F.n + cv F.v v' ≤ E → ∃ r : BitString, r.length = m ∧ isSub v' r = true ∧
        F.y + cv v' r ≤ E ∧ safeV m cv E out f r (F.y + cv v' r)
          (F.n + cv F.v v') = true)) := by
        rfl
    have h_enterStep : mstep m cv E out (0, F :: K) = enterStep m (out F.v) F K := rfl
    have H_good : Good m E (0, F :: K) :=
      ⟨by simp, by simp; omega, List.forall_mem_cons.2 ⟨hF, hK⟩⟩
    cases hout : out F.v
    · have h1 : enterStep m (out F.v) F K = (5, K) := by simp [enterStep, hout]
      have h2 : safeV m cv E out (f + 1) F.v F.y F.n = false := by
        simp [h_safeV, hout]
      have H_good2 : Good m E (5, K) := ⟨by simp, by simp; omega, hK⟩
      have H_safeV2 : safeV m cv E out F.f F.v F.y F.n = false := by rw [f_val, h2]
      have H_final : GoodRun m cv E out (0, F :: K) (5, K) := by
        refine ⟨1, ?_, ?_⟩
        · simp [h_enterStep, h1]
        · intro t ht
          cases t with
          | zero => exact H_good
          | succ t =>
            cases t
            · have : (mstep m cv E out)^[1] (0, F :: K) = (5, K) := by
                simp [h_enterStep, h1]
              rw [this]
              exact H_good2
            · omega
      have htarget : (5, K) =
          (if safeV m cv E out (f + 1) F.v F.y F.n = true then 6 else 5, K) := by
        rw [h2, ite_eq_right (by simp)]
      have htarget2 : GoodRun m cv E out (0, F :: K) (5, K) =
          GoodRun m cv E out (0, F :: K)
            (if safeV m cv E out (f + 1) F.v F.y F.n = true then 6 else 5, K) := by
        rw [htarget]
      have H_final2 : GoodRun m cv E out (0, F :: K)
          (if safeV m cv E out (f + 1) F.v F.y F.n = true then 6 else 5, K) := htarget2 ▸ H_final
      have htarget3 : (if safeV m cv E out (f + 1) F.v F.y F.n = true then 6 else 5, K) =
          (if safeV m cv E out F.f F.v F.y F.n = true then 6 else 5, K) := by rw [f_val]
      exact htarget3 ▸ H_final2
    · have h1 : enterStep m (out F.v) F K = (1, { F with v' := List.replicate m false } :: K) := by
        simp [enterStep, hout, f_val]
      have H_no_phase := mstep_no_phase m cv E out f F K
        (fun C L hCf hC hL hd => ih C L hC hL (by rw [hCf]; exact hd) hCf) f_val hout hF hK hdepth
      have H_step : GoodRun m cv E out (0, F :: K)
          (1, { F with v' := List.replicate m false } :: K) := by
        refine ⟨1, ?_, ?_⟩
        · simp [h_enterStep, h1]
        · intro t ht
          cases t with
          | zero => exact H_good
          | succ t =>
            cases t
            · have : (mstep m cv E out)^[1] (0, F :: K) =
                (1, { F with v' := List.replicate m false } :: K) := by simp [h_enterStep, h1]
              rw [this]
              refine ⟨by simp, by simp; omega, ?_⟩
              intro G hG
              cases hG
              · rcases hF with ⟨hlen1, hlen2, hlen3, hlen4, hlen5, hlen6⟩
                have Hlen : (List.replicate m false).length ≤ m := by simp
                exact ⟨hlen1, hlen2, hlen3, hlen4, Hlen, hlen6⟩
              · exact hK G (by assumption)
            · omega
      have H_trans := goodRun_trans m cv E out H_step H_no_phase
      have H_safeV2 : safeV m cv E out F.f F.v F.y F.n =
          safeV m cv E out (f + 1) F.v F.y F.n := by rw [f_val]
      have htarget : (if safeV m cv E out (f + 1) F.v F.y F.n = true then 6 else 5, K) =
          (if safeV m cv E out F.f F.v F.y F.n = true then 6 else 5, K) := by rw [H_safeV2]
      exact htarget ▸ H_trans

end DFS
end Kolmogorov.RandomStrings
