/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.DFSRoot
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode2
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode3Accept
import KolmogorovMathlib.RandomStrings.Expspace.DFSMode4
import KolmogorovMathlib.RandomStrings.Expspace.DFSEnter
import KolmogorovMathlib.RandomStrings.Expspace.DFSInit

/-!
# The depth-first search: assembly

The facts about the coded search state used by the main loop, the loop body `DFS.body` and the
program `DFS.prog` dispatching on the mode, the correctness `DFS.exec_body` of one iteration
(its hypotheses bundled in `DFS.ModeRoutines`, `DFS.InputOK` and `DFS.SamePrivate`), the
correctness `DFS.exec_prog` of the program, and the contract `exists_dfsStmt` of the whole
search; together with the inlining helpers `Exec.call` and the layout lemmas
`Stacks.layout_append`, `Stacks.layout_three`.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

namespace DFS

/-- The coded search state `encSt base W m st` agrees with `base` on every stack other than `8`,
`9` and `10`. -/
theorem encSt_apply_of_ne (base : Stacks 38) (W m : ℕ) (st : ℕ × List Frame) (j : Fin 38)
    (h8 : j ≠ 8) (h9 : j ≠ 9) (h10 : j ≠ 10) : encSt base W m st j = base j := by
  unfold encSt
  rw [Function.update_of_ne h10, Function.update_of_ne h9, Function.update_of_ne h8]

/-- If the stacks `8`, `9` and `10` of `base` are empty, the space of `encSt base W m st` is the
space of `base` plus the length of the code of the frames on stack `8`, the unary mode `st.1` on
stack `9` and the zero vector of width `m` on stack `10`. -/
theorem encSt_space (base : Stacks 38) (W m : ℕ) (st : ℕ × List Frame) (h8 : base 8 = [])
    (h9 : base 9 = []) (h10 : base 10 = []) :
    (encSt base W m st).space =
      base.space + (Stacks.encList (st.2.flatMap (Frame.fields W))).length + st.1 + m := by
  unfold encSt
  have e1 := Stacks.space_update base 8 (Stacks.encList (st.2.flatMap (Frame.fields W)))
  have e2 := Stacks.space_update (Function.update base 8
    (Stacks.encList (st.2.flatMap (Frame.fields W)))) 9 (List.replicate st.1 true)
  have e3 := Stacks.space_update (Function.update (Function.update base 8
    (Stacks.encList (st.2.flatMap (Frame.fields W)))) 9 (List.replicate st.1 true)) 10
    (List.replicate m false)
  rw [h8] at e1
  rw [Function.update_of_ne (by decide), h9] at e2
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h10] at e3
  simp only [List.length_nil, List.length_replicate, add_zero] at e1 e2 e3
  omega

/-- The code of the fields of a frame `F` of width `W` has length
`2 * (F.v.length + W + W + F.f + F.v'.length + F.r.length) + 6`. -/
theorem length_encList_fields (W : ℕ) (F : Frame) :
    (Stacks.encList (F.fields W)).length =
      2 * (F.v.length + W + W + F.f + F.v'.length + F.r.length) + 6 := by
  simp only [Stacks.length_encList, Frame.fields, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, numBits, List.length_map, List.length_range, List.length_replicate]
  ring

/-- The code of the concatenated fields of a list of frames has length the sum of the lengths of
the codes of the fields of its frames. -/
theorem length_encList_flatMap (W : ℕ) (L : List Frame) :
    (Stacks.encList (L.flatMap (Frame.fields W))).length =
      (L.map fun F => (Stacks.encList (F.fields W)).length).sum := by
  induction L with
  | nil => simp [Stacks.encList]
  | cons F L ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [← ih]
    simp [Stacks.encList, List.flatMap_append]

/-- A list of at most `m + 2` frames, each satisfying `FrameOK m E`, has concatenated fields whose
code has length at most `16 * (m + W + 1) ^ 2 + 16`. -/
theorem length_frames_le (m E W : ℕ) (L : List Frame) (hL : L.length ≤ m + 2)
    (hF : ∀ F ∈ L, FrameOK m E F) :
    (Stacks.encList (L.flatMap (Frame.fields W))).length ≤ 16 * (m + W + 1) ^ 2 + 16 := by
  rw [length_encList_flatMap]
  have : ∀ F ∈ L, (Stacks.encList (F.fields W)).length ≤ 8 * m + 4 * W + 8 := by
    intro F hFm
    obtain ⟨h1, -, -, h4, h5, h6⟩ := hF F hFm
    rw [length_encList_fields]; omega
  have hs : (L.map fun F => (Stacks.encList (F.fields W)).length).sum ≤
      L.length * (8 * m + 4 * W + 8) := by
    have := List.sum_le_length_nsmul (L.map fun F => (Stacks.encList (F.fields W)).length)
      (8 * m + 4 * W + 8) (by
        intro x hx
        obtain ⟨F, hFm, rfl⟩ := List.mem_map.1 hx
        exact this F hFm)
    simpa using this
  have h2 : L.length * (8 * m + 4 * W + 8) ≤ (m + 2) * (8 * m + 4 * W + 8) :=
    Nat.mul_le_mul_right _ hL
  nlinarith

/-- The machine step `mstep` fixes every state whose frame stack is empty. -/
theorem mstep_nil (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool) (i : ℕ) : mstep m cv E out (i, []) = (i, []) := by
  unfold mstep
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> rfl

/-- Any number of machine steps fixes a state whose frame stack is empty. -/
theorem iterate_mstep_nil (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool) (i n : ℕ) : (mstep m cv E out)^[n] (i, []) = (i, []) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, mstep_nil]

/-- The code of the concatenated fields of a list of frames is the empty stack exactly when the
list is empty. -/
theorem encList_frames_eq_nil (W : ℕ) (L : List Frame) :
    Stacks.encList (L.flatMap (Frame.fields W)) = [] ↔ L = [] := by
  cases L with
  | nil => simp [Stacks.encList]
  | cons F L =>
    constructor
    · intro h
      have := congrArg List.length h
      rw [length_encList_flatMap] at this
      simp only [List.map_cons, List.sum_cons, length_encList_fields, List.length_nil] at this
      omega
    · intro h; cases h

/-- Overwriting the mode stack `9` of `encSt base W m (i, L)` with the unary code of `j` gives
`encSt base W m (j, L)`. -/
theorem encSt_mode (base : Stacks 38) (W m i j : ℕ) (L : List Frame) :
    Function.update (encSt base W m (i, L)) 9 (List.replicate j true) = encSt base W m (j, L) := by
  funext x
  unfold encSt
  by_cases h9 : x = 9
  · subst h9
    rw [Function.update_self, Function.update_of_ne (by decide), Function.update_self]
  · rw [Function.update_of_ne h9]
    by_cases h10 : x = 10
    · subst h10
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h10, Function.update_of_ne h10, Function.update_of_ne h9,
        Function.update_of_ne h9]

/-- The loop body: dispatch on the mode. -/
def body {k : ℕ} (h : 38 ≤ k) (sOut : Stmt k) (sPre sPost s1 s2 s3 s4 : Stmt 38) : Stmt k :=
  SimOTM.switchU (Fin.castLE h 9)
    [.seq (sPre.rename (Fin.castLE h)) (.seq sOut (sPost.rename (Fin.castLE h))),
     s1.rename (Fin.castLE h), s2.rename (Fin.castLE h), s3.rename (Fin.castLE h),
     s4.rename (Fin.castLE h), Stmt.pushList (Fin.castLE h 9) (SimOTM.un 4),
     Stmt.pushList (Fin.castLE h 9) (SimOTM.un 2)]

/-- Output the result bit (mode `6` is `true`, mode `5` is `false`) and clear the zero vector. -/
def finalS {k : ℕ} (h : 38 ≤ k) : Stmt k :=
  .seq (SimOTM.switchU (Fin.castLE h 9) [.skip, .skip, .skip, .skip, .skip,
    .push (Fin.castLE h 5) false, .push (Fin.castLE h 5) true]) (Stmt.clear (Fin.castLE h 10))

/-- The search program on `k ≥ 38` stacks. -/
def prog {k : ℕ} (h : 38 ≤ k) (sOut : Stmt k) (sInit sPre sPost s1 s2 s3 s4 : Stmt 38) :
    Stmt k :=
  .seq (sInit.rename (Fin.castLE h)) (.seq (.loop (Fin.castLE h 8) Option.isSome
    (body h sOut sPre sPost s1 s2 s3 s4)) (finalS h))

/-- Stack `8` of the coded state holds the code of the fields of all its frames. -/
theorem encSt_eight (base : Stacks 38) (W m : ℕ) (st : ℕ × List Frame) :
    encSt base W m st 8 = Stacks.encList (st.2.flatMap (Frame.fields W)) := by
  unfold encSt
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

/-- Stack `9` of the coded state holds the current mode in unary. -/
theorem encSt_nine (base : Stacks 38) (W m : ℕ) (st : ℕ × List Frame) :
    encSt base W m st 9 = List.replicate st.1 true := by
  unfold encSt
  rw [Function.update_of_ne (by decide), Function.update_self]

/-- A frame satisfying `FrameOK m E` has size at most `4 * (m + W + 1)`. -/
theorem frameSize_le (m E W : ℕ) (F : Frame) (hF : FrameOK m E F) :
    frameSize W F ≤ 4 * (m + W + 1) := by
  obtain ⟨h1, -, -, h4, h5, h6⟩ := hF
  unfold frameSize; omega

/-- The routines run by the loop body `body` on the `38` stacks of the coded search state, with
the constants bounding their space and their contracts.  Mode `0` runs `sPre`, which copies the
position of the top frame onto stack `6`, then the outcome procedure, then `sPost`, which
performs `enterStep` on the outcome bit on stack `7`; the other four routines perform one machine
step in the modes `1` to `4`. -/
structure ModeRoutines where
  /-- The first half of mode `0`. -/
  sPre : Stmt 38
  /-- The second half of mode `0`. -/
  sPost : Stmt 38
  /-- The routines of the modes `1` to `4`. -/
  (s1 s2 s3 s4 : Stmt 38)
  /-- The space constants of the six routines. -/
  (KPre KPost K1 K2 K3 K4 : ℕ)
  /-- The contract of `sPre`: it copies the position of the top frame onto stack `6`. -/
  hPre : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec sPre (Function.update (encSt base W m (0, F :: Ks)) 9 [])
      (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v)
      ((encSt base W m (0, F :: Ks)).space + KPre * frameSize W F)
  /-- The contract of `sPost`: from the outcome bit `b` on stack `7` it performs `enterStep`. -/
  hPost : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (b : Bool),
    (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
    Exec sPost (Function.update (Function.update (Function.update (encSt base W m (0, F :: Ks))
      9 []) 6 F.v) 7 [b]) (encSt base W m (enterStep m b F Ks))
      ((encSt base W m (0, F :: Ks)).space + KPost * (frameSize W F + m + 1))
  /-- The contract of the routine of mode `1`, which checks the NO move. -/
  h1 : ModeSpec 1 s1 K1
  /-- The contract of the routine of mode `2`, which passes to the next NO move. -/
  h2 : ModeSpec 2 s2 K2
  /-- The contract of the routine of mode `3`, which checks the YES answer. -/
  h3 : ModeSpec 3 s3 K3
  /-- The contract of the routine of mode `4`, which passes to the next YES answer. -/
  h4 : ModeSpec 4 s4 K4

/-- The input of a search is well formed: the board `LX` has no repeated position, the costs `cs`
are aligned with it and, like the budget `eb`, have width `W`, and the budget plus all the costs
fits in `W` bits. -/
structure InputOK (LX cs : List BitString) (eb : BitString) (W : ℕ) : Prop where
  /-- The board has no repeated position. -/
  nodup : LX.Nodup
  /-- There is one cost per position. -/
  length_eq : cs.length = LX.length
  /-- Every cost has width `W`. -/
  width : ∀ b ∈ cs, b.length = W
  /-- The budget has width `W`. -/
  width_eb : eb.length = W
  /-- The budget plus all the costs fits in `W` bits. -/
  sum_lt : binVal eb + (cs.map binVal).sum < 2 ^ W

/-- The private stacks of `σ` are those of `ρ`: the stacks `0` and `4` and every stack `j ≥ 38`
are as in `ρ`. -/
structure SamePrivate {k : ℕ} (h : 38 ≤ k) (ρ σ : Stacks k) : Prop where
  /-- Stack `0` is as in `ρ`. -/
  zero : σ (Fin.castLE h 0) = ρ (Fin.castLE h 0)
  /-- Stack `4` is as in `ρ`. -/
  four : σ (Fin.castLE h 4) = ρ (Fin.castLE h 4)
  /-- Every stack `j ≥ 38` is as in `ρ`. -/
  high : ∀ j : Fin k, 38 ≤ j.val → σ j = ρ j

/-- One iteration of the loop performs one step of the machine: the loop body, built from the
routines `R` and the outcome procedure `sOut`, takes the coded state `(i, F :: K)` to the coded
state after `mstep`, within the space bound of the whole body. -/
theorem exec_body {k : ℕ} (h : 38 ≤ k) (sOut : Stmt k) (B : ℕ)
    (out : Finset BitString → Bool) (LX cs : List BitString) (eb : BitString) (W : ℕ)
    (ρ : Stacks k) (R : ModeRoutines) (hin : InputOK LX cs eb W)
    (hOut : ∀ (τ : Stacks k) (S : Finset BitString), S ⊆ LX.toFinset →
      τ (Fin.castLE h 1) = Stacks.encList LX → τ (Fin.castLE h 6) = Stacks.posBits LX S →
      τ (Fin.castLE h 7) = [] → τ (Fin.castLE h 0) = ρ (Fin.castLE h 0) →
      τ (Fin.castLE h 4) = ρ (Fin.castLE h 4) →
      (∀ j : Fin k, 38 ≤ j.val → τ j = ρ j) →
      Exec sOut τ (Function.update τ (Fin.castLE h 7) [out S]) (τ.space + B))
    (σ : Stacks k) (hbase : BaseOK (fun r => σ (Fin.castLE h r)) LX cs eb)
    (hρ : SamePrivate h ρ σ) (i : ℕ) (F : Frame) (K : List Frame)
    (hg : Good LX.length (binVal eb) (i, F :: K)) :
    Exec (body h sOut R.sPre R.sPost R.s1 R.s2 R.s3 R.s4)
      (Function.extend (Fin.castLE h)
        (encSt (fun r => σ (Fin.castLE h r)) W LX.length (i, F :: K)) σ)
      (Function.extend (Fin.castLE h) (encSt (fun r => σ (Fin.castLE h r)) W LX.length
        (mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v))
          (i, F :: K))) σ)
      (σ.space + 5 * ((R.KPre + R.KPost + R.K1 + R.K2 + R.K3 + R.K4) * (LX.length + W + 1) ^ 2) +
        16 * (LX.length + W + 1) ^ 2 + 2 * LX.length + 26 + B) := by
  obtain ⟨hnd, hcs, hW, heb, hW2⟩ := hin
  obtain ⟨hρ0, hρ4, hρ⟩ := hρ
  obtain ⟨sPre, sPost, s1, s2, s3, s4, KPre, KPost, K1, K2, K3, K4, hPre, hPost, h1, h2, h3,
    h4⟩ := R
  dsimp only
  have hf : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hb5 : ∀ j : Fin 38, 5 ≤ j.val → (fun r => σ (Fin.castLE h r)) j = [] := hbase.2.2.2
  have hb8 := hb5 8 (by decide)
  have hb9 := hb5 9 (by decide)
  have hb10 := hb5 10 (by decide)
  have hσsp : σ.space = Stacks.space (fun r => σ (Fin.castLE h r)) +
      Stacks.rest (Fin.castLE h) σ := by
    have := Stacks.space_extend hf (fun r => σ (Fin.castLE h r)) σ
    rwa [Stacks.extend_comp_self hf] at this
  obtain ⟨hi6, hlen, hall⟩ := hg
  have hFok : FrameOK LX.length (binVal eb) F := hall F (List.mem_cons_self)
  have hsz := frameSize_le LX.length (binVal eb) W F hFok
  have hQ : LX.length + W + 1 ≤ (LX.length + W + 1) ^ 2 := by nlinarith
  have hfr := length_frames_le LX.length (binVal eb) W (F :: K) hlen hall
  have hsp0 := encSt_space (fun r => σ (Fin.castLE h r)) W LX.length (i, F :: K) hb8 hb9 hb10
  have hGsp := Stacks.space_extend hf
    (encSt (fun r => σ (Fin.castLE h r)) W LX.length (i, F :: K)) σ
  simp only at hsp0
  -- the dispatch
  have hupd := Stacks.update_extend hf
    (encSt (fun r => σ (Fin.castLE h r)) W LX.length (i, F :: K)) σ 9 []
  refine SimOTM.exec_switchU _ i (by simp; omega)
    (by rw [hf.extend_apply, encSt_nine]; rfl) (by omega) ?_
  rw [hupd]
  have hσ' : ∀ j : Fin k, 38 ≤ j.val → ∀ r : Fin 38, Fin.castLE h r ≠ j := by
    intro j hj r hr
    have := congrArg Fin.val hr
    simp only [Fin.val_castLE] at this
    omega
  have hKc : ∀ K' : ℕ, K' ≤ KPre + KPost + K1 + K2 + K3 + K4 →
      K' * (LX.length + W + 1) ^ 2 ≤
        (KPre + KPost + K1 + K2 + K3 + K4) * (LX.length + W + 1) ^ 2 :=
    fun K' hK' => Nat.mul_le_mul_right _ hK'
  interval_cases i
  · -- mode 0: outcome of the position
    change Exec (.seq (sPre.rename (Fin.castLE h)) (.seq sOut (sPost.rename (Fin.castLE h)))) _ _ _
    have ePre := (hPre (fun r => σ (Fin.castLE h r)) W LX.length F K hb5).rename hf σ
    have hv : F.v.length = LX.length := hFok.1
    obtain ⟨hpb, hsub⟩ := posBits_toSet LX hnd F.v hv
    have eOut := hOut (Function.extend (Fin.castLE h) (Function.update (Function.update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (0, F :: K)) 9 []) 6 F.v) σ)
      (toSet LX F.v) hsub
      (by rw [hf.extend_apply, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hbase.1)
      (by rw [hf.extend_apply, Function.update_self]; exact hpb.symm)
      (by rw [hf.extend_apply, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide) (by decide)]
          exact hb5 7 (by decide))
      (by rw [hf.extend_apply, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hρ0)
      (by rw [hf.extend_apply, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hρ4)
      (fun j hj => by rw [Stacks.extend_apply_of_not_mem _ _ _ (hσ' j hj)]; exact hρ j hj)
    rw [Stacks.update_extend hf] at eOut
    have ePost := (hPost (fun r => σ (Fin.castLE h r)) W LX.length F K (out (toSet LX F.v))
      hb5).rename hf σ
    -- spaces
    have hs1 := Stacks.space_extend hf (Function.update (Function.update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (0, F :: K)) 9 []) 6 F.v) σ
    have hs2 := Stacks.space_update (Function.update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (0, F :: K)) 9 []) 6 F.v
    have hs3 := Stacks.space_update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (0, F :: K)) 9 []
    have h6 : σ (Fin.castLE h 6) = [] := hb5 6 (by decide)
    rw [Function.update_of_ne (by decide), encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide)
      (by decide)] at hs2
    simp only [h6] at hs2
    simp only [List.length_nil, add_zero] at hs2 hs3
    have hPreK : KPre * frameSize W F ≤ 4 * (KPre * (LX.length + W + 1) ^ 2) := by
      calc KPre * frameSize W F ≤ KPre * (4 * (LX.length + W + 1) ^ 2) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (KPre * (LX.length + W + 1) ^ 2) := by ring
    have hPostK : KPost * (frameSize W F + LX.length + 1) ≤
        5 * (KPost * (LX.length + W + 1) ^ 2) := by
      calc KPost * (frameSize W F + LX.length + 1) ≤ KPost * (5 * (LX.length + W + 1) ^ 2) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 5 * (KPost * (LX.length + W + 1) ^ 2) := by ring
    have h1K := hKc KPre (by omega)
    have h2K := hKc KPost (by omega)
    exact .seq (ePre.mono (by omega)) (.seq (eOut.mono (by omega)) (ePost.mono (by omega)))
  · change Exec (s1.rename (Fin.castLE h)) _ _ _
    have e := (h1 (fun r => σ (Fin.castLE h r)) LX cs eb W F K (fun v => out (toSet LX v)) hbase
      hcs hW heb hW2 hFok).rename hf σ
    have := hKc K1 (by omega)
    exact e.mono (by omega)
  · change Exec (s2.rename (Fin.castLE h)) _ _ _
    have e := (h2 (fun r => σ (Fin.castLE h r)) LX cs eb W F K (fun v => out (toSet LX v)) hbase
      hcs hW heb hW2 hFok).rename hf σ
    have := hKc K2 (by omega)
    exact e.mono (by omega)
  · change Exec (s3.rename (Fin.castLE h)) _ _ _
    have e := (h3 (fun r => σ (Fin.castLE h r)) LX cs eb W F K (fun v => out (toSet LX v)) hbase
      hcs hW heb hW2 hFok).rename hf σ
    have := hKc K3 (by omega)
    exact e.mono (by omega)
  · change Exec (s4.rename (Fin.castLE h)) _ _ _
    have e := (h4 (fun r => σ (Fin.castLE h r)) LX cs eb W F K (fun v => out (toSet LX v)) hbase
      hcs hW heb hW2 hFok).rename hf σ
    have := hKc K4 (by omega)
    exact e.mono (by omega)
  · change Exec (Stmt.pushList (Fin.castLE h 9) (SimOTM.un 4)) _ _ _
    have e := Stmt.exec_pushList (Fin.castLE h 9) (SimOTM.un 4) (Function.extend (Fin.castLE h)
      (Function.update (encSt (fun r => σ (Fin.castLE h r)) W LX.length (5, F :: K)) 9 []) σ)
    have hs1 := Stacks.space_extend hf (Function.update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (5, F :: K)) 9 []) σ
    have hs3 := Stacks.space_update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (5, F :: K)) 9 []
    simp only [List.length_nil, add_zero] at hs3
    refine Stmt.exec_of_eq (e.mono (by simp only [SimOTM.un, List.length_replicate]; omega)) ?_
    rw [hf.extend_apply, Function.update_self, List.append_nil, Stacks.update_extend hf,
      Function.update_idem]
    exact congrArg (fun L => Function.extend (Fin.castLE h) L σ) (encSt_mode _ _ _ _ _ _)
  · change Exec (Stmt.pushList (Fin.castLE h 9) (SimOTM.un 2)) _ _ _
    have e := Stmt.exec_pushList (Fin.castLE h 9) (SimOTM.un 2) (Function.extend (Fin.castLE h)
      (Function.update (encSt (fun r => σ (Fin.castLE h r)) W LX.length (6, F :: K)) 9 []) σ)
    have hs1 := Stacks.space_extend hf (Function.update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (6, F :: K)) 9 []) σ
    have hs3 := Stacks.space_update
      (encSt (fun r => σ (Fin.castLE h r)) W LX.length (6, F :: K)) 9 []
    simp only [List.length_nil, add_zero] at hs3
    refine Stmt.exec_of_eq (e.mono (by simp only [SimOTM.un, List.length_replicate]; omega)) ?_
    rw [hf.extend_apply, Function.update_self, List.append_nil, Stacks.update_extend hf,
      Function.update_idem]
    exact congrArg (fun L => Function.extend (Fin.castLE h) L σ) (encSt_mode _ _ _ _ _ _)

/-- If the stacks `8`, `9` and `10` of `base` are empty, then clearing the mode stack `9` of the
halted coded state `encSt base W m (i, [])`, writing `[b]` on stack `5` and clearing stack `10`
gives `base` with `[b]` on stack `5`. -/
theorem final_local (base : Stacks 38) (W m i : ℕ) (b : Bool) (h8 : base 8 = [])
    (h9 : base 9 = []) (h10 : base 10 = []) :
    Function.update (Function.update (Function.update (encSt base W m (i, [])) 9 []) 5 [b]) 10 [] =
      Function.update base 5 [b] := by
  funext x
  unfold encSt
  by_cases hx10 : x = 10
  · subst hx10; simp [h10]
  by_cases hx5 : x = 5
  · subst hx5; simp
  by_cases hx9 : x = 9
  · subst hx9; simp [h9]
  by_cases hx8 : x = 8
  · subst hx8; simp [h8, Stacks.encList]
  simp [hx10, hx5, hx9, hx8]

/-- The `k` stacks encoding the machine state `st` over the stacks `σ`: the first `38` stacks hold
`encSt` over the restriction of `σ`, and every other stack is as in `σ`. -/
noncomputable def gst {k : ℕ} (h : 38 ≤ k) (σ : Stacks k) (W m : ℕ)
    (st : ℕ × List Frame) : Stacks k :=
  Function.extend (Fin.castLE h) (encSt (fun r => σ (Fin.castLE h r)) W m st) σ

/-- **Correctness of the search program.**  Let the input be well formed, let the routines satisfy
their contracts and let `sOut` compute the outcome bit of a position within `B`.  Started on a
state `σ` with the board `LX` on stack `1`, the costs `cs` on stack `2`, the budget `eb` on
stack `3`, stacks `5` to `37` empty and the private stacks as in `ρ`, the program
`prog h sOut sInit sPre sPost …` writes the value of the game,
`gameV LX.length (costV (cs.map binVal)) (binVal eb) (out ∘ toSet LX)`, on stack `5` and changes
nothing else, within space
`σ.space + KI * (|LX| + W + 1) ^ 2 + 5 * (K * (|LX| + W + 1) ^ 2) + 16 * (|LX| + W + 1) ^ 2 +
2 * |LX| + 30 + B`, where `K = KPre + KPost + K1 + K2 + K3 + K4`. -/
theorem exec_prog {k : ℕ} (h : 38 ≤ k) (sOut : Stmt k) (B : ℕ)
    (out : Finset BitString → Bool) (LX cs : List BitString) (eb : BitString) (W : ℕ)
    (ρ : Stacks k)
    (sInit sPre sPost s1 s2 s3 s4 : Stmt 38) (KI KPre KPost K1 K2 K3 K4 : ℕ)
    (hInit : ∀ (base : Stacks 38) (LX cs : List BitString) (eb : BitString) (W : ℕ),
      BaseOK base LX cs eb → eb.length = W →
      Exec sInit base (encSt base W LX.length (3, [root LX.length]))
        (base.space + KI * (LX.length + W + 1) ^ 2))
    (hPre : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPre (Function.update (encSt base W m (0, F :: Ks)) 9 [])
        (Function.update (Function.update (encSt base W m (0, F :: Ks)) 9 []) 6 F.v)
        ((encSt base W m (0, F :: Ks)).space + KPre * frameSize W F))
    (hPost : ∀ (base : Stacks 38) (W m : ℕ) (F : Frame) (Ks : List Frame) (b : Bool),
      (∀ j : Fin 38, 5 ≤ j.val → base j = []) →
      Exec sPost (Function.update (Function.update (Function.update (encSt base W m (0, F :: Ks))
        9 []) 6 F.v) 7 [b]) (encSt base W m (enterStep m b F Ks))
        ((encSt base W m (0, F :: Ks)).space + KPost * (frameSize W F + m + 1)))
    (h1 : ModeSpec 1 s1 K1) (h2 : ModeSpec 2 s2 K2) (h3 : ModeSpec 3 s3 K3)
    (h4 : ModeSpec 4 s4 K4)
    (hnd : LX.Nodup) (hcs : cs.length = LX.length) (hW : ∀ b ∈ cs, b.length = W)
    (heb : eb.length = W) (hW2 : binVal eb + (cs.map binVal).sum < 2 ^ W)
    (hOut : ∀ (τ : Stacks k) (S : Finset BitString), S ⊆ LX.toFinset →
      τ (Fin.castLE h 1) = Stacks.encList LX → τ (Fin.castLE h 6) = Stacks.posBits LX S →
      τ (Fin.castLE h 7) = [] → τ (Fin.castLE h 0) = ρ (Fin.castLE h 0) →
      τ (Fin.castLE h 4) = ρ (Fin.castLE h 4) →
      (∀ j : Fin k, 38 ≤ j.val → τ j = ρ j) →
      Exec sOut τ (Function.update τ (Fin.castLE h 7) [out S]) (τ.space + B))
    (σ : Stacks k) (hbase : BaseOK (fun r => σ (Fin.castLE h r)) LX cs eb)
    (hρ0 : σ (Fin.castLE h 0) = ρ (Fin.castLE h 0))
    (hρ4 : σ (Fin.castLE h 4) = ρ (Fin.castLE h 4))
    (hρ : ∀ j : Fin k, 38 ≤ j.val → σ j = ρ j) :
    Exec (prog h sOut sInit sPre sPost s1 s2 s3 s4) σ
      (Function.update σ (Fin.castLE h 5)
        [gameV LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v))])
      (σ.space + KI * (LX.length + W + 1) ^ 2 +
        5 * ((KPre + KPost + K1 + K2 + K3 + K4) * (LX.length + W + 1) ^ 2) +
        16 * (LX.length + W + 1) ^ 2 + 2 * LX.length + 30 + B) := by
  classical
  have hf : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  have hb5 : ∀ j : Fin 38, 5 ≤ j.val → (fun r => σ (Fin.castLE h r)) j = [] := hbase.2.2.2
  have hb8 := hb5 8 (by decide)
  have hb9 := hb5 9 (by decide)
  have hb10 := hb5 10 (by decide)
  have hσsp : σ.space = Stacks.space (fun r => σ (Fin.castLE h r)) +
      Stacks.rest (Fin.castLE h) σ := by
    have := Stacks.space_extend hf (fun r => σ (Fin.castLE h r)) σ
    rwa [Stacks.extend_comp_self hf] at this
  obtain ⟨T, hT, hgood⟩ := mstep_root LX.length (costV (cs.map binVal)) (binVal eb)
    (fun v => out (toSet LX v)) (costV_replicate_true_false _ _)
  -- initialisation
  have eI := (hInit (fun r => σ (Fin.castLE h r)) LX cs eb W hbase heb).rename hf σ
  rw [Stacks.extend_comp_self hf] at eI
  -- the loop
  have hstep : ∀ τ : Stacks k, (∃ t ≤ T, τ = gst h σ W LX.length
        ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
          (3, [root LX.length]))) →
      Option.isSome (τ (Fin.castLE h 8)).head? = true →
      ∃ τ', Exec (body h sOut sPre sPost s1 s2 s3 s4) τ τ'
          (σ.space + 5 * ((KPre + KPost + K1 + K2 + K3 + K4) * (LX.length + W + 1) ^ 2) +
            16 * (LX.length + W + 1) ^ 2 + 2 * LX.length + 26 + B) ∧
        (∃ t ≤ T, τ' = gst h σ W LX.length
          ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
            (3, [root LX.length]))) ∧
        T - Nat.findGreatest (fun t => τ' = gst h σ W LX.length
          ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
            (3, [root LX.length]))) T <
        T - Nat.findGreatest (fun t => τ = gst h σ W LX.length
          ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
            (3, [root LX.length]))) T := by
    rintro τ ⟨t, ht, hτ⟩ hc
    have hP := Nat.findGreatest_spec (P := fun t => τ = gst h σ W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length]))) ht hτ
    have hle := Nat.findGreatest_le (P := fun t => τ = gst h σ W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length]))) T
    generalize Nat.findGreatest (fun t => τ = gst h σ W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length]))) T = N at hP hle ⊢
    have hg := hgood N hle
    rcases hsN : (mstep LX.length (costV (cs.map binVal)) (binVal eb)
      (fun v => out (toSet LX v)))^[N] (3, [root LX.length]) with ⟨i, _ | ⟨F, K⟩⟩
    · exfalso
      rw [hP, hsN] at hc
      simp [gst, hf.extend_apply, encSt_eight, Stacks.encList] at hc
    · have hNT : N < T := by
        rcases Nat.lt_or_ge N T with hlt | hge
        · exact hlt
        · exfalso
          have hNT' : N = T := le_antisymm hle hge
          rw [hNT', hT] at hsN
          simp at hsN
      have hsucc : (mstep LX.length (costV (cs.map binVal)) (binVal eb)
          (fun v => out (toSet LX v)))^[N + 1] (3, [root LX.length]) =
          mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v))
            (i, F :: K) := by
        rw [Function.iterate_succ_apply', hsN]
      rw [hsN] at hg
      refine ⟨gst h σ W LX.length (mstep LX.length (costV (cs.map binVal)) (binVal eb)
        (fun v => out (toSet LX v)) (i, F :: K)), ?_, ⟨N + 1, hNT, by rw [hsucc]⟩, ?_⟩
      · rw [hP, hsN]
        exact exec_body h sOut B out LX cs eb W ρ
          ⟨sPre, sPost, s1, s2, s3, s4, KPre, KPost, K1, K2, K3, K4, hPre, hPost, h1, h2, h3,
            h4⟩ ⟨hnd, hcs, hW, heb, hW2⟩ hOut σ hbase ⟨hρ0, hρ4, hρ⟩ i F K hg
      · have := Nat.le_findGreatest (P := fun t => gst h σ W LX.length
          (mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v))
            (i, F :: K)) = gst h σ W LX.length
          ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
            (3, [root LX.length]))) (m := N + 1) (n := T) hNT (by rw [hsucc])
        omega
  have hexit : ∀ τ : Stacks k, (∃ t ≤ T, τ = gst h σ W LX.length
        ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
          (3, [root LX.length]))) →
      τ.space ≤ σ.space + 5 * ((KPre + KPost + K1 + K2 + K3 + K4) * (LX.length + W + 1) ^ 2) +
        16 * (LX.length + W + 1) ^ 2 + 2 * LX.length + 26 + B := by
    rintro τ ⟨t, ht, rfl⟩
    obtain ⟨hi6, hlen, hall⟩ := hgood t ht
    have hfr := length_frames_le LX.length (binVal eb) W _ hlen hall
    have hsp := encSt_space (fun r => σ (Fin.castLE h r)) W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length])) hb8 hb9 hb10
    have hG := Stacks.space_extend hf (encSt (fun r => σ (Fin.castLE h r)) W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length]))) σ
    unfold gst
    omega
  obtain ⟨σ', eL, ⟨t, ht, hσ'⟩, hc⟩ := Exec.loop_of_variant (r := Fin.castLE h 8)
    (cond := Option.isSome) (body := body h sOut sPre sPost s1 s2 s3 s4)
    (fun τ => ∃ t ≤ T, τ = gst h σ W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length])))
    (fun τ => T - Nat.findGreatest (fun t => τ = gst h σ W LX.length
      ((mstep LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))^[t]
        (3, [root LX.length]))) T) _ hstep hexit
    (gst h σ W LX.length (3, [root LX.length])) ⟨0, Nat.zero_le _, rfl⟩
  -- the loop ends in the halted state
  have hhalt : (mstep LX.length (costV (cs.map binVal)) (binVal eb)
      (fun v => out (toSet LX v)))^[t] (3, [root LX.length]) =
      (if gameV LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v))
        then 6 else 5, []) := by
    rcases hst : (mstep LX.length (costV (cs.map binVal)) (binVal eb)
      (fun v => out (toSet LX v)))^[t] (3, [root LX.length]) with ⟨i, _ | ⟨F, K⟩⟩
    · have e := iterate_mstep_nil LX.length (costV (cs.map binVal)) (binVal eb)
        (fun v => out (toSet LX v)) i (T - t)
      have e2 : (mstep LX.length (costV (cs.map binVal)) (binVal eb)
          (fun v => out (toSet LX v)))^[T] (3, [root LX.length]) = (i, []) := by
        rw [← Nat.sub_add_cancel ht, Function.iterate_add_apply, hst, e]
      rw [hT] at e2
      exact e2.symm
    · exfalso
      rw [hσ', hst] at hc
      have hne : Stacks.encList ((F :: K).flatMap (Frame.fields W)) ≠ [] := fun he => by
        have := (encList_frames_eq_nil W (F :: K)).1 he
        cases this
      unfold gst at hc
      rw [hf.extend_apply, encSt_eight] at hc
      dsimp only at hc
      revert hc hne
      cases Stacks.encList ((F :: K).flatMap (Frame.fields W)) with
      | nil => intro _ hne; exact hne rfl
      | cons a l => intro hc _; simp at hc
  rw [hhalt] at hσ'
  subst hσ'
  -- output the bit and clear the zero vector
  have hσ5 : σ (Fin.castLE h 5) = [] := hb5 5 (by decide)
  have hfin : ∀ c : Bool, Exec (finalS h) (gst h σ W LX.length (if c = true then 6 else 5, []))
      (Function.update σ (Fin.castLE h 5) [c]) (σ.space + LX.length + 8) := by
    intro c
    have hsp := encSt_space (fun r => σ (Fin.castLE h r)) W LX.length
      (if c = true then 6 else 5, []) hb8 hb9 hb10
    have hG := Stacks.space_extend hf (encSt (fun r => σ (Fin.castLE h r)) W LX.length
      (if c = true then 6 else 5, [])) σ
    simp only [List.flatMap_nil, Stacks.encList, List.length_nil, add_zero] at hsp
    have hsw : Exec (SimOTM.switchU (Fin.castLE h 9) [.skip, .skip, .skip, .skip, .skip,
        .push (Fin.castLE h 5) false, .push (Fin.castLE h 5) true])
        (gst h σ W LX.length (if c = true then 6 else 5, []))
        (Function.update (Function.extend (Fin.castLE h) (Function.update
          (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if c = true then 6 else 5, [])) 9 [])
            σ) (Fin.castLE h 5) [c]) (σ.space + LX.length + 8) := by
      refine SimOTM.exec_switchU _ (if c = true then 6 else 5) (by cases c <;> simp)
        (by unfold gst; rw [hf.extend_apply, encSt_nine]; rfl)
        (by unfold gst; have : (if c = true then 6 else 5) ≤ 6 := by cases c <;> simp
            omega) ?_
      unfold gst
      rw [Stacks.update_extend hf]
      have h5' : (Function.extend (Fin.castLE h) (Function.update
          (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if c = true then 6 else 5, [])) 9 [])
            σ) (Fin.castLE h 5) = [] := by
        rw [hf.extend_apply, Function.update_of_ne (by decide),
          encSt_apply_of_ne _ _ _ _ _ (by decide) (by decide) (by decide)]
        exact hσ5
      have hs9 := Stacks.space_update
        (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if c = true then 6 else 5, [])) 9 []
      have hG9 := Stacks.space_extend hf (Function.update
        (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if c = true then 6 else 5, [])) 9 []) σ
      simp only [List.length_nil, add_zero] at hs9
      have hle6 : (if c = true then 6 else 5) ≤ 6 := by cases c <;> simp
      cases c
      · change Exec (.push (Fin.castLE h 5) false) _ _ _
        have e := Exec.push (r := Fin.castLE h 5) (b := false) (S := σ.space + LX.length + 8)
          (σ := Function.extend (Fin.castLE h) (Function.update
            (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if false = true then 6 else 5, []))
              9 []) σ)
          (by simp only [Bool.false_eq_true, ite_false] at hG9 hs9 hsp hle6 ⊢; omega)
        rw [h5'] at e
        exact e
      · change Exec (.push (Fin.castLE h 5) true) _ _ _
        have e := Exec.push (r := Fin.castLE h 5) (b := true) (S := σ.space + LX.length + 8)
          (σ := Function.extend (Fin.castLE h) (Function.update
            (encSt (fun r => σ (Fin.castLE h r)) W LX.length (if true = true then 6 else 5, []))
              9 []) σ) (by simp only [ite_true] at hG9 hs9 hsp hle6 ⊢; omega)
        rw [h5'] at e
        exact e
    have hcl := Stmt.exec_clear (Fin.castLE h 10) _ (Function.update (Function.extend
      (Fin.castLE h) (Function.update (encSt (fun r => σ (Fin.castLE h r)) W LX.length
        (if c = true then 6 else 5, [])) 9 []) σ) (Fin.castLE h 5) [c]) rfl
    have hfinEq : Function.update (Function.update (Function.extend (Fin.castLE h)
        (Function.update (encSt (fun r => σ (Fin.castLE h r)) W LX.length
          (if c = true then 6 else 5, [])) 9 []) σ) (Fin.castLE h 5) [c]) (Fin.castLE h 10) [] =
        Function.update σ (Fin.castLE h 5) [c] := by
      rw [Stacks.update_extend hf, Stacks.update_extend hf, final_local _ _ _ _ _ hb8 hb9 hb10,
        Stacks.extend_update_comp hf]
    rw [hfinEq] at hcl
    exact .seq hsw (hcl.mono hsw.space_le.2)
  have eF := hfin (gameV LX.length (costV (cs.map binVal)) (binVal eb) (fun v => out (toSet LX v)))
  have hQ : LX.length + W + 1 ≤ (LX.length + W + 1) ^ 2 := by nlinarith
  exact .seq (eI.mono (by omega)) (.seq (eL.mono (by omega)) (eF.mono (by omega)))

end DFS

/-- **The depth-first search.**  There are a number `kD` of work stacks and a
program transformer `dfs` such that, in any `k ≥ 8 + kD` stacks: for every outcome procedure
`sOut` which, from any contents `τ` with the board `encList LX` on stack `1`, the bit vector
`posBits LX S` of a position `S ⊆ LX` on stack `6`, stack `7` empty, and its private stacks
(`0`, `4` and all `j ≥ 8 + kD`) as in `ρ`, pushes `[out S]` on stack `7` and changes nothing
else, within `τ.space + B`, the statement `dfs k sOut`, started with the board on stack `1`,
the costs `encList cs` (aligned with `LX`, width `W`) on stack `2`, the budget `eb` (width `W`)
on stack `3`, stacks `5`, `6`, `7` and its work stacks `8, …, 7 + kD` empty and the private
stacks as in `ρ`, adds `[gameValB LX.toFinset cost (binVal eb) out]` on stack `5` and changes
nothing else, within `σ.space + C · (|LX| + W + 1) ^ 2 + B`.
Construction: the recursion `safeYesB` (and the first move of `gameValB`) with an explicit stack
of frames `(S, y, n, S', R)` on the work stacks (positions as bit vectors over `LX`, enumerated by
`Stmt.incr`; `costN` by summing the aligned costs with `Stmt.addInto`; the budget tests with
`Stmt.cmpInto`; no overflow by `binVal eb + Σ cost < 2 ^ W`); at most `|LX| + 2` frames of
`O(|LX| + W)` bits; the outcome of a position is obtained by writing its bit vector on stack
`6` and running `sOut`.  Correctness: induction on the fuel as in `safeYesB_iff`. -/
theorem exists_dfsStmt : ∃ (kD : ℕ) (dfs : (k : ℕ) → Stmt k → Stmt k) (C : ℕ),
    ∀ (k : ℕ) (hk : 8 + kD ≤ k) (sOut : Stmt k) (B : ℕ) (out : Finset BitString → Bool)
      (LX cs : List BitString) (eb : BitString) (W : ℕ) (cost : BitString → ℕ)
      (ρ : Stacks k),
      LX.Nodup → cs.length = LX.length → (∀ b ∈ cs, b.length = W) → eb.length = W →
      (∀ i < LX.length, binVal (cs.getD i []) = cost (LX.getD i [])) →
      binVal eb + (LX.map cost).sum < 2 ^ W →
      (∀ (τ : Stacks k) (S : Finset BitString), S ⊆ LX.toFinset →
        τ ⟨1, by omega⟩ = Stacks.encList LX → τ ⟨6, by omega⟩ = Stacks.posBits LX S →
        τ ⟨7, by omega⟩ = [] → τ ⟨0, by omega⟩ = ρ ⟨0, by omega⟩ →
        τ ⟨4, by omega⟩ = ρ ⟨4, by omega⟩ →
        (∀ j : Fin k, 8 + kD ≤ j.val → τ j = ρ j) →
        Exec sOut τ (Function.update τ ⟨7, by omega⟩ [out S]) (τ.space + B)) →
      ∀ σ : Stacks k, σ ⟨1, by omega⟩ = Stacks.encList LX →
        σ ⟨2, by omega⟩ = Stacks.encList cs →
        σ ⟨3, by omega⟩ = eb → σ ⟨5, by omega⟩ = [] → σ ⟨6, by omega⟩ = [] →
        σ ⟨7, by omega⟩ = [] →
        (∀ j : Fin k, 8 ≤ j.val → j.val < 8 + kD → σ j = []) →
        σ ⟨0, by omega⟩ = ρ ⟨0, by omega⟩ →
        σ ⟨4, by omega⟩ = ρ ⟨4, by omega⟩ →
        (∀ j : Fin k, 8 + kD ≤ j.val → σ j = ρ j) →
        Exec (dfs k sOut) σ
          (Function.update σ ⟨5, by omega⟩ [gameValB LX.toFinset cost (binVal eb) out])
          (σ.space + C * (LX.length + W + 1) ^ 2 + B) := by
  obtain ⟨sInit, KI, hInit⟩ := DFS.exists_initStmt
  obtain ⟨sPre, KPre, hPre⟩ := DFS.exists_enterPreStmt
  obtain ⟨sPost, KPost, hPost⟩ := DFS.exists_enterPostStmt
  obtain ⟨s1, K1, h1⟩ := DFS.exists_mode1Stmt
  obtain ⟨s2, K2, h2⟩ := DFS.exists_mode2Stmt
  obtain ⟨s3, K3, h3⟩ := DFS.exists_mode3Stmt
  obtain ⟨s4, K4, h4⟩ := DFS.exists_mode4Stmt
  refine ⟨30, fun k sOut => if h : 38 ≤ k then DFS.prog h sOut sInit sPre sPost s1 s2 s3 s4
    else .skip, KI + 5 * (KPre + KPost + K1 + K2 + K3 + K4) + 50, ?_⟩
  intro k hk sOut B out LX cs eb W cost ρ hnd hcs hW heb hcost hW2 hOut σ hσ1 hσ2 hσ3 hσ5 hσ6
    hσ7 hσw hσ0 hσ4 hσρ
  have h : 38 ≤ k := by omega
  change Exec (if h : 38 ≤ k then DFS.prog h sOut sInit sPre sPost s1 s2 s3 s4 else .skip) _ _ _
  rw [dite_eq_left h]
  have hmap : cs.map binVal = LX.map cost := by
    apply List.ext_getElem (by simp [hcs])
    intro i hi1 hi2
    simp only [List.getElem_map]
    have := hcost i (by simpa using hi2)
    rw [List.getD_eq_getElem _ _ (by simpa [hcs] using hi2),
      List.getD_eq_getElem _ _ (by simpa using hi2)] at this
    exact this
  have hW2' : binVal eb + (cs.map binVal).sum < 2 ^ W := by rw [hmap]; exact hW2
  have hbase : DFS.BaseOK (fun r => σ (Fin.castLE h r)) LX cs eb := by
    refine ⟨hσ1, hσ2, hσ3, fun j hj => ?_⟩
    rcases (show j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ 8 ≤ j.val by omega) with
      hj5 | hj6 | hj7 | hj8
    · have e : Fin.castLE h j = ⟨5, by omega⟩ := Fin.ext (by simp [hj5])
      change σ (Fin.castLE h j) = []
      rw [e]; exact hσ5
    · have e : Fin.castLE h j = ⟨6, by omega⟩ := Fin.ext (by simp [hj6])
      change σ (Fin.castLE h j) = []
      rw [e]; exact hσ6
    · have e : Fin.castLE h j = ⟨7, by omega⟩ := Fin.ext (by simp [hj7])
      change σ (Fin.castLE h j) = []
      rw [e]; exact hσ7
    · exact hσw _ (by simp only [Fin.val_castLE]; omega) (by simp only [Fin.val_castLE]; omega)
  have e := DFS.exec_prog h sOut B out LX cs eb W ρ sInit sPre sPost s1 s2 s3 s4 KI KPre KPost
    K1 K2 K3 K4 hInit hPre hPost h1 h2 h3 h4 hnd hcs hW heb hW2'
    (fun τ S hS e1 e6 e7 e0 e4 hj => hOut τ S hS e1 e6 e7 e0 e4 (fun j hj' => hj j (by omega)))
    σ hbase hσ0 hσ4 (fun j hj => hσρ j (by omega))
  rw [hmap, ← DFS.gameValB_eq_gameV LX hnd cost (binVal eb) out] at e
  have hQ : LX.length + W + 1 ≤ (LX.length + W + 1) ^ 2 := by nlinarith
  have hC : (KI + 5 * (KPre + KPost + K1 + K2 + K3 + K4) + 50) * (LX.length + W + 1) ^ 2 =
      KI * (LX.length + W + 1) ^ 2 +
        5 * ((KPre + KPost + K1 + K2 + K3 + K4) * (LX.length + W + 1) ^ 2) +
        50 * (LX.length + W + 1) ^ 2 := by ring
  exact e.mono (by rw [hC]; omega)

/-- **Procedure call.**  A procedure on `k` stacks that changes only its stack `d`, inlined along
an injective `f`, changes only the stack `f d`; the space grows by at most the current space. -/
theorem Exec.call {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f) {s : Stmt k}
    {τ : Stacks k'} {d : Fin k} {v : BitString} {S : ℕ}
    (h : Exec s (fun r => τ (f r)) (Function.update (fun r => τ (f r)) d v) S) :
    Exec (s.rename f) τ (Function.update τ (f d) v) (S + τ.space) := by
  have r := Exec.rename_of_comp hf h
  rw [Stacks.extend_update_comp hf] at r
  exact r.mono (Nat.add_le_add_left (Stacks.rest_le_space f τ) _)

/-- Appending one entry to a layout updates one stack. -/
theorem Stacks.layout_append {k : ℕ} (l : List BitString) (v : BitString) (h : l.length < k) :
    Stacks.layout k (l ++ [v]) = Function.update (Stacks.layout k l) ⟨l.length, h⟩ v := by
  funext j
  obtain ⟨n, hn⟩ := j
  simp only [Stacks.layout, Function.update_apply, Fin.mk.injEq]
  split_ifs with hnl
  · subst hnl; simp
  · rcases Nat.lt_or_ge n l.length with hlt | hge
    · simp [List.getElem?_append_left hlt]
    · rw [Stacks.getD_nil_of_le (by simp; omega), Stacks.getD_nil_of_le (by omega)]

/-- Appending a third entry `v` to the layout of `[a, b]` updates stack `2` to `v`. -/
theorem Stacks.layout_three {k : ℕ} (a b v : BitString) (h : 2 < k) :
    Stacks.layout k [a, b, v] = Function.update (Stacks.layout k [a, b]) ⟨2, h⟩ v :=
  Stacks.layout_append [a, b] v h

end Kolmogorov.RandomStrings
