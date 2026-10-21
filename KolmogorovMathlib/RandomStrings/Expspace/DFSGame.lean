/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Expspace.Evaluator

/-!
# The depth-first search: the game on bit vectors

Definitions of the depth-first search (`DFS`) over positions coded as bit vectors over the
board (`DFS.isSub`, `DFS.costV`, `DFS.toSet`), the recursions `DFS.safeV` and `DFS.gameV`,
and the transfer `DFS.gameValB_eq_gameV` from the evaluator `gameValB` to bit vectors.

Part of `KolmogorovMathlib.RandomStrings.Expspace`.
-/

namespace Kolmogorov.RandomStrings

/-! #### The depth-first search: definitions and sub-contracts

The search is a machine (`DFS.mstep`) on a stack of frames `(v, y, n, f, v', r)` (position, YES
and NO scores, fuel, NO move and YES answer under examination, positions as bit vectors over the
board); `DFS.gameValB_eq_gameV` and `DFS.mstep_root` relate it to `gameValB`.  On `38` stacks the
frames are coded on stack `8` (`DFS.encSt`), the mode in unary on `9`, the zero vector on `10`;
one mode routine per mode performs one step. -/

/-- Extending the result of a procedure that changed only its stack `d`. -/
theorem Stacks.extend_update_comp {k k' : ℕ} {f : Fin k → Fin k'} (hf : Function.Injective f)
    (τ : Stacks k') (d : Fin k) (v : BitString) :
    Function.extend f (Function.update (fun r => τ (f r)) d v) τ = Function.update τ (f d) v := by
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [hf.extend_apply]
    by_cases hid : i = d
    · subst hid; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hid, Function.update_of_ne (hf.ne hid)]
  · rw [Function.extend_apply' _ _ _ hj, Function.update_of_ne (fun h => hj ⟨d, h.symm⟩)]

namespace DFS

/-- The `W`-bit code (least significant bit first) of `y`. -/
def numBits (W y : ℕ) : BitString := (List.range W).map fun i => y.testBit i

/-- `v ⊆ v'` for bit vectors (on the common length). -/
def isSub (v v' : BitString) : Bool := (v.zip v').all fun p => !p.1 || p.2

/-- The total of the costs `c` at the positions selected by `v'` and not by `v`. -/
def costV (c : List ℕ) (v v' : BitString) : ℕ :=
  ((c.zip (v.zip v')).map fun p => if p.2.2 && !p.2.1 then p.1 else 0).sum

/-- The strings of `LX` selected by the bit vector `v`. -/
def toSet (LX : List BitString) (v : BitString) : Finset BitString :=
  (((LX.zip v).filter fun p => p.2).map Prod.fst).toFinset

open Classical in
/-- `safeYesB` on bit vectors of width `m`. -/
noncomputable def safeV (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ) (out : BitString → Bool) :
    ℕ → BitString → ℕ → ℕ → Bool
  | 0, v, _, _ => out v
  | f + 1, v, y, n => out v && decide (∀ v' : BitString, v'.length = m → isSub v v' = true →
      v ≠ v' → n + cv v v' ≤ E → ∃ r : BitString, r.length = m ∧ isSub v' r = true ∧
        y + cv v' r ≤ E ∧ safeV m cv E out f r (y + cv v' r) (n + cv v v') = true)

open Classical in
/-- `gameValB` on bit vectors of width `m`. -/
noncomputable def gameV (m : ℕ) (cv : BitString → BitString → ℕ) (E : ℕ)
    (out : BitString → Bool) : Bool :=
  decide (∃ r : BitString, r.length = m ∧ cv (List.replicate m false) r ≤ E ∧
    safeV m cv E out m r (cv (List.replicate m false) r) 0 = true)

/-! Helpers for `gameValB_eq_gameV` and `posBits_toSet`: for `LX.Nodup`, `toSet LX` is a bijection
from the bit vectors of length `|LX|` onto the subsets of `LX.toFinset` (inverse `posBits LX`),
turning `isSub` into `⊆` and `costV (LX.map cost)` into `costN cost`. -/

/-- `toSet` on a cons. -/
theorem pv_toSet_cons (z : BitString) (LX : List BitString) (b : Bool) (v : BitString) :
    toSet (z :: LX) (b :: v) = if b then insert z (toSet LX v) else toSet LX v := by
  cases b <;> simp [toSet]

/-- The selected strings lie on the board. -/
theorem pv_toSet_subset (LX : List BitString) (v : BitString) : toSet LX v ⊆ LX.toFinset := by
  intro z hz
  simp only [toSet, List.mem_toFinset, List.mem_map, List.mem_filter] at hz ⊢
  obtain ⟨⟨a, b⟩, ⟨hab, _⟩, rfl⟩ := hz
  exact (List.of_mem_zip hab).1

/-- An element not in `LX` is not selected by any vector over `LX`. -/
theorem pv_notMem_toSet {z : BitString} {LX : List BitString} (hnd : (z :: LX).Nodup)
    (v : BitString) : z ∉ toSet LX v := fun h =>
  (List.nodup_cons.1 hnd).1 (List.mem_toFinset.1 (pv_toSet_subset LX v h))

/-- The zero vector selects nothing. -/
theorem pv_toSet_replicate (LX : List BitString) (m : ℕ) :
    toSet LX (List.replicate m false) = ∅ := by
  induction LX generalizing m with
  | nil => simp [toSet]
  | cons z LX ih =>
    cases m with
    | zero => simp [toSet]
    | succ m => rw [List.replicate_succ, pv_toSet_cons, ih]; rfl

/-- `posBits` outputs a vector of length `|LX|`. -/
theorem pv_posBits_length (LX : List BitString) (S : Finset BitString) :
    (Stacks.posBits LX S).length = LX.length := by
  simp [Stacks.posBits]

/-- `toSet` inverts `posBits` on the subsets of the board. -/
theorem pv_toSet_posBits (LX : List BitString) (S : Finset BitString) (hS : S ⊆ LX.toFinset) :
    toSet LX (Stacks.posBits LX S) = S := by
  have key : ∀ L : List BitString, toSet L (Stacks.posBits L S) = L.toFinset.filter (· ∈ S) := by
    intro L
    induction L with
    | nil => simp [toSet, Stacks.posBits]
    | cons z L ih =>
      rw [show Stacks.posBits (z :: L) S = decide (z ∈ S) :: Stacks.posBits L S from rfl,
        pv_toSet_cons, ih, List.toFinset_cons, Finset.filter_insert]
      by_cases hz : z ∈ S <;> simp [hz]
  rw [key]
  ext z
  simp only [Finset.mem_filter, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hS h), h⟩⟩

/-- `posBits` agrees for sets containing the same elements of `LX`. -/
theorem pv_posBits_congr (LX : List BitString) (S T : Finset BitString)
    (h : ∀ z ∈ LX, (z ∈ S ↔ z ∈ T)) : Stacks.posBits LX S = Stacks.posBits LX T := by
  unfold Stacks.posBits
  exact List.map_congr_left fun z hz => decide_eq_decide.2 (h z hz)

/-- `posBits` inverts `toSet` on the vectors of length `|LX|`. -/
theorem pv_posBits_toSet (LX : List BitString) (hnd : LX.Nodup) (v : BitString)
    (hv : v.length = LX.length) : Stacks.posBits LX (toSet LX v) = v := by
  induction LX generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v => simp at hv
  | cons z LX ih =>
    cases v with
    | nil => simp at hv
    | cons b v =>
      have hzT := pv_notMem_toSet hnd v
      have hz : z ∉ LX := (List.nodup_cons.1 hnd).1
      have hnd' := (List.nodup_cons.1 hnd).2
      have ih' := ih hnd' v (by simpa using hv)
      rw [pv_toSet_cons]
      change decide (z ∈ _) :: Stacks.posBits LX _ = b :: v
      cases b
      · simp only [Bool.false_eq_true, ite_false, ih', hzT, decide_false]
      · simp only [ite_true]
        rw [pv_posBits_congr LX (insert z (toSet LX v)) (toSet LX v) (fun x hx => by
          rw [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left (fun e => hz (e ▸ hx)), Or.inr⟩), ih']
        simp

/-- `toSet` is injective on the vectors of length `|LX|`. -/
theorem pv_toSet_inj (LX : List BitString) (hnd : LX.Nodup) {v w : BitString}
    (hv : v.length = LX.length) (hw : w.length = LX.length) (h : toSet LX v = toSet LX w) :
    v = w := by
  rw [← pv_posBits_toSet LX hnd v hv, ← pv_posBits_toSet LX hnd w hw, h]

/-- `isSub` on a cons is the recursive step on its components. -/
theorem pv_isSub_cons (a b : Bool) (v w : BitString) :
    isSub (a :: v) (b :: w) = ((!a || b) && isSub v w) := rfl

/-- `isSub` is the inclusion of the selected sets. -/
theorem pv_isSub_iff (LX : List BitString) (hnd : LX.Nodup) (v w : BitString)
    (hv : v.length = LX.length) (hw : w.length = LX.length) :
    isSub v w = true ↔ toSet LX v ⊆ toSet LX w := by
  induction LX generalizing v w with
  | nil =>
    cases v with
    | cons => simp at hv
    | nil =>
      cases w with
      | cons => simp at hw
      | nil => simp [isSub, toSet]
  | cons z LX ih =>
    cases v with
    | nil => simp at hv
    | cons a v =>
      cases w with
      | nil => simp at hw
      | cons b w =>
        have hzv := pv_notMem_toSet hnd v
        have hzw := pv_notMem_toSet hnd w
        have hnd' := (List.nodup_cons.1 hnd).2
        have ih' := ih hnd' v w (by simpa using hv) (by simpa using hw)
        rw [pv_isSub_cons, pv_toSet_cons, pv_toSet_cons]
        cases a <;> cases b
        · simpa using ih'
        · simpa [Finset.subset_insert_iff_of_notMem hzv] using ih'
        · simp [Finset.insert_subset_iff, hzw]
        · simpa [Finset.insert_subset_insert_iff hzv] using ih'

/-- `costV` on a cons is the recursive step on its components. -/
theorem pv_costV_cons (c : ℕ) (cs : List ℕ) (a b : Bool) (v w : BitString) :
    costV (c :: cs) (a :: v) (b :: w) = (if b && !a then c else 0) + costV cs v w := by
  simp only [costV, List.zip_cons_cons, List.map_cons, List.sum_cons]

/-- `costV` on the aligned costs is `costN` of the selected sets. -/
theorem pv_costV_eq_costN (LX : List BitString) (hnd : LX.Nodup) (cost : BitString → ℕ)
    (v w : BitString) (hv : v.length = LX.length) (hw : w.length = LX.length) :
    costV (LX.map cost) v w = costN cost (toSet LX v) (toSet LX w) := by
  induction LX generalizing v w with
  | nil =>
    cases v with
    | cons => simp at hv
    | nil =>
      cases w with
      | cons => simp at hw
      | nil => simp [costV, costN, toSet]
  | cons z LX ih =>
    cases v with
    | nil => simp at hv
    | cons a v =>
      cases w with
      | nil => simp at hw
      | cons b w =>
        have hzv := pv_notMem_toSet hnd v
        have hzw := pv_notMem_toSet hnd w
        have hnd' := (List.nodup_cons.1 hnd).2
        have ih' := ih hnd' v w (by simpa using hv) (by simpa using hw)
        rw [List.map_cons, pv_costV_cons, ih', pv_toSet_cons, pv_toSet_cons]
        unfold costN
        cases a <;> cases b
        · simp
        · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.and_self]
          rw [Finset.insert_sdiff_of_notMem _ hzv,
            Finset.sum_insert (fun h => hzw (Finset.mem_sdiff.1 h).1)]
        · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_true, Bool.and_false,
            zero_add]
          rw [Finset.sdiff_insert_of_notMem hzw]
        · simp only [ite_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false,
            zero_add]
          rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hzw]

/-- `safeV` on a vector of length `|LX|` is `safeYesB` on the selected set (induction on the
fuel). -/
theorem pv_safeV_eq_safeYesB (LX : List BitString) (hnd : LX.Nodup) (cost : BitString → ℕ) (E : ℕ)
    (out : Finset BitString → Bool) (f : ℕ) : ∀ (v : BitString) (y n : ℕ), v.length = LX.length →
    safeV LX.length (costV (LX.map cost)) E (fun v => out (toSet LX v)) f v y n =
      safeYesB LX.toFinset cost E out f (toSet LX v) y n := by
  induction f with
  | zero => intro v y n _; rfl
  | succ f ih =>
    intro v y n hv
    simp only [safeV, safeYesB]
    congr 1
    apply decide_eq_decide.2
    constructor
    · intro H S' hS'P hss hcost
      have hS'X := Finset.mem_powerset.1 hS'P
      have hv'len := pv_posBits_length LX S'
      have hT' : toSet LX (Stacks.posBits LX S') = S' := pv_toSet_posBits LX S' hS'X
      have hc : costV (LX.map cost) v (Stacks.posBits LX S') = costN cost (toSet LX v) S' := by
        rw [pv_costV_eq_costN LX hnd cost v _ hv hv'len, hT']
      obtain ⟨r, hrlen, hsubr, hcr, hsafe⟩ := H (Stacks.posBits LX S') hv'len
        ((pv_isSub_iff LX hnd v _ hv hv'len).2 (by
          rw [hT']; exact (Finset.ssubset_iff_subset_ne.1 hss).1))
        (fun h => (Finset.ssubset_iff_subset_ne.1 hss).2 (by rw [h, hT']))
        (by rw [hc]; exact hcost)
      have hc' : costV (LX.map cost) (Stacks.posBits LX S') r = costN cost S' (toSet LX r) := by
        rw [pv_costV_eq_costN LX hnd cost _ r hv'len hrlen, hT']
      refine ⟨toSet LX r, Finset.mem_powerset.2 (pv_toSet_subset LX r), ?_, ?_, ?_⟩
      · have h1 := (pv_isSub_iff LX hnd _ r hv'len hrlen).1 hsubr
        rwa [hT'] at h1
      · rw [← hc']; exact hcr
      · rw [← hc', ← hc, ← ih r _ _ hrlen]; exact hsafe
    · intro H v' hv'len hsub hne hcost
      have hc : costV (LX.map cost) v v' = costN cost (toSet LX v) (toSet LX v') :=
        pv_costV_eq_costN LX hnd cost v v' hv hv'len
      have hss : toSet LX v ⊂ toSet LX v' := Finset.ssubset_iff_subset_ne.2
        ⟨(pv_isSub_iff LX hnd v v' hv hv'len).1 hsub,
          fun h => hne (pv_toSet_inj LX hnd hv hv'len h)⟩
      obtain ⟨R, hRP, hS'R, hRc, hsafe⟩ := H (toSet LX v')
        (Finset.mem_powerset.2 (pv_toSet_subset LX v')) hss (by rw [← hc]; exact hcost)
      have hRX := Finset.mem_powerset.1 hRP
      have hrlen := pv_posBits_length LX R
      have hT := pv_toSet_posBits LX R hRX
      have hc' : costV (LX.map cost) v' (Stacks.posBits LX R) = costN cost (toSet LX v') R := by
        rw [pv_costV_eq_costN LX hnd cost v' _ hv'len hrlen, hT]
      refine ⟨Stacks.posBits LX R, hrlen,
        (pv_isSub_iff LX hnd v' _ hv'len hrlen).2 (by rw [hT]; exact hS'R),
        by rw [hc']; exact hRc, ?_⟩
      rw [ih _ _ _ hrlen, hT, hc', hc]; exact hsafe

/-- **Sub-contract (pure): the bit-vector form of `gameValB`** (remaining). -/
theorem gameValB_eq_gameV (LX : List BitString) (hnd : LX.Nodup) (cost : BitString → ℕ) (E : ℕ)
    (out : Finset BitString → Bool) :
    gameValB LX.toFinset cost E out =
      gameV LX.length (costV (LX.map cost)) E (fun v => out (toSet LX v)) := by
  have hcard : LX.toFinset.card = LX.length := List.toFinset_card_of_nodup hnd
  have h0 : toSet LX (List.replicate LX.length false) = ∅ := pv_toSet_replicate LX _
  have h0len : (List.replicate LX.length false).length = LX.length := List.length_replicate
  unfold gameValB gameV
  apply decide_eq_decide.2
  constructor
  · rintro ⟨S₁, hP, hcost, hsafe⟩
    have hS₁ := Finset.mem_powerset.1 hP
    have hrlen := pv_posBits_length LX S₁
    have hT := pv_toSet_posBits LX S₁ hS₁
    have hc : costV (LX.map cost) (List.replicate LX.length false) (Stacks.posBits LX S₁) =
        costN cost ∅ S₁ := by
      rw [pv_costV_eq_costN LX hnd cost _ _ h0len hrlen, h0, hT]
    refine ⟨Stacks.posBits LX S₁, hrlen, by rw [hc]; exact hcost, ?_⟩
    rw [pv_safeV_eq_safeYesB LX hnd cost E out _ _ _ _ hrlen, hT, hc, ← hcard]
    exact hsafe
  · rintro ⟨r, hrlen, hcost, hsafe⟩
    have hc : costV (LX.map cost) (List.replicate LX.length false) r =
        costN cost ∅ (toSet LX r) := by
      rw [pv_costV_eq_costN LX hnd cost _ _ h0len hrlen, h0]
    refine ⟨toSet LX r, Finset.mem_powerset.2 (pv_toSet_subset LX r), by rw [← hc]; exact hcost,
      ?_⟩
    rw [hcard, ← hc, ← pv_safeV_eq_safeYesB LX hnd cost E out _ _ _ _ hrlen]
    exact hsafe

/-- **Sub-contract (pure): bit vectors are position codes** (remaining). -/
theorem posBits_toSet (LX : List BitString) (hnd : LX.Nodup) (v : BitString)
    (hv : v.length = LX.length) :
    Stacks.posBits LX (toSet LX v) = v ∧ toSet LX v ⊆ LX.toFinset := by
  exact ⟨pv_posBits_toSet LX hnd v hv, pv_toSet_subset LX v⟩

end DFS
end Kolmogorov.RandomStrings
