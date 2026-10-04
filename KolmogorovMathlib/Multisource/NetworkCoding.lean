/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Combinatorics.FlowNetwork
import KolmogorovMathlib.Multisource.FingerprintLadder
import KolmogorovMathlib.Multisource.Requests
/-!
# Networks with one source: algorithmic network coding
For a single-source request the cut-flow conditions are sufficient: the request is fulfillable
with `O(log n)`-precision.  Any number of outputs is handled by the book's random linear
coding: a counting argument shows that good coding matrices exist, and the decoder finds the
first good one by search (the Ford–Fulkerson envelope routing for one output is not needed).
The statement is WEAKER than printed Theorem 236 (capacities may be exceeded by
`O(log n)`, as the book's rounding does); unlimited capacities are replaced by `n`.
SUV Section 12.9, pp. 385–388. -/
namespace Kolmogorov
/-- The shape of a single-source network: the acyclic graph, its input vertex and the nonempty
set of output vertices.  Capacities and the string are not part of it, because the constant in
Theorem 236 depends on the shape alone.  SUV Section 12.9, p. 385. -/
structure NetworkShape (V : Type*) [Fintype V] [LinearOrder V] where
  /-- The channels of the network. -/ edges : Finset (V × V)
  /-- A topological ranking of the vertices. -/ rank : V → ℕ
  /-- Every edge increases the rank. -/ rank_lt : ∀ e ∈ edges, rank e.1 < rank e.2
  /-- The unique input vertex. -/ source : V
  /-- The vertices that must produce the input string. -/ outputs : Finset V
  /-- There is at least one output vertex. -/ outputs_nonempty : outputs.Nonempty
/-- The request asking `G` with capacities `cap` to deliver `A` from its source to every output
vertex.  SUV Section 12.9, p. 385. -/
def NetworkShape.request {V : Type*} [Fintype V] [LinearOrder V] (G : NetworkShape V)
    (cap : V × V → ℕ∞) (A : BitString) : InformationRequest V where
  edges := G.edges; rank := G.rank; rank_lt := G.rank_lt; capacity := cap
  input v := if v = G.source then some A else none
  output v := if v ∈ G.outputs then some A else none
/-- Truncating every capacity to `n` keeps a total that reaches `n` at least `n`: either one
term already reaches `n` on its own, or every term is finite and left unchanged. -/
private lemma le_sum_toNat_min_of_le_sum {α : Type*} (s : Finset α) (cap : α → ℕ∞) (n : ℕ)
    (h : (n : ℕ∞) ≤ ∑ e ∈ s, cap e) : n ≤ ∑ e ∈ s, (min (cap e) n).toNat := by
  by_cases hbig : ∃ e ∈ s, (n : ℕ∞) ≤ cap e
  · obtain ⟨e, he, hn⟩ := hbig
    have hterm : (min (cap e) n).toNat = n := by rw [min_eq_right hn, ENat.toNat_natCast]
    calc n = (min (cap e) n).toNat := hterm.symm
      _ ≤ ∑ e ∈ s, (min (cap e) n).toNat :=
        Finset.single_le_sum (f := fun e => (min (cap e) n).toNat) (fun _ _ => Nat.zero_le _) he
  · push Not at hbig
    have hmin : ∀ e ∈ s, (((min (cap e) n).toNat : ℕ) : ℕ∞) = cap e := fun e he => by
      rw [min_eq_left (hbig e he).le, ENat.natCast_toNat (hbig e he).ne_top]
    have hsum : ((∑ e ∈ s, (min (cap e) n).toNat : ℕ) : ℕ∞) = ∑ e ∈ s, cap e := by
      rw [Nat.cast_sum]; exact Finset.sum_congr rfl hmin
    rw [← hsum] at h; exact_mod_cast h
/-- Slack absorption for the scheme string: a constant, a slack in `n` and a slack in that
slack together form one slack in `n`, because a number has at most as many bits as its
value. -/
private lemma logSlack_logSlack_absorb (k c c₁ : ℕ) :
    ∃ c' : ℕ, ∀ n : ℕ, k + logSlack c n + logSlack c₁ (logSlack c n) ≤ logSlack c' n := by
  refine ⟨k + c + c₁ * c + c₁, fun n => ?_⟩
  have hbits : (Nat.bits (logSlack c n)).length ≤ logSlack c n := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hmul := Nat.mul_le_mul_left c₁ hbits; simp only [logSlack] at hmul ⊢; nlinarith [hmul]
private def allLists {α : Type*} (ch : List α) (k : ℕ) : List (List α) :=
  (fun acc => acc.flatMap fun l => ch.map (· :: l))^[k] [[]]
private def rowBit (x m : BitString) : Bool :=
  (List.range x.length).foldl (fun b i => b != (x.getD i false && m.getD i false)) false
private def edgeOut (c : List (List BitString)) (j len : ℕ) (x : BitString) : BitString :=
  (List.range len).map fun r => rowBit x ((c.getD j []).getD r [])
private def inputOf (st : List BitString) (A : BitString) (d : List ℕ × Bool) : List BitString :=
  d.1.map (fun i => st.getD i []) ++ cond d.2 [A] []
private def simStep (ED : List (List ℕ × Bool)) (L : List ℕ) (c : List (List BitString))
    (A : BitString) (st : List BitString) : List BitString := (List.range ED.length).map fun j =>
  edgeOut c j (L.getD j 0) (inputOf st A (ED.getD j ([], false))).flatten
private def sim (ED : List (List ℕ × Bool)) (L : List ℕ) (c : List (List BitString))
    (A : BitString) : List BitString := (simStep ED L c A)^[ED.length] []
private abbrev GoodFor (ED SD : List (List ℕ × Bool)) (n : ℕ) (L : List ℕ)
    (c : List (List BitString)) (A : BitString) : Prop :=
  ∀ d ∈ SD, ∀ A' ∈ allLists [false, true] n,
    A' = A ∨ inputOf (sim ED L c A') A' d ≠ inputOf (sim ED L c A) A d
private def search (ED SD : List (List ℕ × Bool)) (k n : ℕ) (L : List ℕ) :
    List (List (List BitString)) :=
  let S := allLists (allLists (allLists (allLists [false, true] (k * L.sum + n)) L.sum)
    ED.length) (n + 1)
  S.getD (S.findIdx fun s => decide (∀ A ∈ allLists [false, true] n, ∃ c ∈ s,
    GoodFor ED SD n L c A)) []
private def decodeAt (ED : List (List ℕ × Bool)) (n : ℕ) (L : List ℕ)
    (c : List (List BitString)) (d : List ℕ × Bool) (y : BitString) : BitString :=
  let S := allLists [false, true] n
  S.getD (S.findIdx fun A' => decide (listCode (inputOf (sim ED L c A') A' d) = y)) []
private def netAlg (ED SD VD : List (List ℕ × Bool)) (p : ℕ × List ℕ × ℕ × ℕ × Bool)
    (y : BitString) : BitString :=
  let c := (search ED SD VD.length p.1 p.2.1).getD p.2.2.1 []
  bif p.2.2.2.2 then edgeOut c p.2.2.2.1 (p.2.1.getD p.2.2.2.1 0) (decodeListCode y).flatten
  else decodeAt ED p.1 p.2.1 c (VD.getD p.2.2.2.1 ([], false)) y
private def netParams (w : BitString) : ℕ × List ℕ × ℕ × ℕ × Bool :=
  let a := decodeListCode w
  (bitsToNat (a.getD 0 []), (decodeListCode (a.getD 1 [])).map bitsToNat,
    bitsToNat (a.getD 2 []), bitsToNat (a.getD 3 []), (a.getD 4 []).headI)
private def netDecoder (ED SD VD : List (List ℕ × Bool)) (z : BitString) : BitString :=
  netAlg ED SD VD (netParams ((decodeListCode z).getD 0 [])) ((decodeListCode z).getD 1 [])
section
variable {α : Type*} [Primcodable α]
open Primrec
private lemma allLists_primrec {α : Type*} [Primcodable α] :
    Primrec₂ (allLists : List α → ℕ → List (List α)) := by
  unfold allLists; refine nat_iterate snd (const _) ?_
  exact (list_flatMap snd (list_map (fst.comp (fst.comp
    fst)) (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂
private lemma rowBit_primrec : Primrec fun p : BitString × BitString => rowBit p.1 p.2 := by
  unfold rowBit; refine list_foldl (h := fun (p : BitString × BitString) (s : Bool × ℕ) =>
    s.1 != (p.1.getD s.2 false && p.2.getD s.2 false))
    (list_range.comp (list_length.comp fst)) (const false) ?_
  have hx : Primrec fun p : (BitString × BitString) × Bool × ℕ => p.1.1.getD p.2.2 false :=
    (list_getD false).comp (fst.comp fst) (snd.comp snd)
  have hm : Primrec fun p : (BitString × BitString) × Bool × ℕ => p.1.2.getD p.2.2 false :=
    (list_getD false).comp (snd.comp fst) (snd.comp snd)
  exact Primrec.not.comp (Primrec.beq.comp (fst.comp snd) (Primrec.and.comp hx hm))
private lemma edgeOut_primrec {c : α → List (List BitString)} {j len : α → ℕ}
    {x : α → BitString} (hc : Primrec c) (hj : Primrec j) (hl : Primrec len)
    (hx : Primrec x) : Primrec fun a => edgeOut (c a) (j a) (len a) (x a) := by
  unfold edgeOut; refine list_map (list_range.comp hl) ?_
  exact (rowBit_primrec.comp (pair (hx.comp fst) ((list_getD []).comp
    ((list_getD []).comp (hc.comp fst) (hj.comp fst)) snd))).to₂
private lemma inputOf_primrec {st : α → List BitString} {A : α → BitString}
    {d : α → List ℕ × Bool} (hs : Primrec st) (hA : Primrec A) (hd : Primrec d) :
    Primrec fun a => inputOf (st a) (A a) (d a) := by
  unfold inputOf; refine list_append.comp (list_map (fst.comp hd)
    ((list_getD []).comp (hs.comp fst) snd).to₂) ?_
  exact Primrec.cond (snd.comp hd) (list_cons.comp hA (const [])) (const [])
private lemma sim_primrec (ED : List (List ℕ × Bool)) {L : α → List ℕ}
    {c : α → List (List BitString)} {A : α → BitString} (hL : Primrec L) (hc : Primrec c)
    (hA : Primrec A) : Primrec fun a => sim ED (L a) (c a) (A a) := by
  unfold sim; refine nat_iterate (f := fun _ => ED.length) (g := fun _ => ([] : List BitString))
    (h := fun a st => simStep ED (L a) (c a) (A a) st) (const _) (const _) ?_
  change Primrec fun p : α × List BitString => simStep ED (L p.1) (c p.1) (A p.1) p.2
  unfold simStep; refine list_map (const (List.range ED.length)) ?_
  exact (edgeOut_primrec (hc.comp (fst.comp fst)) snd
    ((list_getD 0).comp (hL.comp (fst.comp fst)) snd)
    (list_flatten.comp (inputOf_primrec (snd.comp fst) (hA.comp (fst.comp fst))
      ((list_getD _).comp (const ED) snd)))).to₂
private lemma goodFor_primrec (ED SD : List (List ℕ × Bool)) {n : α → ℕ} {L : α → List ℕ}
    {c : α → List (List BitString)} {A : α → BitString} (hn : Primrec n) (hL : Primrec L)
    (hc : Primrec c) (hA : Primrec A) :
    PrimrecPred fun a => GoodFor ED SD (n a) (L a) (c a) (A a) := by
  have h1 : PrimrecRel fun (A' : BitString) (q : (List ℕ × Bool) × α) =>
      A' = A q.2 ∨ inputOf (sim ED (L q.2) (c q.2) A') A' q.1 ≠
        inputOf (sim ED (L q.2) (c q.2) (A q.2)) (A q.2) q.1 := by
    refine PrimrecPred.or (Primrec.eq.comp fst (hA.comp (snd.comp
      snd))) (PrimrecPred.not (Primrec.eq.comp ?_ ?_))
    · exact inputOf_primrec (sim_primrec ED (hL.comp (snd.comp snd))
        (hc.comp (snd.comp snd)) fst) fst (fst.comp snd)
    · have hA' := hA.comp (snd.comp (snd (α := BitString) (β := (List ℕ × Bool) × α)))
      exact inputOf_primrec (sim_primrec ED (hL.comp (snd.comp snd))
        (hc.comp (snd.comp snd)) hA') hA' (fst.comp snd)
  have h2 : PrimrecRel fun (d : List ℕ × Bool) (a : α) => ∀ A' ∈ allLists [false, true] (n a),
      A' = A a ∨ inputOf (sim ED (L a) (c a) A') A' d ≠
        inputOf (sim ED (L a) (c a) (A a)) (A a) d :=
    h1.forall_mem_list.comp (allLists_primrec.comp (const _)
      (hn.comp (snd (α := List ℕ × Bool)))) Primrec.id
  exact h2.forall_mem_list.comp (const SD) Primrec.id
private lemma listSum_primrec : Primrec (List.sum : List ℕ → ℕ) :=
  (list_foldr (h := fun _ (p : ℕ × ℕ) => p.1 + p.2) Primrec.id (const 0)
    (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun l => by induction l <;> simp_all
private lemma search_primrec (ED SD : List (List ℕ × Bool)) (k : ℕ) :
    Primrec fun p : ℕ × List ℕ => search ED SD k p.1 p.2 := by
  unfold search; have hS : Primrec fun p : ℕ × List ℕ => allLists (allLists (allLists (allLists
      [false, true] (k * p.2.sum + p.1)) p.2.sum) ED.length) (p.1 + 1) := by
    refine allLists_primrec.comp (allLists_primrec.comp (allLists_primrec.comp
      (allLists_primrec.comp (const _) ?_) ?_) (const _)) (Primrec.succ.comp fst)
    · exact nat_add.comp (nat_mul.comp (const k) (listSum_primrec.comp snd)) fst
    · exact listSum_primrec.comp snd
  refine (list_getD []).comp hS (list_findIdx hS ?_)
  have h1 : PrimrecRel fun (A : BitString) (q : (ℕ × List ℕ) × List (List (List BitString))) =>
      ∃ c ∈ q.2, GoodFor ED SD q.1.1 q.1.2 c A := by
    have := goodFor_primrec ED SD (α := List (List BitString) × BitString ×
      (ℕ × List ℕ) × List (List (List BitString))) (fst.comp (fst.comp (snd.comp snd)))
      (snd.comp (fst.comp (snd.comp snd))) fst (fst.comp snd)
    have h' : PrimrecRel fun (c : List (List BitString))
        (q : BitString × (ℕ × List ℕ) × List (List (List BitString))) =>
        GoodFor ED SD q.2.1.1 q.2.1.2 c q.1 := this
    exact h'.exists_mem_list.comp (snd.comp snd) Primrec.id
  exact (h1.forall_mem_list.comp (allLists_primrec.comp (const _) (fst.comp fst)) Primrec.id).decide
private lemma netDecoder_primrec (ED SD VD : List (List ℕ × Bool)) :
    Primrec (netDecoder ED SD VD) := by
  have hget : ∀ i, Primrec fun w : BitString => (decodeListCode w).getD i [] := fun i =>
    (list_getD []).comp decodeListCode_primrec (const i)
  have hp : Primrec netParams := by
    unfold netParams; refine pair (bitsToNat_primrec.comp (hget 0)) (pair ?_ (pair
      (bitsToNat_primrec.comp (hget 2)) (pair (bitsToNat_primrec.comp (hget 3))
        (list_headI.comp (hget 4)))))
    exact list_map (decodeListCode_primrec.comp (hget 1)) (bitsToNat_primrec.comp snd).to₂
  have hz := hp.comp (hget 0); have hy := hget 1; unfold netDecoder netAlg
  have hc := (list_getD []).comp ((search_primrec ED SD VD.length).comp
    (pair (fst.comp hz) (fst.comp (snd.comp hz)))) (fst.comp (snd.comp (snd.comp hz)))
  have hj := fst.comp (snd.comp (snd.comp (snd.comp hz))); have hL := fst.comp (snd.comp hz)
  refine Primrec.cond (snd.comp (snd.comp (snd.comp
    (snd.comp hz)))) (edgeOut_primrec hc hj ((list_getD 0).comp hL hj)
      (list_flatten.comp (decodeListCode_primrec.comp hy))) ?_
  unfold decodeAt; have hS := allLists_primrec.comp (const [false, true]) (fst.comp hz)
  refine (list_getD []).comp hS (list_findIdx hS ?_)
  have hd := (list_getD ([], false)).comp (const VD) hj
  refine (Primrec.eq.comp (listCode_primrec.comp (inputOf_primrec (sim_primrec ED
    (hL.comp fst) (hc.comp fst) snd) snd (hd.comp fst))) (hy.comp fst)).decide
end
private lemma allLists_succ {α : Type*} (ch : List α) (k : ℕ) :
    allLists ch (k + 1) = (allLists ch k).flatMap fun l => ch.map (· :: l) :=
  Function.iterate_succ_apply' _ _ _
private lemma mem_allLists {α : Type*} (ch : List α) (k : ℕ) (l : List α) :
    l ∈ allLists ch k ↔ l.length = k ∧ ∀ a ∈ l, a ∈ ch := by
  induction k generalizing l with
  | zero => cases l <;> simp [allLists]
  | succ k ih => rw [allLists_succ]; cases l <;> simp [ih]; tauto
private lemma length_allLists {α : Type*} (ch : List α) (k : ℕ) :
    (allLists ch k).length = ch.length ^ k := by
  induction k with
  | zero => simp [allLists]
  | succ k ih => simp [allLists_succ, List.length_flatMap, ih, pow_succ]
private lemma getD_findIdx_spec {α : Type*} (S : List α) (p : α → Bool) (d : α)
    (h : ∃ x ∈ S, p x) : S.getD (S.findIdx p) d ∈ S ∧ p (S.getD (S.findIdx p) d) := by
  have hlt := List.findIdx_lt_length_of_exists h; rw [List.getD_eq_getElem _ _ hlt]
  exact ⟨List.getElem_mem _, List.findIdx_getElem⟩
private lemma foldl_bne_flip (f g : ℕ → Bool) (i0 : ℕ) : ∀ (l : List ℕ) (b : Bool), l.Nodup →
    i0 ∈ l → (∀ i ∈ l, i ≠ i0 → f i = g i) →
    l.foldl (fun b i => b != f i) b = (l.foldl (fun b i => b != g i) b != (f i0 != g i0)) := by
  have shift : ∀ (l : List ℕ) (b δ : Bool),
      l.foldl (fun b i => b != g i) (b != δ) = (l.foldl (fun b i => b != g i) b != δ) := by
    intro l; induction l with
    | nil => simp
    | cons a l ih =>
      intro b δ; simp only [List.foldl_cons, ← ih]; congr 1
      cases b <;> cases δ <;> cases g a <;> rfl
  intro l; induction l with
  | nil => simp
  | cons a l ih =>
    intro b hnd hi hfg; simp only [List.foldl_cons]; rw [List.nodup_cons] at hnd
    by_cases ha : a = i0
    · subst ha; rw [List.foldl_ext _ _ _ fun b i hi => by
        rw [hfg i (List.mem_cons_of_mem _ hi) (fun h => hnd.1 (h ▸ hi))], ← shift]
      congr 1; cases b <;> cases f a <;> cases g a <;> rfl
    · rw [hfg a List.mem_cons_self ha]
      exact ih _ hnd.2 ((List.mem_cons.mp hi).resolve_left (Ne.symm ha))
        fun i h => hfg i (List.mem_cons_of_mem _ h)
private lemma sim_fixed (ED : List (List ℕ × Bool)) (L : List ℕ) (c : List (List BitString))
    (A : BitString) (ρ : ℕ → ℕ)
    (hacyc : ∀ j < ED.length, ∀ i ∈ (ED.getD j ([], false)).1, i < ED.length ∧ ρ i < ρ j)
    (j : ℕ) (hj : j < ED.length) : (sim ED L c A).getD j [] =
      edgeOut c j (L.getD j 0) (inputOf (sim ED L c A) A (ED.getD j ([], false))).flatten := by
  set m := ED.length; let st : ℕ → List BitString := fun k => (simStep ED L c A)^[k] []
  let p : ℕ → ℕ := fun j => ((Finset.range m).filter fun i => ρ i < ρ j).card
  have hstep : ∀ k j, j < m → (st (k + 1)).getD j [] =
      edgeOut c j (L.getD j 0) (inputOf (st k) A (ED.getD j ([], false))).flatten := by
    intro k j (hj : j < ED.length)
    simp [st, Function.iterate_succ_apply', simStep, List.getD_eq_getElem?_getD, hj]
  have key : ∀ k j, j < m → p j < k → (st k).getD j [] = (st (k + 1)).getD j [] := by
    intro k; induction k with
    | zero => intro j _ h; omega
    | succ k ih =>
      intro j hj hk; rw [hstep k j hj, hstep (k + 1) j hj]
      suffices h : inputOf (st k) A (ED.getD j ([], false)) =
          inputOf (st (k + 1)) A (ED.getD j ([], false)) by rw [h]
      unfold inputOf; congr 1; refine List.map_congr_left fun i hi => ?_
      obtain ⟨him, hρ⟩ := hacyc j hj i hi
      refine ih i him (lt_of_lt_of_le ?_ (Nat.lt_succ_iff.mp hk))
      refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hρ⟩
      · have := h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr him, hρ⟩); simp at this
  have hp : p j < m := (Finset.card_lt_card (Finset.filter_ssubset.mpr
    ⟨j, Finset.mem_range.mpr hj, lt_irrefl (ρ j)⟩)).trans_le (Finset.card_range m).le
  change (st m).getD j [] = _; rw [key m j hj hp, hstep m j hj]; rfl
private lemma card_filter_forall_mul_le {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (ρ : ι → ℕ) (Q : ι → (ι → X) → Prop) [∀ j, DecidablePred (Q j)] (ℓ : ι → ℕ) (S : Finset ι)
    (hdep : ∀ j ∈ S, ∀ F F' : ι → X, (∀ k, ρ k < ρ j → F k = F' k) → F j = F' j → (Q j F ↔ Q j F'))
    (hcnt : ∀ j ∈ S, ∀ F : ι → X,
      (Finset.univ.filter fun y => Q j (Function.update F j y)).card * 2 ^ ℓ j ≤ Fintype.card X) :
    (Finset.univ.filter fun F => ∀ j ∈ S, Q j F).card * 2 ^ (∑ j ∈ S, ℓ j) ≤
      Fintype.card X ^ Fintype.card ι := by
  classical
  induction S using Finset.induction_on_max_value ρ with
  | empty => simp
  | insert a s has hmax ih =>
    rw [Finset.sum_insert has, pow_add, ← mul_assoc]
    refine le_trans (Nat.mul_le_mul_right _ ?_) (ih (fun j hj => hdep j (Finset.mem_insert_of_mem
      hj)) fun j hj => hcnt j (Finset.mem_insert_of_mem hj))
    set T := Finset.univ.filter fun F : ι → X => ∀ j ∈ insert a s, Q j F
    rcases T.eq_empty_or_nonempty with hT | ⟨F0, -⟩
    · simp [hT]
    have hP : ∀ F y, (∀ j ∈ s, Q j (Function.update F a y)) ↔ ∀ j ∈ s, Q j F := by
      refine fun F y => forall₂_congr fun j hj => hdep j (Finset.mem_insert_of_mem hj) _ _
        (fun k hk => ?_) ?_
      · exact Function.update_of_ne (fun h => by subst h; have := hmax j hj; omega) _ _
      · exact Function.update_of_ne (fun h : j = a => has (h ▸ hj)) _ _
    let π : (ι → X) → ι → X := fun F => Function.update F a (F0 a)
    rw [Finset.card_eq_sum_card_image π T]
    have hfib : ∀ G ∈ T.image π, (T.filter fun F => π F = G).card * 2 ^ ℓ a ≤ Fintype.card X := by
      intro G _; refine le_trans (Nat.mul_le_mul_right _ ?_) (hcnt a (Finset.mem_insert_self _ _) G)
      refine le_trans (Finset.card_le_card fun F hF => ?_) (Finset.card_image_le (s :=
        Finset.univ.filter fun y => Q a (Function.update G a y)) (f := Function.update G a))
      simp only [Finset.mem_filter, T, Finset.mem_univ, true_and] at hF
      refine Finset.mem_image.mpr ⟨F a, ?_, ?_⟩ <;> rw [← hF.2] <;>
        simp [π, hF.1 a (Finset.mem_insert_self _ _)]
    rw [Finset.sum_mul]; refine le_trans (Finset.sum_le_sum hfib) ?_
    rw [Finset.sum_const, smul_eq_mul, ← Finset.card_univ (α := X), ← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun p => Function.update p.1 a p.2) ?_ ?_
    · rintro ⟨G, y⟩ hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_image] at hp
      obtain ⟨⟨F, hF, rfl⟩, -⟩ := hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, T, π,
        Function.update_idem] at hF ⊢
      exact (hP F y).mpr fun j hj => hF j (Finset.mem_insert_of_mem hj)
    · rintro ⟨G, y⟩ hp ⟨G', y'⟩ hq hpq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_image] at hp hq
      obtain ⟨⟨F, -, rfl⟩, -⟩ := hp; obtain ⟨⟨F', -, rfl⟩, -⟩ := hq
      simpa [π] using congrArg (fun H => (Function.update H a (F0 a), H a)) hpq
private lemma getD_ofFn_bool {C : ℕ} (z : Fin C → Bool) (i : ℕ) :
    (List.ofFn z).getD i false = if h : i < C then z ⟨i, h⟩ else false := by
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]
private lemma rowBit_flip {C : ℕ} (x : BitString) (z : Fin C → Bool) (i0 : Fin C)
    (hi0 : (i0 : ℕ) < x.length) : rowBit x (List.ofFn (Function.update z i0 (!z i0))) =
      (rowBit x (List.ofFn z) != x.getD i0 false) := by
  unfold rowBit; rw [foldl_bne_flip _ _ i0 _ _ List.nodup_range (List.mem_range.mpr hi0)]
  · congr 1; simp only [getD_ofFn_bool, i0.isLt, dite_true, Fin.eta, Function.update_self]
    cases x.getD i0 false <;> cases z i0 <;> rfl
  · intro i _ hi; simp only [getD_ofFn_bool]; split_ifs with h <;> simp [Fin.ext_iff, hi]
private lemma card_rows_agree (R C ℓ : ℕ) (hℓ : ℓ ≤ R) (x x' : BitString)
    (hlen : x.length = x'.length) (hC : x.length ≤ C) (hne : x ≠ x') :
    (Finset.univ.filter fun y : Fin R → Fin C → Bool => ∀ r : Fin R, (r : ℕ) < ℓ →
      rowBit x (List.ofFn (y r)) = rowBit x' (List.ofFn (y r))).card * 2 ^ ℓ ≤
      Fintype.card (Fin R → Fin C → Bool) := by
  obtain ⟨i0, hi0, hx⟩ : ∃ i < x.length, x.getD i false ≠ x'.getD i false := by
    by_contra h; push Not at h; exact hne (List.ext_getElem hlen fun i h1 h2 => by
      have := h i h1; rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this)
  let j0 : Fin C := ⟨i0, hi0.trans_le hC⟩
  let φ : (Fin C → Bool) → Prop := fun z => rowBit x (List.ofFn z) = rowBit x' (List.ofFn z)
  let σ : (Fin C → Bool) → Fin C → Bool := fun z => Function.update z j0 (!z j0)
  have hσ : ∀ z, φ (σ z) ↔ ¬ φ z := by
    intro z; simp only [φ, σ, rowBit_flip x z j0 hi0, rowBit_flip x' z j0 (hlen ▸ hi0)]; revert hx
    cases x.getD i0 false <;> cases x'.getD i0 false <;>
      cases rowBit x (List.ofFn z) <;> cases rowBit x' (List.ofFn z) <;> simp
  have hinj : ∀ z z', σ z = σ z' → z = z' := fun z z' h => by simpa [σ] using congrArg σ h
  have hGd : (Finset.univ.filter φ).card * 2 ≤ 2 ^ C := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) φ
    have h2 : (Finset.univ.filter φ).card ≤ (Finset.univ.filter fun z => ¬ φ z).card :=
      Finset.card_le_card_of_injOn σ (fun z hz => by simpa [hσ] using hz) fun z _ z' _ => hinj z z'
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1; omega
  have key := card_filter_forall_mul_le (fun r : Fin R => (r : ℕ))
    (fun r y => (r : ℕ) < ℓ → φ (y r)) (fun r => if (r : ℕ) < ℓ then 1 else 0) Finset.univ
    (fun j _ F F' _ h => by simp only [h])
    fun j _ F => by by_cases h : (j : ℕ) < ℓ <;> simp [h, hGd]
  simpa [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hℓ, Fintype.card_fun] using key
section Shape
variable {V : Type*} [Fintype V] [LinearOrder V] (G : NetworkShape V)
private noncomputable def edgeList : List (V × V) := G.edges.toList
private noncomputable def eIdx (e : V × V) : ℕ := (edgeList G).idxOf e
private noncomputable def vData (v : V) : List ℕ × Bool :=
  ((((G.edges.filter fun e => e.2 = v).image Prod.fst).sort (· ≤ ·)).map fun u => eIdx G (u, v),
    decide (v = G.source))
private noncomputable def edgeData : List (List ℕ × Bool) :=
  (edgeList G).map fun e => vData G e.1
private noncomputable def trans (L : List ℕ) (c : List (List BitString)) (A : BitString) :
    V × V → BitString := fun e => (sim (edgeData G) L c A).getD (eIdx G e) []
private lemma eIdx_spec {e : V × V} (he : e ∈ G.edges) :
    ∃ h : eIdx G e < (edgeList G).length, (edgeList G)[eIdx G e] = e :=
  have hm : e ∈ edgeList G := Finset.mem_toList.mpr he
  ⟨List.idxOf_lt_length_of_mem hm, List.getElem_idxOf _⟩
private lemma edgeData_getD {e : V × V} (he : e ∈ G.edges) :
    (edgeData G).getD (eIdx G e) ([], false) = vData G e.1 := by
  obtain ⟨h, h'⟩ := eIdx_spec G he; simp [edgeData, List.getD_eq_getElem?_getD, h, h']
private lemma inputOf_vData (cap : V × V → ℕ∞) (L : List ℕ) (c : List (List BitString))
    (A : BitString) (v : V) : inputOf (sim (edgeData G) L c A) A (vData G v) =
      (G.request cap A).incoming (trans G L c A) v := by
  by_cases hv : v = G.source <;>
    simp [inputOf, vData, InformationRequest.incoming, InformationRequest.inNeighbors,
      NetworkShape.request, trans, hv]
private lemma trans_fixed (cap : V × V → ℕ∞) (L : List ℕ) (c : List (List BitString))
    (A : BitString) {e : V × V} (he : e ∈ G.edges) :
    trans G L c A e = edgeOut c (eIdx G e) (L.getD (eIdx G e) 0)
      ((G.request cap A).incoming (trans G L c A) e.1).flatten := by
  obtain ⟨h, h'⟩ := eIdx_spec G he
  have hlen : (edgeData G).length = (edgeList G).length := List.length_map _
  rw [← inputOf_vData, ← edgeData_getD G he]
  refine sim_fixed _ L c A (fun i => G.rank ((edgeList G).getD i (G.source, G.source)).1)
    (fun j hj i hi => ?_) _ (hlen ▸ h)
  rw [hlen] at hj ⊢; have hjd : (edgeData G).getD j ([], false) = vData G (edgeList G)[j].1 := by
    simp [edgeData, List.getD_eq_getElem?_getD, hj]
  simp only [hjd, vData, List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hi
  obtain ⟨u, ⟨w, hw, rfl⟩, rfl⟩ := hi
  have hmem : (w.1, (edgeList G)[j].1) ∈ G.edges := by rw [← hw.2]; exact hw.1
  obtain ⟨hi, hi'⟩ := eIdx_spec G hmem
  exact ⟨hi, by simpa [List.getD_eq_getElem?_getD, hi, hi', hj] using G.rank_lt _ hmem⟩
private lemma trans_length (cap : V × V → ℕ∞) (L : List ℕ) (c : List (List BitString))
    (A : BitString) {e : V × V} (he : e ∈ G.edges) :
    (trans G L c A e).length = L.getD (eIdx G e) 0 := by
  rw [trans_fixed G cap L c A he]; simp [edgeOut]
private lemma mem_inNeighbors_sort (cap : V × V → ℕ∞) (A : BitString) {w u : V} :
    w ∈ ((G.request cap A).inNeighbors u).sort (· ≤ ·) ↔ (w, u) ∈ G.edges := by
  simp [InformationRequest.inNeighbors, NetworkShape.request]
private lemma incoming_congr (cap : V × V → ℕ∞) (A : BitString) (t t' : V × V → BitString)
    (u : V) (h : ∀ w, (w, u) ∈ G.edges → t (w, u) = t' (w, u)) :
    (G.request cap A).incoming t u = (G.request cap A).incoming t' u := by
  simp only [InformationRequest.incoming]; congr 1
  exact List.map_congr_left fun w hw => h w ((mem_inNeighbors_sort G cap A).mp hw)
private lemma incoming_lengths (cap : V × V → ℕ∞) (L : List ℕ) (c : List (List BitString))
    (A : BitString) (u : V) : ((G.request cap A).incoming (trans G L c A) u).map List.length =
      (((G.edges.filter fun e => e.2 = u).image Prod.fst).sort (· ≤ ·)).map
        (fun w => L.getD (eIdx G (w, u)) 0) ++ if u = G.source then [A.length] else [] := by
  simp only [InformationRequest.incoming, List.map_append, List.map_map]; congr 1
  · exact List.map_congr_left fun w hw =>
      trans_length G cap L c A ((mem_inNeighbors_sort G cap A).mp hw)
  · by_cases hu : u = G.source <;> simp [NetworkShape.request, hu]
end Shape
private lemma flatten_inj : ∀ l1 l2 : List BitString, l1.map List.length = l2.map List.length →
    l1.flatten = l2.flatten → l1 = l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, hf => by
    simp only [List.map_cons, List.cons.injEq] at hl; simp only [List.flatten_cons] at hf
    obtain ⟨rfl, h⟩ := List.append_inj hf hl.1; rw [flatten_inj l1 l2 hl.2 h]
private def toCode {m R C : ℕ} (F : Fin m → Fin R → Fin C → Bool) : List (List BitString) :=
  List.ofFn fun j => List.ofFn fun r => List.ofFn (F j r)
private lemma toCode_getD {m R C : ℕ} (F : Fin m → Fin R → Fin C → Bool) (j : Fin m) :
    (toCode F).getD j [] = List.ofFn fun r => List.ofFn (F j r) := by
  simp [toCode, List.getD_eq_getElem?_getD]
private lemma edgeOut_toCode_eq_iff {m R C : ℕ} (F : Fin m → Fin R → Fin C → Bool) (j : Fin m)
    (ℓ : ℕ) (hℓ : ℓ ≤ R) (x x' : BitString) : edgeOut (toCode F) j ℓ x = edgeOut (toCode F) j ℓ x' ↔
      ∀ r : Fin R, (r : ℕ) < ℓ → rowBit x (List.ofFn (F j r)) = rowBit x' (List.ofFn (F j r)) := by
  simp only [edgeOut, toCode_getD, List.map_inj_left, List.mem_range]
  refine ⟨fun h r hr => ?_, fun h r hr => ?_⟩
  · simpa [List.getD_eq_getElem?_getD, r.isLt] using h r hr
  · simpa [List.getD_eq_getElem?_getD, hr.trans_le hℓ] using h ⟨r, hr.trans_le hℓ⟩ hr
section Coding
variable {V : Type*} [Fintype V] [LinearOrder V] (G : NetworkShape V) (cap : V × V → ℕ∞)
  (L : List ℕ) {R C : ℕ}
private lemma trans_local (A : BitString) (F F' : Fin (edgeList G).length → Fin R → Fin C → Bool)
    (r : ℕ) (hF : ∀ k, G.rank (edgeList G)[k].1 < r → F k = F' k) {e : V × V} (he : e ∈ G.edges)
    (hr : G.rank e.1 < r) : trans G L (toCode F) A e = trans G L (toCode F') A e := by
  suffices h : ∀ s, ∀ e ∈ G.edges, G.rank e.1 = s → s < r →
      trans G L (toCode F) A e = trans G L (toCode F') A e from h _ e he rfl hr
  refine fun s => Nat.strong_induction_on s fun s ih => ?_
  intro e he hs hr; rw [trans_fixed G 0 L _ A he, trans_fixed G 0 L _ A he,
    incoming_congr G 0 A _ (trans G L (toCode F') A) e.1 fun w hw => ih _ (hs ▸ G.rank_lt _ hw) _
      hw rfl (by have := G.rank_lt _ hw; simp only at this; change G.rank w < r; omega)]
  obtain ⟨h, h'⟩ := eIdx_spec G he; unfold edgeOut
  rw [toCode_getD F ⟨_, h⟩, toCode_getD F' ⟨_, h⟩, hF ⟨_, h⟩ (by simp [h']; omega)]
private def cutQ (A A' : BitString) (j : Fin (edgeList G).length)
    (F : Fin (edgeList G).length → Fin R → Fin C → Bool) : Prop :=
  ((G.request cap A).incoming (trans G L (toCode F) A) (edgeList G)[j].1).flatten ≠
      ((G.request cap A').incoming (trans G L (toCode F) A') (edgeList G)[j].1).flatten ∧
    edgeOut (toCode F) j (L.getD j 0)
        ((G.request cap A).incoming (trans G L (toCode F) A) (edgeList G)[j].1).flatten =
      edgeOut (toCode F) j (L.getD j 0)
        ((G.request cap A').incoming (trans G L (toCode F) A') (edgeList G)[j].1).flatten
private noncomputable instance (A A' : BitString) (j : Fin (edgeList G).length)
    (F : Fin (edgeList G).length → Fin R → Fin C → Bool) : Decidable (cutQ G cap L A A' j F) := by
  unfold cutQ; infer_instance
private lemma cut_of_collision {A A' : BitString} (hAA : A ≠ A') (hlen : A.length = A'.length)
    (F : Fin (edgeList G).length → Fin R → Fin C → Bool) (W : Finset V)
    (hW : ∀ v, v ∈ W ↔ (G.request cap A).incoming (trans G L (toCode F) A) v =
      (G.request cap A').incoming (trans G L (toCode F) A') v) :
    G.source ∉ W ∧ ∀ j : Fin (edgeList G).length,
      (edgeList G)[j] ∈ (G.request cap A).cutEdges W → cutQ G cap L A A' j F := by
  have hsplit : ∀ e ∈ G.edges, (G.request cap A).incoming (trans G L (toCode F) A) e.2 =
      (G.request cap A').incoming (trans G L (toCode F) A') e.2 →
      trans G L (toCode F) A e = trans G L (toCode F) A' e := by
    intro e he hv; simp only [InformationRequest.incoming] at hv
    exact List.map_inj_left.mp (List.append_inj_left' hv (by
      by_cases h : e.2 = G.source <;> simp [NetworkShape.request, h])) e.1
      ((mem_inNeighbors_sort G cap A).mpr he)
  refine ⟨fun hs => hAA ?_, fun j hj => ?_⟩
  · have h := (hW _).mp hs
    simp only [InformationRequest.incoming, NetworkShape.request, ite_true] at h
    simpa using List.append_inj_right' h rfl
  simp only [InformationRequest.cutEdges, Finset.mem_filter] at hj
  refine ⟨fun hx => hj.2.1 ((hW _).mpr (flatten_inj _ _ ?_ hx)), ?_⟩
  · rw [incoming_lengths G cap L _ A, incoming_lengths G cap L _ A', hlen]
  · have he : (edgeList G)[j] ∈ G.edges := hj.1; have h := hsplit _ he ((hW _).mp hj.2.2)
    have hj' : eIdx G (edgeList G)[j] = j := (Finset.nodup_toList _).idxOf_getElem j j.isLt
    rwa [trans_fixed G cap L _ A he, trans_fixed G cap L _ A' he, hj'] at h
private lemma getD_le_sum (L : List ℕ) (i : ℕ) : L.getD i 0 ≤ L.sum := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : L[i]? with _ | a <;> [simp; exact List.le_sum_of_mem (List.mem_of_getElem? h)]
private lemma length_flatten_incoming (A : BitString) (c : List (List BitString)) (u : V) :
    ((G.request cap A).incoming (trans G L c A) u).flatten.length ≤
      Fintype.card V * L.sum + A.length := by
  rw [List.length_flatten, incoming_lengths G cap L c A u, List.sum_append]
  refine Nat.add_le_add ((List.sum_le_length_nsmul _ L.sum fun x hx => ?_).trans ?_) ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx; exact getD_le_sum L _
  · simpa using Nat.mul_le_mul_right L.sum (Finset.card_le_univ _)
  · split_ifs <;> simp
private lemma cutQ_count (A A' : BitString) (hlen : A.length = A'.length) (hC : Fintype.card V *
    L.sum + A.length ≤ C) (hR : L.sum ≤ R) (j : Fin (edgeList G).length)
    (F : Fin (edgeList G).length → Fin R → Fin C → Bool) :
    (Finset.univ.filter fun y => cutQ G cap L A A' j (Function.update F j y)).card *
      2 ^ L.getD j 0 ≤ Fintype.card (Fin R → Fin C → Bool) := by
  classical
  have hloc : ∀ (B : BitString) y, (G.request cap B).incoming
      (trans G L (toCode (Function.update F j y)) B) (edgeList G)[j].1 =
      (G.request cap B).incoming (trans G L (toCode F) B) (edgeList G)[j].1 := fun B y =>
    incoming_congr G cap B _ _ _ fun w hw => trans_local G L B _ _ (G.rank (edgeList G)[j].1)
      (fun k hk => Function.update_of_ne (fun h => by subst h; omega) _ _) hw
      (by simpa using G.rank_lt _ hw)
  set x := ((G.request cap A).incoming (trans G L (toCode F) A) (edgeList G)[j].1).flatten
  set x' := ((G.request cap A').incoming (trans G L (toCode F) A') (edgeList G)[j].1).flatten
  by_cases hne : x = x'
  · have h0 : ∀ y, ¬ cutQ G cap L A A' j (Function.update F j y) := fun y h => by
      unfold cutQ at h; rw [hloc, hloc] at h; exact h.1 hne
    simp [h0]
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card fun y hy => ?_))
    (card_rows_agree R C _ ((getD_le_sum L j).trans hR) x x' ?_ ?_ hne)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, cutQ, hloc] at hy ⊢
    simpa using (edgeOut_toCode_eq_iff _ j _ ((getD_le_sum L j).trans hR) x x').mp hy.2
  · rw [List.length_flatten, List.length_flatten, incoming_lengths G cap L _ A,
      incoming_lengths G cap L _ A', hlen]
  · exact (length_flatten_incoming G cap L A _ _).trans hC
private lemma cutQ_dep (A A' : BitString) (j : Fin (edgeList G).length)
    (F F' : Fin (edgeList G).length → Fin R → Fin C → Bool)
    (h1 : ∀ k, G.rank (edgeList G)[k].1 < G.rank (edgeList G)[j].1 → F k = F' k)
    (h2 : F j = F' j) : cutQ G cap L A A' j F ↔ cutQ G cap L A A' j F' := by
  have hin : ∀ B, (G.request cap B).incoming (trans G L (toCode F) B) (edgeList G)[j].1 =
      (G.request cap B).incoming (trans G L (toCode F') B) (edgeList G)[j].1 := fun B =>
    incoming_congr G cap B _ _ _ fun w hw => trans_local G L B _ _ _ h1 hw
      (by simpa using G.rank_lt _ hw)
  have hout : ∀ x, edgeOut (toCode F) j (L.getD j 0) x = edgeOut (toCode F') j (L.getD j 0) x :=
    fun x => by unfold edgeOut; rw [toCode_getD F j, toCode_getD F' j, h2]
  unfold cutQ; rw [hin A, hin A', hout, hout]
private lemma bad_count (n s0 : ℕ) (A : BitString) (hA : A.length = n)
    (hs0 : s0 = Fintype.card V + 1) (hcuts : ∀ J : Finset V, G.source ∉ J →
      (J ∩ G.outputs).Nonempty → (n : ℕ∞) ≤ (G.request cap A).cutCapacity J)
    (hL : ∀ j : Fin (edgeList G).length, L.getD j 0 = (min (cap (edgeList G)[j]) n).toNat + s0)
    (hC : Fintype.card V * L.sum + n ≤ C) (hR : L.sum ≤ R) :
    (Finset.univ.filter fun F : Fin (edgeList G).length → Fin R → Fin C → Bool =>
      ¬ GoodFor (edgeData G) ((G.outputs.sort (· ≤ ·)).map (vData G)) n L (toCode F) A).card * 2
      ≤ Fintype.card (Fin R → Fin C → Bool) ^ (edgeList G).length := by
  classical
  set m := (edgeList G).length; set N := Fintype.card (Fin R → Fin C → Bool) ^ m
  let SW : Finset V → Finset (Fin m) := fun W =>
    Finset.univ.filter fun j => (edgeList G)[j] ∈ (G.request cap A).cutEdges W
  set P := ((allLists [false, true] n).toFinset.filter (· ≠ A)) ×ˢ
    (Finset.univ : Finset V).powerset.filter fun W => G.source ∉ W ∧ (W ∩ G.outputs).Nonempty
  have hsub : (Finset.univ.filter fun F : Fin m → Fin R → Fin C → Bool =>
      ¬ GoodFor (edgeData G) ((G.outputs.sort (· ≤ ·)).map (vData G)) n L (toCode F) A) ⊆
      P.biUnion fun p => Finset.univ.filter fun F => ∀ j ∈ SW p.2, cutQ G cap L A p.1 j F := by
    intro F hF; simp only [Finset.mem_filter, Finset.mem_univ, true_and, GoodFor, not_forall,
      not_or, not_not, List.mem_map, Finset.mem_sort] at hF
    obtain ⟨_, ⟨s, hs, rfl⟩, A', hA', hne, heq⟩ := hF
    rw [inputOf_vData G cap, inputOf_vData G cap] at heq
    obtain ⟨hsrc, hQ⟩ := cut_of_collision G cap L (Ne.symm hne)
      (hA.trans ((mem_allLists _ _ _).mp hA').1.symm) F _ fun v =>
      Finset.mem_filter.trans (and_iff_right (Finset.mem_univ v))
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, P,
      Finset.mem_product, List.mem_toFinset, Finset.mem_powerset]
    exact ⟨(A', _), ⟨⟨hA', hne⟩, Finset.subset_univ _, hsrc, s, by simpa [hs] using heq.symm⟩,
      fun j hj => hQ j (by
        simp only [SW, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        convert hj using 1
        congr)⟩
  have hterm : ∀ p ∈ P, (Finset.univ.filter fun F : Fin m → Fin R → Fin C → Bool =>
      ∀ j ∈ SW p.2, cutQ G cap L A p.1 j F).card * 2 ^ (n + s0) ≤ N := by
    rintro ⟨A', W⟩ hp
    simp only [P, Finset.mem_product, Finset.mem_filter, List.mem_toFinset, mem_allLists] at hp
    obtain ⟨⟨⟨hA', -⟩, hAA⟩, -, hW1, hW2⟩ := hp
    have key := card_filter_forall_mul_le (fun k : Fin m => G.rank (edgeList G)[k].1)
      (fun j F => cutQ G cap L A A' j F) (fun j => L.getD j 0) (SW W)
      (fun j _ F F' h1 h2 => cutQ_dep G cap L A A' j F F' h1 h2)
      (fun j _ F => cutQ_count G cap L A A' (hA.trans hA'.symm) (hA ▸ hC) hR j F)
    rw [Fintype.card_fin] at key
    refine le_trans (Nat.mul_le_mul (le_of_eq (by congr)) (Nat.pow_le_pow_right two_pos ?_)) key
    have hcut := hcuts W hW1 hW2
    have hsum : ∑ j ∈ SW W, L.getD j 0 =
        ∑ e ∈ (G.request cap A).cutEdges W, ((min (cap e) n).toNat + s0) := by
      refine Finset.sum_bij (fun j _ => (edgeList G)[j]) (fun j hj => by simpa [SW] using hj)
        (fun j1 _ j2 _ h => Fin.ext ((Finset.nodup_toList _).getElem_inj_iff.mp h))
        (fun e he => ?_) (fun j _ => hL j)
      obtain ⟨h, h'⟩ := eIdx_spec G (Finset.mem_filter.mp he).1
      exact ⟨⟨_, h⟩, by simpa [SW, h'] using he, h'⟩
    rw [hsum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have hne : ((G.request cap A).cutEdges W).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have h0 : n = 0 := by simpa [InformationRequest.cutCapacity, h] using hcut
      exact hAA ((List.length_eq_zero_iff.mp (hA'.trans h0)).trans
        (List.length_eq_zero_iff.mp (hA.trans h0)).symm)
    have := le_sum_toNat_min_of_le_sum _ cap n hcut; have := hne.card_pos; nlinarith
  have hP : P.card ≤ 2 ^ n * 2 ^ Fintype.card V := by
    rw [Finset.card_product]; refine Nat.mul_le_mul ((Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans ?_)) ((Finset.card_filter_le _ _).trans ?_) <;>
      simp [length_allLists]
  have h1 := Nat.mul_le_mul_right (2 ^ (n + s0))
    ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
  rw [Finset.sum_mul] at h1
  have h2 := h1.trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans (Nat.mul_le_mul_right N hP))
  rw [hs0, ← add_assoc, pow_succ, pow_add] at h2
  exact Nat.le_of_mul_le_mul_right (by linarith) (by positivity : 0 < 2 ^ n * 2 ^ Fintype.card V)
private lemma toCode_mem {m : ℕ} (F : Fin m → Fin R → Fin C → Bool) :
    toCode F ∈ allLists (allLists (allLists [false, true] C) R) m := by simp [toCode, mem_allLists]
private lemma search_spec (n s0 : ℕ) (hs0 : s0 = Fintype.card V + 1)
    (hcuts : ∀ A : BitString, ∀ J : Finset V, G.source ∉ J → (J ∩ G.outputs).Nonempty →
      (n : ℕ∞) ≤ (G.request cap A).cutCapacity J)
    (hL : ∀ j : Fin (edgeList G).length, L.getD j 0 = (min (cap (edgeList G)[j]) n).toNat + s0) :
    (search (edgeData G) ((G.outputs.sort (· ≤ ·)).map (vData G)) (Fintype.card V) n L).length
      = n + 1 ∧ ∀ A ∈ allLists [false, true] n, ∃ c ∈ search (edgeData G)
        ((G.outputs.sort (· ≤ ·)).map (vData G)) (Fintype.card V) n L,
        GoodFor (edgeData G) ((G.outputs.sort (· ≤ ·)).map (vData G)) n L c A := by
  classical
  set SD := (G.outputs.sort (· ≤ ·)).map (vData G); set m := (edgeList G).length
  let X := Fin m → Fin L.sum → Fin (Fintype.card V * L.sum + n) → Bool
  let Bad : BitString → Finset X := fun A =>
    Finset.univ.filter fun F => ¬ GoodFor (edgeData G) SD n L (toCode F) A
  have hB : ∀ A ∈ allLists [false, true] n, (Bad A).card * 2 ≤ Fintype.card X := fun A hA => by
    have := bad_count G cap L n s0 A ((mem_allLists _ _ _).mp hA).1 hs0 (hcuts A) hL le_rfl le_rfl
    simpa only [X, Fintype.card_fun, Fintype.card_fin] using this
  let BS := Finset.univ.filter fun Gs : Fin (n + 1) → X =>
    ∃ A ∈ allLists [false, true] n, ∀ i, Gs i ∈ Bad A
  have hsub : BS ⊆ (allLists [false, true] n).toFinset.biUnion fun A =>
      Fintype.piFinset fun _ => Bad A := by
    intro Gs h; simpa [BS, Fintype.mem_piFinset] using h
  have hAc : (allLists [false, true] n).toFinset.card ≤ 2 ^ n :=
    (List.toFinset_card_le _).trans (by simp [length_allLists])
  have h1 := Nat.mul_le_mul_right (2 ^ (n + 1))
    ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
  rw [Finset.sum_mul] at h1
  have h2 := h1.trans ((Finset.sum_le_card_nsmul _ _ (Fintype.card X ^ (n + 1)) fun A hA => by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
    exact Nat.pow_le_pow_left (hB A (List.mem_toFinset.mp hA)) _).trans
      (Nat.mul_le_mul_right _ hAc))
  have hBS : BS.card < (Finset.univ : Finset (Fin (n + 1) → X)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have : 0 < Fintype.card X ^ (n + 1) := by positivity
    have := Nat.le_of_mul_le_mul_right (c := 2 ^ n) (a := BS.card * 2)
      (b := Fintype.card X ^ (n + 1)) (by rw [pow_succ] at h2; linarith) (by positivity)
    omega
  obtain ⟨Gs, -, hGs⟩ := Finset.exists_mem_notMem_of_card_lt_card hBS
  simp only [BS, Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
    not_forall, not_not] at hGs
  have hS : ∃ x ∈ allLists (allLists (allLists (allLists [false, true]
      (Fintype.card V * L.sum + n)) L.sum) (edgeData G).length) (n + 1),
      decide (∀ A ∈ allLists [false, true] n, ∃ c ∈ x, GoodFor (edgeData G) SD n L c A) := by
    refine ⟨List.ofFn fun i => toCode (Gs i), ?_, decide_eq_true fun A hA => ?_⟩
    · rw [show (edgeData G).length = m from List.length_map _, mem_allLists]
      refine ⟨List.length_ofFn, fun c hc => ?_⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc; exact toCode_mem _
    · obtain ⟨i, hi⟩ := hGs A hA; exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  obtain ⟨hmem, hp⟩ := getD_findIdx_spec _ _ [] hS
  exact ⟨((mem_allLists _ _ _).mp hmem).1, of_decide_eq_true hp⟩
private lemma decodeAt_spec (n : ℕ) (A : BitString) (hA : A ∈ allLists [false, true] n)
    (c : List (List BitString)) (hgood : GoodFor (edgeData G) ((G.outputs.sort (· ≤ ·)).map
      (vData G)) n L c A) {v : V} (hv : v ∈ G.outputs) :
    decodeAt (edgeData G) n L c (vData G v)
      (listCode ((G.request cap A).incoming (trans G L c A) v)) = A := by
  unfold decodeAt
  obtain ⟨hmem, hp⟩ := getD_findIdx_spec (allLists [false, true] n) (fun B => decide
    (listCode (inputOf (sim (edgeData G) L c B) B (vData G v)) =
      listCode ((G.request cap A).incoming (trans G L c A) v))) []
    ⟨A, hA, decide_eq_true (by rw [inputOf_vData G cap])⟩
  exact (hgood _ (List.mem_map.mpr ⟨v, (Finset.mem_sort _).mpr hv, rfl⟩) _ hmem).resolve_right
    fun h => h ((listCode_injective (of_decide_eq_true hp)).trans
      (inputOf_vData G cap L c A v).symm)
end Coding
private lemma length_bits_le_add (x n s : ℕ) (h : x ≤ n + s) :
    (Nat.bits x).length ≤ (Nat.bits n).length + s + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le, pow_succ, pow_add]
  nlinarith [Nat.lt_size_self n, (Nat.lt_two_pow_self : s < 2 ^ s),
    Nat.one_le_two_pow (n := Nat.size n), Nat.one_le_two_pow (n := s)]
/-- Algorithmic network coding: for a fixed single-source shape there is a constant `c` (graph
only) so that whenever every cut avoiding the source and meeting the outputs has capacity at
least `n`, delivering an `n`-bit `A` to all outputs is fulfillable with precision `O(log n)`
and capacities exceeded by at most `O(log n)` bits.  This is WEAKER than the printed Theorem
236 (which forbids any excess); the excess is what the book's rounding delivers.
SUV Theorem 236, pp. 385–388. -/
theorem exists_networkCoding_of_cutConditions (D : Map) (hD : isOptimalConditional D)
    {V : Type*} [Fintype V] [LinearOrder V] (G : NetworkShape V) :
    ∃ c : ℕ, ∀ (n : ℕ) (A : BitString) (cap : V × V → ℕ∞), A.length = n →
      (∀ J : Finset V, G.source ∉ J → (J ∩ G.outputs).Nonempty →
        (n : ℕ∞) ≤ (G.request cap A).cutCapacity J) →
      ∃ t : V × V → BitString,
        IsFulfilledUpTo D (G.request cap A) t (logSlack c n) (logSlack c n) := by
  classical
  set s0 := Fintype.card V + 1; set m := (edgeList G).length
  set SD := (G.outputs.sort (· ≤ ·)).map (vData G); set VL := (Finset.univ : Finset V).sort (· ≤ ·)
  set VD := VL.map (vData G); have hVL : VL.length = Fintype.card V := by simp [VL]
  obtain ⟨k₁, hk₁⟩ := condK_comp D hD _ (netDecoder_primrec (edgeData G) SD VD).to_comp
  obtain ⟨k₂, hk₂⟩ := condK_le_condK_cond_map_add_length D hD (fun w y => listCode [w, y])
    (listCode_primrec.comp (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).to₂
  set K0 := (Nat.bits (m + Fintype.card V)).length
  set c₀ := 20 * m + 10 + 10 * (m * (2 * s0 + 3) + K0 + 1) + 5
  obtain ⟨c', hc'⟩ := logSlack_logSlack_absorb k₁ c₀ k₂
  refine ⟨c' + s0, fun n A cap hA hcuts => ?_⟩
  set L := (edgeList G).map fun e => (min (cap e) n).toNat + s0 with hLdef
  have hL : ∀ j : Fin m, L.getD j 0 = (min (cap (edgeList G)[j]) n).toNat + s0 := fun j => by
    simp [L, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
  have hAmem : A ∈ allLists [false, true] n := by simp [mem_allLists, hA]
  obtain ⟨hlen, hres⟩ := search_spec G cap L n s0 rfl (fun _ => hcuts) hL
  obtain ⟨c, hc, hgood⟩ := hres A hAmem; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  set res := search (edgeData G) SD (Fintype.card V) n L
  let adv : ℕ → Bool → BitString := fun j b =>
    listCode [Nat.bits n, listCode (L.map Nat.bits), Nat.bits i, Nat.bits j, [b]]
  have hdec : ∀ j b y, netDecoder (edgeData G) SD VD (listCode [adv j b, y]) =
      netAlg (edgeData G) SD VD (n, L, i, j, b) y := fun j b y => by
    simp only [netDecoder, decodeListCode_listCode, adv, netParams, List.getD_cons_zero,
      List.getD_cons_succ, bitsToNat_bits, List.map_map, Function.comp_def, List.map_id',
      List.headI_cons]
  have hcsel : (search (edgeData G) SD VD.length n L).getD i [] = res[i] := by
    rw [List.length_map, hVL, List.getD_eq_getElem]
  have hadv : ∀ j b, j ≤ m + Fintype.card V → (adv j b).length ≤ logSlack c₀ n := by
    intro j b hj; set B := (Nat.bits n).length
    have hP : ∀ x ∈ [Nat.bits n, listCode (L.map Nat.bits), Nat.bits i, Nat.bits j, [b]],
        x.length ≤ m * (2 * (B + s0 + 1) + 1) + B + K0 + 1 := by
      have hLb : (listCode (L.map Nat.bits)).length ≤ m * (2 * (B + s0 + 1) + 1) := by
        refine (length_listCode_le _ (B + s0 + 1) fun x hx => ?_).trans (by simp [L, m])
        obtain ⟨_, hy, rfl⟩ := List.mem_map.mp hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hy
        exact length_bits_le_add _ _ _ (Nat.add_le_add_right
          (ENat.toNat_le_of_le_natCast (min_le_right _ _)) _)
      have hi' : (Nat.bits i).length ≤ B := length_bits_mono (by omega)
      have hj' : (Nat.bits j).length ≤ K0 := length_bits_mono hj
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl) <;> first | omega | simp
    refine (length_listCode_le _ _ hP).trans ?_; simp only [List.length_cons, List.length_nil,
      logSlack, c₀]
    nlinarith [Nat.zero_le (m * s0 * B), Nat.zero_le (m * B), Nat.zero_le (K0 * B)]
  have hbound : ∀ x y j b, j ≤ m + Fintype.card V →
      netDecoder (edgeData G) SD VD (listCode [adv j b, y]) = x →
      condK D x y ≤ (logSlack (c' + s0) n : ℕ∞) := by
    intro x y j b hj hx; have hw := hadv j b hj; have h2 := hk₁ (listCode [adv j b, y])
    rw [hx] at h2; have h3 := logSlack_mono_right k₂ hw; have h4 := hc' n
    have h5 : logSlack c' n ≤ logSlack (c' + s0) n := by simp only [logSlack]; nlinarith
    refine (hk₂ x y _).trans ((add_le_add (add_le_add h2 le_rfl) le_rfl).trans ?_)
    exact_mod_cast (by omega :
      k₁ + (adv j b).length + logSlack k₂ (adv j b).length ≤ logSlack (c' + s0) n)
  refine ⟨trans G L res[i] A, fun e he => ?_, fun v x hx => ?_⟩
  · obtain ⟨h, h'⟩ := eIdx_spec G he; have h1 := trans_length G cap L res[i] A he
    have h2 := hL ⟨_, h⟩; simp only [Fin.getElem_fin, h'] at h2
    change ((trans G L res[i] A e).length : ℕ∞) ≤ cap e + (logSlack (c' + s0) n : ℕ∞); rw [h1, h2]
    have h3 : s0 ≤ logSlack (c' + s0) n := by simp only [logSlack]; nlinarith
    push_cast
    exact add_le_add ((ENat.natCast_toNat_le_self _).trans (min_le_left _ _))
      (by exact_mod_cast h3)
  · simp only [InformationRequest.outgoing, List.mem_append, List.mem_map, Finset.mem_sort] at hx
    rcases hx with ⟨w, hw, rfl⟩ | hx
    · have he : (v, w) ∈ G.edges := by
        simpa [InformationRequest.outNeighbors, NetworkShape.request] using hw
      obtain ⟨h, -⟩ := eIdx_spec G he; refine hbound _ _ (eIdx G (v, w)) true (by omega) ?_
      rw [hdec]; simp only [netAlg, Bool.cond_true, hcsel, decodeListCode_listCode]
      exact (trans_fixed G cap L _ A he).symm
    · have hv : v ∈ G.outputs ∧ x = A := by
        by_cases hv : v ∈ G.outputs <;> simp_all [NetworkShape.request]
      obtain ⟨hv, rfl⟩ := hv; have hk : VL.idxOf v < VL.length :=
        List.idxOf_lt_length_of_mem ((Finset.mem_sort _).mpr (Finset.mem_univ v))
      have hvd : VD.getD (VL.idxOf v) ([], false) = vData G v := by
        simp [VD, List.getD_eq_getElem?_getD, hk]
      refine hbound _ _ (VL.idxOf v) false (by omega) ?_; rw [hdec]
      simp only [netAlg, Bool.cond_false, hcsel, hvd]
      exact decodeAt_spec G cap L n x hAmem _ hgood hv
end Kolmogorov
