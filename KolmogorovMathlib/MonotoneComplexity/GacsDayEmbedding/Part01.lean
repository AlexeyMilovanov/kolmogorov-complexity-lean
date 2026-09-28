import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay
import KolmogorovMathlib.MonotoneComplexity.GacsDayGame
import KolmogorovMathlib.MonotoneComplexity.GacsDayBinaryEncoding
import KolmogorovMathlib.MonotoneComplexity.GacsDayBlockCode
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable



namespace Kolmogorov

/-!
# Gacs-Day Game Binary Embedding

This file provides the conditional reduction of the binary Gacs-Day game statement
from the standard Gacs-Day game statement. The original game is played on a tree
of depth `O(d)` with branching factor `2 ^ ((O(d)) ^ (O(d)))`. By encoding each
branch index into a fixed-width binary block, we embed this into a binary tree.
-/

/-- The total depth of the binary embedding is bounded by the original height
times the block width (which is `ceil(log2 b)`). -/
lemma embeddedDepth_le_height_mul_ceilLog (h b : ℕ) {x : GacsDayNode}
    (hx : x.length ≤ h) :
    (fixedWidthBlocks (Nat.log2 b + 1) x).length ≤ h * (Nat.log2 b + 1) := by
  rw [fixedWidthBlocks_length, Nat.mul_comm h]
  exact Nat.mul_le_mul_left _ hx

/-- Pure arithmetic: bounding the binary height by `O(d)^O(d)`.
  Proof: set `x = C * d`; then LHS = `x^(x+1)` and RHS with `C' = C + 1`
  is `y^y` where `y = (C+1)*d ≥ x + 1`. -/
lemma gacsDay_binary_height_bound (C : ℕ) :
    ∃ C' : ℕ, ∀ d, C * d * ((C * d) ^ (C * d)) ≤ (C' * d) ^ (C' * d) := by
  use C + 1
  intro d
  cases d with
  | zero => simp
  | succ d =>
    set x := C * (d + 1) with hx_def
    rw [show x * x ^ x = x ^ (x + 1) from by ring]
    have hy_ge : x + 1 ≤ (C + 1) * (d + 1) := by
      have : (C + 1) * (d + 1) = C * (d + 1) + (d + 1) := by ring
      omega
    have hy_pos : 0 < (C + 1) * (d + 1) := by omega
    calc
      x ^ (x + 1) ≤ ((C + 1) * (d + 1)) ^ (x + 1) :=
        Nat.pow_le_pow_left (by omega) _
      _ ≤ ((C + 1) * (d + 1)) ^ ((C + 1) * (d + 1)) :=
        Nat.pow_le_pow_right hy_pos hy_ge

/-- The fixed block width used by the Gács–Day binary encoding is computable
uniformly in the game parameter. -/
lemma computable_gacsDay_blockWidth (C : ℕ) :
    Computable (fun d : ℕ => (C * d) ^ (C * d)) := by
  have hmul : Computable (fun d : ℕ => C * d) :=
    (Primrec.nat_mul.comp (Primrec.const C) Primrec.id).to_comp
  exact (Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp hmul hmul

/-
The previous formulation of the `d = 2 ^ c` specialisation was

```
lemma gacsDay_binary_height_bound_pow (C c : ℕ) :
    ∃ C' : ℕ, C * 2^c * ((C * 2^c) ^ (C * 2^c)) ≤ 2 ^ (C' * c * 2^c)
```

which is **false**: for `c = 0` the right-hand exponent `C' * 0 * 1` is `0` for
every witness `C'`, so the right-hand side is `1`, while for `C = 2` the
left-hand side is `2 * 2 ^ 2 = 8`.  This is recorded as
`gacsDay_binary_height_bound_pow_false` below, and the corrected statement
(with `c + 1` in place of `c`, and with the constant chosen uniformly in `c`)
is `gacsDay_binary_height_bound_pow`.
-/

/-- The naive `d = 2 ^ c` height bound with exponent `C' * c * 2 ^ c` is false,
because the exponent degenerates to `0` at `c = 0`. -/
lemma gacsDay_binary_height_bound_pow_false :
    ¬ ∀ C c : ℕ, ∃ C' : ℕ, C * 2^c * ((C * 2^c) ^ (C * 2^c)) ≤ 2 ^ (C' * c * 2^c) := by
  intro h
  obtain ⟨C', hC'⟩ := h 2 0
  norm_num at hC'

/-- Pure arithmetic: for `d = 2 ^ c`, the binary height is bounded by
`2 ^ (O(c) * 2 ^ c)`, with the constant depending only on `C` (uniformly in `c`).
The exponent is written `C' * (c + 1) * 2 ^ c` rather than `C' * c * 2 ^ c`,
which is necessary: see `gacsDay_binary_height_bound_pow_false`. -/
lemma gacsDay_binary_height_bound_two_pow {C : ℕ} :
    ∃ C', ∀ d, C * d * ((C * d) ^ (C * d)) ≤ 2 ^ ((C' * d) ^ (C' * d)) := by
  obtain ⟨C', hC'⟩ := gacsDay_binary_height_bound C
  use C'
  intro d
  exact le_trans (hC' d) (Nat.le_two_pow_self _)

/-- The tower `C * 2 ^ c` raised to itself is bounded by `2 ^ (C' * (c + 1) * 2 ^ c)` for a
constant `C'` depending only on `C`. -/
lemma gacsDay_binary_height_bound_pow (C : ℕ) :
    ∃ C' : ℕ, ∀ c : ℕ,
      C * 2^c * ((C * 2^c) ^ (C * 2^c)) ≤ 2 ^ (C' * (c + 1) * 2^c) := by
  refine ⟨(C + 1) * (Nat.log 2 C + 1), fun c => ?_⟩
  set L := Nat.log 2 C with hL
  set n := C * 2 ^ c with hn
  have h2c : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  have hCk : C < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) C
  have hnk : n < 2 ^ (L + 1 + c) := by
    have h : C * 2 ^ c < 2 ^ (L + 1) * 2 ^ c :=
      Nat.mul_lt_mul_of_lt_of_le hCk le_rfl (by positivity)
    simpa [hn, pow_add] using h
  have hexp : (L + 1 + c) * (n + 1) ≤ (C + 1) * (L + 1) * (c + 1) * 2 ^ c := by
    have h1 : L + 1 + c ≤ (L + 1) * (c + 1) := by nlinarith
    have h2 : n + 1 ≤ (C + 1) * 2 ^ c := by simp only [hn]; nlinarith
    calc (L + 1 + c) * (n + 1) ≤ ((L + 1) * (c + 1)) * ((C + 1) * 2 ^ c) :=
          Nat.mul_le_mul h1 h2
      _ = (C + 1) * (L + 1) * (c + 1) * 2 ^ c := by ring
  calc n * n ^ n = n ^ (n + 1) := by ring
    _ ≤ (2 ^ (L + 1 + c)) ^ (n + 1) := Nat.pow_le_pow_left hnk.le _
    _ = 2 ^ ((L + 1 + c) * (n + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ ((C + 1) * (L + 1) * (c + 1) * 2 ^ c) := Nat.pow_le_pow_right (by norm_num) hexp

/-! ### Elementary facts about the extension machinery -/

/-! ### Coherence of the intermediate request assignment -/

/-! ### Finite realization of the intermediate request assignment

`intermediateRequestSum` is a *function* on nodes, whereas a `ClientMove` is a
finite association list.  The lemmas in this section show that the intermediate
assignment has finite support, hence is realized by an actual client move. -/

/-- All lists of a given length with entries bounded by `M`. -/
def natListsLen (M : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range (M + 1)).flatMap
      (fun a => (natListsLen M n).map (fun l => a :: l))

/-- All lists of length at most `L` with entries bounded by `M`. -/
def natListsUpTo (M L : ℕ) : List (List ℕ) :=
  (List.range (L + 1)).flatMap (natListsLen M)

/-- The largest depth of a node mentioned by a client move. -/
def keyMaxLen (req : ClientMove) : ℕ :=
  (req.map (fun p => p.1.length)).foldr max 0

/-- The largest branch index mentioned by a client move. -/
def keyMaxEntry (req : ClientMove) : ℕ :=
  (req.map (fun p => p.1.foldr max 0)).foldr max 0

/-! ### Transfer of a winning strategy along the embedding -/

/-- Every move of a play is an application of the strategy to some history. -/
lemma exists_history_playClient (σ : ClientStrategy) (sms : ℕ → ServerMove) (t : ℕ) :
    ∃ hist : GameHistory, playClient σ sms t = σ hist := by
  cases t with
  | zero => exact ⟨([], []), by rw [playClient]⟩
  | succ t =>
      exact ⟨(List.ofFn (fun i : Fin (t + 1) => playClient σ sms i.val),
        List.ofFn (fun i : Fin (t + 1) => sms i.val)), by rw [playClient]⟩

/-! ### Computability of the embedding data -/

private lemma natListsLen_eq_rec (M n : ℕ) :
    natListsLen M n = Nat.rec [[]]
      (fun _ ih => ((List.range (M + 1)).map (fun a => ih.map (fun l => a :: l))).flatten) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natListsLen, ih, List.flatMap_def]

/-- Listing the number lists of a given length with entries below a bound is primitive recursive. -/
lemma primrec_natListsLen : Primrec₂ natListsLen := by
  have hinner : Primrec₂ (fun (z : (ℕ × ℕ) × (ℕ × List (List ℕ))) (a : ℕ) =>
      z.2.2.map (fun l => a :: l)) :=
    Primrec₂.mk (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  have hstep : Primrec₂ (fun (p : ℕ × ℕ) (q : ℕ × List (List ℕ)) =>
      ((List.range (p.1 + 1)).map (fun a => q.2.map (fun l => a :: l))).flatten) :=
    Primrec₂.mk (Primrec.list_flatten.comp
      (Primrec.list_map
        (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
        hinner))
  have hrec := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ : ℕ × ℕ => ([[]] : List (List ℕ))) Primrec.snd (Primrec.const _) hstep
  exact hrec.of_eq (fun p => (natListsLen_eq_rec p.1 p.2).symm)

/-- Listing the number lists up to a given length is primitive recursive. -/
lemma primrec_natListsUpTo : Primrec₂ natListsUpTo := by
  have hmap : Primrec (fun p : ℕ × ℕ =>
      (List.range (p.2 + 1)).map (fun n => natListsLen p.1 n)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (primrec_natListsLen.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  refine Primrec₂.mk ((Primrec.list_flatten.comp hmap).of_eq (fun p => ?_))
  simp [natListsUpTo, List.flatMap_def]

private lemma primrec_foldrMax : Primrec (fun l : List ℕ => l.foldr max 0) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

/-- The maximal key length of a move is primitive recursive in the move. -/
lemma primrec_keyMaxLen : Primrec keyMaxLen := by
  have hmap : Primrec (fun req : ClientMove => req.map (fun p => p.1.length)) :=
    Primrec.list_map Primrec.id
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)).to₂
  exact primrec_foldrMax.comp hmap

/-- The maximal key entry of a move is primitive recursive in the move. -/
lemma primrec_keyMaxEntry : Primrec keyMaxEntry := by
  have hmap : Primrec (fun req : ClientMove => req.map (fun p => p.1.foldr max 0)) :=
    Primrec.list_map Primrec.id (primrec_foldrMax.comp (Primrec.fst.comp Primrec.snd)).to₂
  exact primrec_foldrMax.comp hmap

/-- Reading off a request from a client move is primitive recursive. -/
lemma primrec_getReq : Primrec₂ (fun (req : ClientMove) (n : GacsDayNode) => getReq req n) := by
  have hstep : Primrec (fun w : (ClientMove × GacsDayNode) × ((GacsDayNode × ℚ) × ℚ) =>
      if w.2.1.1 = w.1.2 then w.2.1.2 else w.2.2) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec (fun z : ClientMove × GacsDayNode =>
      z.1.foldr (fun p s => if p.1 = z.2 then p.2 else s) 0) :=
    Primrec.list_foldr Primrec.fst (Primrec.const 0) hstep.to₂
  refine Primrec₂.mk (hfold.of_eq (fun z => ?_))
  obtain ⟨req, n⟩ := z
  simp only
  induction req with
  | nil => rfl
  | cons p t ih =>
    unfold getReq at *
    simp only [List.foldr_cons, List.lookup]
    by_cases hp : p.1 = n
    · subst hp
      simp
    · have hb : (n == p.1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hq => hp hq.symm
      rw [if_neg hp]
      simp only [hb]
      exact ih

/-- Reading a bit list as a number is primitive recursive. -/
lemma primrec_bitsToNatLocal : Primrec bitsToNatLocal := by
  have h : Primrec (fun l : List ℕ => l.foldr (fun b s => b + 2 * s) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂
  refine h.of_eq (fun l => ?_)
  induction l with
  | nil => rfl
  | cons a t ih => simp [bitsToNatLocal, ih]

/-- Chunking stops as soon as the block width is zero or the list is too short. -/
lemma chunkNat_eq_nil (m : ℕ) (l : List ℕ) (h : ¬ (0 < m ∧ m ≤ l.length)) :
    chunkNat m l = [] := by
  cases l with
  | nil => exact chunkNat_nil m
  | cons a t =>
    rw [chunkNat, dif_neg h]
    simp

/-- One step of the block-splitting loop: peel off the first `m` bits. -/
private def chunkStep (s : ℕ × List ℕ × List ℕ) : ℕ × List ℕ × List ℕ :=
  if 0 < s.1 ∧ s.1 ≤ s.2.2.length then
    (s.1, s.2.1 ++ [bitsToNatLocal (s.2.2.take s.1)], s.2.2.drop s.1)
  else s

private lemma primrec_chunkStep : Primrec chunkStep := by
  have hm : Primrec (fun s : ℕ × List ℕ × List ℕ => s.1) := Primrec.fst
  have hacc : Primrec (fun s : ℕ × List ℕ × List ℕ => s.2.1) := Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun s : ℕ × List ℕ × List ℕ => s.2.2) := Primrec.snd.comp Primrec.snd
  have hcond : PrimrecPred (fun s : ℕ × List ℕ × List ℕ => 0 < s.1 ∧ s.1 ≤ s.2.2.length) :=
    PrimrecPred.and (Primrec.nat_lt.comp (Primrec.const 0) hm)
      (Primrec.nat_le.comp hm (Primrec.list_length.comp hrest))
  have hthen : Primrec (fun s : ℕ × List ℕ × List ℕ =>
      (s.1, s.2.1 ++ [bitsToNatLocal (s.2.2.take s.1)], s.2.2.drop s.1)) :=
    Primrec.pair hm (Primrec.pair
      (Primrec.list_append.comp hacc
        (Primrec.list_cons.comp
          (primrec_bitsToNatLocal.comp (Primrec.list_take.comp hrest hm)) (Primrec.const [])))
      (Primrec.list_drop.comp hrest hm))
  exact (Primrec.ite hcond hthen Primrec.id).of_eq (fun _ => rfl)

private lemma chunkStep_fst (m : ℕ) :
    ∀ (n : ℕ) (acc rest : List ℕ), rest.length ≤ n →
      (chunkStep^[n] (m, acc, rest)).2.1 = acc ++ chunkNat m rest := by
  intro n
  induction n with
  | zero =>
    intro acc rest hr
    have hnil : rest = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hr)
    subst hnil
    simp [chunkNat_nil]
  | succ n ih =>
    intro acc rest hr
    rw [Function.iterate_succ_apply]
    by_cases hc : 0 < m ∧ m ≤ rest.length
    · have hstep : chunkStep (m, acc, rest)
          = (m, acc ++ [bitsToNatLocal (rest.take m)], rest.drop m) := by
        simp only [chunkStep, if_pos hc]
      rw [hstep, ih _ _ (by simp only [List.length_drop]; omega)]
      rw [chunkNat_eq m hc.1 rest hc.2]
      simp
    · have hstep : chunkStep (m, acc, rest) = (m, acc, rest) := by
        simp only [chunkStep, if_neg hc]
      have hfix : ∀ k, chunkStep^[k] (m, acc, rest) = (m, acc, rest) := by
        intro k
        induction k with
        | zero => rfl
        | succ k ihk => rw [Function.iterate_succ_apply, hstep, ihk]
      rw [hstep, hfix n, chunkNat_eq_nil m rest hc]
      simp

private lemma chunkNat_eq_iterate (m : ℕ) (l : List ℕ) :
    chunkNat m l = (chunkStep^[l.length] (m, [], l)).2.1 := by
  rw [chunkStep_fst m l.length [] l le_rfl]
  simp

/-- Chunking a list into blocks is primitive recursive in the width and the list. -/
lemma primrec_chunkNat : Primrec₂ chunkNat := by
  have hiter : Primrec₂ (fun (a : ℕ × List ℕ × List ℕ) (n : ℕ) => chunkStep^[n] a) :=
    Primrec.nat_iterate' primrec_chunkStep
  have h : Primrec (fun p : ℕ × List ℕ => chunkStep^[p.2.length] (p.1, [], p.2)) :=
    hiter.comp (Primrec.pair Primrec.fst (Primrec.pair (Primrec.const []) Primrec.snd))
      (Primrec.list_length.comp Primrec.snd)
  refine Primrec₂.mk (((Primrec.fst.comp (Primrec.snd.comp h))).of_eq (fun p => ?_))
  exact (chunkNat_eq_iterate p.1 p.2).symm

/-- The fixed-width binary encoding is primitive recursive in the width and the number. -/
lemma primrec_bitsOfNat : Primrec₂ bitsOfNat := by
  have hinner : Primrec (fun w : (ℕ × ℕ) × ℕ => (w.1.2 / 2 ^ w.2) % 2) :=
    Primrec.nat_mod.comp
      (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
        ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.snd))
      (Primrec.const 2)
  have h : Primrec (fun z : ℕ × ℕ => (List.range z.1).map (fun i => (z.2 / 2 ^ i) % 2)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst) hinner.to₂
  refine Primrec₂.mk (h.of_eq (fun z => ?_))
  simp [bitsOfNat, Nat.shiftRight_eq_div_pow]

private lemma filterMap_ite {α β : Type*} (c : α → Prop) [DecidablePred c] (g : α → β)
    (l : List α) :
    l.filterMap (fun p => if c p then some (g p) else none)
      = (l.filter (fun p => decide (c p))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hc : c a
    · simp [hc, ih]
    · simp [hc, ih]

/-- Transporting a server move along the block code is primitive recursive. -/
lemma primrec₂_baseServerMove : Primrec₂ baseServerMove := by
  have hpred : Primrec (fun w : ℕ × (GacsDayNode × Allocation) =>
      (w.2.1.all (fun a => decide (a < 2)) && decide (w.2.1.length % w.1 = 0))) := by
    have h1 : Primrec (fun w : ℕ × (GacsDayNode × Allocation) =>
        w.2.1.all (fun a => decide (a < 2))) := by
      have hlt : Primrec (fun i : ℕ => decide (i < 2)) := by
        have h : PrimrecPred (fun i : ℕ => i < 2) :=
          Primrec.nat_lt.comp Primrec.id (Primrec.const 2)
        obtain ⟨_, h⟩ := h
        exact h.of_eq (fun i => by simp)
      exact (Primrec.list_all hlt).comp (Primrec.fst.comp Primrec.snd)
    have h2 : Primrec (fun w : ℕ × (GacsDayNode × Allocation) =>
        decide (w.2.1.length % w.1 = 0)) := by
      have h : PrimrecPred (fun w : ℕ × (GacsDayNode × Allocation) => w.2.1.length % w.1 = 0) :=
        Primrec.eq.comp
          (Primrec.nat_mod.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
            Primrec.fst)
          (Primrec.const 0)
      obtain ⟨_, h⟩ := h
      exact h.of_eq (fun w => by simp)
    exact Primrec.dom_bool₂ (fun x1 x2 => x1 && x2) |>.comp h1 h2
  have hfilter : Primrec (fun z : ℕ × ServerMove => z.2.filter
      (fun p => (p.1.all (fun a => decide (a < 2)) && decide (p.1.length % z.1 = 0)))) := by
    have hstep : Primrec (fun w : (ℕ × ServerMove) × (GacsDayNode × Allocation) =>
        (w.2.1.all (fun a => decide (a < 2)) && decide (w.2.1.length % w.1.1 = 0))) :=
      hpred.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_filter Primrec.snd hstep.to₂
  have hmap : Primrec (fun z : ℕ × ServerMove =>
      (z.2.filter (fun p =>
        (p.1.all (fun a => decide (a < 2)) && decide (p.1.length % z.1 = 0)))).map
        (fun p => (chunkNat z.1 p.1, p.2))) :=
    Primrec.list_map hfilter
      (Primrec.pair
        (primrec_chunkNat.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine Primrec₂.mk (hmap.of_eq (fun z => ?_))
  rw [baseServerMove, filterMap_ite]
  congr 1
  refine List.filter_congr (fun p _ => ?_)
  rw [Bool.eq_iff_iff]
  simp [Nat.dvd_iff_mod_eq_zero]

/-! ### Truncating a client strategy to the `b`-ary subtree -/

/-- The client move `req` with every request outside the first `b` children deleted. -/
def truncMove (b : ℕ) (req : ClientMove) : ClientMove :=
  req.filter (fun p => p.1.all (fun i => i < b))

private lemma lookup_filter_fst (P : GacsDayNode → Bool) (l : ClientMove) (y : GacsDayNode) :
    (l.filter (fun p => P p.1)).lookup y = if P y then l.lookup y else none := by
  induction l with
  | nil => simp
  | cons a t ih =>
    obtain ⟨k, q⟩ := a
    by_cases hk : P k
    · simp only [List.filter_cons, hk, if_true, List.lookup]
      by_cases hy : y = k
      · subst hy; simp [hk]
      · have hyk : (y == k) = false := by simpa using hy
        simp [hyk, ih]
    · have hk' : P k = false := by simpa using hk
      simp only [List.filter_cons, hk', Bool.false_eq_true, if_false]
      rw [ih]
      by_cases hy : y = k
      · subst hy; simp [hk']
      · have hyk : (y == k) = false := by simpa using hy
        simp [List.lookup, hyk]

/-- The truncated move keeps the requests at nodes with entries below `b` and zeroes the rest. -/
lemma getReq_truncMove (b : ℕ) (req : ClientMove) (y : GacsDayNode) :
    getReq (truncMove b req) y = if y.all (fun i => i < b) then getReq req y else 0 := by
  unfold getReq truncMove
  rw [lookup_filter_fst (fun k => k.all (fun i => decide (i < b)))]
  by_cases hy : y.all (fun i => decide (i < b))
  · simp [hy]
  · simp [hy]

/-- Truncating to the first `b` children preserves request coherence. -/
lemma requestCoherent_truncMove (b d : ℕ) (req : ClientMove)
    (h : requestCoherent b d req) : requestCoherent b d (truncMove b req) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [getReq_truncMove]
    split
    · exact h1 x
    · exact le_refl 0
  · rw [getReq_truncMove]
    simpa using h2
  · intro x
    rw [getReq_truncMove]
    by_cases hx : x.all (fun i => decide (i < b))
    · simp only [hx, if_true]
      refine le_trans (le_of_eq ?_) (h3 x)
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [getReq_truncMove]
      have hxc : ((x ++ [c.val]).all (fun i => decide (i < b))) = true := by
        simp [List.all_append, hx, c.isLt]
      simp [hxc]
    · simp only [hx, Bool.false_eq_true, if_false]
      have hz : ∀ c : Fin b, getReq (truncMove b req) (x ++ [c.val]) = 0 := by
        intro c
        rw [getReq_truncMove]
        have hxc : ((x ++ [c.val]).all (fun i => decide (i < b))) = false := by
          simp only [List.all_append, Bool.and_eq_false_iff]
          left
          simpa using hx
        simp [hxc]
      simp [hz]

/-- The truncated strategy.  It is built on top of `replayStrategy` rather than
directly on `σ`: a strategy that only saw the *truncated* record of its own past
moves could react to that record, so `playClient (fun hist => truncMove b (σ hist))`
need not be the truncation of `playClient σ`.  Replaying `σ` against the server
history makes the client history irrelevant and restores the identity
`playClient_truncStrategy`. -/
def truncStrategy (b : ℕ) (σ : ClientStrategy) : ClientStrategy :=
  fun hist => truncMove b (replayStrategy σ hist)

/-- The truncated strategy plays the truncation of the move the original strategy plays. -/
lemma playClient_truncStrategy (b : ℕ) (σ : ClientStrategy) (sms : ℕ → ServerMove) (t : ℕ) :
    playClient (truncStrategy b σ) sms t = truncMove b (playClient σ sms t) := by
  cases t with
  | zero =>
    rw [playClient, playClient]
    change truncMove b (replayStrategy σ ([], [])) = _
    rw [replayStrategy]
    simp [selfPlay, selfPlayAux]
  | succ t =>
    rw [playClient]
    change truncMove b (replayStrategy σ (_, List.ofFn fun i : Fin (t + 1) => sms i.val)) = _
    rw [replayStrategy]
    dsimp only
    rw [selfPlay_ofFn, playClient]

/-- The truncated strategy only requests inside the first `b` children. -/
lemma rangeSupported_truncStrategy (b : ℕ) (σ : ClientStrategy) :
    RangeSupported b (truncStrategy b σ) := by
  intro hist x i hi
  change getReq (truncMove b (replayStrategy σ hist)) (x ++ [i]) = 0
  rw [getReq_truncMove]
  have hxi : ((x ++ [i]).all (fun j => decide (j < b))) = false := by
    simp only [List.all_append, Bool.and_eq_false_iff]
    right
    simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not, Nat.not_lt]
    exact hi
  simp [hxi]

/-- Truncating to the first `b` children preserves winning by unserved requests. -/
lemma isWinningStrategyUnserved_truncStrategy (h b d : ℕ) (σ : ClientStrategy)
    (hwin : IsWinningStrategyUnserved (h := h) (b := b) d σ) :
    IsWinningStrategyUnserved (h := h) (b := b) d (truncStrategy b σ) := by
  intro sms hsms
  obtain ⟨⟨hcoh, hmono⟩, hw⟩ := hwin sms hsms
  refine ⟨⟨fun t => ?_, fun t x => ?_⟩, ?_⟩
  · rw [playClient_truncStrategy]
    exact requestCoherent_truncMove b d _ (hcoh t)
  · rw [playClient_truncStrategy, playClient_truncStrategy, getReq_truncMove, getReq_truncMove]
    by_cases hx : x.all (fun i => decide (i < b))
    · simp only [hx, if_true]; exact hmono t x
    · simp only [hx, Bool.false_eq_true, if_false]
      exact le_refl 0
  · obtain ⟨T, x, hlen, hin, hfail⟩ := hw
    refine ⟨T, x, hlen, hin, fun t => ?_⟩
    rw [playClient_truncStrategy, getReq_truncMove]
    have hx : (x.all (fun i => decide (i < b))) = true := by
      simp only [List.all_eq_true, decide_eq_true_eq]
      exact hin
    rw [if_pos hx]
    exact hfail t

private lemma primrec_natLtPred (b : ℕ) : Primrec (fun i : ℕ => decide (i < b)) := by
  have h : PrimrecPred (fun i : ℕ => i < b) :=
    Primrec.nat_lt.comp Primrec.id (Primrec.const b)
  obtain ⟨_, h⟩ := h
  exact h.of_eq (fun i => by simp)

/-- Truncating a move to the first `b` children is primitive recursive. -/
lemma primrec_truncMove (b : ℕ) : Primrec (truncMove b) :=
  Primrec.list_filter Primrec.id
    (((Primrec.list_all (primrec_natLtPred b)).comp
      (Primrec.fst.comp Primrec.snd)) : Primrec (fun w : ClientMove × (GacsDayNode × ℚ) =>
        w.2.1.all (fun i => decide (i < b)))).to₂

/-- Truncating a computable family of strategies to the binary tree keeps it computable. -/
lemma computable₂_truncStrategy {σ : ℕ → ClientStrategy} (hcomp : Computable₂ σ) :
    Computable₂ (fun d => truncStrategy 2 (σ d)) :=
  (primrec_truncMove 2).to_comp.comp (computable₂_replayStrategy hcomp)

end Kolmogorov
