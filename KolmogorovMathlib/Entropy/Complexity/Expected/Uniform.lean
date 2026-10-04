import KolmogorovMathlib.Entropy.Complexity.Expected.Basic

/-!
# The expected complexity of an i.i.d. word: the uniform version

SUV Problem 237, p. 228.

When the rational distribution `p` is given in the condition together with `N`
(`lengthDistCode`), the bounds of Theorem 147 hold with a constant that does not depend on `p`
(`mul_entropyDist_le_expect_KP_lengthDist`, `exists_expect_KP_lengthDist_le`).  The upper bound
uses one Shannon code, computed uniformly from `N` and `p`, whose decompressor reads the
distribution from the condition.
-/

namespace Kolmogorov

open Finset

open scoped ENNReal

/-! ### The uniform version -/

/-- The condition of the uniform version of Theorem 147: the length `N` together with the
rational distribution `p`, packed into one bit string.  SUV Problem 237, p. 228. -/
def lengthDistCode {A : Type*} [Fintype A] [DecidableEq A] [Encodable A] (N : ℕ) (p : A → ℚ) :
    BitString :=
  pairCode (natCode N) (natCode (Encodable.encode p))

/-- **The uniform lower bound of Theorem 147.**  With the distribution added to the condition, the
expected value of `K(ξ^N | N, p₁, …, p_k)` is still at least `N H(ξ)`; the lower bound holds for
every prefix code and is therefore unaffected by the extra condition.  The complexity is the
prefix complexity of the block encoding `finWordBits` of the word.

**Stronger than the printed statement**: the setup of p. 228 fixes *positive* rational `p_i`,
while the lower bound holds for every rational distribution, zero values included.
SUV Problem 237, p. 228. -/
theorem mul_entropyDist_le_expect_KP_lengthDist (A : Type*) [Fintype A] [DecidableEq A]
    [Encodable A] (p : A → ℚ) (μ : FiniteProbSpace A) (hμ : ∀ a, μ.prob a = (p a : ℝ))
    (U : Map) (hU : IsOptimalPrefixConditional U) (N : ℕ) :
    (N : ℝ) * entropyDist μ.prob ≤
      (μ.power N).expect fun w =>
        ((KP U (finWordBits A w) (lengthDistCode N p)).toNat : ℝ) := by
  have _ := hμ
  have _ := p
  rw [← entropyDist_prod_eq μ.prob_nonneg μ.sum_prob N]
  exact entropyDist_le_expect_of_kraft (μ.power N)
    (fun w => (KP U (finWordBits A w) (lengthDistCode N p)).toNat)
    (sum_inv_pow_KP_toNat_le_one A U hU N (lengthDistCode N p))

private theorem exists_shannon_prefix_code_of_pos {Ω : Type*} [Fintype Ω]
    (ν : FiniteProbSpace Ω) (hpos : ∀ ω, 0 < ν.prob ω) :
    ∃ d : Code Ω, d.IsPrefixFree ∧ d.avgLength ν.prob ≤ entropyDist ν.prob + 1 := by
  classical
  by_cases htwo : ∃ x y : Ω, x ≠ y ∧ 0 < ν.prob x ∧ 0 < ν.prob y
  · obtain ⟨d, hd, havg⟩ :=
      exists_isPrefixFree_avgLength_lt_entropyDist_add_one ν.prob_nonneg ν.sum_prob htwo
    exact ⟨d, hd, havg.le⟩
  · let d : Code Ω := fun _ => [false]
    have hd : d.IsPrefixFree := by
      refine ⟨fun _ => by simp [d], ?_⟩
      intro x y hxy
      exact (htwo ⟨x, y, hxy, hpos x, hpos y⟩).elim
    have hone : ∀ x, ν.prob x = 1 := by
      intro x
      rw [← ν.sum_prob]
      exact (Finset.sum_eq_single x (fun y _ hy =>
        (htwo ⟨x, y, Ne.symm hy, hpos x, hpos y⟩).elim)
        (fun hx => (hx (Finset.mem_univ x)).elim)).symm
    have hcard : Fintype.card Ω ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro x y
      by_contra hxy
      exact htwo ⟨x, y, hxy, hpos x, hpos y⟩
    refine ⟨d, hd, ?_⟩
    simp [Code.avgLength, entropyDist, hone, d, negMulLog2, hcard]

private def distEntryNum (c : ℕ) : ℕ := c.unpair.2.unpair.1 / 2
private def distEntryDen (c : ℕ) : ℕ := c.unpair.2.unpair.2

private def fracSum (L : List ℕ) : ℕ × ℕ :=
  L.foldr (fun c s => (distEntryNum c * s.2 + s.1 * distEntryDen c, distEntryDen c * s.2)) (0, 1)

private def wordNum (L idx : List ℕ) : ℕ := (idx.map fun i => distEntryNum (L.getD i 0)).prod
private def wordDen (L idx : List ℕ) : ℕ := (idx.map fun i => distEntryDen (L.getD i 0)).prod

private def shannonLen (X Y : ℕ) : ℕ :=
  max 1 ((List.range (X + 1)).findIdx fun l => decide (X ≤ 2 ^ l * Y))

private def shannonLenOf (L idx : List ℕ) : ℕ :=
  shannonLen ((fracSum L).1 ^ idx.length * wordDen L idx)
    (wordNum L idx * (fracSum L).2 ^ idx.length)

private def letterTable (A : Type*) [Fintype A] [Encodable A] : List BitString :=
  List.ofFn fun i : Fin (Fintype.card A) => alphabetCode A (Encodable.fintypeEquivFin.symm i)

private def idxBits (A : Type*) [Fintype A] [Encodable A] (idx : List ℕ) : BitString :=
  (idx.map fun i => (letterTable A).getD i []).flatten

private def shannonOk (A : Type*) [Fintype A] [Encodable A] (ctx : BitString) (e : ℕ)
    (L idx : List ℕ) : Bool :=
  decide (ctx = pairCode (natCode idx.length) (natCode e)) &&
    (decide (L.length = Fintype.card A) &&
      (decide (0 < wordNum L idx) && (decide (0 < (fracSum L).1) && decide (0 < (fracSum L).2))))

private def shannonReq (A : Type*) [Fintype A] [Encodable A] (ctx : BitString) (n : ℕ) :
    Option (BitString × ℕ) :=
  (Encodable.decode₂ (List ℕ) n.unpair.1).bind fun L =>
    (Encodable.decode₂ (List ℕ) n.unpair.2).bind fun idx =>
      bif shannonOk A ctx n.unpair.1 L idx then some (idxBits A idx, shannonLenOf L idx)
      else none

private theorem primrec_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem primrec_distEntryNum : Primrec distEntryNum :=
  Primrec.nat_div.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.const 2)

private theorem primrec_distEntryDen : Primrec distEntryDen :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem primrec_fracSum : Primrec fracSum := by
  unfold fracSum
  refine Primrec.list_foldr (h := fun _ (p : ℕ × ℕ × ℕ) =>
    (distEntryNum p.1 * p.2.2 + p.2.1 * distEntryDen p.1, distEntryDen p.1 * p.2.2))
    Primrec.id (Primrec.const _) ?_
  refine Primrec.pair ?_ ?_
  · exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (primrec_distEntryNum.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (primrec_distEntryDen.comp (Primrec.fst.comp Primrec.snd)))
  · exact Primrec.nat_mul.comp (primrec_distEntryDen.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem primrec_list_prod_map {f : ℕ → ℕ} (hf : Primrec f) :
    Primrec₂ fun (L idx : List ℕ) => (idx.map fun i => f (L.getD i 0)).prod := by
  have : (fun (L idx : List ℕ) => (idx.map fun i => f (L.getD i 0)).prod) =
      fun L idx => idx.foldr (fun i s => f (L.getD i 0) * s) 1 := by
    funext L idx
    induction idx with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.prod_cons, ih]; rfl
  rw [this]
  exact Primrec.list_foldr (h := fun (x : List ℕ × List ℕ) (p : ℕ × ℕ) =>
      f (x.1.getD p.1 0) * p.2) Primrec.snd (Primrec.const 1)
    (Primrec.nat_mul.comp (hf.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))

private theorem primrec_shannonLen : Primrec₂ shannonLen := by
  unfold shannonLen
  refine Primrec.nat_max.comp (Primrec.const 1) ?_
  refine Primrec.list_findIdx
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) ?_
  exact (PrimrecRel.decide Primrec.nat_le).comp (Primrec.fst.comp Primrec.fst)
    (Primrec.nat_mul.comp (primrec_nat_pow.comp (Primrec.const 2) Primrec.snd)
      (Primrec.snd.comp Primrec.fst))

private theorem primrec_shannonLenOf : Primrec₂ shannonLenOf := by
  unfold shannonLenOf
  have hs := primrec_fracSum.comp (Primrec.fst (α := List ℕ) (β := List ℕ))
  have hl := Primrec.list_length.comp (Primrec.snd (α := List ℕ) (β := List ℕ))
  exact primrec_shannonLen.comp
    (Primrec.nat_mul.comp (primrec_nat_pow.comp (Primrec.fst.comp hs) hl)
      (primrec_list_prod_map primrec_distEntryDen))
    (Primrec.nat_mul.comp (primrec_list_prod_map primrec_distEntryNum)
      (primrec_nat_pow.comp (Primrec.snd.comp hs) hl))

private theorem primrec_idxBits (A : Type*) [Fintype A] [Encodable A] :
    Primrec (idxBits A) := by
  unfold idxBits
  exact Primrec.list_flatten.comp (Primrec.list_map Primrec.id
    ((Primrec.list_getD []).comp (Primrec.const _) Primrec.snd))

private theorem computable_shannonOk (A : Type*) [Fintype A] [Encodable A] :
    Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      shannonOk A x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hL : Primrec fun x : BitString × ℕ × List ℕ × List ℕ => x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hI : Primrec fun x : BitString × ℕ × List ℕ × List ℕ => x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec fun x : BitString × ℕ × List ℕ × List ℕ => fracSum x.2.2.1 :=
    primrec_fracSum.comp hL
  have hand : Computable₂ fun a b : Bool => a && b :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp
  have hp2 : Computable₂ pairCode := pairCode_computable
  have hn1 : Computable fun x : BitString × ℕ × List ℕ × List ℕ => x.2.2.2.length :=
    (Primrec.list_length.comp hI).to_comp
  have hn2 : Computable fun x : BitString × ℕ × List ℕ × List ℕ => x.2.1 :=
    Computable.fst.comp Computable.snd
  have hpc : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      pairCode (natCode x.2.2.2.length) (natCode x.2.1) :=
    hp2.comp (natCode_computable.comp hn1) (natCode_computable.comp hn2)
  have heq : Computable₂ fun a b : BitString => decide (a = b) :=
    (PrimrecRel.decide Primrec.eq).to_comp
  have hctx : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      decide (x.1 = pairCode (natCode x.2.2.2.length) (natCode x.2.1)) :=
    heq.comp Computable.fst hpc
  have hlen : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      decide (x.2.2.1.length = Fintype.card A) :=
    ((PrimrecRel.decide Primrec.eq).comp (Primrec.list_length.comp hL)
      (Primrec.const _)).to_comp
  have hnum : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      decide (0 < wordNum x.2.2.1 x.2.2.2) :=
    ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0)
      ((primrec_list_prod_map primrec_distEntryNum).comp hL hI)).to_comp
  have hs1 : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      decide (0 < (fracSum x.2.2.1).1) :=
    ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0)
      (Primrec.fst.comp hs)).to_comp
  have hs2 : Computable fun x : BitString × ℕ × List ℕ × List ℕ =>
      decide (0 < (fracSum x.2.2.1).2) :=
    ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.const 0)
      (Primrec.snd.comp hs)).to_comp
  exact hand.comp hctx (hand.comp hlen (hand.comp hnum (hand.comp hs1 hs2)))

private theorem computable_shannonReq (A : Type*) [Fintype A] [Encodable A] :
    Computable fun p : BitString × ℕ => shannonReq A p.1 p.2 := by
  have h1 : Computable fun p : BitString × ℕ => p.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have h2 : Computable fun p : BitString × ℕ => p.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have htup : Computable fun x : ((BitString × ℕ) × List ℕ) × List ℕ =>
      (x.1.1.1, x.1.1.2.unpair.1, x.1.2, x.2) :=
    Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (h1.comp (Computable.fst.comp Computable.fst))
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
  have hok : Computable fun x : ((BitString × ℕ) × List ℕ) × List ℕ =>
      shannonOk A x.1.1.1 x.1.1.2.unpair.1 x.1.2 x.2 := by
    have h := (computable_shannonOk A).comp htup
    exact h
  have hbits : Computable fun x : ((BitString × ℕ) × List ℕ) × List ℕ => idxBits A x.2 :=
    (primrec_idxBits A).to_comp.comp Computable.snd
  have hlen : Computable fun x : ((BitString × ℕ) × List ℕ) × List ℕ =>
      shannonLenOf x.1.2 x.2 :=
    primrec_shannonLenOf.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd
  have hsome : Computable fun x : ((BitString × ℕ) × List ℕ) × List ℕ =>
      (some (idxBits A x.2, shannonLenOf x.1.2 x.2) : Option (BitString × ℕ)) :=
    Computable.option_some.comp (hbits.pair hlen)
  have hin : Computable₂ fun (x : (BitString × ℕ) × List ℕ) (idx : List ℕ) =>
      bif shannonOk A x.1.1 x.1.2.unpair.1 x.2 idx then
        (some (idxBits A idx, shannonLenOf x.2 idx) : Option (BitString × ℕ))
      else none :=
    Computable.cond hok hsome (Computable.const none)
  have hdec2 : Computable fun x : (BitString × ℕ) × List ℕ =>
      Encodable.decode₂ (List ℕ) x.1.2.unpair.2 :=
    Primrec.decode₂.to_comp.comp (h2.comp Computable.fst)
  have hmid : Computable₂ fun (p : BitString × ℕ) (L : List ℕ) =>
      (Encodable.decode₂ (List ℕ) p.2.unpair.2).bind fun idx =>
        bif shannonOk A p.1 p.2.unpair.1 L idx then
          (some (idxBits A idx, shannonLenOf L idx) : Option (BitString × ℕ))
        else none :=
    Computable.option_bind hdec2 hin
  exact Computable.option_bind (Primrec.decode₂.to_comp.comp h1) hmid



private theorem one_le_shannonLen (X Y : ℕ) : 1 ≤ shannonLen X Y := le_max_left _ _

private theorem le_two_pow_shannonLen_mul {X Y : ℕ} (hY : 0 < Y) :
    X ≤ 2 ^ shannonLen X Y * Y := by
  unfold shannonLen
  have hex : ∃ x ∈ List.range (X + 1), decide (X ≤ 2 ^ x * Y) = true :=
    ⟨X, List.mem_range.2 (Nat.lt_succ_self X), by
      rw [decide_eq_true_eq]
      calc X ≤ 2 ^ X := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ X * Y := Nat.le_mul_of_pos_right _ hY⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hp := List.findIdx_getElem (w := hlt)
  rw [List.getElem_range, decide_eq_true_eq] at hp
  exact hp.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))

private theorem shannonLen_le {X Y l : ℕ} (hl : 1 ≤ l) (h : X ≤ 2 ^ l * Y) :
    shannonLen X Y ≤ l := by
  unfold shannonLen
  refine max_le hl ?_
  by_contra hcon
  push Not at hcon
  have hlen : l < (List.range (X + 1)).length :=
    lt_of_lt_of_le hcon (List.findIdx_le_length)
  have hp := List.not_of_lt_findIdx hcon
  rw [List.getElem_range, decide_eq_false_iff_not] at hp
  exact hp h

private theorem fracSum_cons (c : ℕ) (L : List ℕ) :
    fracSum (c :: L) = (distEntryNum c * (fracSum L).2 + (fracSum L).1 * distEntryDen c,
      distEntryDen c * (fracSum L).2) := rfl

private theorem fracSum_snd (L : List ℕ) : (fracSum L).2 = (L.map distEntryDen).prod := by
  induction L with
  | nil => rfl
  | cons c L ih => rw [fracSum_cons, List.map_cons, List.prod_cons, ih]

private theorem fracSum_div (L : List ℕ) (h : (fracSum L).2 ≠ 0) :
    ((fracSum L).1 : ℝ) / (fracSum L).2 =
      (L.map fun c => (distEntryNum c : ℝ) / distEntryDen c).sum := by
  induction L with
  | nil => simp [fracSum]
  | cons c L ih =>
    rw [fracSum_cons] at h ⊢
    have hd : distEntryDen c ≠ 0 := left_ne_zero_of_mul h
    have hy : (fracSum L).2 ≠ 0 := right_ne_zero_of_mul h
    rw [List.map_cons, List.sum_cons, ← ih hy]
    push_cast
    field_simp

private theorem wordNum_ofFn (L : List ℕ) {N : ℕ} (u : Fin N → ℕ) :
    wordNum L (List.ofFn u) = ∏ j, distEntryNum (L.getD (u j) 0) := by
  rw [wordNum, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem wordDen_ofFn (L : List ℕ) {N : ℕ} (u : Fin N → ℕ) :
    wordDen L (List.ofFn u) = ∏ j, distEntryDen (L.getD (u j) 0) := by
  rw [wordDen, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem lt_length_of_wordNum_pos {L idx : List ℕ} (h : 0 < wordNum L idx) :
    ∀ i ∈ idx, i < L.length := by
  intro i hi
  by_contra hlt
  push Not at hlt
  have h0 : distEntryNum (L.getD i 0) = 0 := by
    rw [List.getD_eq_default _ _ hlt]
    rfl
  have hmem : 0 ∈ idx.map fun i => distEntryNum (L.getD i 0) :=
    List.mem_map.2 ⟨i, hi, h0⟩
  exact h.ne' (List.prod_eq_zero hmem)

private theorem distEntryDen_pos {L : List ℕ} (h : 0 < (fracSum L).2) :
    ∀ c ∈ L, 0 < distEntryDen c := by
  intro c hc
  rw [fracSum_snd] at h
  refine Nat.pos_of_ne_zero fun h0 => h.ne' (List.prod_eq_zero ?_)
  exact List.mem_map.2 ⟨c, hc, h0⟩

private theorem wordDen_pos {L idx : List ℕ} (hs : 0 < (fracSum L).2)
    (hnum : 0 < wordNum L idx) : 0 < wordDen L idx := by
  refine List.prod_pos fun d hd => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
  have hlt := lt_length_of_wordNum_pos hnum i hi
  rw [List.getD_eq_getElem _ _ hlt]
  exact distEntryDen_pos hs _ (List.getElem_mem hlt)

private theorem inv_two_pow_shannonLenOf_le {L idx : List ℕ} (hs1 : 0 < (fracSum L).1)
    (hs2 : 0 < (fracSum L).2) (hnum : 0 < wordNum L idx) :
    (2 : ℝ)⁻¹ ^ shannonLenOf L idx ≤
      ((wordNum L idx : ℝ) / wordDen L idx) /
        (((fracSum L).1 : ℝ) / (fracSum L).2) ^ idx.length := by
  have hden := wordDen_pos hs2 hnum
  have hY : 0 < wordNum L idx * (fracSum L).2 ^ idx.length := by positivity
  have h := le_two_pow_shannonLen_mul
    (X := (fracSum L).1 ^ idx.length * wordDen L idx) hY
  have hXr : (((fracSum L).1 : ℝ) ^ idx.length * wordDen L idx) ≤
      2 ^ shannonLenOf L idx * ((wordNum L idx : ℝ) * (fracSum L).2 ^ idx.length) := by
    exact_mod_cast h
  have hX : (0 : ℝ) < ((fracSum L).1 : ℝ) ^ idx.length * wordDen L idx := by positivity
  have heq : ((wordNum L idx : ℝ) / wordDen L idx) /
      (((fracSum L).1 : ℝ) / (fracSum L).2) ^ idx.length =
      ((wordNum L idx : ℝ) * (fracSum L).2 ^ idx.length) /
        (((fracSum L).1 : ℝ) ^ idx.length * wordDen L idx) := by
    rw [div_pow]
    field_simp
  rw [heq, le_div_iff₀ hX, inv_pow, inv_mul_le_iff₀ (by positivity)]
  exact hXr

private noncomputable def entryVal (L : List ℕ) (i : ℕ) : ℝ :=
  (distEntryNum (L.getD i 0) : ℝ) / distEntryDen (L.getD i 0)

private theorem entryVal_nonneg (L : List ℕ) (i : ℕ) : 0 ≤ entryVal L i := by
  unfold entryVal
  positivity

private theorem fracSum_div_eq_sum (L : List ℕ) (h : (fracSum L).2 ≠ 0) :
    ((fracSum L).1 : ℝ) / (fracSum L).2 = ∑ i : Fin L.length, entryVal L i := by
  rw [fracSum_div L h]
  conv_lhs => rw [← List.ofFn_getElem (xs := L)]
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, entryVal, List.getD_eq_getElem _ _ i.isLt]

private theorem wordNum_div_wordDen_ofFn (L : List ℕ) {N : ℕ} (u : Fin N → ℕ) :
    (wordNum L (List.ofFn u) : ℝ) / wordDen L (List.ofFn u) = ∏ j, entryVal L (u j) := by
  rw [wordNum_ofFn, wordDen_ofFn]
  push_cast
  rw [← Finset.prod_div_distrib]
  rfl

private theorem shannonOk_eq_true {A : Type*} [Fintype A] [Encodable A] {ctx : BitString}
    {e : ℕ} {L idx : List ℕ} :
    shannonOk A ctx e L idx = true ↔
      ctx = pairCode (natCode idx.length) (natCode e) ∧ L.length = Fintype.card A ∧
        0 < wordNum L idx ∧ 0 < (fracSum L).1 ∧ 0 < (fracSum L).2 := by
  simp [shannonOk]

private theorem shannonReq_eq_some {A : Type*} [Fintype A] [Encodable A] {ctx : BitString}
    {n : ℕ} {o : BitString} {l : ℕ} :
    shannonReq A ctx n = some (o, l) ↔ ∃ L idx,
      Encodable.decode₂ (List ℕ) n.unpair.1 = some L ∧
      Encodable.decode₂ (List ℕ) n.unpair.2 = some idx ∧
      shannonOk A ctx n.unpair.1 L idx = true ∧ idxBits A idx = o ∧ shannonLenOf L idx = l := by
  unfold shannonReq
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨L, h1, idx, h2, h3⟩
    cases hok : shannonOk A ctx n.unpair.1 L idx
    · simp [hok] at h3
    · simp only [hok, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h3
      exact ⟨L, idx, h1, h2, hok, h3⟩
  · rintro ⟨L, idx, h1, h2, h3, h4, h5⟩
    exact ⟨L, h1, idx, h2, by simp [h3, h4, h5]⟩

open scoped ENNReal in
private theorem shannonReq_kraft (A : Type*) [Fintype A] [Encodable A] (ctx : BitString) :
    (∑' n, match shannonReq A ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
      | none => 0) ≤ 1 := by
  classical
  set W : ℕ → ℝ≥0∞ := fun n => match shannonReq A ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
      | none => 0 with hWdef
  have hW : ∀ n, W n ≠ 0 → ∃ L idx, Encodable.decode₂ (List ℕ) n.unpair.1 = some L ∧
      Encodable.decode₂ (List ℕ) n.unpair.2 = some idx ∧
      shannonOk A ctx n.unpair.1 L idx = true ∧ W n = 2⁻¹ ^ shannonLenOf L idx := by
    intro n hn
    rcases hr : shannonReq A ctx n with _ | ⟨o, l⟩
    · simp [W, hr] at hn
    · obtain ⟨L, idx, h1, h2, h3, -, h5⟩ := shannonReq_eq_some.1 hr
      exact ⟨L, idx, h1, h2, h3, by simp [W, hr, h5]⟩
  by_cases hex : ∃ n, W n ≠ 0
  swap
  · push Not at hex
    have hW0 : W = 0 := funext hex
    change ∑' n, W n ≤ 1
    rw [hW0]
    simp
  obtain ⟨n₀, hn₀⟩ := hex
  obtain ⟨L, idx₀, hL, -, hok₀, -⟩ := hW n₀ hn₀
  set e := n₀.unpair.1 with he
  set N := idx₀.length with hN
  have hctx : ctx = pairCode (natCode N) (natCode e) := (shannonOk_eq_true.1 hok₀).1
  have hsupp : ∀ n, W n ≠ 0 → ∃ idx, n.unpair.1 = e ∧
      Encodable.decode₂ (List ℕ) n.unpair.2 = some idx ∧ idx.length = N ∧
      shannonOk A ctx e L idx = true ∧ W n = 2⁻¹ ^ shannonLenOf L idx := by
    intro n hn
    obtain ⟨L', idx, h1, h2, h3, h4⟩ := hW n hn
    have hc := (shannonOk_eq_true.1 h3).1
    rw [hctx] at hc
    have hp := @pairCode_injective (natCode N, natCode e)
      (natCode idx.length, natCode n.unpair.1) hc
    simp only [Prod.mk.injEq] at hp
    have hNe := natCode_injective hp.1
    have hee := natCode_injective hp.2
    rw [hee, h1] at hL
    cases hL
    rw [← hee] at h3
    exact ⟨idx, hee.symm, h2, hNe.symm, h3, h4⟩
  set k := L.length with hk
  let ι : (Fin N → Fin k) → ℕ := fun u =>
    Nat.pair e (Encodable.encode (List.ofFn fun j => (u j : ℕ)))
  have hinj : Set.InjOn ι (Finset.univ : Finset (Fin N → Fin k)) := by
    intro u _ u' _ huu
    have h := congrArg (fun n => (Nat.unpair n).2) huu
    simp only [ι, Nat.unpair_pair] at h
    have h' := List.ofFn_injective (Encodable.encode_injective h)
    funext j
    exact Fin.ext (congrFun h' j)
  have hzero : ∀ n ∉ Finset.univ.image ι, W n = 0 := by
    intro n hn
    by_contra hne
    obtain ⟨idx, hne1, hdec, hlen, hok, -⟩ := hsupp n hne
    have hlt := lt_length_of_wordNum_pos (shannonOk_eq_true.1 hok).2.2.1
    let u : Fin N → Fin k := fun j =>
      ⟨idx[(j : ℕ)]'(by omega), hlt _ (List.getElem_mem _)⟩
    have hidx : (List.ofFn fun j => (u j : ℕ)) = idx := by
      refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
      simp [u]
    apply hn
    refine Finset.mem_image.2 ⟨u, Finset.mem_univ _, ?_⟩
    simp only [ι, hidx, Encodable.mem_decode₂.1 hdec, ← hne1, Nat.pair_unpair]
  change ∑' n, W n ≤ 1
  rw [tsum_eq_sum hzero, Finset.sum_image hinj]
  set S : ℝ := ∑ i : Fin k, entryVal L i with hS
  have hbound : ∀ u : Fin N → Fin k,
      W (ι u) ≤ ENNReal.ofReal ((∏ j, entryVal L (u j)) / S ^ N) := by
    intro u
    by_cases h0 : W (ι u) = 0
    · rw [h0]
      exact zero_le
    obtain ⟨idx, -, hdec, hlen, hok, hWu⟩ := hsupp (ι u) h0
    simp only [ι, Nat.unpair_pair, Encodable.decode₂_encode, Option.some.injEq] at hdec
    subst hdec
    obtain ⟨-, -, hnum, hs1, hs2⟩ := shannonOk_eq_true.1 hok
    have hreal := inv_two_pow_shannonLenOf_le hs1 hs2 hnum
    rw [wordNum_div_wordDen_ofFn, fracSum_div_eq_sum L hs2.ne', List.length_ofFn] at hreal
    rw [hWu]
    have hconv : (2 : ℝ≥0∞)⁻¹ ^ shannonLenOf L (List.ofFn fun j => (u j : ℕ)) =
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ shannonLenOf L (List.ofFn fun j => (u j : ℕ))) := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    rw [hconv]
    exact ENNReal.ofReal_le_ofReal hreal
  refine (Finset.sum_le_sum fun u _ => hbound u).trans ?_
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => entryVal_nonneg L i
  have hnn : ∀ u ∈ (Finset.univ : Finset (Fin N → Fin k)),
      0 ≤ (∏ j, entryVal L (u j)) / S ^ N := fun u _ =>
    div_nonneg (Finset.prod_nonneg fun j _ => entryVal_nonneg L _)
      (pow_nonneg hS0 N)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.sum_div]
  have hprod : ∑ u : Fin N → Fin k, ∏ j, entryVal L (u j) = S ^ N := by
    rw [hS, ← Fintype.prod_sum (fun (_ : Fin N) (i : Fin k) => entryVal L i),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  exact ENNReal.ofReal_le_one.2 (div_self_le_one _)

private theorem shannonLenOf_le_neg_logb_add_one {L idx : List ℕ} (hs1 : 0 < (fracSum L).1)
    (hs2 : 0 < (fracSum L).2) (hnum : 0 < wordNum L idx)
    (hS : ((fracSum L).1 : ℝ) / (fracSum L).2 = 1)
    (hQ : (wordNum L idx : ℝ) / wordDen L idx ≤ 1) :
    (shannonLenOf L idx : ℝ) ≤ -Real.logb 2 ((wordNum L idx : ℝ) / wordDen L idx) + 1 := by
  set Q : ℝ := (wordNum L idx : ℝ) / wordDen L idx with hQdef
  have hden := wordDen_pos hs2 hnum
  have hQpos : 0 < Q := by positivity
  have ht : 0 ≤ -Real.logb 2 Q := by
    linarith [Real.logb_nonpos (b := 2) (by norm_num) hQpos.le hQ]
  set c := ⌈-Real.logb 2 Q⌉₊ with hc
  have hc2 : (2 : ℝ)⁻¹ ^ c ≤ Q := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    calc (2 : ℝ) ^ (-(c : ℝ)) ≤ (2 : ℝ) ^ Real.logb 2 Q :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith [Nat.le_ceil (-Real.logb 2 Q)])
      _ = Q := Real.rpow_logb (by norm_num) (by norm_num) hQpos
  have hmax : (2 : ℝ)⁻¹ ^ max 1 c ≤ Q :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right 1 c)).trans hc2
  have hX : (0 : ℝ) < ((fracSum L).1 : ℝ) ^ idx.length * wordDen L idx := by positivity
  have hle : (fracSum L).1 ^ idx.length * wordDen L idx ≤
      2 ^ max 1 c * (wordNum L idx * (fracSum L).2 ^ idx.length) := by
    have hYX : ((wordNum L idx : ℝ) * (fracSum L).2 ^ idx.length) /
        (((fracSum L).1 : ℝ) ^ idx.length * wordDen L idx) = Q := by
      have h1 : ((fracSum L).1 : ℝ) = (fracSum L).2 := by
        have h2 : ((fracSum L).2 : ℝ) ≠ 0 := by positivity
        field_simp at hS
        exact hS
      rw [hQdef, h1]
      have h3 : ((fracSum L).2 : ℝ) ^ idx.length ≠ 0 := by positivity
      field_simp
    rw [← hYX, inv_pow, inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div,
      le_div_iff₀ hX, one_mul] at hmax
    exact_mod_cast (hmax.trans_eq (mul_comm _ _))
  have hl := shannonLen_le (le_max_left 1 c) hle
  calc (shannonLenOf L idx : ℝ) ≤ (max 1 c : ℕ) := by exact_mod_cast hl
    _ ≤ -Real.logb 2 Q + 1 := by
      rw [Nat.cast_max, Nat.cast_one]
      refine max_le (by linarith) (Nat.ceil_lt_add_one ht).le

private theorem encode_list_eq_encode_map {α : Type*} [Encodable α] (l : List α) :
    Encodable.encode l = Encodable.encode (l.map Encodable.encode) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change _ = Nat.succ (Nat.pair (Encodable.encode a) (Encodable.encode (l.map Encodable.encode)))
    rw [← ih]
    rfl

private theorem encode_finArrow_eq {β : Type*} [Encodable β] (n : ℕ) (f : Fin n → β) :
    @Encodable.encode (Fin n → β) Encodable.finArrow f = Encodable.encode (List.ofFn f) := by
  have h := @Encodable.encode_ofEquiv _ _ _ (Equiv.vectorEquivFin β n).symm f
  refine h.trans ?_
  change Encodable.encode ((Equiv.vectorEquivFin β n).symm f).val = _
  exact congrArg _ (List.Vector.toList_ofFn f)

private theorem encode_finPi_eq {β : Type*} [Encodable β] (n : ℕ) (f : Fin n → β) :
    @Encodable.encode (Fin n → β) (Encodable.finPi n (fun _ => β)) f =
      Encodable.encode (List.ofFn fun i => (⟨i, f i⟩ : Σ _ : Fin n, β)) := by
  have h := @Encodable.encode_ofEquiv _ _ (@Subtype.encodable _ _ Encodable.finArrow _)
    (Equiv.piEquivSubtypeSigma (Fin n) (fun _ => β)) f
  refine h.trans ?_
  refine (@Encodable.Subtype.encode_eq _ _ Encodable.finArrow _ _).trans ?_
  exact encode_finArrow_eq _ _

/-- The code list of a rational distribution: the entry of the `i`-th letter pairs `i` with the
code of its probability. -/
private def distCodeList {A : Type*} [Fintype A] [Encodable A] (p : A → ℚ) : List ℕ :=
  List.ofFn fun i : Fin (Fintype.card A) =>
    Nat.pair i (Encodable.encode (p (Encodable.fintypeEquivFin.symm i)))

private theorem encode_fun_eq_encode_distCodeList {A : Type*} [Fintype A] [Encodable A]
    (p : A → ℚ) : Encodable.encode p = Encodable.encode (distCodeList p) := by
  have h1 : Encodable.encode p = @Encodable.encode _ (Encodable.finPi _ (fun _ => ℚ))
      (fun i => p (Encodable.fintypeEquivFin.symm i)) :=
    Encodable.encode_ofEquiv (Equiv.arrowCongr Encodable.fintypeEquivFin (Equiv.refl _)) p
  rw [h1, encode_finPi_eq, encode_list_eq_encode_map, List.map_ofFn]
  rfl

private theorem encode_int_natCast (m : ℕ) : Encodable.encode (m : ℤ) = 2 * m := by
  rw [Encodable.encode_ofEquiv]
  rfl

private theorem distEntry_pair_encode {r : ℚ} (hr : 0 < r) (i : ℕ) :
    distEntryNum (Nat.pair i (Encodable.encode r)) = r.num.toNat ∧
      distEntryDen (Nat.pair i (Encodable.encode r)) = r.den := by
  have henc : Encodable.encode r = Nat.pair (Encodable.encode r.num) r.den := rfl
  have hnum : r.num = (r.num.toNat : ℤ) := (Int.toNat_of_nonneg (Rat.num_pos.2 hr).le).symm
  refine ⟨?_, ?_⟩
  · simp only [distEntryNum, henc, Nat.unpair_pair]
    rw [hnum, encode_int_natCast, Int.toNat_natCast]
    omega
  · simp only [distEntryDen, henc, Nat.unpair_pair]

private theorem entryVal_distCodeList {A : Type*} [Fintype A] [Encodable A] {p : A → ℚ}
    (hp : ∀ a, 0 < p a) (i : Fin (Fintype.card A)) :
    entryVal (distCodeList p) i = (p (Encodable.fintypeEquivFin.symm i) : ℝ) := by
  have hget : (distCodeList p).getD i 0 =
      Nat.pair i (Encodable.encode (p (Encodable.fintypeEquivFin.symm i))) := by
    rw [List.getD_eq_getElem _ _ (by simp [distCodeList])]
    simp [distCodeList]
  obtain ⟨h1, h2⟩ := distEntry_pair_encode (hp (Encodable.fintypeEquivFin.symm i)) i
  rw [entryVal, hget, h1, h2, Rat.cast_def]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.2 (hp _)).le

private theorem sum_entryVal_distCodeList {A : Type*} [Fintype A] [Encodable A] {p : A → ℚ}
    (hp : ∀ a, 0 < p a) (hsum : ∑ a, (p a : ℝ) = 1) :
    ∑ i : Fin (distCodeList p).length, entryVal (distCodeList p) i = 1 := by
  have hlen : (distCodeList p).length = Fintype.card A := by simp [distCodeList]
  rw [Fin.sum_univ_eq_sum_range (fun i => entryVal (distCodeList p) i), hlen,
    ← Fin.sum_univ_eq_sum_range (fun i => entryVal (distCodeList p) i)]
  simp only [entryVal_distCodeList hp]
  rw [← hsum]
  exact Equiv.sum_comp Encodable.fintypeEquivFin.symm (fun a => (p a : ℝ))

/-- The letters of a word, as their indices in the enumeration `Encodable.fintypeEquivFin`. -/
private def wordIdx {A : Type*} [Fintype A] [Encodable A] {N : ℕ} (w : Fin N → A) : List ℕ :=
  List.ofFn fun j => ((Encodable.fintypeEquivFin (w j) : Fin (Fintype.card A)) : ℕ)

private theorem idxBits_wordIdx {A : Type*} [Fintype A] [Encodable A] {N : ℕ}
    (w : Fin N → A) : idxBits A (wordIdx w) = finWordBits A w := by
  unfold idxBits wordIdx finWordBits wordBits Code.encodeWord
  rw [List.map_ofFn, List.map_ofFn]
  congr 2
  funext j
  simp [letterTable]

private theorem wordNum_div_wordDen_wordIdx {A : Type*} [Fintype A] [Encodable A]
    {p : A → ℚ} (hp : ∀ a, 0 < p a) {N : ℕ} (w : Fin N → A) :
    (wordNum (distCodeList p) (wordIdx w) : ℝ) / wordDen (distCodeList p) (wordIdx w) =
      ∏ j, (p (w j) : ℝ) := by
  rw [wordIdx, wordNum_div_wordDen_ofFn]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [entryVal_distCodeList hp, Equiv.symm_apply_apply]

private theorem fracSum_distCodeList {A : Type*} [Fintype A] [Encodable A] {p : A → ℚ}
    (hp : ∀ a, 0 < p a) (hsum : ∑ a, (p a : ℝ) = 1) :
    0 < (fracSum (distCodeList p)).1 ∧ 0 < (fracSum (distCodeList p)).2 ∧
      ((fracSum (distCodeList p)).1 : ℝ) / (fracSum (distCodeList p)).2 = 1 := by
  have hs2 : 0 < (fracSum (distCodeList p)).2 := by
    rw [fracSum_snd]
    refine List.prod_pos fun d hd => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    rw [(distEntry_pair_encode (hp _) _).2]
    exact Rat.den_pos _
  have hS := fracSum_div_eq_sum (distCodeList p) hs2.ne'
  rw [sum_entryVal_distCodeList hp hsum] at hS
  refine ⟨?_, hs2, hS⟩
  by_contra h0
  push Not at h0
  rw [Nat.le_zero.1 h0] at hS
  simp at hS

private theorem wordNum_wordIdx_pos {A : Type*} [Fintype A] [Encodable A] {p : A → ℚ}
    (hp : ∀ a, 0 < p a) {N : ℕ} (w : Fin N → A) :
    0 < wordNum (distCodeList p) (wordIdx w) := by
  rw [wordIdx, wordNum_ofFn]
  refine Finset.prod_pos fun j _ => ?_
  rw [List.getD_eq_getElem _ _ (by simp [distCodeList])]
  simp only [distCodeList, List.getElem_ofFn]
  rw [(distEntry_pair_encode (hp _) _).1]
  exact Int.lt_toNat.2 (Rat.num_pos.2 (hp _))

private theorem shannonReq_word {A : Type*} [Fintype A] [DecidableEq A] [Encodable A]
    {p : A → ℚ} (hp : ∀ a, 0 < p a) (hsum : ∑ a, (p a : ℝ) = 1) {N : ℕ} (w : Fin N → A) :
    shannonReq A (lengthDistCode N p)
        (Nat.pair (Encodable.encode p) (Encodable.encode (wordIdx w))) =
      some (finWordBits A w, shannonLenOf (distCodeList p) (wordIdx w)) := by
  obtain ⟨hs1, hs2, -⟩ := fracSum_distCodeList hp hsum
  refine shannonReq_eq_some.2 ⟨distCodeList p, wordIdx w, ?_, ?_, ?_, idxBits_wordIdx w, rfl⟩
  · rw [Nat.unpair_pair]
    exact Encodable.mem_decode₂.2 (encode_fun_eq_encode_distCodeList p).symm
  · rw [Nat.unpair_pair, Encodable.decode₂_encode]
  · rw [Nat.unpair_pair]
    refine shannonOk_eq_true.2 ⟨?_, by simp [distCodeList], wordNum_wordIdx_pos hp w, hs1, hs2⟩
    simp [lengthDistCode, wordIdx]

private theorem exists_uniform_shannon_code_decompressor (A : Type*) [Fintype A]
    [DecidableEq A] [Encodable A] :
    ∃ M : Map, IsPrefixDecompressor M ∧
      ∀ (p : A → ℚ) (μ : FiniteProbSpace A), (∀ a, μ.prob a = (p a : ℝ)) →
        (∀ a, 0 < p a) → ∀ N : ℕ,
          ∃ d : Code (Fin N → A), d.IsPrefixFree ∧
            d.avgLength (μ.power N).prob ≤ (N : ℝ) * entropyDist μ.prob + 1 ∧
            ∀ w, KP M (finWordBits A w) (lengthDistCode N p) ≤
              ((d w).length : ENat) := by
  obtain ⟨alloc, hallocc, hallocl, hallocp⟩ :=
    exists_online_prefixFree_family (shannonReq A) (computable_shannonReq A) (shannonReq_kraft A)
  obtain ⟨M, hM, hMout⟩ := construct_prefix_machine (shannonReq A) alloc
    (computable_shannonReq A) hallocc hallocl hallocp
  refine ⟨M, hM, fun p μ hμ hp N => ?_⟩
  have hsum : ∑ a, (p a : ℝ) = 1 := by
    simp_rw [← hμ]
    exact μ.sum_prob
  obtain ⟨hs1, hs2, hS⟩ := fracSum_distCodeList hp hsum
  let n : (Fin N → A) → ℕ := fun w =>
    Nat.pair (Encodable.encode p) (Encodable.encode (wordIdx w))
  have hreq := fun w : Fin N → A => shannonReq_word hp hsum w
  choose d hd hdlen using fun w => hallocl (lengthDistCode N p) (n w) _ _ (hreq w)
  have hQ : ∀ w, (wordNum (distCodeList p) (wordIdx w) : ℝ) /
      wordDen (distCodeList p) (wordIdx w) = (μ.power N).prob w := fun w => by
    rw [wordNum_div_wordDen_wordIdx hp]
    exact Finset.prod_congr rfl fun j _ => (hμ (w j)).symm
  have hlen : ∀ w, ((d w).length : ℝ) ≤ -Real.logb 2 ((μ.power N).prob w) + 1 := fun w => by
    have hQ1 : (μ.power N).prob w ≤ 1 := by
      rw [← (μ.power N).sum_prob]
      exact Finset.single_le_sum (fun v _ => (μ.power N).prob_nonneg v) (Finset.mem_univ w)
    rw [hdlen, ← hQ w]
    rw [← hQ w] at hQ1
    exact shannonLenOf_le_neg_logb_add_one hs1 hs2 (wordNum_wordIdx_pos hp w) hS hQ1
  refine ⟨d, ⟨fun w hnil => ?_, fun w w' hne => ?_⟩, ?_, fun w => ?_⟩
  · have h1 := hdlen w
    rw [hnil, List.length_nil] at h1
    exact absurd h1.symm (Nat.one_le_iff_ne_zero.1 (one_le_shannonLen _ _))
  · refine hallocp (lengthDistCode N p) (n w) (n w') (d w) (d w') (hd w) (hd w') fun h => hne ?_
    have h2 := congrArg (fun m => (Nat.unpair m).2) h
    simp only [n, Nat.unpair_pair] at h2
    have h3 := List.ofFn_injective (Encodable.encode_injective h2)
    funext j
    exact Encodable.fintypeEquivFin.injective (Fin.ext (congrFun h3 j))
  · unfold Code.avgLength
    calc ∑ w, (μ.power N).prob w * ((d w).length : ℝ)
        ≤ ∑ w, (μ.power N).prob w * (-Real.logb 2 ((μ.power N).prob w) + 1) :=
          Finset.sum_le_sum fun w _ =>
            mul_le_mul_of_nonneg_left (hlen w) ((μ.power N).prob_nonneg w)
      _ = entropyDist (μ.power N).prob + 1 := by
          simp_rw [mul_add, mul_one]
          rw [Finset.sum_add_distrib, (μ.power N).sum_prob, entropyDist]
          congr 1
          refine Finset.sum_congr rfl fun w _ => ?_
          unfold negMulLog2 Real.negMulLog Real.logb
          ring
      _ = (N : ℝ) * entropyDist μ.prob + 1 := by
          rw [← entropyDist_prod_eq μ.prob_nonneg μ.sum_prob N]
          rfl
  · have hprod : produces M (d w) (lengthDistCode N p) (finWordBits A w) := by
      rw [produces, hMout (lengthDistCode N p) (n w) _ _ (d w) (hreq w) (hd w)]
      exact Part.mem_some _
    exact KP_le_programLength_of_produces hprod

private theorem expect_KP_toNat_le_avgLength_of_code {Ω : Type*} [Fintype Ω]
    (ν : FiniteProbSpace Ω) (M : Map) (x y : Ω → BitString) (d : Code Ω)
    (hle : ∀ ω, KP M (x ω) (y ω) ≤ ((d ω).length : ENat)) :
    ν.expect (fun ω => ((KP M (x ω) (y ω)).toNat : ℝ)) ≤ d.avgLength ν.prob := by
  unfold FiniteProbSpace.expect Code.avgLength
  refine Finset.sum_le_sum fun ω _ => ?_
  apply mul_le_mul_of_nonneg_left _ (ν.prob_nonneg ω)
  change ((KP M (x ω) (y ω)).toNat : ℝ) ≤ ((d ω).length : ℝ)
  exact_mod_cast ENat.toNat_le_of_le_natCast (hle ω)

/-- **The uniform upper bound of Theorem 147.**  With the distribution added to the condition the
constant no longer depends on it: one constant serves all rational distributions `p` on the fixed
alphabet, because the code construction needs only `N` and `p`, which are both in the condition.
This is the exact statement the book leaves to the reader.  The complexity is the prefix
complexity of the block encoding `finWordBits` of the word.  SUV Problem 237, p. 228. -/
theorem exists_expect_KP_lengthDist_le (A : Type*) [Fintype A] [DecidableEq A] [Encodable A]
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : A → ℚ) (μ : FiniteProbSpace A), (∀ a, μ.prob a = (p a : ℝ)) →
      (∀ a, 0 < p a) → ∀ N : ℕ,
        ((μ.power N).expect fun w =>
            ((KP U (finWordBits A w) (lengthDistCode N p)).toNat : ℝ)) ≤
          (N : ℝ) * entropyDist μ.prob + c := by
  obtain ⟨M, hM, hMcode⟩ := exists_uniform_shannon_code_decompressor A
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c + 1, ?_⟩
  intro p μ hμ hpos N
  obtain ⟨d, _hd, havg, hcode⟩ := hMcode p μ hμ hpos N
  have hfinite : ∀ w, KP M (finWordBits A w) (lengthDistCode N p) ≠ ⊤ := fun w =>
    ne_top_of_le_natCast (hcode w)
  calc
    (μ.power N).expect (fun w =>
        ((KP U (finWordBits A w) (lengthDistCode N p)).toNat : ℝ)) ≤
        (μ.power N).expect (fun w =>
          ((KP M (finWordBits A w) (lengthDistCode N p)).toNat : ℝ)) + c := by
      apply expect_KP_toNat_le_add_of_invariance
      · exact hfinite
      · exact fun w => hc (finWordBits A w) (lengthDistCode N p)
    _ ≤ d.avgLength (μ.power N).prob + c := by
      gcongr
      exact expect_KP_toNat_le_avgLength_of_code (μ.power N) M
        (finWordBits A) (fun _ => lengthDistCode N p) d hcode
    _ ≤ ((N : ℝ) * entropyDist μ.prob + 1) + c := by gcongr
    _ = (N : ℝ) * entropyDist μ.prob + (c + 1 : ℕ) := by
      push_cast
      ring

end Kolmogorov
