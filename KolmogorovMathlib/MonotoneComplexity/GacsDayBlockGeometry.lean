import KolmogorovMathlib.MonotoneComplexity.GacsDayV2Multiplicity
import KolmogorovMathlib.MonotoneComplexity.GacsDayLadderTailConstruction

/-!
# Stage C1: block slot geometry and capacity

Blueprint Stage C (blocks restored, per the export-anchor audit): spend pass
`i` runs `2^{(7−i)L}` child roots per deficient outer root at the pass anchor
`a+3+(7−i)L`; the passes' spare-pair windows are laid out by cumulative
offsets.  This module provides the offsets and the capacity fact: at the
pinned gap the spare region of the frozen branching holds all eight windows.
-/

namespace Kolmogorov

/-- Cumulative spare-pair offset of spend pass `i`: the total block size of
the earlier passes. -/
def grayBlockSpendOffset (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => grayBlockSpendOffset L i + graySpendMult L i

/-- The spend offset of block `i + 1` exceeds that of block `i` by the spend multiplicity
`graySpendMult L i` of block `i`. -/
lemma grayBlockSpendOffset_succ (L i : ℕ) :
    grayBlockSpendOffset L (i + 1) =
      grayBlockSpendOffset L i + graySpendMult L i := rfl

/-- Each pass's window fits before the next one begins. -/
lemma grayBlockSpendOffset_mono {L i j : ℕ} (hij : i ≤ j) :
    grayBlockSpendOffset L i ≤ grayBlockSpendOffset L j := by
  induction j with
  | zero => simpa using Nat.le_zero.mp hij ▸ le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
      · have : i = j + 1 := by omega
        subst this
        exact le_rfl

/-- The total spend block population: `Σ_{i<8} 2^{(7−i)L} ≤ 8·2^{7L}`. -/
lemma grayBlockSpendOffset_total_le (L : ℕ) :
    grayBlockSpendOffset L 8 ≤ 8 * 2 ^ (7 * L) := by
  have hterm : ∀ i, i < 8 → graySpendMult L i ≤ 2 ^ (7 * L) := by
    intro i hi
    unfold graySpendMult
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right L (by omega))
  have h0 := hterm 0 (by norm_num)
  have h1 := hterm 1 (by norm_num)
  have h2 := hterm 2 (by norm_num)
  have h3 := hterm 3 (by norm_num)
  have h4 := hterm 4 (by norm_num)
  have h5 := hterm 5 (by norm_num)
  have h6 := hterm 6 (by norm_num)
  have h7 := hterm 7 (by norm_num)
  change grayBlockSpendOffset L 8 ≤ 8 * 2 ^ (7 * L)
  simp only [grayBlockSpendOffset]
  omega

/-- **Capacity at the pinned gap** (blueprint C1): the spare-son population
of the frozen branching dominates the whole spend block population — the
eight pass windows fit inside the spare pairs.  At `e = a + 8L + 3` the
source slab has `2^{8L+3}` sons while all blocks together need at most
`8·2^{7L} ≤ 2^{7L+3}` pairs, and the branching grants `2·2^{8L+3}` sons. -/
theorem grayBlockSpend_capacity {q L a e : ℕ}
    (hgap : e = a + 8 * L + 3) :
    grayBlockSpendOffset L 8 ≤
      grayTailBranch q L a e - grayChargedSourceCount a e := by
  have htot := grayBlockSpendOffset_total_le L
  have hsource : grayChargedSourceCount a e = 2 ^ (8 * L + 3) := by
    unfold grayChargedSourceCount
    congr 1
    omega
  have hbranch : 2 * 2 ^ (e - a) ≤ grayTailBranch q L a e := by
    unfold grayTailBranch ladderBranching
    exact le_max_left _ _
  have hea : e - a = 8 * L + 3 := by omega
  rw [hea] at hbranch
  have hspare : 2 ^ (8 * L + 3) ≤
      grayTailBranch q L a e - grayChargedSourceCount a e := by
    rw [hsource]
    omega
  refine le_trans htot (le_trans ?_ hspare)
  have h73 : 7 * L + 3 ≤ 8 * L + 3 := by omega
  calc 8 * 2 ^ (7 * L) = 2 ^ 3 * 2 ^ (7 * L) := by norm_num
    _ = 2 ^ (7 * L + 3) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (8 * L + 3) := Nat.pow_le_pow_right (by norm_num) h73

/-! ## Advantage-block cumulative capacity (audit verdict: Reading C)

The advantage block of round `r` occupies `grayAdvBlockMult q L r =
2^{(roundCount−1−r)·L}` distinct grandson coordinates (the wide two-level
block of proof doc v14 §9.0 item 2).  Distinct rounds must occupy disjoint
grandson ranges; the cumulative offset over all used rounds must stay inside
the frozen branching.  This is the cumulative disjoint-offset bound the
block-encoding audit flagged as the one unchecked capacity fact. -/

/-- The advantage-block multiplicity of round `r`: `2^{(roundCount−1−r)·L}`
(= `grayAdvMult (grayCallDepth q e) (grayTailRoundEps q L e r)`, since
`ε_r − callDepth = (roundCount−1−r)·L`). -/
def grayAdvBlockMult (q L r : Nat) : Nat :=
  2 ^ ((grayTailRoundCount q - 1 - r) * L)

/-- Cumulative grandson offset of round `r`: the total block size of the
earlier rounds. -/
def grayAdvBlockOffset (q L : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => grayAdvBlockOffset q L r + grayAdvBlockMult q L r

/-- The adversary block offset advances from round `r` to round `r + 1` by the block multiplicity
`grayAdvBlockMult q L r`. -/
lemma grayAdvBlockOffset_succ (q L r : Nat) :
    grayAdvBlockOffset q L (r + 1) =
      grayAdvBlockOffset q L r + grayAdvBlockMult q L r := rfl

/-- The adversary block offset is monotone in the round index. -/
lemma grayAdvBlockOffset_mono {q L r r' : Nat} (h : r ≤ r') :
    grayAdvBlockOffset q L r ≤ grayAdvBlockOffset q L r' := by
  induction r' with
  | zero => simpa using Nat.le_zero.mp h ▸ le_rfl
  | succ r' ih =>
      rcases Nat.lt_or_ge r (r' + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
      · have : r = r' + 1 := by omega
        subst this; exact le_rfl

/-- Each block is bounded by the top block `2^{(roundCount−1)·L}`. -/
lemma grayAdvBlockMult_le_top (q L r : Nat) :
    grayAdvBlockMult q L r ≤ 2 ^ ((grayTailRoundCount q - 1) * L) := by
  unfold grayAdvBlockMult
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right L (Nat.sub_le _ _))

/-- The crude cumulative bound: `offset R ≤ R · 2^{(roundCount−1)·L}`. -/
lemma grayAdvBlockOffset_le_crude (q L R : Nat) :
    grayAdvBlockOffset q L R ≤ R * 2 ^ ((grayTailRoundCount q - 1) * L) := by
  induction R with
  | zero => simp [grayAdvBlockOffset]
  | succ R ih =>
      rw [grayAdvBlockOffset_succ]
      calc grayAdvBlockOffset q L R + grayAdvBlockMult q L R
          ≤ R * 2 ^ ((grayTailRoundCount q - 1) * L) +
              2 ^ ((grayTailRoundCount q - 1) * L) :=
            Nat.add_le_add ih (grayAdvBlockMult_le_top q L R)
        _ = (R + 1) * 2 ^ ((grayTailRoundCount q - 1) * L) := by ring

/-- **The advantage-block cumulative capacity** (blueprint C1, the flagged
unchecked fact): all used rounds' blocks fit inside the frozen branching's
grandson coordinate space, disjointly.  Proof: `offset ≤ roundCount ·
2^{(roundCount−1)L}` and, since `roundCount = 256(q+1)²`, this is dominated by
`256(q+1) · 2^{roundCount·L + 256(q+1)} ≤ grayTailBaseBranch`. -/
theorem grayAdvBlock_capacity (q L : Nat) :
    grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q) ≤
      grayTailBaseBranch q L := by
  have hRle : grayChargedAdvantageRoundCount q ≤ grayTailRoundCount q := by
    rw [grayChargedAdvantageRoundCount_eq, grayTailRoundCount]; omega
  have hcrude := grayAdvBlockOffset_le_crude q L (grayChargedAdvantageRoundCount q)
  -- offset ≤ roundCount · 2^{(RC-1)L}
  have h1 : grayAdvBlockOffset q L (grayChargedAdvantageRoundCount q) ≤
      grayTailRoundCount q * 2 ^ ((grayTailRoundCount q - 1) * L) :=
    le_trans hcrude (Nat.mul_le_mul_right _ hRle)
  -- reduce baseBranch to its large branch
  refine le_trans h1 ?_
  rw [grayTailBaseBranch]
  refine le_trans ?_ (le_max_right _ _)
  -- RC · 2^{(RC-1)L} ≤ 256(q+1) · 2^{RC·L + 256(q+1)}
  rw [grayTailRoundCount]
  set c := 256 * (q + 1) ^ 2 with hc
  -- c = 256(q+1)^2 = 256(q+1) · (q+1)
  have hcfac : c = 256 * (q + 1) * (q + 1) := by rw [hc]; ring
  have hqpow : (q + 1) ≤ 2 ^ (256 * (q + 1)) := by
    have h1 : q + 1 ≤ 2 ^ (q + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hexp : (c - 1) * L ≤ c * L := Nat.mul_le_mul_right L (Nat.sub_le _ _)
  calc c * 2 ^ ((c - 1) * L)
      = 256 * (q + 1) * ((q + 1) * 2 ^ ((c - 1) * L)) := by rw [hcfac]; ring
    _ ≤ 256 * (q + 1) * (2 ^ (256 * (q + 1)) * 2 ^ (c * L)) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul hqpow
        exact Nat.pow_le_pow_right (by norm_num) hexp
    _ = 256 * (q + 1) * 2 ^ (c * L + 256 * (q + 1)) := by
        rw [← pow_add]; ring_nf
    _ = 256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
        rw [hc]

/-- The grandson coordinate belongs to round `r`'s advantage block. -/
def grayInAdvBlock (q L r g : Nat) : Prop :=
  grayAdvBlockOffset q L r ≤ g ∧
    g < grayAdvBlockOffset q L r + grayAdvBlockMult q L r

/-- **Cross-round grandson disjointness** (Reading C): distinct rounds occupy
disjoint grandson ranges, so their block coordinates never collide.  This is
what the chase's node-foreignness step consumes in place of the flattened
`grandson = roundIndex`. -/
lemma grayInAdvBlock_ne_of_round_ne {q L r r' g g' : Nat}
    (hg : grayInAdvBlock q L r g) (hg' : grayInAdvBlock q L r' g')
    (hne : r ≠ r') : g ≠ g' := by
  obtain ⟨hlo, hhi⟩ := hg
  obtain ⟨hlo', hhi'⟩ := hg'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hstep : grayAdvBlockOffset q L r + grayAdvBlockMult q L r =
        grayAdvBlockOffset q L (r + 1) := (grayAdvBlockOffset_succ q L r).symm
    have hmono : grayAdvBlockOffset q L (r + 1) ≤ grayAdvBlockOffset q L r' :=
      grayAdvBlockOffset_mono (by omega)
    omega
  · have hstep : grayAdvBlockOffset q L r' + grayAdvBlockMult q L r' =
        grayAdvBlockOffset q L (r' + 1) := (grayAdvBlockOffset_succ q L r').symm
    have hmono : grayAdvBlockOffset q L (r' + 1) ≤ grayAdvBlockOffset q L r :=
      grayAdvBlockOffset_mono (by omega)
    omega

end Kolmogorov
