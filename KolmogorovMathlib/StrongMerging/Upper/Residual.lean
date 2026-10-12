import KolmogorovMathlib.StrongMerging.Upper.Decoders

/-!
# Residual compression (blueprint H04, `UpperResidualBound`)

`sublinear-merging.tex`, Lemma `lem:residual` (tex ~383) and appendix "The plain residual-rank
decoder" (tex ~2594) and "Why choosing the large constant is not circular" (tex ~2687); blueprint
`bp-upper-hierarchy`, paragraph "The residual contradiction".

`upperResidualBound`: there is a constant `u` (depending only on the plain machine `V`) such that
for every hierarchy step constant `c₂` with `u + u ⌈log₂ (c₂ + 2)⌉ < c₂`, at every calibrated
instance in the hierarchy branch `JL < a, b`, if the actual `x` lies in the residual of a depth-`j`
block `F` (`j < J`), then `log₂ |F| - C(x | F) ≤ R + 3`.

The proof follows the paper.  Put `K = C(x | F)` and suppose `log₂ |F| - K > R + 3`.

* `resEnum`: the dovetailed enumeration, for a fixed code `cV` of `V`, of the residual edges `z`
  that some program of length `≤ K` prints on the condition `F`.  Every arrival is such an edge
  (`mem_arrivals_resEnum`) and `x` arrives (`exists_mem_arrivals_resEnum`).
* The arrivals at any stage are fewer than `2^(K+1)` (counting), hence fit in the fixed cap
  `⌊|F| / 2^R⌋` (`two_pow_succ_le_blockCap`), hence are core-free for the next-depth capacities
  (`coreFree_of_subset_residual`); the online orientation bounds the rank of `x` at its owner by
  `3 (⌊log₂ W⌋ + 1) 2^(a - (j+1)L)` (or with `b`), with `W ≤ 2^(n + 1 + max a b)`.
* `rankDecoder`: the plain residual-rank decoder.  Its packet `rankPacket` carries the header
  `n, a, b, R, L, j, side, K`, the two witness bodies, the local rank `s` of `F` in exactly `jL + 1`
  bits and the rank `r` of `x` as the rest of the packet.  Given the owner's model it recomputes
  the tables, `F`, its residual, the enumeration and the orientation, and decodes `x`
  (`exists_rankPacket`).  It may diverge on other advice; only its actual run must halt.
* The leading lengths cancel, `jL + (a - (j+1)L) = a - L`, and the typicality bound
  `C(x | A) ≥ a - b_typ H` (`upperTypicality`) contradicts the choice of `c₂`
  (`residual_arith`, with the overhead estimates `hdrCost_rank_le`, `size_rank_le`).
-/

namespace Kolmogorov.StrongMerging.Upper

open Nat.Partrec (Code)

/-! ### Elementary bounds on header lengths -/

/-- `headerLog` is monotone. -/
theorem headerLog_mono {x y : ℕ} (h : x ≤ y) : headerLog x ≤ headerLog y := by
  unfold headerLog
  exact Nat.clog_mono_right 2 (by omega)

/-- **Header of a sum** `⌈log₂ (x + y + 2)⌉ ≤ ⌈log₂ (x + 2)⌉ + ⌈log₂ (y + 2)⌉`.

Proof: `x + y + 2 ≤ (x + 2)(y + 2) ≤ 2^(headerLog x) 2^(headerLog y)`
(`Nat.le_pow_clog`), so `Nat.clog_le_of_le_pow`/`Nat.clog_le_iff_le_pow` gives the bound. -/
theorem headerLog_add_le (x y : ℕ) : headerLog (x + y) ≤ headerLog x + headerLog y := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two, pow_add]
  have h1 := Nat.le_pow_clog one_lt_two (x + 2)
  have h2 := Nat.le_pow_clog one_lt_two (y + 2)
  have h3 : (x + 2) * (y + 2) = x * y + 2 * x + 2 * y + 4 := by ring
  calc x + y + 2 ≤ (x + 2) * (y + 2) := by omega
    _ ≤ 2 ^ Nat.clog 2 (x + 2) * 2 ^ Nat.clog 2 (y + 2) := Nat.mul_le_mul h1 h2

/-- **Header of a product** `⌈log₂ (x y + 2)⌉ ≤ ⌈log₂ (x + 2)⌉ + ⌈log₂ (y + 2)⌉`.

Proof: `x y + 2 ≤ (x + 2)(y + 2) ≤ 2^(headerLog x + headerLog y)` (`Nat.le_pow_clog`,
`pow_add`), then `Nat.clog_le_iff_le_pow`. -/
theorem headerLog_mul_le (x y : ℕ) : headerLog (x * y) ≤ headerLog x + headerLog y := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two, pow_add]
  have h1 := Nat.le_pow_clog one_lt_two (x + 2)
  have h2 := Nat.le_pow_clog one_lt_two (y + 2)
  have h3 : (x + 2) * (y + 2) = x * y + 2 * x + 2 * y + 4 := by ring
  calc x * y + 2 ≤ (x + 2) * (y + 2) := by omega
    _ ≤ 2 ^ Nat.clog 2 (x + 2) * 2 ^ Nat.clog 2 (y + 2) := Nat.mul_le_mul h1 h2

/-- **Header of a successor** `⌈log₂ (x + 3)⌉ ≤ ⌈log₂ (x + 2)⌉ + 1`.

Proof: `x + 3 ≤ 2 (x + 2) ≤ 2^(headerLog x + 1)` (`Nat.le_pow_clog`, `pow_succ`), then
`Nat.clog_le_iff_le_pow`. -/
theorem headerLog_succ_le (x : ℕ) : headerLog (x + 1) ≤ headerLog x + 1 := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two, pow_succ]
  have h1 := Nat.le_pow_clog one_lt_two (x + 2)
  omega

/-- **A header is at most linear** `⌈log₂ (x + 2)⌉ ≤ x + 1`.

Proof: `x + 2 ≤ 2^(x+1)` (induction, or `Nat.lt_two_pow_self` twice), then
`Nat.clog_le_iff_le_pow`. -/
theorem headerLog_le_add_one (x : ℕ) : headerLog x ≤ x + 1 := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h1 : x + 1 < 2 ^ (x + 1) := Nat.lt_two_pow_self
  omega

/-- **Binary length is at most the header** `Nat.size x ≤ ⌈log₂ (x + 2)⌉`.

Proof: `x < x + 2 ≤ 2^(headerLog x)` (`Nat.le_pow_clog`), hence
`Nat.size x ≤ headerLog x` by `Nat.size_le`. -/
theorem size_le_headerLog (x : ℕ) : Nat.size x ≤ headerLog x := by
  rw [Nat.size_le]
  unfold headerLog
  have h1 := Nat.le_pow_clog one_lt_two (x + 2)
  omega

/-- **The fixed cap holds the short-description set** (tex ~399–404).  If
`log₂ |F| > K + R + 3` then `2^(K+1) ≤ ⌊|F| / 2^R⌋`.

Proof: `|F| > 0` (else `log₂ 0 = 0 < K + R + 3` fails), and `Real.lt_logb_iff_rpow_lt`
gives `2^(K+R+3) < |F|` as reals, hence as naturals (`Real.rpow_natCast`, `exact_mod_cast`);
then `2^(K+1) · 2^R ≤ 2^(K+R+3) ≤ |F|` and `Nat.le_div_iff_mul_le`. -/
theorem two_pow_succ_le_blockCap {F : Finset BitString} {K R : ℕ}
    (h : (K : ℝ) + R + 3 < Real.logb 2 F.card) : 2 ^ (K + 1) ≤ blockCap R F := by
  have hpos : 0 < F.card := by
    rcases Nat.eq_zero_or_pos F.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.logb_zero] at h
      have : (0 : ℝ) ≤ (K : ℝ) + R := by positivity
      linarith
    · exact h0
  have h1 : (2 : ℝ) ^ (((K + R + 3 : ℕ) : ℝ)) < F.card := by
    rw [← Real.lt_logb_iff_rpow_lt one_lt_two (by exact_mod_cast hpos)]
    push_cast
    linarith
  rw [Real.rpow_natCast] at h1
  have h2 : 2 ^ (K + R + 3) < F.card := by exact_mod_cast h1
  unfold blockCap
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 2 ^ (K + 1) * 2 ^ R = 2 ^ (K + 1 + R) := (pow_add 2 _ _).symm
    _ ≤ 2 ^ (K + R + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ F.card := h2.le

/-! ### The enumeration of short residual descriptions -/

/-- **The dovetailed enumeration** of the residual edges with short descriptions given the parent
(`ResidualRank`, tex ~2614–2627).  Step `i = ⟪t, k⟫` runs the `k`-th program of length `≤ K` (in
`boundedPrograms K`) for `t` stages of the code `cV` on the condition `Fcode`, and emits its output
if it lies in the residual `Lres`.  Duplicates are removed later by `arrivals`. -/
def resEnum (cV : Code) (Lres : Finset BitString) (Fcode : BitString) (K : ℕ) (i : ℕ) :
    Option BitString :=
  ((boundedPrograms K)[(Nat.unpair i).2]?).bind fun p =>
    (conditionalRunOut cV (Nat.unpair i).1 p Fcode).filter fun z => decide (z ∈ Lres)

/-- **Soundness of the enumeration.**  Every arrival lies in the residual and has a description
of length at most `K` given the parent.

Proof: `mem_arrivals_iff` gives `i < s` with `resEnum … i = some z`; unfolding
`Option.bind_eq_some_iff`, `Option.filter_eq_some_iff` gives a program `p ∈ boundedPrograms K`
(`List.mem_of_getElem?`, `mem_boundedPrograms_iff`) with `conditionalRunOut cV t p Fcode = some z`
and `z ∈ Lres`; `conditionalRunOut_sound hcV` gives `produces V p Fcode z`, so
`condK V z Fcode ≤ p.length ≤ K` (`condK_le_iff`), and `condC` is its natural value
(`ENat.toNat_le_of_le_natCast`). -/
theorem mem_arrivals_resEnum {V : Map} {cV : Code} (hcV : IsCodeFor cV V)
    {Lres : Finset BitString} {Fcode : BitString} {K s : ℕ} {z : BitString}
    (hz : z ∈ arrivals (resEnum cV Lres Fcode K) s) :
    z ∈ Lres ∧ condC V z Fcode ≤ K := by
  obtain ⟨i, -, hi⟩ := (mem_arrivals_iff _ s z).mp hz
  unfold resEnum at hi
  rw [Option.bind_eq_some_iff] at hi
  obtain ⟨p, hp, hz'⟩ := hi
  cases hrun : conditionalRunOut cV (Nat.unpair i).1 p Fcode with
  | none =>
    rw [hrun] at hz'
    simp at hz'
  | some y =>
    rw [hrun] at hz'
    simp only [Option.filter_some, decide_eq_true_eq] at hz'
    split_ifs at hz' with hy
    obtain rfl : y = z := Option.some_inj.mp hz'
    refine ⟨hy, ?_⟩
    have hpK : p.length ≤ K := (mem_boundedPrograms_iff p K).mp (List.mem_of_getElem? hp)
    have hprod := conditionalRunOut_sound hcV hrun
    have h1 : condK V y Fcode ≤ (p.length : ℕ∞) :=
      (condK_le_iff V y Fcode p.length).2 ⟨p, le_rfl, hprod⟩
    have h2 : (condK V y Fcode).toNat ≤ K := (toNat_le_of_le_natCast h1).trans hpK
    unfold condC
    exact_mod_cast h2

/-- **Completeness of the enumeration.**  A residual edge printed on the condition `Fcode` by some
program of length at most `K` eventually arrives.

Proof: `conditionalRunOut_complete hcV` gives a stage `t`; `p ∈ boundedPrograms K`
(`mem_boundedPrograms_iff`) has an index `k` (`List.mem_iff_getElem?`); then
`resEnum … (Nat.pair t k) = some z` (`Nat.unpair_pair`, `Option.filter`), and
`mem_arrivals_iff` at stage `Nat.pair t k + 1`. -/
theorem exists_mem_arrivals_resEnum {V : Map} {cV : Code} (hcV : IsCodeFor cV V)
    {Lres : Finset BitString} {Fcode : BitString} {K : ℕ} {z p : BitString} (hz : z ∈ Lres)
    (hp : p.length ≤ K) (hprod : produces V p Fcode z) :
    ∃ s, z ∈ arrivals (resEnum cV Lres Fcode K) s := by
  obtain ⟨t, ht⟩ := conditionalRunOut_complete hcV hprod
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ((mem_boundedPrograms_iff p K).mpr hp)
  refine ⟨Nat.pair t k + 1, (mem_arrivals_iff _ _ _).mpr ⟨Nat.pair t k, Nat.lt_succ_self _, ?_⟩⟩
  simp [resEnum, Nat.unpair_pair, hk, ht, hz]

/-! ### The plain residual-rank decoder -/

/-- The typed endpoint label of a side: a row (`false`) or a column (`true`). -/
def typedEnd (side : Bool) (w : BitString) : BitString ⊕ BitString :=
  if side then Sum.inr w else Sum.inl w

/-- The packet of the residual-rank decoder: header fields `n, a, b, R, L, j, side, K`, the two
witness bodies, the local rank `s` of the parent in exactly `jL + 1` bits, and the rank `r` of the
edge in its owner's assignment list as the rest of the packet. -/
def rankPacket (side : Bool) (n a b R L j K : ℕ) (pA pB : BitString) (s r : ℕ) : BitString :=
  numPacket [n, a, b, R, L, j, side.toNat, K]
    (totalProgramPairCode pA (totalProgramPairCode pB (chunkAddress s (j * L + 1) ++ Nat.bits r)))

/-- A numeric packet costs at most four header units per field:
`|numPacket ks body| ≤ |body| + 4 hdrCost ks`. -/
theorem length_numPacket_le_hdrCost (ks : List ℕ) (body : BitString) :
    (numPacket ks body).length ≤ body.length + 4 * hdrCost ks := by
  induction ks with
  | nil => simp [numPacket, hdrCost]
  | cons k ks ih =>
    have hlen : (numPacket (k :: ks) body).length = (Nat.bits k).length +
        (numPacket ks body).length + 2 * (Nat.bits (Nat.bits k).length).length + 1 := by
      simp only [numPacket, List.foldr_cons]
      exact length_totalProgramPairCode _ _
    have hc : hdrCost (k :: ks) = headerLog k + hdrCost ks := by
      simp [hdrCost]
    have h1 := size_le_headerLog k
    have h2 : Nat.size (Nat.size k) ≤ Nat.size k := Nat.size_le.mpr Nat.lt_two_pow_self
    have h3 := one_le_headerLog k
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hlen
    rw [hlen, hc]
    omega

/-- **Packet length** (tex ~2660–2684): coefficient one on the `jL + 1` bits of the local rank and
on the binary length of the assignment rank, logarithmic headers otherwise.

Proof: as `length_localPacket_le`: each `numField k` costs
`|bits k| + 2 |bits |bits k|| + 1 ≤ 4 headerLog k` (`length_totalProgramPairCode`,
`size_le_headerLog`, `1 ≤ headerLog k`), the side field at most `4`; each
`totalProgramPairCode p _` costs `2 |bits |p|| + 1 ≤ 3 headerLog |p|`; the tail has length
`(jL + 1) + |bits r|` (`chunkAddress_length`). -/
theorem length_rankPacket_le (side : Bool) (n a b R L j K : ℕ) (pA pB : BitString) (s r : ℕ)
    (hs : s < 2 ^ (j * L + 1)) :
    (rankPacket side n a b R L j K pA pB s r).length ≤
      j * L + 1 + (Nat.bits r).length + pA.length + pB.length +
        4 * hdrCost [n, a, b, R, L, j, K, pA.length, pB.length] + 9 := by
  have hpair : ∀ p q : BitString,
      (totalProgramPairCode p q).length ≤ p.length + q.length + 3 * headerLog p.length := by
    intro p q
    rw [length_totalProgramPairCode, Nat.size_eq_bits_len]
    have h1 := size_le_headerLog p.length
    have h3 := one_le_headerLog p.length
    omega
  have htail : (chunkAddress s (j * L + 1) ++ Nat.bits r).length =
      j * L + 1 + (Nat.bits r).length := by
    rw [List.length_append, chunkAddress_length s _ hs]
  have hside : headerLog side.toNat ≤ 2 := by
    have h1 : side.toNat ≤ 1 := Bool.toNat_le side
    have h2 := headerLog_mono h1
    have h3 : headerLog 1 = 2 := by
      unfold headerLog
      decide
    omega
  have hhdr := length_numPacket_le_hdrCost [n, a, b, R, L, j, side.toNat, K]
    (totalProgramPairCode pA (totalProgramPairCode pB (chunkAddress s (j * L + 1) ++ Nat.bits r)))
  have h1 := hpair pA (totalProgramPairCode pB (chunkAddress s (j * L + 1) ++ Nat.bits r))
  have h2 := hpair pB (chunkAddress s (j * L + 1) ++ Nat.bits r)
  have hc1 : hdrCost [n, a, b, R, L, j, side.toNat, K] = headerLog n + headerLog a +
      headerLog b + headerLog R + headerLog L + headerLog j + headerLog side.toNat +
        headerLog K := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hc2 : hdrCost [n, a, b, R, L, j, K, pA.length, pB.length] = headerLog n + headerLog a +
      headerLog b + headerLog R + headerLog L + headerLog j + headerLog K +
        headerLog pA.length + headerLog pB.length := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  unfold rankPacket
  omega

/-- The core of the residual-rank decoder on a shape `P`: recover the parent `F` as the local
block of rank `s` at the typed endpoint `(side, w)`, enumerate its residual edges with descriptions
of length `≤ K`, and decode the edge of rank `r` owned by `(side, w)` in the online orientation
with the next-depth capacities. -/
noncomputable def rankCore (cV : Code) (P : ShapeParams) (R L j : ℕ) (side : Bool) (K : ℕ)
    (w : BitString) (s r : ℕ) : Part BitString :=
  decodeOwned (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1))
    (resEnum cV (residual P R L j (localBlock P R L j side w s))
      (canonicalFiniteSetCode (localBlock P R L j side w s)) K) (typedEnd side w) r

/-- The residual-rank decoder from decoded fields `ks = [n, a, b, R, L, j, side, K]`, the two
witness bodies and the tail (the local rank in `jL + 1` bits, then the assignment rank): complete
runs of the witnesses, then `rankCore` on the table shape. -/
noncomputable def rankOut (cV : Code) (ks : List ℕ) (pA pB tail w : BitString) :
    Part BitString :=
  (runTable pA (ks.getD 0 0)).bind fun TA => (runTable pB (ks.getD 0 0)).bind fun TB =>
    rankCore cV (tableShape TA TB (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)) (ks.getD 3 0)
      (ks.getD 4 0) (ks.getD 5 0) (decide (ks.getD 6 0 ≠ 0)) (ks.getD 7 0) w
      (bitsToNat (tail.take (ks.getD 5 0 * ks.getD 4 0 + 1)))
      (decodeBits (tail.drop (ks.getD 5 0 * ks.getD 4 0 + 1)))

/-- **The plain residual-rank decoder** `ResidualRank(Y; θ, j, side, s, K, r)` (tex ~2611), as a
machine reading `rankPacket` and the condition `w` (the owner's model code).  It is partial. -/
noncomputable def rankDecoder (cV : Code) : Map := fun q =>
  rankOut cV (decodeFields 8 q.1).1 (decodeTotalProgramPairFirst (decodeFields 8 q.1).2)
    (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (decodeFields 8 q.1).2))
    (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (decodeFields 8 q.1).2)) q.2

/-- The parameter tuple of the residual-rank decoder core: the two output tables, `(n, a, b)`,
`(R, L, j)`, the side, `K`, the endpoint label `w`, the local rank `s` and the assignment rank
`r`. -/
abbrev RankParams : Type :=
  (List (BitString × BitString) × List (BitString × BitString)) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) ×
    Bool × ℕ × BitString × ℕ × ℕ

/-- The table shape of a parameter tuple. -/
def rpShape (q : RankParams) : ShapeParams :=
  tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2

/-- The parent block named by a parameter tuple: the local block of rank `s` at `(side, w)`. -/
noncomputable def rpBlock (q : RankParams) : Finset BitString :=
  localBlock (rpShape q) q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1

/-- The enumeration of short residual descriptions named by a parameter tuple. -/
noncomputable def rpEnum (cV : Code) (q : RankParams) : ℕ → Option BitString :=
  resEnum cV (residual (rpShape q) q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 (rpBlock q))
    (canonicalFiniteSetCode (rpBlock q)) q.2.2.2.2.1

/-- **Row endpoints are computable in the parameters.**

Proof: `shapeSrc (rpShape q) z = Sum.inl (tableOut q.1.1 z)`; `Computable.sumInl` composed
with `tableOut_primrec.to_comp` and the projections. -/
theorem rpShape_src_computable :
    Computable₂ fun (q : RankParams) (z : BitString) => shapeSrc (rpShape q) z := by
  have h : Computable fun p : RankParams × BitString => tableOut p.1.1.1 p.2 :=
    tableOut_primrec.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      Computable.snd
  exact (Computable.sumInl.comp h).of_eq fun p => rfl

/-- **Column endpoints are computable in the parameters.**

Proof: `shapeTgt (rpShape q) z = Sum.inr (tableOut q.1.2 z)`; `Computable.sumInr` composed
with `tableOut_primrec.to_comp` and the projections. -/
theorem rpShape_tgt_computable :
    Computable₂ fun (q : RankParams) (z : BitString) => shapeTgt (rpShape q) z := by
  have h : Computable fun p : RankParams × BitString => tableOut p.1.1.2 p.2 :=
    tableOut_primrec.to_comp.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
      Computable.snd
  exact (Computable.sumInr.comp h).of_eq fun p => rfl

/-- **Next-depth capacities are computable in the parameters.**

Proof: `shapeCap (rpShape q) L (j+1) v` is `Sum.elim` of the constants
`2^(a - (j+1)L)`, `2^(b - (j+1)L)`; use `Computable.sumCasesOn` (or `Primrec.sumCasesOn`) with
`Primrec.nat_sub`, `Primrec.nat_mul`, `Primrec.pow`-style lemmas (`Nat.pow` is primitive
recursive: `Primrec.nat_pow`). -/
theorem rpShape_cap_computable :
    Computable₂ fun (q : RankParams) (v : BitString ⊕ BitString) =>
      shapeCap (rpShape q) q.2.2.1.2.1 (q.2.2.1.2.2 + 1) v := by
  have hpow : Primrec₂ (fun x y : ℕ => x ^ y) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hL : Primrec fun q : RankParams => q.2.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hj : Primrec fun q : RankParams => q.2.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hthr : ∀ f : RankParams → ℕ, Primrec f → Primrec fun q : RankParams =>
      2 ^ (f q - (q.2.2.1.2.2 + 1) * q.2.2.1.2.1) := fun f hf =>
    hpow.comp (Primrec.const 2) (Primrec.nat_sub.comp hf
      (Primrec.nat_mul.comp (Primrec.succ.comp hj) hL))
  have hrow := hthr (fun q => q.2.1.2.1)
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hcol := hthr (fun q => q.2.1.2.2)
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have h := Computable.sumCasesOn (f := fun p : RankParams × (BitString ⊕ BitString) => p.2)
    (g := fun p (_ : BitString) => 2 ^ (p.1.2.1.2.1 - (p.1.2.2.1.2.2 + 1) * p.1.2.2.1.2.1))
    (h := fun p (_ : BitString) => 2 ^ (p.1.2.1.2.2 - (p.1.2.2.1.2.2 + 1) * p.1.2.2.1.2.1))
    Computable.snd (hrow.to_comp.comp (Computable.fst.comp Computable.fst))
    (hcol.to_comp.comp (Computable.fst.comp Computable.fst))
  refine h.of_eq fun p => ?_
  rcases p with ⟨q, v⟩
  cases v <;> rfl

/-- A filter of a computable option by a computable test is computable. -/
theorem computable_option_filter {α : Type} [Primcodable α] {o : α → Option BitString}
    {t : α → BitString → Bool} (ho : Computable o) (ht : Computable₂ t) :
    Computable fun a => (o a).filter (t a) := by
  refine (Computable.option_bind ho (Computable.cond ht (Computable.option_some.comp Computable.snd)
    (Computable.const none)).to₂).of_eq fun a => ?_
  rcases o a with _ | z
  · rfl
  · simp [Option.filter]

/-- **The enumeration is computable in the parameters**: the parent code is
`localBlockCode_primrec`, the residual code is `residual_code_primrec` at that parent code, residual
membership is a list membership in the decoded residual, and the dovetailing step uses
`primrec_boundedPrograms` and `Lower.conditionalRunOut_computable`. -/
theorem rpEnum_computable (cV : Code) : Computable₂ (rpEnum cV) := by
  have p21 : Primrec fun q : RankParams => q.2.1 := Primrec.fst.comp Primrec.snd
  have p221 : Primrec fun q : RankParams => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have pside : Primrec fun q : RankParams => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have pK : Primrec fun q : RankParams => q.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have pw : Primrec fun q : RankParams => q.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))
  have ps : Primrec fun q : RankParams => q.2.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hFcode : Primrec fun q : RankParams => canonicalFiniteSetCode (rpBlock q) :=
    (localBlockCode_primrec.comp (Primrec.fst.pair (p21.pair (p221.pair (pside.pair
      (pw.pair ps)))))).of_eq fun q => rfl
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hres := residual_code_primrec
    (fun (T : List (BitString × BitString) × List (BitString × BitString)) z => tableOut T.1 z)
    (fun (T : List (BitString × BitString) × List (BitString × BitString)) z => tableOut T.2 z)
    hA hB
  have hRcode : Primrec fun q : RankParams => canonicalFiniteSetCode
      (residual (rpShape q) q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 (rpBlock q)) :=
    (hres.comp ((Primrec.fst.pair (p21.pair p221)).pair hFcode)).of_eq fun q => by
      rw [parseModel_canonicalFiniteSetCode]
      rfl
  have hmem : Primrec₂ fun (q : RankParams) (z : BitString) =>
      decide (z ∈ residual (rpShape q) q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 (rpBlock q)) :=
    (bitString_mem_primrec.comp Primrec.snd
      (canonicalPointListOfCode_primrec.comp (hRcode.comp Primrec.fst))).of_eq fun p => by
        simp [canonicalPointListOfCode_canonicalFiniteSetCode]
  have hf : Computable fun p : RankParams × ℕ =>
      (boundedPrograms p.1.2.2.2.2.1)[(Nat.unpair p.2).2]? :=
    (Primrec.list_getElem?.comp (primrec_boundedPrograms.comp (pK.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hrun := Lower.conditionalRunOut_computable cV
  have htup : Computable fun x : (RankParams × ℕ) × BitString =>
      ((Nat.unpair x.1.2).1, x.2, canonicalFiniteSetCode (rpBlock x.1.1)) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp.pair
      (Computable.snd.pair (hFcode.to_comp.comp (Computable.fst.comp Computable.fst)))
  have ho : Computable fun x : (RankParams × ℕ) × BitString =>
      conditionalRunOut cV (Nat.unpair x.1.2).1 x.2 (canonicalFiniteSetCode (rpBlock x.1.1)) :=
    Computable.comp (f := fun q : ℕ × BitString × BitString => conditionalRunOut cV q.1 q.2.1 q.2.2)
      (g := fun x : (RankParams × ℕ) × BitString =>
        ((Nat.unpair x.1.2).1, x.2, canonicalFiniteSetCode (rpBlock x.1.1))) hrun htup
  have ht : Computable₂ fun (x : (RankParams × ℕ) × BitString) (z : BitString) =>
      decide (z ∈ residual (rpShape x.1.1) x.1.1.2.2.1.1 x.1.1.2.2.1.2.1 x.1.1.2.2.1.2.2
        (rpBlock x.1.1)) :=
    hmem.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hg : Computable₂ fun (p : RankParams × ℕ) (prog : BitString) =>
      (conditionalRunOut cV (Nat.unpair p.2).1 prog (canonicalFiniteSetCode (rpBlock p.1))).filter
        fun z => decide (z ∈ residual (rpShape p.1) p.1.2.2.1.1 p.1.2.2.1.2.1 p.1.2.2.1.2.2
          (rpBlock p.1)) :=
    computable_option_filter (o := fun x : (RankParams × ℕ) × BitString =>
      conditionalRunOut cV (Nat.unpair x.1.2).1 x.2 (canonicalFiniteSetCode (rpBlock x.1.1)))
      (t := fun (x : (RankParams × ℕ) × BitString) (z : BitString) =>
        decide (z ∈ residual (rpShape x.1.1) x.1.1.2.2.1.1 x.1.1.2.2.1.2.1 x.1.1.2.2.1.2.2
          (rpBlock x.1.1))) ho ht
  exact (Computable.option_bind hf hg).of_eq fun p => rfl

/-- **Typed endpoints are computable.**

Proof: `typedEnd side w = bif side then Sum.inr w else Sum.inl w`; `Computable.cond`
(or `Primrec.cond`) with `Computable.sumInl`, `Computable.sumInr`. -/
theorem typedEnd_computable : Computable₂ typedEnd := by
  refine (Computable.cond Computable.fst (Computable.sumInr.comp Computable.snd)
    (Computable.sumInl.comp Computable.snd)).of_eq fun p => ?_
  rcases p with ⟨side, w⟩
  cases side <;> rfl

/-- The decoder core read from a parameter tuple. -/
noncomputable def rankCoreP (cV : Code) (q : RankParams) : Part BitString :=
  rankCore cV (rpShape q) q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
    q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2

/-- **The decoder core is partial recursive in its parameters**, by `decodeOwned_partrec` (G03)
with the computable endpoint maps, capacities and enumeration of the tuple. -/
theorem rankCore_partrec (cV : Code) : Partrec (rankCoreP cV) := by
  have h := decodeOwned_partrec (fun q : RankParams => shapeSrc (rpShape q))
    (fun q => shapeTgt (rpShape q)) (fun q => shapeCap (rpShape q) q.2.2.1.2.1 (q.2.2.1.2.2 + 1))
    (rpEnum cV) rpShape_src_computable rpShape_tgt_computable rpShape_cap_computable
    (rpEnum_computable cV)
  have hside : Computable fun q : RankParams => q.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hw : Computable fun q : RankParams => q.2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))))
  have hr : Computable fun q : RankParams => q.2.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
  have hv : Computable fun q : RankParams =>
      (typedEnd q.2.2.2.1 q.2.2.2.2.2.1, q.2.2.2.2.2.2.2) :=
    (typedEnd_computable.comp hside hw).pair hr
  exact (h.comp (Computable.id.pair hv)).of_eq fun q => rfl

/-- The decoded header fields of a rank packet. -/
def rkFields (q : BitString × BitString) : List ℕ :=
  (decodeFields 8 q.1).1

/-- The first witness body of a rank packet. -/
def rkPA (q : BitString × BitString) : BitString :=
  decodeTotalProgramPairFirst (decodeFields 8 q.1).2

/-- The second witness body of a rank packet. -/
def rkPB (q : BitString × BitString) : BitString :=
  decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (decodeFields 8 q.1).2)

/-- The tail of a rank packet: the local rank bits, then the assignment rank bits. -/
def rkTail (q : BitString × BitString) : BitString :=
  decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (decodeFields 8 q.1).2)

/-- The decoder-core parameter tuple of a rank packet and condition `q`, given the two tables. -/
def rkTuple (q : BitString × BitString) (TA TB : List (BitString × BitString)) : RankParams :=
  ((TA, TB), ((rkFields q).getD 0 0, (rkFields q).getD 1 0, (rkFields q).getD 2 0),
    ((rkFields q).getD 3 0, (rkFields q).getD 4 0, (rkFields q).getD 5 0),
    decide ((rkFields q).getD 6 0 ≠ 0), (rkFields q).getD 7 0, q.2,
    bitsToNat ((rkTail q).take ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1)),
    decodeBits ((rkTail q).drop ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1)))

/-- Packet parsing into the decoder-core tuple is computable. -/
theorem rkTuple_computable :
    Computable fun x : ((BitString × BitString) × List (BitString × BitString)) ×
        List (BitString × BitString) => rkTuple x.1.1 x.1.2 x.2 := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 8 q.1 :=
    decodeFields_computable.comp (Computable.const 8) Computable.fst
  have hks : Computable rkFields := Computable.fst.comp hdf
  have hget : ∀ i : ℕ, Computable fun q : BitString × BitString => (rkFields q).getD i 0 :=
    fun i => (Primrec.list_getD 0).to_comp.comp hks (Computable.const i)
  have htail : Computable rkTail :=
    decodeTotalProgramPairSecond_computable.comp
      (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf))
  have hidx : Computable fun q : BitString × BitString =>
      (rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1 :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (hget 5) (hget 4))
      (Computable.const 1)
  have hs : Computable fun q : BitString × BitString =>
      bitsToNat ((rkTail q).take ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1)) :=
    bitsToNat_primrec.to_comp.comp (Primrec.list_take.to_comp.comp hidx htail)
  have hr : Computable fun q : BitString × BitString =>
      decodeBits ((rkTail q).drop ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1)) :=
    decodeBits_computable.comp (Primrec.list_drop.to_comp.comp hidx htail)
  have hside : Computable fun q : BitString × BitString => decide ((rkFields q).getD 6 0 ≠ 0) :=
    (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp (hget 6)
      (Computable.const 0))).of_eq fun q => by simp
  have hpar : Computable fun q : BitString × BitString =>
      (((rkFields q).getD 0 0, (rkFields q).getD 1 0, (rkFields q).getD 2 0),
        ((rkFields q).getD 3 0, (rkFields q).getD 4 0, (rkFields q).getD 5 0),
        decide ((rkFields q).getD 6 0 ≠ 0), (rkFields q).getD 7 0, q.2,
        bitsToNat ((rkTail q).take ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1)),
        decodeBits ((rkTail q).drop ((rkFields q).getD 5 0 * (rkFields q).getD 4 0 + 1))) :=
    ((hget 0).pair ((hget 1).pair (hget 2))).pair (((hget 3).pair ((hget 4).pair (hget 5))).pair
      (hside.pair ((hget 7).pair (Computable.snd.pair (hs.pair hr)))))
  exact (((Computable.snd.comp Computable.fst).pair Computable.snd).pair
    (hpar.comp (Computable.fst.comp Computable.fst))).of_eq fun x => rfl

/-- **The residual-rank decoder is partial recursive**: packet parsing is computable
(`rkTuple_computable`), the two complete runs are partial recursive (`runTable_partrec`), and the
core is partial recursive (`rankCore_partrec`); compose by `Partrec.bind`. -/
theorem rankDecoder_partrec (cV : Code) : isDecompressor (rankDecoder cV) := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 8 q.1 :=
    decodeFields_computable.comp (Computable.const 8) Computable.fst
  have hn : Computable fun q : BitString × BitString => (rkFields q).getD 0 0 :=
    (Primrec.list_getD 0).to_comp.comp (Computable.fst.comp hdf) (Computable.const 0)
  have hpA : Computable rkPA :=
    decodeTotalProgramPairFirst_computable.comp (Computable.snd.comp hdf)
  have hpB : Computable rkPB := decodeTotalProgramPairFirst_computable.comp
    (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf))
  have hcore : Partrec₂ fun (p : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) => rankCoreP cV (rkTuple p.1 p.2 TB) :=
    (rankCore_partrec cV).comp rkTuple_computable
  have hinner : Partrec₂ fun (q : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (rkPB q) ((rkFields q).getD 0 0)).bind fun TB => rankCoreP cV (rkTuple q TA TB) :=
    Partrec.bind (runTable_partrec.comp (hpB.comp Computable.fst) (hn.comp Computable.fst)) hcore
  refine (Partrec.bind (runTable_partrec.comp hpA hn) hinner).of_eq fun q => ?_
  simp only [rankDecoder, rankOut, rankCoreP, rkTuple, rpShape, rkFields, rkPA, rkPB, rkTail]
  rfl

/-- **The decoder on its packet.**  If `TA`, `TB` are the complete-run tables of `pA`, `pB` at
length `n` and `s < 2^(jL+1)`, the decoder on `rankPacket` and any condition `w` is `rankCore` on
the table shape.

Proof: `decodeFields_numPacket` (eight fields), `decodeTotalProgramPairFirst_pair`,
`decodeTotalProgramPairSecond_pair`; the tail splits at `jL + 1` (`chunkAddress_length`,
`List.take_left'`, `List.drop_left'`), `bitsToNat_chunkAddress`, `decodeBits_natBits`; the side
field decodes to `side` (cases); `runTable pA n = Part.some TA` (`Part.eq_some_iff`) and
`Part.bind_some`. -/
theorem rankDecoder_spec (cV : Code) (side : Bool) (n a b R L j K : ℕ) (pA pB : BitString)
    (s r : ℕ) (w : BitString) {TA TB : List (BitString × BitString)}
    (hTA : TA ∈ runTable pA n) (hTB : TB ∈ runTable pB n) (hs : s < 2 ^ (j * L + 1)) :
    rankDecoder cV (rankPacket side n a b R L j K pA pB s r, w) =
      rankCore cV (tableShape TA TB n a b) R L j side K w s r := by
  have hTA' : runTable pA n = Part.some TA := Part.eq_some_iff.mpr hTA
  have hTB' : runTable pB n = Part.some TB := Part.eq_some_iff.mpr hTB
  have hfields : decodeFields 8 (rankPacket side n a b R L j K pA pB s r) =
      ([n, a, b, R, L, j, side.toNat, K], totalProgramPairCode pA
        (totalProgramPairCode pB (chunkAddress s (j * L + 1) ++ Nat.bits r))) :=
    decodeFields_numPacket [n, a, b, R, L, j, side.toNat, K] _
  have hlen : (chunkAddress s (j * L + 1)).length = j * L + 1 := chunkAddress_length s _ hs
  have hside : decide (side.toNat ≠ 0) = side := by
    cases side <;> rfl
  simp only [rankDecoder, rankOut, hfields, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair, List.getD_cons_zero, List.getD_cons_succ, hTA', hTB',
    Part.bind_some, hside]
  rw [List.take_left' hlen, List.drop_left' hlen, bitsToNat_chunkAddress, decodeBits_natBits]

/-! ### The compression step -/

/-- **The residual-rank description** (tex ~386–420, ~2594–2660).  Let `TA, TB` be the complete-run
tables of total witnesses at length `n`, `P` the table shape, and `F` a depth-`j` block whose
residual contains `x`, with `(j+1)L ≤ a, b`.  If `K = C(x | F)` and `2^(K+1) ≤ ⌊|F| / 2^R⌋`, then
for one side (the owner of `x` in the online orientation of the short-description residual edges)
there are a local rank `s < 2^(jL+1)` of `F` and an assignment rank
`r < 3 (n + 2 + max a b) 2^(a - (j+1)L)` (`b` on the column side) such that the residual-rank
decoder prints `x` from that packet and the owner's model. -/
theorem exists_rankPacket {V : Map} (hV : isOptimalConditional V) {cV : Code}
    (hcV : IsCodeFor cV V) {pA pB : BitString} {n a b R L j : ℕ}
    {TA TB : List (BitString × BitString)} (hTA : TA ∈ runTable pA n)
    (hTB : TB ∈ runTable pB n) (ha : (j + 1) * L ≤ a) (hb : (j + 1) * L ≤ b)
    {F : Finset BitString} (hF : F ∈ level (tableShape TA TB n a b) R L j) {x : BitString}
    (hxres : x ∈ residual (tableShape TA TB n a b) R L j F) {K : ℕ}
    (hK : condC V x (canonicalFiniteSetCode F) = K) (hcap : 2 ^ (K + 1) ≤ blockCap R F) :
    ∃ (side : Bool) (s r : ℕ), s < 2 ^ (j * L + 1) ∧
      r < 3 * (n + 2 + max a b) * 2 ^ ((if side then b else a) - (j + 1) * L) ∧
      x ∈ rankDecoder cV (rankPacket side n a b R L j K pA pB s r,
        sideOut (tableShape TA TB n a b) side x) := by
  set P := tableShape TA TB n a b
  set en := resEnum cV (residual P R L j F) (canonicalFiniteSetCode F) K
  have hxF : x ∈ F := (children_residual_spec P R L j F).2.2.2.1 hxres
  obtain ⟨p, hprod, hplen⟩ := Lower.exists_program_of_condC V hV x (canonicalFiniteSetCode F)
  have hpK : p.length ≤ K := by
    have h1 : (p.length : ℝ) = K := hplen.trans hK
    exact_mod_cast h1.le
  obtain ⟨s₀, hs₀⟩ := exists_mem_arrivals_resEnum hcV hxres hpK hprod
  set l := arrivals en s₀
  have hnd : l.Nodup := arrivals_nodup en s₀
  have hsound : ∀ z ∈ l, z ∈ residual P R L j F ∧ condC V z (canonicalFiniteSetCode F) ≤ K :=
    fun z hz => mem_arrivals_resEnum hcV hz
  have hsub : l.toFinset ⊆ residual P R L j F := fun z hz =>
    (hsound z (List.mem_toFinset.mp hz)).1
  have hcard : l.toFinset.card < 2 ^ (K + 1) := by
    refine Lower.card_lt_two_pow_of_condC_lt V hV (canonicalFiniteSetCode F) (K + 1) l.toFinset
      fun z hz => ?_
    have h1 := (hsound z (List.mem_toFinset.mp hz)).2
    have h2 : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by norm_num
    rw [h2]
    linarith
  have hfree : CoreFree (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) l.toFinset :=
    coreFree_of_subset_residual P R L j hsub (by omega)
  have hpos : ∀ v ∈ incidentVerts (shapeSrc P) (shapeTgt P) l.toFinset,
      0 < shapeCap P L (j + 1) v := fun v _ => shapeCap_pos P L (j + 1) v
  have hrank := rank_lt_of_orientation l hnd hpos hfree hs₀
  have hinv := (upperOnlineOrientation l hnd hpos hfree).1
  have hown := hinv.owner_mem x (List.mem_toFinset.mpr hs₀)
  have hcardn : l.toFinset.card ≤ 2 ^ n := by
    have h1 : l.toFinset ⊆ shapeEdges P :=
      hsub.trans (((children_residual_spec P R L j F).2.2.2.1).trans (level_subset P R L j F hF))
    exact (Finset.card_le_card h1).trans (card_shapeEdges_le P)
  have hW := log_sum_incidentVerts_le (src := shapeSrc P) (tgt := shapeTgt P) hcardn
    (shapeCap_le P L (j + 1))
  have hW' : 3 * (Nat.log 2 (∑ u ∈ incidentVerts (shapeSrc P) (shapeTgt P) l.toFinset,
      shapeCap P L (j + 1) u) + 1) ≤ 3 * (n + 2 + max a b) := by
    have : max P.a P.b = max a b := rfl
    omega
  have hjLa : j * L ≤ a := le_trans (Nat.mul_le_mul_right L (Nat.le_succ j)) ha
  have hjLb : j * L ≤ b := le_trans (Nat.mul_le_mul_right L (Nat.le_succ j)) hb
  rcases hown with hsrc | htgt
  · obtain ⟨s, hs, hsF⟩ := exists_localBlock_index P R L j false hjLa hjLb hF hxF
    refine ⟨false, s, (orient (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) l).rank x, hs,
      ?_, ?_⟩
    · rw [hsrc] at hrank
      have hcap' : shapeCap P L (j + 1) (shapeSrc P x) = 2 ^ (a - (j + 1) * L) := rfl
      rw [hcap'] at hrank
      exact lt_of_lt_of_le hrank (Nat.mul_le_mul_right _ hW')
    · rw [rankDecoder_spec cV false n a b R L j K pA pB s _ _ hTA hTB hs]
      unfold rankCore
      rw [hsF]
      have hend : typedEnd false (sideOut P false x) =
          (orient (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) l).owner x := by
        rw [hsrc]
        rfl
      rw [hend]
      exact upperOrientationStream en hs₀
  · obtain ⟨s, hs, hsF⟩ := exists_localBlock_index P R L j true hjLa hjLb hF hxF
    refine ⟨true, s, (orient (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) l).rank x, hs,
      ?_, ?_⟩
    · rw [htgt] at hrank
      have hcap' : shapeCap P L (j + 1) (shapeTgt P x) = 2 ^ (b - (j + 1) * L) := rfl
      rw [hcap'] at hrank
      exact lt_of_lt_of_le hrank (Nat.mul_le_mul_right _ hW')
    · rw [rankDecoder_spec cV true n a b R L j K pA pB s _ _ hTA hTB hs]
      unfold rankCore
      rw [hsF]
      have hend : typedEnd true (sideOut P true x) =
          (orient (shapeSrc P) (shapeTgt P) (shapeCap P L (j + 1)) l).owner x := by
        rw [htgt]
        rfl
      rw [hend]
      exact upperOrientationStream en hs₀

/-! ### The overhead estimates and the constant choice -/

/-- The constant `u` of `upperResidualBound` in terms of the typicality loss `b_typ`, the bucket
slack `b_size`, the literal-description slack `c_K` of `K = C(x | F) ≤ n + c_K`, and the decoder
constant `c_rank` of the residual-rank decoder. -/
def residualConst (btyp bsize cK crank : ℕ) : ℕ :=
  btyp + crank + headerLog (15 + 3 * bsize) + 4 * (2 * headerLog (2 + bsize) + headerLog cK + 3) +
    60

/-- **Header cost of the rank packet in the calibrated instance** (tex ~2694–2705):
`hdrCost [n, a, b, R, L, j, K, |p_A|, |p_B|] ≤ 9 H + ⌈log₂ (c₂ + 2)⌉ + D₁` with
`D₁ = 2 ⌈log₂ (b_size + 4)⌉ + ⌈log₂ (c_K + 2)⌉ + 3`, using `L = c₂ H`.  The field `L` costs
`⌈log₂ (c₂ + 2)⌉ + H + 1`, the other fields `O(log n)`. -/
theorem hdrCost_rank_le {n e a b R j K mA mB bsize cK c₂ : ℕ} (hen : e ≤ n) (hmA : mA ≤ e)
    (hmB : mB ≤ e) (ha : a ≤ 2 * n + bsize) (hb : b ≤ 2 * n + bsize) (hR : R ≤ n) (hj : j ≤ n)
    (hK : K ≤ n + cK) :
    hdrCost [n, a, b, R, c₂ * baseBudget n e, j, K, mA, mB] ≤
      9 * baseBudget n e + headerLog c₂ + (2 * headerLog (2 + bsize) + headerLog cK + 3) := by
  set L := c₂ * baseBudget n e with hL
  have hexp : hdrCost [n, a, b, R, L, j, K, mA, mB] = headerLog n + headerLog a + headerLog b +
      headerLog R + headerLog L + headerLog j + headerLog K + headerLog mA + headerLog mB := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hlin : ∀ x, x ≤ 2 * n + bsize → headerLog x ≤ headerLog (2 + bsize) + headerLog n + 1 := by
    intro x hx
    have h1 : x ≤ (2 + bsize) * (n + 1) := by
      have : (2 + bsize) * (n + 1) = 2 * n + 2 + bsize * n + bsize := by ring
      omega
    have h2 := headerLog_mul_le (2 + bsize) (n + 1)
    have h3 := headerLog_succ_le n
    have h4 := headerLog_mono h1
    omega
  have hA := hlin a ha
  have hB := hlin b hb
  have hRn := headerLog_mono hR
  have hjn := headerLog_mono hj
  have hmAn := headerLog_mono (hmA.trans hen)
  have hmBn := headerLog_mono (hmB.trans hen)
  have hKn := (headerLog_mono hK).trans (headerLog_add_le n cK)
  have hLc : headerLog L ≤ headerLog c₂ + baseBudget n e + 1 := by
    rw [hL]
    have h1 := headerLog_mul_le c₂ (baseBudget n e)
    have h2 := headerLog_le_add_one (baseBudget n e)
    omega
  have hnH : headerLog n ≤ baseBudget n e := Nat.le_add_left _ _
  rw [hexp]
  omega

/-- **Binary length of the assignment rank** (tex ~2668–2684): if
`r < 3 (n + 2 + max a b) 2^k` with `a, b ≤ 2n + b_size`, then
`|bits r| ≤ k + ⌈log₂ (17 + 3 b_size)⌉ + ⌈log₂ (n + 2)⌉ + 1`. -/
theorem size_rank_le {n a b k bsize r : ℕ} (ha : a ≤ 2 * n + bsize) (hb : b ≤ 2 * n + bsize)
    (hr : r < 3 * (n + 2 + max a b) * 2 ^ k) :
    (Nat.bits r).length ≤ k + headerLog (15 + 3 * bsize) + headerLog n + 1 := by
  rw [Nat.size_eq_bits_len]
  set M := 3 * (n + 2 + max a b)
  have h1 : r < 2 ^ (Nat.size M + k) := by
    rw [pow_add]
    exact lt_of_lt_of_le hr (Nat.mul_le_mul_right _ (Nat.lt_size_self M).le)
  have h2 : Nat.size r ≤ Nat.size M + k := Nat.size_le.mpr h1
  have h3 := size_le_headerLog M
  have h4 : M ≤ (15 + 3 * bsize) * (n + 1) := by
    have : (15 + 3 * bsize) * (n + 1) = 15 * n + 15 + 3 * (bsize * n) + 3 * bsize := by ring
    have hmax : max a b ≤ 2 * n + bsize := max_le ha hb
    omega
  have h5 := headerLog_mono h4
  have h6 := headerLog_mul_le (15 + 3 * bsize) (n + 1)
  have h7 := headerLog_succ_le n
  omega

/-- **The constant choice closes the contradiction** (tex ~412–420, ~2687–2720).  If the owner's
bucket `a₀` satisfies `(j+1)L ≤ a₀`, the decoder packet has the length bound of
`length_rankPacket_le` with an assignment rank `r < 3 (n + 2 + max a b) 2^(a₀ - (j+1)L)`, the
description `C ≤ |packet| + c_rank`, and typicality `a₀ - b_typ H ≤ C`, then
`c₂ > u + u ⌈log₂ (c₂ + 2)⌉` with `u = residualConst` is impossible: the leading lengths cancel to
`a₀ - L` and the remaining overhead is `(b_typ + 39) H + 4 ⌈log₂ (c₂ + 2)⌉ + O(1) < L = c₂ H`. -/
theorem residual_arith {btyp bsize cK crank c₂ n e a b a₀ R j K mA mB r P : ℕ} {C : ℝ}
    (hc₂ : residualConst btyp bsize cK crank +
      residualConst btyp bsize cK crank * headerLog c₂ < c₂)
    (hen : e ≤ n) (hmA : mA ≤ e) (hmB : mB ≤ e)
    (ha : a ≤ 2 * n + bsize) (hb : b ≤ 2 * n + bsize) (hR : R ≤ n) (hj : j ≤ n)
    (hK : K ≤ n + cK) (hjL : (j + 1) * (c₂ * baseBudget n e) ≤ a₀)
    (hr : r < 3 * (n + 2 + max a b) * 2 ^ (a₀ - (j + 1) * (c₂ * baseBudget n e)))
    (hP : P ≤ j * (c₂ * baseBudget n e) + 1 + (Nat.bits r).length + mA + mB +
      4 * hdrCost [n, a, b, R, c₂ * baseBudget n e, j, K, mA, mB] + 9)
    (hC : C ≤ P + crank) (htyp : (a₀ : ℝ) - btyp * baseBudget n e ≤ C) : False := by
  have h1 := hdrCost_rank_le (c₂ := c₂) hen hmA hmB ha hb hR hj hK
  set L := c₂ * baseBudget n e with hL
  have h2 := size_rank_le ha hb hr
  have hH1 : 1 ≤ baseBudget n e := le_trans (one_le_headerLog n) (Nat.le_add_left _ _)
  have hnH : headerLog n ≤ baseBudget n e := Nat.le_add_left _ _
  have heH : e ≤ baseBudget n e := Nat.le_add_right _ _
  have hjL' : (j + 1) * L = j * L + L := by ring
  -- the natural-number budget of the description
  have hPL : P + L ≤ a₀ + 39 * baseBudget n e + 4 * headerLog c₂ +
      (headerLog (15 + 3 * bsize) + 4 * (2 * headerLog (2 + bsize) + headerLog cK + 3) + 11) := by
    omega
  -- the constant choice: `L = c₂ H` beats the overhead
  set u := residualConst btyp bsize cK crank with hu
  have hu' : u = btyp + crank + (headerLog (15 + 3 * bsize) +
      4 * (2 * headerLog (2 + bsize) + headerLog cK + 3) + 11) + 49 := by
    rw [hu, residualConst]
    ring
  set D := headerLog (15 + 3 * bsize) + 4 * (2 * headerLog (2 + bsize) + headerLog cK + 3) + 11
  set H := baseBudget n e
  have hmul : (u + u * headerLog c₂ + 1) * H ≤ c₂ * H := Nat.mul_le_mul_right _ hc₂
  have hexp : (u + u * headerLog c₂ + 1) * H = u * H + u * headerLog c₂ * H + H := by ring
  have hf1 : u * headerLog c₂ ≤ u * headerLog c₂ * H := Nat.le_mul_of_pos_right _ hH1
  have hf2 : 4 * headerLog c₂ ≤ u * headerLog c₂ := Nat.mul_le_mul_right _ (by omega)
  have hf3 : u * H = btyp * H + 39 * H + (crank + D + 10) * H := by
    rw [hu']
    ring
  have hf4 : crank + D + 10 ≤ (crank + D + 10) * H := Nat.le_mul_of_pos_right _ hH1
  have hLbig : btyp * H + 39 * H + crank + D + 4 * headerLog c₂ + 1 ≤ L := by
    rw [hL]
    omega
  have hnat : P + crank + btyp * H + 1 ≤ a₀ := by omega
  have hreal : ((P + crank + btyp * H + 1 : ℕ) : ℝ) ≤ a₀ := by exact_mod_cast hnat
  push_cast at hreal
  linarith

/-! ### H04 -/

/-- **Residual compression (blueprint H04, `UpperResidualBound`; `lem:residual`).**  For an optimal
plain machine `V` there is a constant `u` such that for every `c₂` with `u + u ⌈log₂ (c₂ + 2)⌉ < c₂`
the following holds.  Let `n ≥ 2`, `e ≤ n`, `|x| = n`, let `A, B` be `e`-sufficient for `x`, and let
`p_A, p_B` be total witnesses of length `≤ e` producing the codes of `A, B` from `x`.  Let
`1 ≤ R ≤ n`, `H = e + ⌈log₂ (n + 2)⌉`, `L = c₂ H`, `J = ⌊n / R⌋ + 1`, `a = ⌊log₂ |A|⌋`,
`b = ⌊log₂ |B|⌋`, and assume the hierarchy branch `JL < a`, `JL < b`.  If `x` lies in the residual
of a depth-`j` block `F` of the instance's hierarchy with `j < J`, then
`log₂ |F| - C(x | F) ≤ R + 3`.

The constant `u` collects the typicality loss `u₀ = b_typ` and the packet, rank and framing
overhead `u₁ + u₂ ⌈log₂ (c₂ + 2)⌉` of the residual-rank decoder, all fixed before `c₂` (appendix
"Why choosing the large constant is not circular"). -/
theorem upperResidualBound (V : Map) (hV : isOptimalConditional V) :
    ∃ u : ℕ, ∀ c₂ : ℕ, u + u * headerLog c₂ < c₂ →
      ∀ (n e : ℕ) (x : BitString) (A B : Finset BitString) (pA pB : BitString) (R j : ℕ)
        (F : Finset BitString),
        2 ≤ n → x.length = n → e ≤ n → IsSufficientModel V x A e → IsSufficientModel V x B e →
        IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
        pA.length ≤ e → pB.length ≤ e →
        canonicalFiniteSetCode A ∈ universalDecompressor (pA, x) →
        canonicalFiniteSetCode B ∈ universalDecompressor (pB, x) →
        1 ≤ R → R ≤ n →
        (n / R + 1) * (c₂ * baseBudget n e) < Nat.log 2 A.card →
        (n / R + 1) * (c₂ * baseBudget n e) < Nat.log 2 B.card →
        j < n / R + 1 →
        F ∈ level (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) R
          (c₂ * baseBudget n e) j →
        x ∈ residual (instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)) R
          (c₂ * baseBudget n e) j F →
        Real.logb 2 F.card - condC V x (canonicalFiniteSetCode F) ≤ R + 3 := by
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨cV, hcV⟩ := Lower.exists_isCodeFor_of_isDecompressor hV.1
  obtain ⟨crank, hrank⟩ := condC_le_of_decoder V hV (rankDecoder cV) (rankDecoder_partrec cV)
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨cpl, hpl⟩ := condC_le_plainC_add V hV
  refine ⟨residualConst btyp bsize (blit + cpl) crank, fun c₂ hc₂ n e x A B pA pB R j F _ hx hen
    hA hB hpA hpB hlA hlB hAx hBx _ hRn haJ hbJ hj hF hxres => ?_⟩
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA n)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB n)
  have hag := tableShape_agreeOn (a := Nat.log 2 A.card) (b := Nat.log 2 B.card) hTA hTB
  have hlenF := length_eq_of_mem_level _ R _ j hF
  have hF' : F ∈ level (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) R
      (c₂ * baseBudget n e) j := by
    rw [level_congr hag]
    exact hF
  have hres' : x ∈ residual (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) R
      (c₂ * baseBudget n e) j F := by
    rw [(children_residual_congr hag R _ j hlenF).2]
    exact hxres
  set K := (condK V x (canonicalFiniteSetCode F)).toNat
  have hKC : condC V x (canonicalFiniteSetCode F) = K := rfl
  by_contra hcon
  have hlt : (K : ℝ) + R + 3 < Real.logb 2 F.card := by
    rw [hKC] at hcon
    linarith [not_le.mp hcon]
  have hcap := two_pow_succ_le_blockCap hlt
  have hjJ : (j + 1) * (c₂ * baseBudget n e) ≤ (n / R + 1) * (c₂ * baseBudget n e) :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨side, s, r, hs, hr, hmem⟩ := exists_rankPacket hV hcV hTA hTB
    (le_of_lt (lt_of_le_of_lt hjJ haJ)) (le_of_lt (lt_of_le_of_lt hjJ hbJ)) hF' hres' hKC hcap
  have hdesc := hrank _ _ _ hmem
  have hplen := length_rankPacket_le side n (Nat.log 2 A.card) (Nat.log 2 B.card) R
    (c₂ * baseBudget n e) j K pA pB s r hs
  have hKn : K ≤ n + (blit + cpl) := by
    have h1 := hpl x (canonicalFiniteSetCode F)
    have h2 := hlit x
    rw [hx] at h2
    have h3 : (K : ℝ) ≤ n + (blit + cpl) := by
      rw [← hKC]
      linarith
    exact_mod_cast h3
  obtain ⟨htA, haA⟩ := htyp n e x A hx hen hA
  obtain ⟨htB, haB⟩ := htyp n e x B hx hen hB
  have hjn : j ≤ n := by
    have := Nat.div_le_self n R
    omega
  cases side
  · have hw : sideOut (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) false x =
        canonicalFiniteSetCode A := by
      change tableOut TA x = _
      rw [tableOut_of_mem_runTable hTA hx, progOut_eq_of_mem hAx]
    rw [hw] at hdesc
    exact residual_arith hc₂ hen hlA hlB haA haB hRn hjn hKn
      (le_of_lt (lt_of_le_of_lt hjJ haJ)) hr hplen hdesc htA
  · have hw : sideOut (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) true x =
        canonicalFiniteSetCode B := by
      change tableOut TB x = _
      rw [tableOut_of_mem_runTable hTB hx, progOut_eq_of_mem hBx]
    rw [hw] at hdesc
    exact residual_arith hc₂ hen hlA hlB haA haB hRn hjn hKn
      (le_of_lt (lt_of_le_of_lt hjJ hbJ)) hr hplen hdesc htB

end Kolmogorov.StrongMerging.Upper
