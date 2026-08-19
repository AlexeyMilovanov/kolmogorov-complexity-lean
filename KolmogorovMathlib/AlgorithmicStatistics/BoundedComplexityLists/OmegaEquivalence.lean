import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.EnumerationTail

/-!
# VS40 Section 4, Milestone B4: finite Omega equivalence (`prop:omega-equivalence`)

The source considers `Ω_m` as a bit string (of length `m + O(1)`), and its first
`k` bits `(Ω_m)_k`.  With the high-bit-first fixed-width encoding
`omegaFixedCode c m = fixedWidthNatCode (omegaCount c m) (m + 1)`, the "first `k`
bits" are literally `(omegaFixedCode c m).take k`.

This file develops the *exact* arithmetic bridge between a high-bit prefix and
the underlying number: taking the top `k` bits of a width-`width` code and
decoding yields exactly `n / 2 ^ (width - k)`, i.e. the number `n` truncated to
its high `k` bits.  Consequently the prefix pins `n` down to an interval of
width `2 ^ (width - k)`.  This is precisely the quantitative content the
`prop:omega-equivalence` reconstructions rely on (knowing `(Ω_m)_k` determines
`Ω_m` with error `< 2 ^ (m + 1 - k)`).
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### `bitsToNat` and low-order truncation

`bitsToNat` reads a little-endian bit list, so dropping the first `j` entries
(the `j` low-order bits) divides the value by `2 ^ j`. -/

/-- Dropping the least significant bit halves the little-endian value. -/
theorem bitsToNat_tail (l : List Bool) :
    bitsToNat l.tail = bitsToNat l / 2 := by
  cases l with
  | nil => simp [bitsToNat]
  | cons b rest =>
    simp only [List.tail_cons]
    rw [show bitsToNat (b :: rest) =
        2 * bitsToNat rest + (if b then 1 else 0) from rfl]
    rw [Nat.mul_add_div (by norm_num)]
    cases b <;> simp

/-- Dropping the `j` least significant bits divides the little-endian value by
`2 ^ j`. -/
theorem bitsToNat_drop (l : List Bool) (j : ℕ) :
    bitsToNat (l.drop j) = bitsToNat l / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← List.tail_drop, bitsToNat_tail, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Reading a little-endian `cons` peels one low bit: `bitsToNat (b :: l)` is the
`Nat.bit` recombination of `b` with `bitsToNat l`. -/
theorem bitsToNat_cons (b : Bool) (rest : List Bool) :
    bitsToNat (b :: rest) = Nat.bit b (bitsToNat rest) := by
  simp only [bitsToNat, List.foldr_cons]
  rw [show (rest).foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0
        = bitsToNat rest from rfl, Nat.bit_val]
  cases b <;> simp

/-- Any little-endian bit list equals `Nat.bits` of its value padded with
high-order zeros back to its original length.  In other words, `Nat.bits`
recovers a bit list up to (and including) trailing zeros, which the padding
restores.  This makes fixed-width decoding invertible on codes of a fixed
length. -/
theorem bits_bitsToNat_append (w : List Bool) :
    Nat.bits (bitsToNat w) ++
      List.replicate (w.length - (Nat.bits (bitsToNat w)).length) false = w := by
  induction w with
  | nil => simp [bitsToNat, Nat.zero_bits]
  | cons b rest ih =>
    rw [bitsToNat_cons]
    by_cases hz : bitsToNat rest = 0 ∧ b = false
    · obtain ⟨hr, hb⟩ := hz
      subst hb
      have hrest : rest = List.replicate rest.length false := by
        rw [hr, Nat.zero_bits] at ih
        simpa using ih.symm
      rw [hr]
      simp only [Nat.bit_false, Nat.mul_zero, Nat.zero_bits, List.nil_append,
        List.length_nil, Nat.sub_zero, List.length_cons]
      rw [List.replicate_succ, ← hrest]
    · push Not at hz
      have hbtrue : bitsToNat rest = 0 → b = true := by
        intro h0; cases b <;> simp_all
      have hbits : (Nat.bit b (bitsToNat rest)).bits = b :: (bitsToNat rest).bits :=
        Nat.bits_append_bit _ _ hbtrue
      rw [hbits, List.cons_append]
      simp only [List.length_cons, Nat.add_sub_add_right, ih]

/-! ### High-bit prefixes of the fixed-width code -/

/-- Fixed-width encoding is primitive recursive uniformly in the value and
width.  This is used by both executable B4 reconstruction directions. -/
theorem fixedWidthNatCode_primrec :
    Primrec (fun p : ℕ × ℕ => fixedWidthNatCode p.1 p.2) := by
  have hbits : Primrec (fun p : ℕ × ℕ => Nat.bits p.1) :=
    primrecNatBits.comp Primrec.fst
  have hpadLength : Primrec (fun p : ℕ × ℕ =>
      p.2 - (Nat.bits p.1).length) :=
    Primrec.nat_sub.comp Primrec.snd
      (Primrec.list_length.comp hbits)
  have hpadding : Primrec (fun p : ℕ × ℕ =>
      List.replicate (p.2 - (Nat.bits p.1).length) false) :=
    Primrec.list_replicate.comp hpadLength (Primrec.const false)
  unfold fixedWidthNatCode chunkAddress
  exact Primrec.list_reverse.comp
    (Primrec.list_append.comp hbits hpadding)

/-- **The high `k` bits of a width-`width` code decode to `n / 2 ^ (width - k)`.**
Since `fixedWidthNatCode` is high-bit-first, `take k` keeps the `k` most
significant bits; decoding recovers `n` truncated to those bits.  (No `k ≤ width`
hypothesis is needed: for `k ≥ width` the prefix is the whole code and
`width - k = 0`, so both sides equal `n`.) -/
theorem decodeFixedWidthNatCode_take
    {n width : ℕ} (hn : n < 2 ^ width) (k : ℕ) :
    decodeFixedWidthNatCode ((fixedWidthNatCode n width).take k)
      = n / 2 ^ (width - k) := by
  unfold decodeFixedWidthNatCode fixedWidthNatCode
  rw [List.reverse_take, List.reverse_reverse]
  rw [List.length_reverse, chunkAddress_length _ _ hn, bitsToNat_drop,
    bitsToNat_chunkAddress]

/-- **Interval bracket from a high-bit prefix.**  Reading the top `k` bits of the
width-`width` code of `n` pins `n` down to the dyadic interval
`[p · 2 ^ (width - k), (p + 1) · 2 ^ (width - k))`, where `p` is the decoded
prefix value.  This is the exact form of "knowing `(Ω_m)_k` determines `Ω_m` with
error `< 2 ^ (width - k)`". -/
theorem fixedWidthNatCode_take_interval
    {n width : ℕ} (hn : n < 2 ^ width) (k : ℕ) :
    decodeFixedWidthNatCode ((fixedWidthNatCode n width).take k) *
        2 ^ (width - k) ≤ n ∧
      n < (decodeFixedWidthNatCode ((fixedWidthNatCode n width).take k) + 1) *
        2 ^ (width - k) := by
  rw [decodeFixedWidthNatCode_take hn k]
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm]
    exact Nat.mul_div_le n (2 ^ (width - k))
  · have hdm := Nat.div_add_mod n (2 ^ (width - k))
    have hmod : n % 2 ^ (width - k) < 2 ^ (width - k) :=
      Nat.mod_lt _ (by positivity)
    calc
      n = 2 ^ (width - k) * (n / 2 ^ (width - k)) + n % 2 ^ (width - k) := hdm.symm
      _ < 2 ^ (width - k) * (n / 2 ^ (width - k)) + 2 ^ (width - k) := by omega
      _ = (n / 2 ^ (width - k) + 1) * 2 ^ (width - k) := by ring

/-- The high `k` bits of `omegaFixedCode c m` decode to `Ω_m` truncated to those
bits: `Ω_m / 2 ^ (m + 1 - k)`.  This is the well-defined value of `(Ω_m)_k`. -/
theorem decode_take_omegaFixedCode
    (c : Code) (m k : ℕ) :
    decodeFixedWidthNatCode ((omegaFixedCode c m).take k)
      = omegaCount c m / 2 ^ (m + 1 - k) := by
  unfold omegaFixedCode
  exact decodeFixedWidthNatCode_take (omegaCount_lt_two_pow_succ c m) k

/-! ### The high-bit prefix as a genuine fixed-width code

To phrase `prop:omega-equivalence` about the literal string `(Ω_m)_k` and let a
reconstruction *emit* it, we need the prefix to equal the fixed-width code of its
own value.  This rests on the fact that fixed-width decoding is invertible on
codes of a fixed length. -/

/-- `chunkAddress (bitsToNat w) |w| = w`: padding the significant `Nat.bits` back
to the original length reproduces `w`. -/
theorem chunkAddress_bitsToNat (w : List Bool) :
    chunkAddress (bitsToNat w) w.length = w := by
  unfold chunkAddress
  exact bits_bitsToNat_append w

/-- Fixed-width decoding is invertible: re-encoding the decoded value at the
*same length* recovers the original code. -/
theorem fixedWidthNatCode_decode_length (z : BitString) :
    fixedWidthNatCode (decodeFixedWidthNatCode z) z.length = z := by
  unfold fixedWidthNatCode decodeFixedWidthNatCode
  have hlen : z.length = z.reverse.length := by rw [List.length_reverse]
  rw [hlen, chunkAddress_bitsToNat z.reverse, List.reverse_reverse]

/-- **The high-bit prefix is itself a fixed-width code.**  For `k ≤ width` the top
`k` bits of the width-`width` code of `n` are exactly the width-`k` code of the
truncated value `n / 2 ^ (width - k)`.  This is what lets a reconstruction that
has computed the truncated value emit the literal prefix string. -/
theorem fixedWidthNatCode_take_eq
    {n width : ℕ} (hn : n < 2 ^ width) {k : ℕ} (hk : k ≤ width) :
    (fixedWidthNatCode n width).take k = fixedWidthNatCode (n / 2 ^ (width - k)) k := by
  have hz_len : ((fixedWidthNatCode n width).take k).length = k := by
    rw [List.length_take, fixedWidthNatCode_length hn, Nat.min_eq_left hk]
  have hdec : decodeFixedWidthNatCode ((fixedWidthNatCode n width).take k)
      = n / 2 ^ (width - k) := decodeFixedWidthNatCode_take hn k
  calc (fixedWidthNatCode n width).take k
      = fixedWidthNatCode
          (decodeFixedWidthNatCode ((fixedWidthNatCode n width).take k))
          ((fixedWidthNatCode n width).take k).length :=
        (fixedWidthNatCode_decode_length _).symm
    _ = fixedWidthNatCode (n / 2 ^ (width - k)) k := by rw [hdec, hz_len]

/-- `(Ω_m)_k`, the first `k` bits of `Ω_m`, is the width-`k` fixed code of the
truncated count `Ω_m / 2 ^ (m + 1 - k)` (for `k ≤ m + 1`). -/
theorem omegaFixedCode_take_eq
    (c : Code) (m : ℕ) {k : ℕ} (hk : k ≤ m + 1) :
    (omegaFixedCode c m).take k
      = fixedWidthNatCode (omegaCount c m / 2 ^ (m + 1 - k)) k := by
  unfold omegaFixedCode
  exact fixedWidthNatCode_take_eq (omegaCount_lt_two_pow_succ c m) hk

/-! ### The reverse-direction prefix offset

At time `B'(k)`, let `L` be the number of bound-`m` outputs already seen.  The
top-`k` values of `Ω_m` and `L` differ by at most the tail divided by the width
of one top-prefix interval, plus one for a possible division carry.  The B3
upper-tail theorem then makes this offset logarithmically describable. -/

/-- Dyadic cutoff arithmetic for the forward-direction interval bound. -/
theorem lt_mul_of_lt_succ_mul_of_two_mul_le_sub
    (omega stage pre quantum : ℕ)
    (hstage : stage ≤ omega)
    (homega : omega < (pre + 1) * quantum)
    (htail : 2 * quantum ≤ omega - stage) :
    stage < pre * quantum := by
  have h1 : (pre + 1) * quantum = pre * quantum + quantum := by ring
  omega

/-- Division changes a difference by at most the divided difference plus one.
This is the carry estimate used when comparing the high-bit prefixes of two
nearby natural numbers. -/
theorem div_sub_div_le_add_one
    (a b c : ℕ) (hbc : b ≤ a) (hc : 0 < c) :
    a / c - b / c ≤ (a - b) / c + 1 := by
  have hadd : a = b + (a - b) := by omega
  have hle :
      (b + (a - b)) / c ≤ b / c + (a - b) / c + 1 := by
    rw [Nat.add_div hc]
    split <;> omega
  rw [hadd, Nat.add_sub_cancel_left]
  rw [Nat.sub_le_iff_le_add']
  simpa [Nat.add_assoc] using hle

/-- Dividing a number bounded by `2^(a+ell)` by `2^(a+1)` leaves at most
`2^ell`. -/
theorem div_pow_succ_le_pow_of_le_pow_add
    {a ell tail : ℕ} (htail : tail ≤ 2 ^ (a + ell)) :
    tail / 2 ^ (a + 1) ≤ 2 ^ ell := by
  rw [Nat.div_le_iff_le_mul (by positivity)]
  calc
    tail ≤ 2 ^ (a + ell) := htail
    _ ≤ 2 ^ ell * 2 ^ (a + 1) := by
      rw [pow_add, pow_succ]
      nlinarith [Nat.zero_le (2 ^ a), Nat.zero_le (2 ^ ell)]
    _ ≤ 2 ^ ell * 2 ^ (a + 1) + 2 ^ (a + 1) - 1 := by
      have hq : 0 < 2 ^ (a + 1) := by positivity
      omega

/-- Exact quotient-offset bound at the lower completion stage.  The difference
between the top-`k` quotient of the final count and the top-`k` quotient of the
current stage length is controlled by the exact B3 tail count. -/
theorem omegaPrefix_stage_offset_le_tail_div
    (c : Code) (m k : ℕ) (hk : k ≤ m) :
    omegaCount c m / 2 ^ (m + 1 - k) -
        (boundedOutputStage c m
          (boundedOutputCompletionTime c k)).length /
            2 ^ (m + 1 - k) ≤
      enumerationTailCount c m (m - k) /
          2 ^ (m + 1 - k) + 1 := by
  let stageLength :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c k)).length
  have hsum :
      stageLength + enumerationTailCount c m (m - k) =
        omegaCount c m := by
    have hsubsub : m - (m - k) = k := by omega
    simpa [stageLength, hsubsub] using
      stageLength_add_enumerationTailCount c m (m - k)
  have hstage : stageLength ≤ omegaCount c m := by omega
  have hsub :
      omegaCount c m - stageLength =
        enumerationTailCount c m (m - k) := by omega
  simpa [stageLength, hsub] using
    div_sub_div_le_add_one
      (omegaCount c m) stageLength (2 ^ (m + 1 - k))
      hstage (by positivity)

/-- Uniform logarithmic bound for the reverse reconstruction's numeric offset.
This is the quantitative leaf needed to encode `(Ω_m)_k` from `Ω_k`: after
running the bound-`m` enumeration for `B'(k)` stages, its high-prefix quotient
is within `2^O(log m) + 1` of the final high-prefix quotient. -/
theorem omegaPrefix_stage_offset_upper_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      omegaCount c m / 2 ^ (m + 1 - k) -
          (boundedOutputStage c m
            (boundedOutputCompletionTime c k)).length /
              2 ^ (m + 1 - k) ≤
        2 ^ logSlack C m + 1 := by
  obtain ⟨C, hC⟩ := enumerationTailCount_upper_bound V hV c hc
  refine ⟨C, fun m k hk => ?_⟩
  have hoffset :=
    omegaPrefix_stage_offset_le_tail_div c m k hk
  have htail :
      enumerationTailCount c m (m - k) ≤
        2 ^ ((m - k) + logSlack C m) :=
    hC m (m - k) (Nat.sub_le _ _)
  have hexp : m + 1 - k = (m - k) + 1 := by omega
  have hquot :
      enumerationTailCount c m (m - k) /
          2 ^ (m + 1 - k) ≤
        2 ^ logSlack C m := by
    rw [hexp]
    exact div_pow_succ_le_pow_of_le_pow_add htail
  omega

/-! ### Executable reverse reconstruction

The condition supplies `Ω_k`.  The advice supplies `m` and the small quotient
offset bounded above.  From `Ω_k` the selector recovers `B'(k)`, runs the
bound-`m` enumeration to that stage, adds the advised offset to the observed
high-prefix quotient, and emits the literal `k`-bit prefix. -/

def omegaPrefixReverseAdvice
    (m offset offsetWidth : ℕ) : BitString :=
  pairCode (Nat.bits m) (fixedWidthNatCode offset offsetWidth)

def omegaPrefixReverseM (p : BitString) : ℕ :=
  bitsToNat (decodeFirst p)

def omegaPrefixReverseOffset (p : BitString) : ℕ :=
  decodeFixedWidthNatCode (decodeSecond p)

@[simp] theorem omegaPrefixReverseM_advice
    (m offset offsetWidth : ℕ) :
    omegaPrefixReverseM
      (omegaPrefixReverseAdvice m offset offsetWidth) = m := by
  unfold omegaPrefixReverseM omegaPrefixReverseAdvice
  rw [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem omegaPrefixReverseOffset_advice
    (m offset offsetWidth : ℕ) :
    omegaPrefixReverseOffset
      (omegaPrefixReverseAdvice m offset offsetWidth) = offset := by
  unfold omegaPrefixReverseOffset omegaPrefixReverseAdvice
  rw [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]

theorem omegaPrefixReverseAdvice_length
    {m offset offsetWidth : ℕ}
    (hoffset : offset < 2 ^ offsetWidth) :
    (omegaPrefixReverseAdvice m offset offsetWidth).length =
      2 * (Nat.bits m).length + offsetWidth + 1 := by
  unfold omegaPrefixReverseAdvice
  rw [length_pairCode, fixedWidthNatCode_length hoffset]
  omega

/-- Partial reverse reconstruction from condition `Ω_k` and advice `(m,δ)`. -/
noncomputable def omegaPrefixReverseSelector
    (c : Code) (y p : BitString) : Part BitString := do
  let tBits ← completionFromOmega c y
  let m := omegaPrefixReverseM p
  let k := y.length - 1
  let divisor := 2 ^ (m + 1 - k)
  let base :=
    (boundedOutputStage c m (bitsToNat tBits)).length / divisor
  Part.some
    (fixedWidthNatCode (base + omegaPrefixReverseOffset p) k)

theorem omegaPrefixReverseM_primrec :
    Primrec omegaPrefixReverseM := by
  exact bitsToNat_primrec.comp decodeFirst_primrec'

theorem omegaPrefixReverseOffset_primrec :
    Primrec omegaPrefixReverseOffset := by
  exact decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec'

theorem omegaPrefixReverseSelector_partrec
    (c : Code) :
    Partrec (fun q : BitString × BitString =>
      omegaPrefixReverseSelector c q.1 q.2) := by
  have hcompletion : Partrec (fun q : BitString × BitString =>
      completionFromOmega c q.1) :=
    (completionFromOmega_partrec c).comp Computable.fst
  have hm : Primrec
      (fun q : (BitString × BitString) × BitString =>
        omegaPrefixReverseM q.1.2) :=
    omegaPrefixReverseM_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have hk : Primrec
      (fun q : (BitString × BitString) × BitString =>
        q.1.1.length - 1) :=
    Primrec.nat_sub.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 1)
  have ht : Primrec
      (fun q : (BitString × BitString) × BitString =>
        bitsToNat q.2) :=
    bitsToNat_primrec.comp Primrec.snd
  have hstage : Primrec
      (fun q : (BitString × BitString) × BitString =>
        boundedOutputStage c
          (omegaPrefixReverseM q.1.2) (bitsToNat q.2)) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hm ht)
  have hdivisor : Primrec
      (fun q : (BitString × BitString) × BitString =>
        2 ^ (omegaPrefixReverseM q.1.2 + 1 -
          (q.1.1.length - 1))) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_add.comp hm (Primrec.const 1)) hk)
  have hbase : Primrec
      (fun q : (BitString × BitString) × BitString =>
        (boundedOutputStage c
          (omegaPrefixReverseM q.1.2) (bitsToNat q.2)).length /
            2 ^ (omegaPrefixReverseM q.1.2 + 1 -
              (q.1.1.length - 1))) :=
    Primrec.nat_div.comp
      (Primrec.list_length.comp hstage) hdivisor
  have hoffset : Primrec
      (fun q : (BitString × BitString) × BitString =>
        omegaPrefixReverseOffset q.1.2) :=
    omegaPrefixReverseOffset_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have hvalue : Primrec
      (fun q : (BitString × BitString) × BitString =>
        (boundedOutputStage c
          (omegaPrefixReverseM q.1.2) (bitsToNat q.2)).length /
            2 ^ (omegaPrefixReverseM q.1.2 + 1 -
              (q.1.1.length - 1)) +
          omegaPrefixReverseOffset q.1.2) :=
    Primrec.nat_add.comp hbase hoffset
  have hbody : Computable₂
      (fun (q : BitString × BitString) (tBits : BitString) =>
        fixedWidthNatCode
          ((boundedOutputStage c
            (omegaPrefixReverseM q.2) (bitsToNat tBits)).length /
              2 ^ (omegaPrefixReverseM q.2 + 1 -
                (q.1.length - 1)) +
            omegaPrefixReverseOffset q.2)
          (q.1.length - 1)) :=
    (fixedWidthNatCode_primrec.comp
      (Primrec.pair hvalue hk)).to_comp.to₂
  unfold omegaPrefixReverseSelector
  exact (Partrec.bind hcompletion hbody.partrec₂).of_eq
    (fun _ => rfl)

/-- On the intended advice, the reverse selector emits the literal prefix
`(Ω_m)_k`.  No size bound is needed for correctness; the offset bound above is
used only to charge the advice length. -/
theorem omegaPrefixReverseSelector_intended_input
    (c : Code) (m k offsetWidth : ℕ) (hk : k ≤ m) :
    let divisor := 2 ^ (m + 1 - k)
    let stageLength :=
      (boundedOutputStage c m
        (boundedOutputCompletionTime c k)).length
    let offset :=
      omegaCount c m / divisor - stageLength / divisor
    (omegaFixedCode c m).take k ∈
      omegaPrefixReverseSelector c (omegaFixedCode c k)
        (omegaPrefixReverseAdvice m offset offsetWidth) := by
  dsimp only
  let divisor := 2 ^ (m + 1 - k)
  let stageLength :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c k)).length
  have hstage : stageLength ≤ omegaCount c m := by
    exact (boundedOutputStage_prefix_completed c m
      (boundedOutputCompletionTime c k)).length_le
  have hdiv :
      stageLength / divisor ≤ omegaCount c m / divisor :=
    Nat.div_le_div_right hstage
  have hvalue :
      stageLength / divisor +
          (omegaCount c m / divisor - stageLength / divisor) =
        omegaCount c m / divisor :=
    Nat.add_sub_of_le hdiv
  unfold omegaPrefixReverseSelector
  simp only [omegaPrefixReverseM_advice,
    omegaPrefixReverseOffset_advice, omegaFixedCode_length,
    Nat.add_sub_cancel_right]
  change (omegaFixedCode c m).take k ∈
    (completionFromOmega c (omegaFixedCode c k)).bind
      (fun tBits => Part.some
        (fixedWidthNatCode
          ((boundedOutputStage c m (bitsToNat tBits)).length /
              2 ^ (m + 1 - k) +
            (omegaCount c m / 2 ^ (m + 1 - k) -
              (boundedOutputStage c m
                (boundedOutputCompletionTime c k)).length /
                  2 ^ (m + 1 - k)))
          k))
  rw [Part.mem_bind_iff]
  refine ⟨Nat.bits (boundedOutputCompletionTime c k),
    completionFromOmega_omegaFixedCode c k, ?_⟩
  simp only [bitsToNat_bits]
  rw [show
    (boundedOutputStage c m
      (boundedOutputCompletionTime c k)).length = stageLength by rfl,
    show 2 ^ (m + 1 - k) = divisor by rfl, hvalue]
  rw [← omegaFixedCode_take_eq c m (show k ≤ m + 1 by omega)]
  exact Part.mem_some _

/-! ### Executable forward reconstruction

The condition supplies `(Ω_m)_k`. The advice supplies `m` and the small number of
still-missing bound-`k` outputs at the threshold stage. -/

def omegaPrefixForwardAdvice
    (m delta deltaWidth : ℕ) : BitString :=
  pairCode (Nat.bits m) (fixedWidthNatCode delta deltaWidth)

def omegaPrefixForwardM (p : BitString) : ℕ :=
  bitsToNat (decodeFirst p)

def omegaPrefixForwardDelta (p : BitString) : ℕ :=
  decodeFixedWidthNatCode (decodeSecond p)

@[simp] theorem omegaPrefixForwardM_advice
    (m delta deltaWidth : ℕ) :
    omegaPrefixForwardM
      (omegaPrefixForwardAdvice m delta deltaWidth) = m := by
  unfold omegaPrefixForwardM omegaPrefixForwardAdvice
  rw [decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem omegaPrefixForwardDelta_advice
    (m delta deltaWidth : ℕ) :
    omegaPrefixForwardDelta
      (omegaPrefixForwardAdvice m delta deltaWidth) = delta := by
  unfold omegaPrefixForwardDelta omegaPrefixForwardAdvice
  rw [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]

theorem omegaPrefixForwardAdvice_length
    {m delta deltaWidth : ℕ}
    (hdelta : delta < 2 ^ deltaWidth) :
    (omegaPrefixForwardAdvice m delta deltaWidth).length =
      2 * (Nat.bits m).length + deltaWidth + 1 := by
  unfold omegaPrefixForwardAdvice
  rw [length_pairCode, fixedWidthNatCode_length hdelta]
  omega

noncomputable def omegaPrefixForwardSelector
    (c : Code) (_Ctail : ℕ) (y p : BitString) : Part BitString := do
  let m := omegaPrefixForwardM p
  let delta := omegaPrefixForwardDelta p
  let k := y.length
  let base := decodeFixedWidthNatCode y
  let quantum := 2 ^ (m - k)
  let threshold := base * (2 * quantum)
  let t ← Nat.rfind (fun t => Part.some
    (decide (threshold ≤ (boundedOutputStage c m t).length)))
  let stageLength_k := (boundedOutputStage c k t).length
  let finalLength_k := stageLength_k + delta
  Part.some (fixedWidthNatCode finalLength_k (k + 1))

theorem omegaPrefixForwardM_primrec :
    Primrec omegaPrefixForwardM := by
  exact bitsToNat_primrec.comp decodeFirst_primrec'

theorem omegaPrefixForwardDelta_primrec :
    Primrec omegaPrefixForwardDelta := by
  exact decodeFixedWidthNatCode_primrec.comp decodeSecond_primrec'

theorem omegaPrefixForwardSelector_partrec
    (c : Code) (_Ctail : ℕ) :
    Partrec (fun q : BitString × BitString =>
      omegaPrefixForwardSelector c _Ctail q.2 q.1) := by
  have hm : Primrec (fun q : (BitString × BitString) =>
      omegaPrefixForwardM q.1) :=
    omegaPrefixForwardM_primrec.comp Primrec.fst
  have hdelta : Primrec (fun q : (BitString × BitString) =>
      omegaPrefixForwardDelta q.1) :=
    omegaPrefixForwardDelta_primrec.comp Primrec.fst
  have hk : Primrec (fun q : (BitString × BitString) =>
      q.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have hbase : Primrec (fun q : (BitString × BitString) =>
      decodeFixedWidthNatCode q.2) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.snd
  have hquantum : Primrec (fun q : (BitString × BitString) =>
      2 ^ (omegaPrefixForwardM q.1 - q.2.length)) :=
    Kolmogorov.CodedFiniteDistribution.twoPow_primrec.comp
      (Primrec.nat_sub.comp hm hk)
  have hthreshold : Primrec (fun q : (BitString × BitString) =>
      decodeFixedWidthNatCode q.2 *
        (2 * 2 ^ (omegaPrefixForwardM q.1 - q.2.length))) :=
    Primrec.nat_mul.comp hbase
      (Primrec.nat_mul.comp (Primrec.const 2) hquantum)
  have hstage : Primrec (fun q : (BitString × BitString) × ℕ =>
      boundedOutputStage c (omegaPrefixForwardM q.1.1) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair (hm.comp Primrec.fst) Primrec.snd)
  have hcheck : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      decide
        (decodeFixedWidthNatCode q.2 *
            (2 * 2 ^ (omegaPrefixForwardM q.1 - q.2.length)) ≤
          (boundedOutputStage c (omegaPrefixForwardM q.1) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp (hthreshold.comp Primrec.fst)
        (Primrec.list_length.comp hstage))).to_comp.to₂
  have hsearch : Partrec (fun q : BitString × BitString =>
      Nat.rfind (fun t => Part.some
        (decide
          (decodeFixedWidthNatCode q.2 *
              (2 * 2 ^ (omegaPrefixForwardM q.1 - q.2.length)) ≤
            (boundedOutputStage c (omegaPrefixForwardM q.1) t).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hpost : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
      fixedWidthNatCode
        ((boundedOutputStage c q.2.length t).length +
          omegaPrefixForwardDelta q.1)
        (q.2.length + 1)) := by
    have hstage_k : Primrec (fun q : (BitString × BitString) × ℕ =>
        boundedOutputStage c q.1.2.length q.2) :=
      (boundedOutputStage_primrec c).comp
        (Primrec.pair (hk.comp Primrec.fst) Primrec.snd)
    have hfinal : Primrec (fun q : (BitString × BitString) × ℕ =>
        (boundedOutputStage c q.1.2.length q.2).length +
          omegaPrefixForwardDelta q.1.1) :=
      Primrec.nat_add.comp (Primrec.list_length.comp hstage_k)
        (hdelta.comp Primrec.fst)
    have hwidth : Primrec (fun q : (BitString × BitString) × ℕ =>
        q.1.2.length + 1) :=
      Primrec.nat_add.comp (hk.comp Primrec.fst) (Primrec.const 1)
    exact (fixedWidthNatCode_primrec.comp (Primrec.pair hfinal hwidth)).to_comp.to₂
  unfold omegaPrefixForwardSelector
  exact (Partrec.bind hsearch hpost.partrec₂).of_eq (fun _ => rfl)

theorem omegaPrefixForwardSelector_intended_input
    (c : Code) (Ctail m k deltaWidth : ℕ) (hk : k ≤ m) :
    let y := (omegaFixedCode c m).take k
    let base := decodeFixedWidthNatCode y
    let quantum := 2 ^ (m - k)
    let threshold := base * (2 * quantum)
    let hex : ∃ t, threshold ≤ (boundedOutputStage c m t).length :=
      ⟨boundedOutputCompletionTime c m, by
        rw [show
          (boundedOutputStage c m
            (boundedOutputCompletionTime c m)).length =
              omegaCount c m by
          simpa [omegaCount] using boundedOutputCompletionTime_spec c m]
        have h_int := fixedWidthNatCode_take_interval (omegaCount_lt_two_pow_succ c m) k
        have h2 : 2 ^ (m + 1 - k) = 2 * 2 ^ (m - k) := by
          have heq : m + 1 - k = m - k + 1 := by omega
          rw [heq, pow_succ, Nat.mul_comm]
        rw [h2] at h_int
        exact h_int.1⟩
    let t := Nat.find hex
    let delta := omegaCount c k - (boundedOutputStage c k t).length
    omegaFixedCode c k ∈
      omegaPrefixForwardSelector c Ctail
        ((omegaFixedCode c m).take k)
        (omegaPrefixForwardAdvice m delta deltaWidth) := by
  intro y base quantum threshold hex t delta
  unfold omegaPrefixForwardSelector
  simp only [omegaPrefixForwardM_advice, omegaPrefixForwardDelta_advice, List.length_take,
    omegaFixedCode_length, Nat.min_eq_left (by omega : k ≤ m + 1)]
  change omegaFixedCode c k ∈
    (Nat.rfind (fun t' => Part.some
      (decide (base * (2 * quantum) ≤ (boundedOutputStage c m t').length)))).bind
        (fun t' => Part.some
          (fixedWidthNatCode ((boundedOutputStage c k t').length + delta) (k + 1)))
  rw [Part.mem_bind_iff]
  refine ⟨t, ?_, ?_⟩
  · rw [Nat.mem_rfind]
    refine ⟨by simpa using Nat.find_spec hex, ?_⟩
    intro n hn
    have hnot := Nat.find_min hex hn
    simpa using hnot
  · have h_delta_add :
        (boundedOutputStage c k t).length + delta =
          omegaCount c k := by
      change (boundedOutputStage c k t).length +
        (omegaCount c k -
          (boundedOutputStage c k t).length) = omegaCount c k
      exact Nat.add_sub_of_le ((boundedOutputStage_prefix_completed c k t).length_le)
    rw [h_delta_add]
    change omegaFixedCode c k ∈ Part.some (omegaFixedCode c k)
    exact Part.mem_some _

/-- At the first stage where the bound-`m` enumeration reaches the dyadic
threshold determined by `(Ω_m)_k`, only `2^O(log m)` bound-`k` outputs remain.

For `k` larger than the logarithmic margin, the B3 lower bound shows that this
threshold stage is after `B'(k-O(log m))`; the B3 upper bound then controls the
remaining bound-`k` outputs.  Small `k` is handled directly by
`Ω_k < 2^(k+1)`. -/
theorem omegaPrefixForward_delta_upper_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ Ctail : ℕ, ∀ (m k : ℕ), k ≤ m →
      ∀ hex : ∃ t,
        decodeFixedWidthNatCode ((omegaFixedCode c m).take k) *
            (2 * 2 ^ (m - k)) ≤
          (boundedOutputStage c m t).length,
        let t := Nat.find hex
        let delta :=
          omegaCount c k - (boundedOutputStage c k t).length
        delta < 2 ^ (2 * logSlack Ctail m + 3) := by
  obtain ⟨Ctail, htail⟩ :=
    prop_enumeration_tail V hV c hc
  refine ⟨Ctail, fun m k hk hex => ?_⟩
  let t := Nat.find hex
  let slack := logSlack Ctail m
  let margin := slack + 2
  change omegaCount c k - (boundedOutputStage c k t).length <
    2 ^ (2 * logSlack Ctail m + 3)
  by_cases hmargin : margin ≤ k
  · let r := k - margin
    let s := m - r
    have hrk : r ≤ k := by
      dsimp [r]
      omega
    have hrm : r ≤ m := hrk.trans hk
    have hsle : s ≤ m := by
      dsimp [s]
      exact Nat.sub_le _ _
    have hms : m - s = r := by
      dsimp [s]
      omega
    have hsub :
        s - logSlack Ctail m = m - k + 2 := by
      dsimp [s, r, margin, slack]
      omega
    have hslack : logSlack Ctail m ≤ s := by
      dsimp [s, r, margin, slack]
      omega
    have hlower :
        2 ^ (m - k + 2) ≤ enumerationTailCount c m s := by
      have h := (htail m s hsle).1 hslack
      rwa [hsub] at h
    let lowerStage :=
      (boundedOutputStage c m
        (boundedOutputCompletionTime c r)).length
    have hsum :
        lowerStage + enumerationTailCount c m s =
          omegaCount c m := by
      simpa [lowerStage, hms] using
        stageLength_add_enumerationTailCount c m s
    have hstage : lowerStage ≤ omegaCount c m := by
      omega
    have hdiff :
        omegaCount c m - lowerStage =
          enumerationTailCount c m s := by
      omega
    let base :=
      decodeFixedWidthNatCode ((omegaFixedCode c m).take k)
    let quantum := 2 * 2 ^ (m - k)
    have hquantum :
        2 ^ (m + 1 - k) = quantum := by
      dsimp [quantum]
      have heq : m + 1 - k = m - k + 1 := by omega
      rw [heq, pow_succ, Nat.mul_comm]
    have homega :
        omegaCount c m < (base + 1) * quantum := by
      have hinterval :=
        fixedWidthNatCode_take_interval
          (omegaCount_lt_two_pow_succ c m) k
      simpa [omegaFixedCode, base, hquantum] using hinterval.2
    have htwoQuantum :
        2 * quantum ≤ omegaCount c m - lowerStage := by
      have hpow :
          2 * quantum = 2 ^ (m - k + 2) := by
        dsimp [quantum]
        rw [show m - k + 2 = (m - k) + 2 by omega, pow_add]
        norm_num
        ring
      rw [hpow, hdiff]
      exact hlower
    have hlowerBefore :
        lowerStage < base * quantum :=
      lt_mul_of_lt_succ_mul_of_two_mul_le_sub
        (omegaCount c m) lowerStage base quantum
        hstage homega htwoQuantum
    have htSpec :
        base * quantum ≤ (boundedOutputStage c m t).length := by
      simpa [t, base, quantum] using Nat.find_spec hex
    have htime :
        boundedOutputCompletionTime c r ≤ t := by
      by_contra hnot
      have htlt :
          t < boundedOutputCompletionTime c r := by
        omega
      have hprefix :=
        boundedOutputStage_prefix_of_le c m htlt.le
      have hle := hprefix.length_le
      exact (not_lt_of_ge (htSpec.trans hle)) hlowerBefore
    have hmissing :
        omegaCount c k - (boundedOutputStage c k t).length ≤
          enumerationTailCount c k (k - r) :=
      missingAtStage_le_enumerationTailCount c hrk htime
    have hkr : k - r = margin := by
      dsimp [r]
      omega
    have hupper :
        enumerationTailCount c k margin ≤
          2 ^ (margin + logSlack Ctail k) :=
      (htail k margin hmargin).2
    have hslackMono :
        logSlack Ctail k ≤ logSlack Ctail m :=
      logSlack_mono_right Ctail hk
    have hexp :
        margin + logSlack Ctail k ≤
          2 * logSlack Ctail m + 2 := by
      dsimp [margin, slack]
      omega
    calc
      omegaCount c k - (boundedOutputStage c k t).length
          ≤ enumerationTailCount c k margin := by
            simpa [hkr] using hmissing
      _ ≤ 2 ^ (margin + logSlack Ctail k) := hupper
      _ ≤ 2 ^ (2 * logSlack Ctail m + 2) :=
        Nat.pow_le_pow_right (by decide) hexp
      _ < 2 ^ (2 * logSlack Ctail m + 3) := by
        apply (Nat.pow_lt_pow_iff_right
          (by norm_num : 1 < 2)).mpr
        omega
  · have hkMargin : k < margin := Nat.lt_of_not_ge hmargin
    calc
      omegaCount c k - (boundedOutputStage c k t).length
          ≤ omegaCount c k := Nat.sub_le _ _
      _ < 2 ^ (k + 1) := omegaCount_lt_two_pow_succ c k
      _ ≤ 2 ^ (2 * logSlack Ctail m + 3) := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [margin, slack] at hkMargin
        omega

/-! ### Conditional reconstruction-with-advice bound

The two directions of `prop:omega-equivalence` reconstruct one Omega prefix from
the other (given for free as a *condition*) plus a short `O(log m)` advice.  The
following is the conditional-complexity coding tool this needs: the plain
`condK V _ y` analogue of `plainK_partrec_map_le`. -/

/-- **Conditional partial-recursive reconstruction bound for the plain machine.**
If a partial-recursive `g` reconstructs `w` from a condition `y` and an advice
program `p`, then `w` has plain conditional complexity given `y` at most
`|p| + O(1)`.  This is the coding tool for the reconstruction-with-advice
arguments of `prop:omega-equivalence`, where the condition carries `Ω_k` or
`(Ω_m)_k` for free and only a logarithmic advice `p` is charged. -/
theorem condK_partrec_cond_map_le (V : Map) (hV : isOptimalConditional V)
    (g : BitString → BitString →. BitString)
    (hg : Partrec (fun q : BitString × BitString => g q.1 q.2)) :
    ∃ C : ℕ, ∀ (y p w : BitString), w ∈ g y p →
      condK V w y ≤ (p.length : ENat) + (C : ENat) := by
  set D : Map := fun pr => g pr.2 pr.1 with hDdef
  have hD_decomp : isDecompressor D :=
    hg.comp (Computable.pair Computable.snd Computable.fst)
  obtain ⟨C, hC⟩ := hV.2 D hD_decomp
  refine ⟨C, fun y p w hw => ?_⟩
  have hprod : produces D p y w := by
    simp only [produces, hDdef]; exact hw
  calc condK V w y ≤ condK D w y + (C : ENat) := hC w y
    _ ≤ (p.length : ENat) + (C : ENat) := by
      have : condK D w y ≤ (p.length : ENat) :=
        sInf_le ⟨p, hprod, rfl⟩
      gcongr

/-- Program/context-order variant of `condK_partrec_cond_map_le`.  Here the
partial-recursiveness hypothesis receives `(program, condition)`, which is the
native argument order of a decompressor. -/
theorem condK_partrec_cond_map_le_swapped
    (V : Map) (hV : isOptimalConditional V)
    (g : BitString → BitString →. BitString)
    (hg : Partrec (fun q : BitString × BitString => g q.2 q.1)) :
    ∃ C : ℕ, ∀ (y p w : BitString), w ∈ g y p →
      condK V w y ≤ (p.length : ENat) + (C : ENat) := by
  set D : Map := fun pr => g pr.2 pr.1 with hDdef
  obtain ⟨C, hC⟩ := hV.2 D hg
  refine ⟨C, fun y p w hw => ?_⟩
  have hprod : produces D p y w := by
    simp only [produces, hDdef]
    exact hw
  calc
    condK V w y ≤ condK D w y + (C : ENat) := hC w y
    _ ≤ (p.length : ENat) + (C : ENat) := by
      have hprogram : condK D w y ≤ (p.length : ENat) :=
        sInf_le ⟨p, hprod, rfl⟩
      gcongr

/-- **Forward half of finite Omega equivalence.**  Given the first `k` bits of
`Ω_m`, the fixed-width code of `Ω_k` has plain conditional complexity
`O(log m)`, uniformly for `k ≤ m`. -/
theorem condK_omegaCode_le_of_omegaPrefix
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      condK V (omegaFixedCode c k)
        ((omegaFixedCode c m).take k) ≤
          (logSlack C m : ENat) := by
  obtain ⟨Ctail, hdeltaBound⟩ :=
    omegaPrefixForward_delta_upper_bound V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le_swapped V hV
      (omegaPrefixForwardSelector c Ctail)
      (omegaPrefixForwardSelector_partrec c Ctail)
  let C := 2 * Ctail + Cmap + 6
  refine ⟨C, fun m k hk => ?_⟩
  let y := (omegaFixedCode c m).take k
  let base := decodeFixedWidthNatCode y
  let quantum := 2 ^ (m - k)
  let threshold := base * (2 * quantum)
  let hex : ∃ t,
      threshold ≤ (boundedOutputStage c m t).length :=
    ⟨boundedOutputCompletionTime c m, by
      rw [show
        (boundedOutputStage c m
          (boundedOutputCompletionTime c m)).length =
            omegaCount c m by
        simpa [omegaCount] using
          boundedOutputCompletionTime_spec c m]
      have hinterval :=
        fixedWidthNatCode_take_interval
          (omegaCount_lt_two_pow_succ c m) k
      have hquantum :
          2 ^ (m + 1 - k) = 2 * quantum := by
        dsimp [quantum]
        have heq : m + 1 - k = m - k + 1 := by omega
        rw [heq, pow_succ, Nat.mul_comm]
      simpa [omegaFixedCode, threshold, base, y, hquantum] using hinterval.1⟩
  let t := Nat.find hex
  let delta :=
    omegaCount c k - (boundedOutputStage c k t).length
  let deltaWidth := 2 * logSlack Ctail m + 3
  have hdelta :
      delta < 2 ^ deltaWidth := by
    simpa [delta, deltaWidth, t, threshold, base, quantum, y] using
      hdeltaBound m k hk hex
  have hselector :
      omegaFixedCode c k ∈
        omegaPrefixForwardSelector c Ctail y
          (omegaPrefixForwardAdvice m delta deltaWidth) := by
    simpa [y, base, quantum, threshold, hex, t, delta] using
      omegaPrefixForwardSelector_intended_input
        c Ctail m k deltaWidth hk
  have hadviceLength :
      (omegaPrefixForwardAdvice m delta deltaWidth).length =
        2 * (Nat.bits m).length + deltaWidth + 1 :=
    omegaPrefixForwardAdvice_length hdelta
  have hbudget :
      (omegaPrefixForwardAdvice m delta deltaWidth).length +
          Cmap ≤ logSlack C m := by
    rw [hadviceLength]
    dsimp [deltaWidth, C, logSlack]
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le Ctail, Nat.zero_le Cmap]
  calc
    condK V (omegaFixedCode c k)
        ((omegaFixedCode c m).take k) ≤
      ((omegaPrefixForwardAdvice m delta deltaWidth).length : ENat) +
        (Cmap : ENat) := by
      simpa [y] using hmap y
        (omegaPrefixForwardAdvice m delta deltaWidth)
        (omegaFixedCode c k) hselector
    _ = (((omegaPrefixForwardAdvice m delta deltaWidth).length +
        Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast hbudget

/-- **Reverse half of finite Omega equivalence.**  Given `Ω_k`, the first `k`
bits of `Ω_m` have plain conditional complexity `O(log m)`, uniformly for
`k ≤ m`.  The proof uses the executable reverse selector and charges only its
fixed-width quotient offset. -/
theorem condK_omegaPrefix_le_of_omegaCode
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      condK V ((omegaFixedCode c m).take k)
        (omegaFixedCode c k) ≤ (logSlack C m : ENat) := by
  obtain ⟨Ctail, htail⟩ :=
    omegaPrefix_stage_offset_upper_bound V hV c hc
  obtain ⟨Cmap, hmap⟩ :=
    condK_partrec_cond_map_le V hV
      (omegaPrefixReverseSelector c)
      (omegaPrefixReverseSelector_partrec c)
  let C := Ctail + Cmap + 3
  refine ⟨C, fun m k hk => ?_⟩
  let divisor := 2 ^ (m + 1 - k)
  let stageLength :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c k)).length
  let offset :=
    omegaCount c m / divisor - stageLength / divisor
  let offsetWidth := logSlack Ctail m + 2
  have hoffsetLe :
      offset ≤ 2 ^ logSlack Ctail m + 1 := by
    simpa [offset, divisor, stageLength] using htail m k hk
  have hoffset :
      offset < 2 ^ offsetWidth := by
    dsimp [offsetWidth]
    rw [show logSlack Ctail m + 2 =
      logSlack Ctail m + 1 + 1 by omega, pow_succ, pow_succ]
    have hpow : 0 < 2 ^ logSlack Ctail m := by positivity
    nlinarith
  have hselector :
      (omegaFixedCode c m).take k ∈
        omegaPrefixReverseSelector c (omegaFixedCode c k)
          (omegaPrefixReverseAdvice m offset offsetWidth) := by
    simpa [offset, divisor, stageLength] using
      omegaPrefixReverseSelector_intended_input c m k offsetWidth hk
  have hadviceLength :
      (omegaPrefixReverseAdvice m offset offsetWidth).length =
        2 * (Nat.bits m).length + offsetWidth + 1 :=
    omegaPrefixReverseAdvice_length hoffset
  have hbudget :
      (omegaPrefixReverseAdvice m offset offsetWidth).length + Cmap ≤
        logSlack C m := by
    rw [hadviceLength]
    dsimp [offsetWidth, C, logSlack]
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le Ctail, Nat.zero_le Cmap]
  calc
    condK V ((omegaFixedCode c m).take k)
        (omegaFixedCode c k) ≤
      ((omegaPrefixReverseAdvice m offset offsetWidth).length : ENat) +
        (Cmap : ENat) :=
      hmap _ _ _ hselector
    _ = (((omegaPrefixReverseAdvice m offset offsetWidth).length +
        Cmap : ℕ) : ENat) := by
      rw [Nat.cast_add]
    _ ≤ (logSlack C m : ENat) := by
      exact_mod_cast hbudget

/-- **VS40 Proposition `prop:omega-equivalence`.**  For `k ≤ m`, the fixed
finite Omega code `Ω_k` and the literal first `k` high bits `(Ω_m)_k` determine
each other with `O(log m)` plain conditional advice. -/
theorem prop_omega_equivalence
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m k : ℕ, k ≤ m →
      condK V (omegaFixedCode c k)
          ((omegaFixedCode c m).take k) ≤
            (logSlack C m : ENat) ∧
      condK V ((omegaFixedCode c m).take k)
          (omegaFixedCode c k) ≤
            (logSlack C m : ENat) := by
  obtain ⟨Cforward, hforward⟩ :=
    condK_omegaCode_le_of_omegaPrefix V hV c hc
  obtain ⟨Creverse, hreverse⟩ :=
    condK_omegaPrefix_le_of_omegaCode V hV c hc
  let C := max Cforward Creverse
  refine ⟨C, fun m k hk => ⟨?_, ?_⟩⟩
  · exact (hforward m k hk).trans (by
      exact_mod_cast logSlack_mono_left
        (le_max_left Cforward Creverse) m)
  · exact (hreverse m k hk).trans (by
      exact_mod_cast logSlack_mono_left
        (le_max_right Cforward Creverse) m)

end Kolmogorov
