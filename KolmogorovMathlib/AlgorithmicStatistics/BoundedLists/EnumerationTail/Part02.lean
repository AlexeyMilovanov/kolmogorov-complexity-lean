import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.BusyBeaver
import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.EnumerationTail.Part01

/-!
# The tail of the bounded enumeration: how large it is, and how to name a member

`enumerationTailCount_lower_bound`: the tail at slack `s` holds at least `2 ^ (s - logSlack C m)`
outputs.  The proof is a description argument, so most of the module is the description
format and the selector that reads it.

`enumerationTailUpperInput` assembles a self-delimiting header `(m, s, d)` followed by a
fixed-width block index; `enumerationTailUpperM`, `…S`, `…D`, `…BlockIndex` read the four
fields back, with the corresponding `_input` lemmas showing the round trip and
`enumerationTailUpperInput_length` giving the exact length.
`enumerationTailUpperSelector` is the partial-recursive selector that waits for the bound-`m`
enumeration to pass the end of the addressed block and returns the member; the `_primrec`
lemmas make the field readers effective.

Builds on `Part01`, which contains the membership characterisation and the upper bounds.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

/-- The tail at slack `s` contains at least `2 ^ (s - logSlack C m)` outputs. -/
theorem enumerationTailCount_lower_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      logSlack C m ≤ s →
      2 ^ (s - logSlack C m) ≤ enumerationTailCount c m s := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (enumerationTailLowerSelector c)
      (enumerationTailLowerSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  let C := 6 + Clen + Cmap
  refine ⟨C, fun m s hsm hslack => ?_⟩
  by_contra htail
  push_neg at htail
  let tailWidth := s - logSlack C m
  obtain ⟨x, hxSelector, _, hxMissing⟩ :=
    enumerationTailLowerSelector_intended_input c m s tailWidth
  have hxLower : (m : ENat) < plainK V x :=
    plainK_gt_of_not_mem_completed hc hxMissing
  have hinputLength :
      (enumerationTailLowerInput c m s tailWidth).length =
        m - s + tailWidth +
          4 * (Nat.bits m).length + 2 * (Nat.bits s).length + 4 :=
    enumerationTailLowerInput_length htail
  have hbits :
      (Nat.bits s).length ≤ (Nat.bits m).length :=
    length_natBits_mono hsm
  have hbudget :
      6 * (Nat.bits m).length + 4 + Clen + Cmap ≤
        logSlack C m := by
    dsimp [C, logSlack]
    nlinarith [Nat.zero_le ((Nat.bits m).length),
      Nat.zero_le Clen, Nat.zero_le Cmap]
  have htotal :
      (enumerationTailLowerInput c m s tailWidth).length +
        Clen + Cmap ≤ m := by
    rw [hinputLength]
    dsimp [tailWidth]
    omega
  have hxUpper : plainK V x ≤ (m : ENat) := by
    calc
      plainK V x ≤
          plainK V (enumerationTailLowerInput c m s tailWidth) +
            (Cmap : ENat) :=
        hmap _ _ hxSelector
      _ ≤
          (((enumerationTailLowerInput c m s tailWidth).length : ENat) +
            (Clen : ENat)) + (Cmap : ENat) := by
        gcongr
        exact hlen _
      _ = (((enumerationTailLowerInput c m s tailWidth).length +
          Clen + Cmap : ℕ) : ENat) := by
        push_cast
        ring
      _ ≤ (m : ENat) := by
        exact_mod_cast htotal
  exact (not_lt_of_ge hxUpper) hxLower

/-- A self-delimiting header `(m,s,d)` followed by an undoubled fixed-width
block index.  This is the short description used by the upper-tail block
argument. -/
def enumerationTailUpperInput
    (m s d blockIdx blockWidth : ℕ) : BitString :=
  pairCode
    (pairCode (Nat.bits m) (pairCode (Nat.bits s) (Nat.bits d)))
    (fixedWidthNatCode blockIdx blockWidth)

/-- The bound read off an upper-tail input. -/
def enumerationTailUpperM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst z))

/-- The slack read off an upper-tail input. -/
def enumerationTailUpperS (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeFirst z)))

/-- The block exponent read off an upper-tail input. -/
def enumerationTailUpperD (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond (decodeFirst z)))

/-- The block index read off an upper-tail input. -/
def enumerationTailUpperBlockIndex (z : BitString) : ℕ :=
  decodeFixedWidthNatCode (decodeSecond z)

/-- The bound is read back from an assembled upper-tail input. -/
@[simp] theorem enumerationTailUpperM_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperM
      (enumerationTailUpperInput m s d blockIdx blockWidth) = m := by
  unfold enumerationTailUpperM enumerationTailUpperInput
  simp only [decodeFirst_pairCode, bitsToNat_bits]

/-- The slack is read back from an assembled upper-tail input. -/
@[simp] theorem enumerationTailUpperS_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperS
      (enumerationTailUpperInput m s d blockIdx blockWidth) = s := by
  unfold enumerationTailUpperS enumerationTailUpperInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The block exponent is read back from an assembled upper-tail input. -/
@[simp] theorem enumerationTailUpperD_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperD
      (enumerationTailUpperInput m s d blockIdx blockWidth) = d := by
  unfold enumerationTailUpperD enumerationTailUpperInput
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The block index is read back from an assembled upper-tail input. -/
@[simp] theorem enumerationTailUpperBlockIndex_input
    (m s d blockIdx blockWidth : ℕ) :
    enumerationTailUpperBlockIndex
      (enumerationTailUpperInput m s d blockIdx blockWidth) = blockIdx := by
  unfold enumerationTailUpperBlockIndex enumerationTailUpperInput
  simp only [decodeSecond_pairCode, decodeFixedWidthNatCode_encode]

/-- The exact length of an upper-tail input in terms of the index width and the
three parameters. -/
theorem enumerationTailUpperInput_length
    {m s d blockIdx blockWidth : ℕ}
    (hblock : blockIdx < 2 ^ blockWidth) :
    (enumerationTailUpperInput m s d blockIdx blockWidth).length =
      blockWidth + 4 * (Nat.bits m).length +
        4 * (Nat.bits s).length + 2 * (Nat.bits d).length + 5 := by
  unfold enumerationTailUpperInput
  rw [length_pairCode, length_pairCode, length_pairCode,
    fixedWidthNatCode_length hblock]
  omega

/-- From `(m,s,d)` and a block index, wait until the bound-`m` enumeration has
reached the end of that block.  The returned natural is enlarged to at least
`m-s`, so `lateCutoff_complexity_implication` can be applied directly. -/
noncomputable def enumerationTailUpperSelector
    (c : Code) (z : BitString) : Part BitString := do
  let blockEnd :=
    enumerationTailUpperBlockIndex z *
      2 ^ (enumerationTailUpperS z + enumerationTailUpperD z)
  let t ← Nat.rfind (fun t => Part.some
    (decide (blockEnd ≤
      (boundedOutputStage c (enumerationTailUpperM z) t).length)))
  Part.some (Nat.bits (max
    (enumerationTailUpperM z - enumerationTailUpperS z) t))

/-- Reading the bound off an upper-tail input is primitive recursive. -/
theorem enumerationTailUpperM_primrec : Primrec enumerationTailUpperM := by
  exact bitsToNat_primrec.comp
    (CodedFiniteDistribution.decodeFirst_primrec.comp CodedFiniteDistribution.decodeFirst_primrec)

/-- Reading the slack off an upper-tail input is primitive recursive. -/
theorem enumerationTailUpperS_primrec : Primrec enumerationTailUpperS := by
  exact bitsToNat_primrec.comp
    (CodedFiniteDistribution.decodeFirst_primrec.comp
      (CodedFiniteDistribution.decodeSecond_primrec.comp
        CodedFiniteDistribution.decodeFirst_primrec))

/-- Reading the block exponent off an upper-tail input is primitive recursive. -/
theorem enumerationTailUpperD_primrec : Primrec enumerationTailUpperD := by
  exact bitsToNat_primrec.comp
    (CodedFiniteDistribution.decodeSecond_primrec.comp
      (CodedFiniteDistribution.decodeSecond_primrec.comp
        CodedFiniteDistribution.decodeFirst_primrec))

/-- Reading the block index off an upper-tail input is primitive recursive. -/
theorem enumerationTailUpperBlockIndex_primrec :
    Primrec enumerationTailUpperBlockIndex := by
  exact decodeFixedWidthNatCode_primrec.comp CodedFiniteDistribution.decodeSecond_primrec

/-- The upper-tail selector is a partial recursive function of its input. -/
theorem enumerationTailUpperSelector_partrec
    (c : Code) :
    Partrec (enumerationTailUpperSelector c) := by
  have hm : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperM q.1) :=
    enumerationTailUpperM_primrec.comp Primrec.fst
  have hs : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperS q.1) :=
    enumerationTailUpperS_primrec.comp Primrec.fst
  have hd : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperD q.1) :=
    enumerationTailUpperD_primrec.comp Primrec.fst
  have hpow : Primrec (fun q : BitString × ℕ =>
      2 ^ (enumerationTailUpperS q.1 +
        enumerationTailUpperD q.1)) :=
    Kolmogorov.primrec_two_pow_aux.comp
      (Primrec.nat_add.comp hs hd)
  have hblock : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperBlockIndex q.1) :=
    enumerationTailUpperBlockIndex_primrec.comp Primrec.fst
  have hend : Primrec (fun q : BitString × ℕ =>
      enumerationTailUpperBlockIndex q.1 *
        2 ^ (enumerationTailUpperS q.1 +
          enumerationTailUpperD q.1)) :=
    Primrec.nat_mul.comp hblock hpow
  have hstage : Primrec (fun q : BitString × ℕ =>
      boundedOutputStage c (enumerationTailUpperM q.1) q.2) :=
    (boundedOutputStage_primrec c).comp
      (Primrec.pair hm Primrec.snd)
  have hcheck : Computable₂ (fun (z : BitString) (t : ℕ) =>
      decide
        (enumerationTailUpperBlockIndex z *
            2 ^ (enumerationTailUpperS z + enumerationTailUpperD z) ≤
          (boundedOutputStage c (enumerationTailUpperM z) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hend
        (Primrec.list_length.comp hstage))).to_comp.to₂
  have hsearch : Partrec (fun z : BitString =>
      Nat.rfind (fun t => Part.some
        (decide
          (enumerationTailUpperBlockIndex z *
              2 ^ (enumerationTailUpperS z +
                enumerationTailUpperD z) ≤
            (boundedOutputStage c
              (enumerationTailUpperM z) t).length)))) :=
    Partrec.rfind hcheck.partrec₂
  have hpost : Computable₂ (fun (z : BitString) (t : ℕ) =>
      Nat.bits (max
        (enumerationTailUpperM z - enumerationTailUpperS z) t)) := by
    have hlower : Primrec (fun q : BitString × ℕ =>
        enumerationTailUpperM q.1 - enumerationTailUpperS q.1) :=
      Primrec.nat_sub.comp hm hs
    exact (natBits_computable.comp
      (Primrec.nat_max.comp hlower Primrec.snd).to_comp).to₂
  unfold enumerationTailUpperSelector
  exact (Partrec.bind hsearch hpost.partrec₂).of_eq (fun _ => rfl)

/-- If the addressed block starts after the completion stage of `m - s` and before
the enumeration ends, the selector outputs a stage past that completion time. -/
theorem enumerationTailUpperSelector_intended_input
    (c : Code) (m s d blockIdx blockWidth : ℕ)
    (hbefore :
      (boundedOutputStage c m
        (boundedOutputCompletionTime c (m - s))).length <
          blockIdx * 2 ^ (s + d))
    (hcomplete :
      blockIdx * 2 ^ (s + d) < omegaCount c m) :
    ∃ t,
      Nat.bits (max (m - s) t) ∈
        enumerationTailUpperSelector c
          (enumerationTailUpperInput m s d blockIdx blockWidth) ∧
      boundedOutputCompletionTime c (m - s) < t := by
  let blockEnd := blockIdx * 2 ^ (s + d)
  let hex : ∃ t,
      blockEnd ≤ (boundedOutputStage c m t).length :=
    ⟨boundedOutputCompletionTime c m, by
      rw [show
        (boundedOutputStage c m
          (boundedOutputCompletionTime c m)).length =
            omegaCount c m by
        simpa [omegaCount] using
          boundedOutputCompletionTime_spec c m]
      exact hcomplete.le⟩
  let t := Nat.find hex
  have htSpec :
      blockEnd ≤ (boundedOutputStage c m t).length :=
    Nat.find_spec hex
  have htSearch :
      t ∈ Nat.rfind (fun t => Part.some
        (decide
          (blockEnd ≤ (boundedOutputStage c m t).length))) := by
    rw [Nat.mem_rfind]
    refine ⟨by simp [htSpec], ?_⟩
    intro n hn
    have hnot := Nat.find_min hex hn
    simp [hnot]
  have hlowerTime :
      boundedOutputCompletionTime c (m - s) < t := by
    by_contra hnot
    push_neg at hnot
    have hprefix :=
      boundedOutputStage_prefix_of_le c m hnot
    have hle := hprefix.length_le
    dsimp [blockEnd] at htSpec
    exact (not_lt_of_ge (htSpec.trans hle)) hbefore
  refine ⟨t, ?_, hlowerTime⟩
  unfold enumerationTailUpperSelector
  simp only [enumerationTailUpperM_input,
    enumerationTailUpperS_input, enumerationTailUpperD_input,
    enumerationTailUpperBlockIndex_input]
  change Nat.bits (max (m - s) t) ∈
    (Nat.rfind (fun t => Part.some
      (decide
        (blockIdx * 2 ^ (s + d) ≤
          (boundedOutputStage c m t).length)))).bind
      (fun t => Part.some (Nat.bits (max (m - s) t)))
  rw [Part.mem_bind_iff]
  exact ⟨t, by simpa [blockEnd] using htSearch,
    Part.mem_some (Nat.bits (max (m - s) t))⟩

/-- If more than one `2^(s+d)`-block remains, the first block boundary strictly
after the current stage is still strictly before completion.  Its block index
fits in `m-s-d+2` bits. -/
theorem exists_enumerationTail_full_block
    (c : Code) (m s d : ℕ)
    (htail : 2 ^ (s + d) < enumerationTailCount c m s) :
    ∃ blockIdx,
      (boundedOutputStage c m
          (boundedOutputCompletionTime c (m - s))).length <
        blockIdx * 2 ^ (s + d) ∧
      blockIdx * 2 ^ (s + d) < omegaCount c m ∧
      s + d ≤ m ∧
      blockIdx < 2 ^ (m - s - d + 2) := by
  let a :=
    (boundedOutputStage c m
      (boundedOutputCompletionTime c (m - s))).length
  let q := 2 ^ (s + d)
  let blockIdx := a / q + 1
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hsum : a + enumerationTailCount c m s = omegaCount c m := by
    simpa [a] using stageLength_add_enumerationTailCount c m s
  have hdivle : a / q * q ≤ a := Nat.div_mul_le_self a q
  have hmodlt : a % q < q := Nat.mod_lt a hqpos
  have hdivmod : a / q * q + a % q = a :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod a q
  have habove : a < blockIdx * q := by
    dsimp [blockIdx]
    nlinarith
  have hbelow : blockIdx * q < omegaCount c m := by
    have hblockLe : blockIdx * q ≤ a + q := by
      dsimp [blockIdx]
      nlinarith
    omega
  have hsd : s + d ≤ m := by
    have hpow :
        2 ^ (s + d) < 2 ^ (m + 1) :=
      lt_trans htail
        (lt_of_le_of_lt
          (enumerationTailCount_le_omegaCount c m s)
          (omegaCount_lt_two_pow_succ c m))
    have hexp : s + d < m + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    omega
  have haPow : a < 2 ^ (m + 1) := by
    exact lt_trans (lt_trans habove hbelow)
      (omegaCount_lt_two_pow_succ c m)
  have hquot :
      a / q < 2 ^ (m - s - d + 1) := by
    rw [Nat.div_lt_iff_lt_mul hqpos]
    dsimp [q]
    calc
      a < 2 ^ (m + 1) := haPow
      _ = 2 ^ (m - s - d + 1 + (s + d)) := by
        congr 1
        omega
      _ = 2 ^ (m - s - d + 1) * 2 ^ (s + d) := by
        rw [pow_add]
  have hblockWidth :
      blockIdx < 2 ^ (m - s - d + 2) := by
    have hpowpos : 0 < 2 ^ (m - s - d + 1) := by positivity
    have hle : blockIdx ≤ 2 ^ (m - s - d + 1) := by
      dsimp [blockIdx]
      omega
    rw [show m - s - d + 2 = (m - s - d + 1) + 1 by omega,
      pow_succ]
    omega
  exact ⟨blockIdx, by simpa [a, q] using habove,
    by simpa [q] using hbelow, hsd, hblockWidth⟩

/-- The binary length of a logarithmic slack is itself logarithmic.  The
constant's binary length is kept explicit because the upper-tail proof chooses
that constant only after all machine overheads are known. -/
theorem length_natBits_logSlack_le (C m : ℕ) :
    (Nat.bits (logSlack C m)).length ≤
      (Nat.bits m).length + (Nat.bits C).length + 1 := by
  let B := (Nat.bits m).length
  let LC := (Nat.bits C).length
  have hB : B + 1 ≤ 2 ^ (B + 1) := by
    exact Nat.recOn (B + 1) (by norm_num) fun n ihn => by
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n :=
        Nat.one_le_pow n 2 zero_lt_two
      omega
  have hC : C < 2 ^ LC := by
    simpa [LC] using lt_two_pow_length_natBits C
  apply length_natBits_lt_pow
  calc
    logSlack C m = C * (B + 1) := by
      dsimp [B, logSlack]
      ring
    _ < 2 ^ LC * (B + 1) :=
      Nat.mul_lt_mul_of_pos_right hC (Nat.succ_pos B)
    _ ≤ 2 ^ LC * 2 ^ (B + 1) :=
      Nat.mul_le_mul_left _ hB
    _ = 2 ^ (B + LC + 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ = 2 ^ ((Nat.bits m).length + (Nat.bits C).length + 1) := by
      rfl

/-- The elementary estimate `3 * K + 22 ≤ 2 ^ (K + 10)`. -/
theorem three_mul_add_twenty_two_le_two_pow_add_ten (K : ℕ) :
    3 * K + 22 ≤ 2 ^ (K + 10) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [show K + 1 + 10 = (K + 10) + 1 by omega, pow_succ]
      omega

/-- The tail at slack `s` contains at most `2 ^ (s + logSlack C m)` outputs. -/
theorem enumerationTailCount_upper_bound
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      enumerationTailCount c m s ≤ 2 ^ (s + logSlack C m) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (enumerationTailUpperSelector c)
      (enumerationTailUpperSelector_partrec c)
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  obtain ⟨Ccut, hcut⟩ :=
    lateCutoff_complexity_implication V hV c hc
  let K := 9 + Clen + Cmap + Ccut
  let C := 2 ^ (K + 10)
  refine ⟨C, fun m s hsm => ?_⟩
  by_contra htail
  push_neg at htail
  let d := logSlack C m
  obtain ⟨blockIdx, hbefore, hcomplete, hsd, hblock⟩ :=
    exists_enumerationTail_full_block c m s d (by
      simpa [d] using htail)
  let blockWidth := m - s - d + 2
  obtain ⟨t, htSelector, hlowerTime⟩ :=
    enumerationTailUpperSelector_intended_input
      c m s d blockIdx blockWidth hbefore hcomplete
  let N := max (m - s) t
  have hqN : m - s ≤ N := by
    exact le_max_left _ _
  have hdone :
      boundedOutputCompletionTime c (m - s) ≤ N := by
    exact le_trans hlowerTime.le (le_max_right _ _)
  have hlate :
      ((m - s : ℕ) : ENat) <
        plainKNat V N + (Ccut : ENat) :=
    hcut (m - s) N hqN hdone
  have hselector :
      plainKNat V N ≤
        plainK V
          (enumerationTailUpperInput
            m s d blockIdx blockWidth) + (Cmap : ENat) := by
    exact hmap _ _ (by simpa [N] using htSelector)
  have hinputLength :
      (enumerationTailUpperInput
        m s d blockIdx blockWidth).length =
          blockWidth + 4 * (Nat.bits m).length +
            4 * (Nat.bits s).length +
              2 * (Nat.bits d).length + 5 :=
    enumerationTailUpperInput_length (by
      simpa [blockWidth] using hblock)
  have hbitsS :
      (Nat.bits s).length ≤ (Nat.bits m).length :=
    length_natBits_mono hsm
  have hbitsD :
      (Nat.bits d).length ≤
        (Nat.bits m).length + (Nat.bits C).length + 1 := by
    simpa [d] using length_natBits_logSlack_le C m
  have hCbits :
      (Nat.bits C).length ≤ K + 11 := by
    apply length_natBits_lt_pow
    dsimp [C]
    exact (Nat.pow_lt_pow_iff_right
      (by norm_num : 1 < 2)).mpr (by omega)
  have hCten : 10 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : 10 ≤ 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 10 K))
  have hCconst :
      2 * (Nat.bits C).length + K ≤ C := by
    calc
      2 * (Nat.bits C).length + K ≤ 3 * K + 22 := by
        omega
      _ ≤ 2 ^ (K + 10) :=
        three_mul_add_twenty_two_le_two_pow_add_ten K
      _ = C := rfl
  have hbudget :
      10 * (Nat.bits m).length +
          2 * (Nat.bits C).length + K ≤ d := by
    dsimp [d, logSlack]
    have hmul :
        10 * (Nat.bits m).length ≤
          C * (Nat.bits m).length :=
      Nat.mul_le_mul_right _ hCten
    omega
  have htotal :
      (enumerationTailUpperInput
          m s d blockIdx blockWidth).length +
        Clen + Cmap + Ccut ≤ m - s := by
    rw [hinputLength]
    dsimp [blockWidth, K] at *
    omega
  have hupper :
      plainKNat V N + (Ccut : ENat) ≤
        ((m - s : ℕ) : ENat) := by
    calc
      plainKNat V N + (Ccut : ENat) ≤
          (plainK V
            (enumerationTailUpperInput
              m s d blockIdx blockWidth) +
                (Cmap : ENat)) + (Ccut : ENat) := by
        gcongr
      _ ≤
          ((((enumerationTailUpperInput
              m s d blockIdx blockWidth).length : ENat) +
                (Clen : ENat)) + (Cmap : ENat)) +
                  (Ccut : ENat) := by
        gcongr
        exact hlen _
      _ = (((enumerationTailUpperInput
          m s d blockIdx blockWidth).length +
            Clen + Cmap + Ccut : ℕ) : ENat) := by
        push_cast
        ring
      _ ≤ ((m - s : ℕ) : ENat) := by
        exact_mod_cast htotal
  exact (not_lt_of_ge hupper) hlate

/-- Two-sided estimate of the tail count: between `2 ^ (s - logSlack C m)` and
`2 ^ (s + logSlack C m)`. -/
theorem prop_enumeration_tail
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m s : ℕ, s ≤ m →
      (logSlack C m ≤ s → 2 ^ (s - logSlack C m) ≤ enumerationTailCount c m s) ∧
      enumerationTailCount c m s ≤ 2 ^ (s + logSlack C m) := by
  obtain ⟨Clower, hlower⟩ := enumerationTailCount_lower_bound V hV c hc
  obtain ⟨Cupper, hupper⟩ := enumerationTailCount_upper_bound V hV c hc
  let C := max Clower Cupper
  refine ⟨C, fun m s hsm => ⟨fun hslack => ?_, ?_⟩⟩
  · have hC_lower : logSlack Clower m ≤ logSlack C m := by
      dsimp [logSlack, C]
      have h1 : Clower ≤ max Clower Cupper := le_max_left _ _
      have h2 :
          Clower * (Nat.bits m).length ≤
            max Clower Cupper * (Nat.bits m).length :=
        Nat.mul_le_mul_right _ h1
      omega
    have hslack_lower : logSlack Clower m ≤ s :=
      le_trans hC_lower hslack
    have h_pow := hlower m s hsm hslack_lower
    have h_sub : s - logSlack C m ≤ s - logSlack Clower m := by
      omega
    exact (Nat.pow_le_pow_right (by decide) h_sub).trans h_pow
  · have hC_upper : logSlack Cupper m ≤ logSlack C m := by
      dsimp [logSlack, C]
      have h1 : Cupper ≤ max Clower Cupper := le_max_right _ _
      have h2 :
          Cupper * (Nat.bits m).length ≤
            max Clower Cupper * (Nat.bits m).length :=
        Nat.mul_le_mul_right _ h1
      omega
    have h_pow := hupper m s hsm
    have h_add : s + logSlack Cupper m ≤ s + logSlack C m := by
      omega
    exact h_pow.trans (Nat.pow_le_pow_right (by decide) h_add)

end Kolmogorov
