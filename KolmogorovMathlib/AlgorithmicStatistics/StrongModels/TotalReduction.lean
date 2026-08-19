import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalMaps
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Directed total reduction and total equivalence

VS40 Section 7 introduces the directed relation `x →ε y` (there is a short total
program mapping `x` to `y`, i.e. `KT(y ∣ x) ≤ ε`) and calls `x` and `y`
`ε`-equivalent when reduction holds in both directions.  This module records the
directed relation and its elementary structure, together with the bridge
`condK ≤ totalCondK` (a total producing program is in particular a producing
program).

These are the S1 primitives on which Proposition `prop:equivalence` and the
strong-model theory are built.  Nothing here assumes any winning strategy,
partition, or profile neighborhood; those are the mathematical content of later
results.
-/

namespace Kolmogorov

/-- Plain conditional complexity never exceeds total conditional complexity for
the *same* decompressor `D`: every total producing program is in particular a
producing program, so its length is already counted by `condK`.  This is the
formal content of the source remark that a total program "is in particular a
program". -/
theorem condK_le_totalCondK (D : Map) (x y : BitString) :
    condK D x y ≤ totalCondK D x y := by
  apply sInf_le_sInf
  rintro n ⟨p, _htot, hprod, rfl⟩
  exact ⟨p, hprod, rfl⟩

/-- Directed total reduction `x →ε y`: there is a total program of length at most
`ε` mapping `x` to `y`, i.e. `KT(y ∣ x) ≤ ε`. -/
def TotalReducesWithin (U : Map) (x y : BitString) (epsilon : Nat) : Prop :=
  totalCondK U y x ≤ (epsilon : ENat)

/-- `x →ε y` unfolds by definition to the finite total-program witness. -/
theorem totalReducesWithin_iff (U : Map) (x y : BitString) (epsilon : Nat) :
    TotalReducesWithin U x y epsilon ↔
      ∃ p, IsTotalProgram U p ∧ programLength p ≤ epsilon ∧ produces U p x y := by
  unfold TotalReducesWithin
  exact totalCondK_le_iff U y x epsilon

/-- Directed reduction is monotone in the budget `ε`. -/
theorem TotalReducesWithin.mono {U : Map} {x y : BitString} {epsilon epsilon' : Nat}
    (h : epsilon ≤ epsilon') (hred : TotalReducesWithin U x y epsilon) :
    TotalReducesWithin U x y epsilon' :=
  hred.trans (by exact_mod_cast h)

/-- Every string reduces to itself with a uniform constant budget: the constant
comes from the self bound `KT(x ∣ x) = O(1)`. -/
theorem exists_totalReducesWithin_self (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x, TotalReducesWithin T x x c := by
  obtain ⟨c, hc⟩ := totalCondK_self_le_const T hT
  exact ⟨c, fun x => hc x⟩

/-- `ε`-equivalence is exactly directed reduction in both directions. -/
theorem totalEquivalentWithin_iff (U : Map) (x y : BitString) (epsilon : Nat) :
    TotalEquivalentWithin U x y epsilon ↔
      TotalReducesWithin U x y epsilon ∧ TotalReducesWithin U y x epsilon := by
  unfold TotalEquivalentWithin TotalReducesWithin
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- `ε`-equivalence is symmetric. -/
theorem TotalEquivalentWithin.symm {U : Map} {x y : BitString} {epsilon : Nat}
    (h : TotalEquivalentWithin U x y epsilon) :
    TotalEquivalentWithin U y x epsilon :=
  ⟨h.2, h.1⟩

/-- `ε`-equivalence is monotone in the budget `ε`. -/
theorem TotalEquivalentWithin.mono {U : Map} {x y : BitString} {epsilon epsilon' : Nat}
    (h : epsilon ≤ epsilon') (heq : TotalEquivalentWithin U x y epsilon) :
    TotalEquivalentWithin U x y epsilon' :=
  ⟨heq.1.trans (by exact_mod_cast h), heq.2.trans (by exact_mod_cast h)⟩

/-- Every string is `ε`-equivalent to itself for a uniform constant budget. -/
theorem exists_totalEquivalentWithin_self (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x, TotalEquivalentWithin T x x c := by
  obtain ⟨c, hc⟩ := totalCondK_self_le_const T hT
  exact ⟨c, fun x => ⟨hc x, hc x⟩⟩

/-- A decompressor that sequentially executes a pair of programs.  Given
`pairCode p q` and a condition `z`, it runs `p` on `z` to obtain `y`,
and then runs `q` on `y`. -/
def totalComposeDecompressor (T : Map) : Map := fun pr =>
  (T (decodeFirst pr.1, pr.2)).bind fun y =>
    T (decodeSecond pr.1, y)

lemma totalComposeDecompressor_partrec {T : Map} (hT : isDecompressor T) :
    isDecompressor (totalComposeDecompressor T) := by
  have hfirst :
      Partrec (fun input : BitString × BitString =>
        T (decodeFirst input.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond :
      Partrec (fun input : (BitString × BitString) × BitString =>
        T (decodeSecond input.1.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeSecond_computable.comp (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

lemma IsTotalProgram.compose
    {T : Map} {p q : BitString}
    (hp : IsTotalProgram T p) (hq : IsTotalProgram T q) :
    IsTotalProgram (totalComposeDecompressor T) (pairCode p q) := by
  intro z
  unfold totalComposeDecompressor
  rw [decodeFirst_pairCode, decodeSecond_pairCode]
  rw [Part.bind_dom]
  exact ⟨hp z, hq _⟩

lemma totalComposeDecompressor_produces
    {T : Map} {p q y z w : BitString}
    (hp : produces T p z y) (hq : produces T q y w) :
    produces (totalComposeDecompressor T) (pairCode p q) z w := by
  unfold totalComposeDecompressor produces
  rw [Part.mem_bind_iff]
  exact ⟨y, by rwa [decodeFirst_pairCode], by rwa [decodeSecond_pairCode]⟩

/-- Coarse, explicitly pair-coded composition of directed total reductions.

This is not the logarithmically sharp triangle inequality: the repository's
`pairCode p q` has length `2 * |p| + |q| + 1`, so this reusable S1 bound keeps
that exact asymmetry visible.  A later length-prefixed composition theorem can
sharpen the `2 * epsilon` term without changing this primitive. -/
theorem TotalReducesWithin.trans_pair
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalReducesWithin T x y epsilon →
      TotalReducesWithin T y z delta →
      TotalReducesWithin T x z (2 * epsilon + delta + c) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (totalComposeDecompressor T)
      (totalComposeDecompressor_partrec hT.1)
  refine ⟨c + 1, ?_⟩
  intro x y z epsilon delta hxy hyz
  obtain ⟨p, hp_total, hp_len, hp_prod⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hxy
  obtain ⟨q, hq_total, hq_len, hq_prod⟩ :=
    (totalReducesWithin_iff T y z delta).mp hyz
  change p.length ≤ epsilon at hp_len
  change q.length ≤ delta at hq_len
  unfold TotalReducesWithin
  calc
    totalCondK T z x
        ≤ totalCondK (totalComposeDecompressor T) z x + (c : ENat) :=
      hc z x
    _ ≤ (programLength (pairCode p q) : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength
        (hp_total.compose hq_total)
        (totalComposeDecompressor_produces hp_prod hq_prod)
    _ ≤ ((2 * epsilon + delta + (c + 1) : Nat) : ENat) := by
      change ((pairCode p q).length : ENat) + (c : ENat) ≤ _
      rw [length_pairCode]
      exact_mod_cast (show
        p.length + 1 + p.length + q.length + c ≤
          2 * epsilon + delta + (c + 1) by omega)

/-- Symmetric corollary of `TotalReducesWithin.trans_pair`.  Two successive
total equivalences compose with the explicit coarse budget
`2 * (epsilon + delta) + O(1)`. -/
theorem TotalEquivalentWithin.trans_pair
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalEquivalentWithin T x y epsilon →
      TotalEquivalentWithin T y z delta →
      TotalEquivalentWithin T x z (2 * (epsilon + delta) + c) := by
  obtain ⟨c, htrans⟩ := TotalReducesWithin.trans_pair T hT
  refine ⟨c, ?_⟩
  intro x y z epsilon delta hxy hyz
  obtain ⟨hxy_forward, hxy_backward⟩ :=
    (totalEquivalentWithin_iff T x y epsilon).mp hxy
  obtain ⟨hyz_forward, hyz_backward⟩ :=
    (totalEquivalentWithin_iff T y z delta).mp hyz
  apply (totalEquivalentWithin_iff T x z
    (2 * (epsilon + delta) + c)).mpr
  constructor
  · exact (htrans hxy_forward hyz_forward).mono (by omega)
  · exact (htrans hyz_backward hxy_backward).mono (by omega)

/-! ### Binary-length-framed composition

The unary header in `pairCode p q` duplicates `|p|`.  For the sharp
total-complexity triangle bound we instead encode the binary representation of
`|p|` in the self-delimiting first component of `pairCode`, followed by the raw
concatenation `p ++ q`.  This costs
`|p| + |q| + 2 * |Nat.bits |p|| + 1`.
-/

/-- A binary-length-framed pair of total programs. -/
def totalProgramPairCode (p q : BitString) : BitString :=
  pairCode (Nat.bits p.length) (p ++ q)

/-- Recover the first program from a binary-length-framed pair. -/
def decodeTotalProgramPairFirst (w : BitString) : BitString :=
  (decodeSecond w).take (decodeBits (decodeFirst w))

/-- Recover the second program from a binary-length-framed pair. -/
def decodeTotalProgramPairSecond (w : BitString) : BitString :=
  (decodeSecond w).drop (decodeBits (decodeFirst w))

@[simp] theorem decodeTotalProgramPairFirst_pair
    (p q : BitString) :
    decodeTotalProgramPairFirst (totalProgramPairCode p q) = p := by
  simp [decodeTotalProgramPairFirst, totalProgramPairCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]

@[simp] theorem decodeTotalProgramPairSecond_pair
    (p q : BitString) :
    decodeTotalProgramPairSecond (totalProgramPairCode p q) = q := by
  simp [decodeTotalProgramPairSecond, totalProgramPairCode,
    decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]

theorem length_totalProgramPairCode (p q : BitString) :
    (totalProgramPairCode p q).length =
      p.length + q.length + 2 * (Nat.bits p.length).length + 1 := by
  simp [totalProgramPairCode, length_pairCode]
  omega

theorem totalProgramPairCode_computable :
    Computable (fun input : BitString × BitString =>
      totalProgramPairCode input.1 input.2) := by
  exact (pairCode_primrec.comp
    (primrecNatBits.comp (Primrec.list_length.comp Primrec.fst))
    (Primrec.list_append.comp Primrec.fst Primrec.snd)).to_comp

theorem decodeTotalProgramPairFirst_computable :
    Computable decodeTotalProgramPairFirst := by
  unfold decodeTotalProgramPairFirst
  exact Primrec.list_take.to_comp.comp
    (decodeBitsComputable.comp decodeFirst_computable) decodeSecond_computable

theorem decodeTotalProgramPairSecond_computable :
    Computable decodeTotalProgramPairSecond := by
  unfold decodeTotalProgramPairSecond
  exact Primrec.list_drop.to_comp.comp
    (decodeBitsComputable.comp decodeFirst_computable) decodeSecond_computable

/-- Sequential composition using the binary-length-framed program pair. -/
def totalLengthPrefixedComposeDecompressor (T : Map) : Map := fun pr =>
  (T (decodeTotalProgramPairFirst pr.1, pr.2)).bind fun y =>
    T (decodeTotalProgramPairSecond pr.1, y)

theorem totalLengthPrefixedComposeDecompressor_partrec
    {T : Map} (hT : isDecompressor T) :
    isDecompressor (totalLengthPrefixedComposeDecompressor T) := by
  have hfirst :
      Partrec (fun input : BitString × BitString =>
        T (decodeTotalProgramPairFirst input.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        Computable.snd)
  have hsecond :
      Partrec (fun input : (BitString × BitString) × BitString =>
        T (decodeTotalProgramPairSecond input.1.1, input.2)) :=
    Partrec.comp hT
      (Computable.pair
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        Computable.snd)
  exact Partrec.bind hfirst hsecond

theorem IsTotalProgram.compose_lengthPrefixed
    {T : Map} {p q : BitString}
    (hp : IsTotalProgram T p) (hq : IsTotalProgram T q) :
    IsTotalProgram (totalLengthPrefixedComposeDecompressor T)
      (totalProgramPairCode p q) := by
  intro z
  unfold totalLengthPrefixedComposeDecompressor
  rw [decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair, Part.bind_dom]
  exact ⟨hp z, hq _⟩

theorem totalLengthPrefixedComposeDecompressor_produces
    {T : Map} {p q y z w : BitString}
    (hp : produces T p z y) (hq : produces T q y w) :
    produces (totalLengthPrefixedComposeDecompressor T)
      (totalProgramPairCode p q) z w := by
  unfold totalLengthPrefixedComposeDecompressor produces
  rw [Part.mem_bind_iff]
  exact ⟨y, by simpa using hp, by simpa using hq⟩

/-- Logarithmically sharp composition of directed total reductions.  The only
nonconstant framing cost is twice the binary length of the first budget. -/
theorem TotalReducesWithin.trans_log
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalReducesWithin T x y epsilon →
      TotalReducesWithin T y z delta →
      TotalReducesWithin T x z
        (epsilon + delta + 2 * (Nat.bits epsilon).length + c) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (totalLengthPrefixedComposeDecompressor T)
      (totalLengthPrefixedComposeDecompressor_partrec hT.1)
  refine ⟨c + 1, ?_⟩
  intro x y z epsilon delta hxy hyz
  obtain ⟨p, hp_total, hp_len, hp_prod⟩ :=
    (totalReducesWithin_iff T x y epsilon).mp hxy
  obtain ⟨q, hq_total, hq_len, hq_prod⟩ :=
    (totalReducesWithin_iff T y z delta).mp hyz
  change p.length ≤ epsilon at hp_len
  change q.length ≤ delta at hq_len
  have hp_bits :
      (Nat.bits p.length).length ≤ (Nat.bits epsilon).length :=
    length_natBits_mono hp_len
  unfold TotalReducesWithin
  calc
    totalCondK T z x
        ≤ totalCondK (totalLengthPrefixedComposeDecompressor T) z x +
            (c : ENat) :=
      hc z x
    _ ≤ (programLength (totalProgramPairCode p q) : ENat) +
          (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength
        (hp_total.compose_lengthPrefixed hq_total)
        (totalLengthPrefixedComposeDecompressor_produces hp_prod hq_prod)
    _ ≤ ((epsilon + delta + 2 * (Nat.bits epsilon).length +
          (c + 1) : Nat) : ENat) := by
      change ((totalProgramPairCode p q).length : ENat) +
        (c : ENat) ≤ _
      rw [length_totalProgramPairCode]
      exact_mod_cast (show
        p.length + q.length + 2 * (Nat.bits p.length).length + 1 + c ≤
          epsilon + delta + 2 * (Nat.bits epsilon).length +
            (c + 1) by omega)

/-- Symmetric logarithmic composition.  The common framing budget uses the
binary length of `epsilon + delta`, which dominates either directed header. -/
theorem TotalEquivalentWithin.trans_log
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalEquivalentWithin T x y epsilon →
      TotalEquivalentWithin T y z delta →
      TotalEquivalentWithin T x z
        (epsilon + delta +
          2 * (Nat.bits (epsilon + delta)).length + c) := by
  obtain ⟨c, htrans⟩ := TotalReducesWithin.trans_log T hT
  refine ⟨c, ?_⟩
  intro x y z epsilon delta hxy hyz
  obtain ⟨hxy_forward, hxy_backward⟩ :=
    (totalEquivalentWithin_iff T x y epsilon).mp hxy
  obtain ⟨hyz_forward, hyz_backward⟩ :=
    (totalEquivalentWithin_iff T y z delta).mp hyz
  apply (totalEquivalentWithin_iff T x z
    (epsilon + delta +
      2 * (Nat.bits (epsilon + delta)).length + c)).mpr
  constructor
  · refine (htrans hxy_forward hyz_forward).mono ?_
    have hbits :
        (Nat.bits epsilon).length ≤
          (Nat.bits (epsilon + delta)).length :=
      length_natBits_mono (Nat.le_add_right epsilon delta)
    omega
  · refine (htrans hyz_backward hxy_backward).mono ?_
    have hbits :
        (Nat.bits delta).length ≤
          (Nat.bits (epsilon + delta)).length :=
      length_natBits_mono (Nat.le_add_left delta epsilon)
    omega

/-- `logSlack` packaging of the sharp directed composition theorem. -/
theorem TotalReducesWithin.trans_logSlack
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalReducesWithin T x y epsilon →
      TotalReducesWithin T y z delta →
      TotalReducesWithin T x z
        (epsilon + delta + logSlack c (epsilon + delta)) := by
  obtain ⟨c, htrans⟩ := TotalReducesWithin.trans_log T hT
  refine ⟨c + 2, ?_⟩
  intro x y z epsilon delta hxy hyz
  refine (htrans hxy hyz).mono ?_
  have hbits :
      (Nat.bits epsilon).length ≤
        (Nat.bits (epsilon + delta)).length :=
    length_natBits_mono (Nat.le_add_right epsilon delta)
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits (epsilon + delta)).length)]

/-- `logSlack` packaging of symmetric logarithmic composition. -/
theorem TotalEquivalentWithin.trans_logSlack
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ {x y z : BitString} {epsilon delta : Nat},
      TotalEquivalentWithin T x y epsilon →
      TotalEquivalentWithin T y z delta →
      TotalEquivalentWithin T x z
        (epsilon + delta + logSlack c (epsilon + delta)) := by
  obtain ⟨c, htrans⟩ := TotalEquivalentWithin.trans_log T hT
  refine ⟨c + 2, ?_⟩
  intro x y z epsilon delta hxy hyz
  refine (htrans hxy hyz).mono ?_
  unfold logSlack
  nlinarith [Nat.zero_le ((Nat.bits (epsilon + delta)).length)]

end Kolmogorov
