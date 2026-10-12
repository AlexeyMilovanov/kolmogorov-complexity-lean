import KolmogorovMathlib.StrongMerging.Coding.Encodings
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.StepWiseTotal.Part01
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalReduction
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.Complexity.Information.MutualInformation
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Strong merging, coding foundation II: programs, packets and interpreters (U02, L03, L04)

* **U02, `UpperLiteralAndHeaders`** (`sublinear-merging.tex`, appendix "Coding lemmas and
  constants before asymptotic notation", item 1, and the finite index of item 2).  Literal
  printing `C(x) ≤ |x| + b_lit`; the conversions `C(u | v) ≤ C(u) + c` and
  `C(u | v) ≤ CT(u | v) + c`; realization of a fixed decoder by the plain machine
  (`condC_le_of_decoder`) and, through the structural compiler of S01, by the canonical total
  interpreter (`totalC_le_of_decoder`); finite indexing in a model and in an intersection of two
  models; self-delimiting numeric fields `numField`, packets `numPacket` and the point packet
  `pointPacket` of two program bodies and `e`, with explicit length bounds.  Packets of program
  bodies use `totalProgramPairCode`, which does not double the first body (the library's
  `pairCode` does).
* **L03, `totalCodingInterface`.**  Extraction of an actual total witness from `CT(u | v) ≤ t`,
  the converse bound, and composition with logarithmic overhead, all at the canonical total
  interpreter `universalDecompressor` of S01.
* **L04, `boundedEvaluationInterface`.**  A `Nat.Partrec.Code` for every partial recursive
  machine (from `Partrec` alone, no ordinary optimality), and the step-indexed evaluator
  `conditionalRunOut` with soundness, completeness and monotonicity.
-/

namespace Kolmogorov.StrongMerging

/-! ### Real-valued conditional complexity -/

/-- The plain conditional complexity `C(u | v)` with respect to the plain machine `V`, as a real
number: the natural value of `condK V u v`.  For an optimal `V` it is finite
(`condK_ne_top_of_optimal`). -/
noncomputable def condC (V : Map) (u v : BitString) : ℝ :=
  ((condK V u v).toNat : ℝ)

/-- Plain complexity is conditional complexity with the empty condition. -/
theorem plainC_eq_condC_nil (V : Map) (u : BitString) : plainC V u = condC V u [] :=
  rfl

/-- `condC` is nonnegative. -/
theorem condC_nonneg (V : Map) (u v : BitString) : 0 ≤ condC V u v :=
  Nat.cast_nonneg _

/-- `plainC` is nonnegative. -/
theorem plainC_nonneg (V : Map) (u : BitString) : 0 ≤ plainC V u :=
  Nat.cast_nonneg _

/-- `totalC` is nonnegative. -/
theorem totalC_nonneg (u v : BitString) : 0 ≤ totalC u v :=
  Nat.cast_nonneg _

/-- For an optimal plain machine, conditional complexity is finite. -/
theorem condK_ne_top_of_optimal (V : Map) (hV : isOptimalConditional V) (u v : BitString) :
    condK V u v ≠ ⊤ := by
  obtain ⟨c, hc⟩ := condK_le_plainK V hV
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV u)
  exact ne_top_of_le_natCast (n := k + c)
    ((hc u v).trans (le_of_eq (by rw [← hk]; norm_cast)))

/-- An `ℕ∞` upper bound by a natural number bounds the natural value. -/
theorem toNat_le_of_le_natCast {a : ℕ∞} {n : ℕ} (h : a ≤ (n : ℕ∞)) : a.toNat ≤ n :=
  ENat.toNat_le_of_le_natCast h

/-- Transfer of an additive `ℕ∞` bound between conditional complexities to their real values,
given finiteness of the right side. -/
theorem condC_le_condC_add_of_condK {V : Map} {u v u' v' : BitString} {c : ℕ}
    (hfin : condK V u' v' ≠ ⊤) (h : condK V u v ≤ condK V u' v' + c) :
    condC V u v ≤ condC V u' v' + c := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have h1 : condK V u v ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have e : condC V u' v' = k := by rw [condC, ← hk, ENat.toNat_natCast]
  rw [e]
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- The binary length of a positive natural `m` is at most `log₂ m + 1`. -/
theorem bits_length_le_logb_add_one {m : ℕ} (hm : 0 < m) :
    ((Nat.bits m).length : ℝ) ≤ Real.logb 2 m + 1 := by
  rw [Nat.size_eq_bits_len]
  have hs : 0 < Nat.size m := Nat.size_pos.2 hm
  have hpow : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (by omega)
  have hreal : ((Nat.size m - 1 : ℕ) : ℝ) ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hm), Real.rpow_natCast]
    exact_mod_cast hpow
  have hsub : ((Nat.size m - 1 : ℕ) : ℝ) = (Nat.size m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  linarith

/-! ### U02: literal printing and conversions -/

/-- **Literal printing** (node U02): `C(x) ≤ |x| + b_lit`. -/
theorem plainC_le_length_add (V : Map) (hV : isOptimalConditional V) :
    ∃ blit : ℕ, ∀ x : BitString, plainC V x ≤ x.length + blit := by
  obtain ⟨c, hc⟩ := plainK_le_length V hV
  refine ⟨c, fun x => ?_⟩
  have h : (plainK V x).toNat ≤ x.length + c :=
    toNat_le_of_le_natCast (by exact_mod_cast hc x)
  unfold plainC
  exact_mod_cast h

/-- **A condition never hurts by more than a constant**: `C(u | v) ≤ C(u) + c`. -/
theorem condC_le_plainC_add (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, condC V u v ≤ plainC V u + c := by
  obtain ⟨c, hc⟩ := condK_le_plainK V hV
  refine ⟨c, fun u v => ?_⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV u)
  have h1 : condK V u v ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact hc u v
  have h3 : plainC V u = k := by rw [plainC, ← hk, ENat.toNat_natCast]
  rw [h3]
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Total-to-plain conversion** (node U02, used by U05): `C(u | v) ≤ CT(u | v) + c`.

Reference: appendix "Coding lemmas", item 5 ("charge total-to-plain interpreter overhead"). -/
theorem condC_le_totalC_add (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, condC V u v ≤ totalC u v + c := by
  obtain ⟨c, hc⟩ := hV.2 universalDecompressor isDecompressor_universalDecompressor
  refine ⟨c, fun u v => ?_⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (totalCondK_universalDecompressor_ne_top u v)
  have h1 : condK V u v ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact (hc u v).trans (add_le_add (condK_le_totalCondK _ u v) le_rfl)
  have h3 : totalC u v = k := by rw [totalC, ← hk, ENat.toNat_natCast]
  rw [h3]
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Plain realization of a fixed decoder** (node U02): for a fixed partial recursive decoder
`D` there is a constant `c` such that every program `p` producing `u` from the condition `y`
under `D` gives `C(u | y) ≤ |p| + c`. -/
theorem condC_le_of_decoder (V : Map) (hV : isOptimalConditional V) (D : Map)
    (hD : isDecompressor D) :
    ∃ c : ℕ, ∀ p y u : BitString, u ∈ D (p, y) → condC V u y ≤ p.length + c := by
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p y u hp => ?_⟩
  have h0 : condK D u y ≤ (p.length : ℕ∞) := (condK_le_iff D u y p.length).2 ⟨p, le_rfl, hp⟩
  have h1 : condK V u y ≤ ((p.length + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add]
    exact (hc u y).trans (add_le_add h0 le_rfl)
  unfold condC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Total realization of a fixed decoder through S01** (node U02): for a fixed partial
recursive decoder `D` there is a constant `c` such that every program `p` on which `D` halts for
every condition, and which produces `u` from `y`, gives `CT(u | y) ≤ |p| + c` at the canonical
total interpreter.  The constant is fixed with `D`, before `p`.

Reference: appendix "Two interpreters, with explicit realization obligations". -/
theorem totalC_le_of_decoder (D : Map) (hD : isDecompressor D) :
    ∃ c : ℕ, ∀ p : BitString, (∀ y : BitString, (D (p, y)).Dom) →
      ∀ y u : BitString, u ∈ D (p, y) → totalC u y ≤ p.length + c := by
  obtain ⟨pre, hpre⟩ := exists_prefix_universalDecompressor_eq D hD
  refine ⟨pre.length, fun p hp y u hu => ?_⟩
  have htot : IsTotalProgram universalDecompressor (pre ++ p) := fun z => by
    rw [hpre]
    exact hp z
  have hprod : produces universalDecompressor (pre ++ p) y u := by
    change u ∈ universalDecompressor (pre ++ p, y)
    rw [hpre]
    exact hu
  have h := totalCondK_le_programLength htot hprod
  have h' : totalCondK universalDecompressor u y ≤ ((p.length + pre.length : ℕ) : ℕ∞) := by
    simp only [programLength, List.length_append] at h
    rw [Nat.add_comm]
    exact h
  have h'' : (totalCondK universalDecompressor u y).toNat ≤ p.length + pre.length :=
    toNat_le_of_le_natCast h'
  unfold totalC
  exact_mod_cast h''

/-! ### U02: finite indexing -/

/-- **Index program** (node U02): a member `x` of a finite model `F` is produced from the canonical
code of `F` by the fixed index decoder `reductionSetIndexDecompressor`, from a program of length
`Nat.clog 2 |F|`. -/
theorem exists_index_program (F : Finset BitString) (x : BitString) (hx : x ∈ F) :
    ∃ r : BitString, x ∈ reductionSetIndexDecompressor (r, canonicalFiniteSetCode F) ∧
      r.length = Nat.clog 2 F.card := by
  have hF : F.Nonempty := ⟨x, hx⟩
  have hidxCard : (canonicalFinsetList F).findIdx (· == x) < F.card := by
    rw [← length_canonicalFinsetList, List.findIdx_lt_length]
    exact ⟨x, mem_canonicalFinsetList.mpr hx, by simp⟩
  have hidxPow : (canonicalFinsetList F).findIdx (· == x) < 2 ^ finiteSetLogCard F :=
    hidxCard.trans_le (finiteSetLogCard_spec F)
  refine ⟨chunkAddress ((canonicalFinsetList F).findIdx (· == x)) (finiteSetLogCard F), ?_, ?_⟩
  · rw [canonicalFiniteSetCode_eq_codedUniformOn_code F hF]
    exact reductionSetIndexDecompressor_produces F hF x hx
  · exact chunkAddress_length _ _ hidxPow

/-- The ceiling binary logarithm exceeds the real one by less than one:
`⌈log₂ N⌉ ≤ log₂ N + 1` (at `N = 0` both logarithms are `0`). -/
theorem clog_le_logb_add_one (N : ℕ) : (Nat.clog 2 N : ℝ) ≤ Real.logb 2 N + 1 := by
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h := Real.ceil_logb_natCast (b := 2) hNr
  rw [Int.clog_natCast] at h
  push_cast at h
  have h2 := Int.ceil_lt_add_one (Real.logb 2 (N : ℝ))
  rw [h] at h2
  push_cast at h2
  linarith

/-- **Finite index in a model** (node U02, appendix item 2, `UpperFiniteIndex`): a member `x` of a
finite model `F` has `C(x | F) ≤ log₂ |F| + c`. -/
theorem condC_le_logb_card (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (F : Finset BitString) (x : BitString), x ∈ F →
      condC V x (canonicalFiniteSetCode F) ≤ Real.logb 2 F.card + c := by
  obtain ⟨c, hc⟩ := condC_le_of_decoder V hV reductionSetIndexDecompressor
    reductionSetIndexDecompressor_partrec
  refine ⟨c + 1, fun F x hx => ?_⟩
  obtain ⟨r, hr, hlen⟩ := exists_index_program F x hx
  have h := hc r (canonicalFiniteSetCode F) x hr
  have hcl := clog_le_logb_add_one F.card
  rw [hlen] at h
  push_cast
  linarith

/-- The code of the intersection of the two models decoded from a pair code `pairCode a b`: the
canonical code of the members of the first decoded list that occur in the second. -/
noncomputable def interCode (w : BitString) : BitString :=
  listModelCode ((canonicalPointListOfCode (decodeFirst w)).filter
    (fun z => decide (z ∈ canonicalPointListOfCode (decodeSecond w))))

/-- On a pair of canonical model codes, `interCode` is the canonical code of the intersection. -/
theorem interCode_pairCode (A B : Finset BitString) :
    interCode (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) =
      canonicalFiniteSetCode (A ∩ B) := by
  rw [interCode, decodeFirst_pairCode, decodeSecond_pairCode,
    canonicalPointListOfCode_canonicalFiniteSetCode,
    canonicalPointListOfCode_canonicalFiniteSetCode]
  apply listModelCode_eq
  ext z
  simp

/-- `interCode` is computable. -/
theorem interCode_computable : Computable interCode := by
  have hfilter : Primrec₂ (fun (L : List BitString) (l₂ : List BitString) =>
      L.filter (fun z => decide (z ∈ l₂))) :=
    PrimrecRel.listFilter (R := fun (z : BitString) (l₂ : List BitString) => z ∈ l₂)
      (Primrec₂.primrecRel bitString_mem_primrec)
  exact listModelCode_computable.comp (hfilter.to_comp.comp
    (canonicalPointListOfCode_computable.comp decodeFirst_computable)
    (canonicalPointListOfCode_computable.comp decodeSecond_computable))

/-- **Finite index in an intersection** (node U02, used by U06): a member `x` of `A ∩ B` has
`C(x | (A, B)) ≤ log₂ |A ∩ B| + c`, where the condition is the pair of the two model codes. -/
theorem condC_le_logb_card_inter (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (A B : Finset BitString) (x : BitString), x ∈ A ∩ B →
      condC V x (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) ≤
        Real.logb 2 (A ∩ B).card + c := by
  obtain ⟨c₁, h₁⟩ := condK_cond_map_le V hV interCode interCode_computable
  obtain ⟨c₂, h₂⟩ := condC_le_logb_card V hV
  refine ⟨c₁ + c₂, fun A B x hx => ?_⟩
  have h := h₁ x (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B))
  rw [interCode_pairCode] at h
  have h3 := condC_le_condC_add_of_condK (condK_ne_top_of_optimal V hV _ _) h
  have h2 := h₂ (A ∩ B) x hx
  push_cast
  linarith

/-- `headerLog n ≥ 1`. -/
theorem one_le_headerLog (n : ℕ) : 1 ≤ headerLog n := by
  unfold headerLog
  exact Nat.succ_le_of_lt (Nat.clog_pos one_lt_two (by omega))

/-! ### U02: packets and headers -/

/-- A self-delimiting numeric field: the binary digits of `k` framed by the binary-length-framed
pair code `totalProgramPairCode`, followed by the rest `rest` of the packet. -/
def numField (k : ℕ) (rest : BitString) : BitString :=
  totalProgramPairCode (Nat.bits k) rest

/-- The total decoder of a numeric field: the number and the rest of the packet. -/
def numFieldDecode (w : BitString) : ℕ × BitString :=
  (decodeBits (decodeTotalProgramPairFirst w), decodeTotalProgramPairSecond w)

/-- Decoding a numeric field recovers the number and the rest of the packet. -/
@[simp] theorem numFieldDecode_numField (k : ℕ) (rest : BitString) :
    numFieldDecode (numField k rest) = (k, rest) := by
  simp [numFieldDecode, numField, decodeBits_natBits]

/-- The numeric-field decoder is computable. -/
theorem numFieldDecode_computable : Computable numFieldDecode := by
  exact (decodeBits_computable.comp decodeTotalProgramPairFirst_computable).pair
    decodeTotalProgramPairSecond_computable

/-- A packet of numeric fields `ks` in front of a body. -/
def numPacket (ks : List ℕ) (body : BitString) : BitString :=
  ks.foldr numField body

/-- The point packet of the merger: the integer budget `e` and the two total witness bodies
`pA`, `pB`, framed so that the first body is not doubled. -/
def pointPacket (e : ℕ) (pA pB : BitString) : BitString :=
  numField e (totalProgramPairCode pA pB)

/-- **Point-packet length** (node U02): a point packet with bodies of length at most `e` has
length at most `7 (e + 1)`. -/
theorem length_pointPacket_le (e : ℕ) (pA pB : BitString) (hA : pA.length ≤ e)
    (hB : pB.length ≤ e) : (pointPacket e pA pB).length ≤ 7 * (e + 1) := by
  have hs : ∀ k : ℕ, (Nat.bits k).length ≤ k := fun k => by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  unfold pointPacket numField
  rw [length_totalProgramPairCode, length_totalProgramPairCode]
  have h1 := hs e
  have h2 := hs (Nat.bits e).length
  have h3 := hs pA.length
  omega

/-- **Header bound** (node U02): a packet of at most `K` numeric fields, each at most `b (n + 1)`,
costs at most `c ⌈log₂ (n + 2)⌉` bits beyond its body, with `c` depending only on `b` and `K`. -/
theorem length_numPacket_le (b K : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (ks : List ℕ) (body : BitString), ks.length ≤ K →
      (∀ k ∈ ks, k ≤ b * (n + 1)) → (numPacket ks body).length ≤ body.length + c * headerLog n := by
  refine ⟨K * (3 * Nat.size b + 4), fun n ks body hK hks => ?_⟩
  have hl1 := one_le_headerLog n
  have hsizeN : Nat.size (n + 1) ≤ headerLog n := by
    unfold headerLog
    rw [Nat.size_le]
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (n + 2))
  have hfield : ∀ k, k ≤ b * (n + 1) → (Nat.bits k).length +
      2 * (Nat.bits (Nat.bits k).length).length + 1 ≤ (3 * Nat.size b + 4) * headerLog n := by
    intro k hk
    have h1 : (Nat.bits k).length ≤ Nat.size b + Nat.size (n + 1) := by
      rw [Nat.size_eq_bits_len, Nat.size_le]
      calc k ≤ b * (n + 1) := hk
        _ < 2 ^ Nat.size b * 2 ^ Nat.size (n + 1) :=
          Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self b) (Nat.lt_size_self _)
        _ = 2 ^ (Nat.size b + Nat.size (n + 1)) := (pow_add 2 _ _).symm
    have h2 : (Nat.bits (Nat.bits k).length).length ≤ (Nat.bits k).length := by
      rw [Nat.size_eq_bits_len (Nat.bits k).length]
      exact Nat.size_le.2 Nat.lt_two_pow_self
    have h3 : Nat.size b ≤ Nat.size b * headerLog n := Nat.le_mul_of_pos_right _ hl1
    have h4 : (3 * Nat.size b + 4) * headerLog n = 3 * (Nat.size b * headerLog n) +
        4 * headerLog n := by ring
    rw [h4]
    omega
  have key : ∀ ks : List ℕ, (∀ k ∈ ks, k ≤ b * (n + 1)) →
      (numPacket ks body).length ≤
        body.length + ks.length * ((3 * Nat.size b + 4) * headerLog n) := by
    intro ks
    induction ks with
    | nil =>
      intro _
      simp [numPacket]
    | cons k ks ih =>
      intro h
      have hk := hfield k (h k (by simp))
      have ih' := ih (fun j hj => h j (by simp [hj]))
      have hlen : (numPacket (k :: ks) body).length = (Nat.bits k).length +
          (numPacket ks body).length + 2 * (Nat.bits (Nat.bits k).length).length + 1 := by
        simp only [numPacket, List.foldr_cons]
        exact length_totalProgramPairCode _ _
      rw [hlen, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  have h := key ks hks
  have hmul : ks.length * ((3 * Nat.size b + 4) * headerLog n) ≤
      K * (3 * Nat.size b + 4) * headerLog n := by
    rw [Nat.mul_assoc K]
    exact Nat.mul_le_mul_right _ hK
  omega

/-- **Node U02, `UpperLiteralAndHeaders`.**  For an optimal plain machine `V` there are constants
for literal printing, the plain conditions bound, the total-to-plain conversion and the finite
indices in a model and in an intersection; every fixed decoder is realized by `V` and, through
the structural compiler S01, by `universalDecompressor`, each with a constant fixed with the
decoder; point packets have length at most `7 (e + 1)`. -/
theorem upperLiteralAndHeaders (V : Map) (hV : isOptimalConditional V) :
    (∃ blit : ℕ, ∀ x : BitString, plainC V x ≤ x.length + blit) ∧
      (∃ c : ℕ, ∀ u v : BitString, condC V u v ≤ plainC V u + c) ∧
      (∃ c : ℕ, ∀ u v : BitString, condC V u v ≤ totalC u v + c) ∧
      (∃ c : ℕ, ∀ (F : Finset BitString) (x : BitString), x ∈ F →
        condC V x (canonicalFiniteSetCode F) ≤ Real.logb 2 F.card + c) ∧
      (∃ c : ℕ, ∀ (A B : Finset BitString) (x : BitString), x ∈ A ∩ B →
        condC V x (pairCode (canonicalFiniteSetCode A) (canonicalFiniteSetCode B)) ≤
          Real.logb 2 (A ∩ B).card + c) ∧
      (∀ D : Map, isDecompressor D → ∃ c : ℕ, ∀ p y u : BitString, u ∈ D (p, y) →
        condC V u y ≤ p.length + c) ∧
      (∀ D : Map, isDecompressor D → ∃ c : ℕ, ∀ p : BitString,
        (∀ y : BitString, (D (p, y)).Dom) → ∀ y u : BitString, u ∈ D (p, y) →
          totalC u y ≤ p.length + c) ∧
      (∀ (e : ℕ) (pA pB : BitString), pA.length ≤ e → pB.length ≤ e →
        (pointPacket e pA pB).length ≤ 7 * (e + 1)) :=
  ⟨plainC_le_length_add V hV, condC_le_plainC_add V hV, condC_le_totalC_add V hV,
    condC_le_logb_card V hV, condC_le_logb_card_inter V hV, condC_le_of_decoder V hV,
    totalC_le_of_decoder, length_pointPacket_le⟩

/-! ### L03: the total coding interface at the canonical interpreter -/

namespace Lower

/-- **Total-witness extraction** (node L03): `CT(u | v) ≤ t` yields an actual program body of
length at most `t` that halts on every condition and produces `u` from `v` under
`universalDecompressor`. -/
theorem exists_totalProgram_of_totalC_le {u v : BitString} {t : ℕ} (h : totalC u v ≤ t) :
    ∃ p : BitString, IsTotalProgram universalDecompressor p ∧ p.length ≤ t ∧
      produces universalDecompressor p v u := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (totalCondK_universalDecompressor_ne_top u v)
  have hkt : k ≤ t := by
    have : totalC u v = k := by rw [totalC, ← hk, ENat.toNat_natCast]
    rw [this] at h
    exact_mod_cast h
  have hle : totalCondK universalDecompressor u v ≤ (t : ℕ∞) := by
    rw [← hk]
    exact_mod_cast hkt
  obtain ⟨p, hp, hlen, hprod⟩ := (totalCondK_le_iff universalDecompressor u v t).1 hle
  exact ⟨p, hp, hlen, hprod⟩

/-- **Witness bound** (node L03): a total program producing `u` from `v` bounds `CT(u | v)` by its
length. -/
theorem totalC_le_length_of_totalProgram {p u v : BitString}
    (hp : IsTotalProgram universalDecompressor p) (h : produces universalDecompressor p v u) :
    totalC u v ≤ p.length := by
  have h' := totalCondK_le_programLength hp h
  have h'' : (totalCondK universalDecompressor u v).toNat ≤ p.length :=
    toNat_le_of_le_natCast h'
  unfold totalC
  exact_mod_cast h''

/-- **Composition of total reductions** (node L03): `CT(z | x) ≤ CT(y | x) + CT(z | y) +
2 log₂ (CT(y | x) + 2) + c`, from the library's `TotalReducesWithin.trans_log` at the canonical
total interpreter. -/
theorem totalC_trans : ∃ c : ℕ, ∀ x y z : BitString,
    totalC z x ≤ totalC y x + totalC z y + 2 * Real.logb 2 (totalC y x + 2) + c := by
  obtain ⟨c, hc⟩ := TotalReducesWithin.trans_log universalDecompressor
    isOptimalTotalConditional_universalDecompressor
  refine ⟨c + 2, fun x y z => ?_⟩
  obtain ⟨ε, hε⟩ := ENat.ne_top_iff_exists.mp (totalCondK_universalDecompressor_ne_top y x)
  obtain ⟨δ, hδ⟩ := ENat.ne_top_iff_exists.mp (totalCondK_universalDecompressor_ne_top z y)
  have h : totalCondK universalDecompressor z x ≤
      ((ε + δ + 2 * (Nat.bits ε).length + c : ℕ) : ℕ∞) :=
    hc (le_of_eq hε.symm) (le_of_eq hδ.symm)
  have h' := toNat_le_of_le_natCast h
  have e1 : totalC y x = ε := by rw [totalC, ← hε, ENat.toNat_natCast]
  have e2 : totalC z y = δ := by rw [totalC, ← hδ, ENat.toNat_natCast]
  have hb : ((Nat.bits ε).length : ℝ) ≤ Real.logb 2 ((ε : ℝ) + 2) + 1 := by
    rcases Nat.eq_zero_or_pos ε with h0 | h0
    · have hb0 : (Nat.bits ε).length = 0 := by
        subst h0
        simp
      have hε0 := Nat.cast_nonneg (α := ℝ) ε
      have := Real.logb_nonneg (b := 2) one_lt_two (show (1 : ℝ) ≤ (ε : ℝ) + 2 by linarith)
      rw [hb0, Nat.cast_zero]
      linarith
    · have h1 := bits_length_le_logb_add_one h0
      have h2 : Real.logb 2 (ε : ℝ) ≤ Real.logb 2 ((ε : ℝ) + 2) :=
        Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h0) (by linarith)
      linarith
  have e3 : totalC z x = ((totalCondK universalDecompressor z x).toNat : ℝ) := rfl
  have h'' := (Nat.cast_le (α := ℝ)).2 h'
  push_cast at h''
  rw [e1, e2, e3]
  push_cast
  linarith

/-- **A strong model has a short total witness** (node L03): if `F` is `ε`-strong for `x`, some
program of length at most `⌊ε⌋₊` halts on every condition under `universalDecompressor` and
produces the canonical code of `F` from `x`. -/
theorem exists_totalProgram_of_isStrongModel {x : BitString} {F : Finset BitString} {ε : ℝ}
    (h : IsStrongModel x F ε) : ∃ p : BitString, IsTotalProgram universalDecompressor p ∧
      p.length ≤ ⌊ε⌋₊ ∧ produces universalDecompressor p x (canonicalFiniteSetCode F) := by
  apply exists_totalProgram_of_totalC_le
  have h' : totalC (canonicalFiniteSetCode F) x ≤ ε := h
  unfold totalC at h' ⊢
  exact_mod_cast Nat.le_floor h'

/-- **One compiled total program per packet** (node L03, the uniform-compilation interface of
S01): for a fixed partial recursive decoder `D` there is one prefix `pre`, fixed before every
packet, such that for every packet `p` on which `D` halts for all conditions, `pre ++ p` is an
all-input total program of `universalDecompressor` of length `|pre| + |p|` with the outputs
of `D` on `p`.  This is the single program that later finite searches over candidate programs
must meet. -/
theorem exists_compiled_totalProgram (D : Map) (hD : isDecompressor D) :
    ∃ pre : BitString, ∀ p : BitString, (∀ y : BitString, (D (p, y)).Dom) →
      IsTotalProgram universalDecompressor (pre ++ p) ∧
        (pre ++ p).length = pre.length + p.length ∧
        ∀ y u : BitString, u ∈ D (p, y) → produces universalDecompressor (pre ++ p) y u := by
  obtain ⟨pre, hpre⟩ := exists_prefix_universalDecompressor_eq D hD
  refine ⟨pre, fun p hp => ⟨fun z => ?_, by simp, fun y u hu => ?_⟩⟩
  · rw [hpre]
    exact hp z
  · change u ∈ universalDecompressor (pre ++ p, y)
    rw [hpre]
    exact hu

/-- **Node L03, `totalCodingInterface`.**  At the canonical total interpreter
`universalDecompressor` of S01: the structural compiler (one prefix per machine, fixed before
programs and conditions), total optimality, extraction of total witnesses, the witness bound,
realization of fixed decoders on all-input-total programs, and composition with logarithmic
overhead. -/
theorem totalCodingInterface :
    (∀ D : Map, isDecompressor D → ∃ pre : BitString, ∀ p y : BitString,
        universalDecompressor (pre ++ p, y) = D (p, y)) ∧
      IsOptimalTotalConditional universalDecompressor ∧
      (∀ (u v : BitString) (t : ℕ), totalC u v ≤ t → ∃ p : BitString,
        IsTotalProgram universalDecompressor p ∧ p.length ≤ t ∧
          produces universalDecompressor p v u) ∧
      (∀ p u v : BitString, IsTotalProgram universalDecompressor p →
        produces universalDecompressor p v u → totalC u v ≤ p.length) ∧
      (∀ D : Map, isDecompressor D → ∃ c : ℕ, ∀ p : BitString,
        (∀ y : BitString, (D (p, y)).Dom) → ∀ y u : BitString, u ∈ D (p, y) →
          totalC u y ≤ p.length + c) ∧
      (∃ c : ℕ, ∀ x y z : BitString,
        totalC z x ≤ totalC y x + totalC z y + 2 * Real.logb 2 (totalC y x + 2) + c) :=
  ⟨exists_prefix_universalDecompressor_eq, isOptimalTotalConditional_universalDecompressor,
    fun _ _ _ h => exists_totalProgram_of_totalC_le h,
    fun _ _ _ hp h => totalC_le_length_of_totalProgram hp h, totalC_le_of_decoder, totalC_trans⟩

/-! ### L04: bounded evaluation -/

/-- **A code for every partial recursive machine** (node L04): `Partrec D` alone gives a
`Nat.Partrec.Code` whose evaluation is the encoded graph of `D`; no ordinary optimality is
assumed, so it applies to the total interpreter. -/
theorem exists_isCodeFor_of_isDecompressor {D : Map} (hD : isDecompressor D) :
    ∃ c : Nat.Partrec.Code, IsCodeFor c D :=
  Nat.Partrec.Code.exists_code.mp hD

/-- The step-indexed evaluator `conditionalRunOut c` is computable in the stage, the program and
the condition. -/
theorem conditionalRunOut_computable (c : Nat.Partrec.Code) :
    Computable (fun q : ℕ × BitString × BitString => conditionalRunOut c q.1 q.2.1 q.2.2) := by
  have h : Primrec (fun q : ℕ × BitString × BitString =>
      conditionalRunOut c q.1 q.2.1 q.2.2) := by
    unfold conditionalRunOut
    apply Primrec.option_bind
    · exact (evaln_primrec c).comp Primrec.fst
        (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.decode.comp Primrec.snd
  exact h.to_comp

/-- **Node L04, `boundedEvaluationInterface`.**  Every partial recursive machine `D` (the plain
machine `V`, or the total interpreter `universalDecompressor`) has a code `c` whose finite,
decidable stage evaluator `conditionalRunOut c` is sound, complete for eventual halting and
monotone in the stage, and computable as a function of the stage. -/
theorem boundedEvaluationInterface (D : Map) (hD : isDecompressor D) :
    ∃ c : Nat.Partrec.Code,
      (∀ (t : ℕ) (p y u : BitString), conditionalRunOut c t p y = some u → produces D p y u) ∧
      (∀ p y u : BitString, produces D p y u → ∃ t, conditionalRunOut c t p y = some u) ∧
      (∀ (t t' : ℕ) (p y u : BitString), t ≤ t' → conditionalRunOut c t p y = some u →
        conditionalRunOut c t' p y = some u) ∧
      Computable (fun q : ℕ × BitString × BitString => conditionalRunOut c q.1 q.2.1 q.2.2) := by
  obtain ⟨c, hc⟩ := exists_isCodeFor_of_isDecompressor hD
  exact ⟨c, fun _ _ _ _ h => conditionalRunOut_sound hc h,
    fun _ _ _ h => conditionalRunOut_complete hc h,
    fun _ _ _ _ _ htt' h => conditionalRunOut_mono c htt' h, conditionalRunOut_computable c⟩

end Lower

end Kolmogorov.StrongMerging
