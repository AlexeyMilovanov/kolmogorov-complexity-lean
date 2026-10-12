import KolmogorovMathlib.StrongMerging.Upper.Cores
import KolmogorovMathlib.StrongMerging.Upper.DecodersCore

/-!
# Qualifying instances and the generic table machine

The qualifying instances of the core decoders and the generic table machine on which
the component decoder (M01) and the local and point decoders (M03) are built.

Part of `KolmogorovMathlib.StrongMerging.Upper.CoreDecoders`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### Qualifying instances -/

/-- **A qualifying instance of the minimum-core layer**: total witnesses `pA, pB` of length at most
`e ≤ n`, an `n`-bit string `x`, witness outputs on `x` equal to the canonical codes of `A` and `B`,
and `A, B` `e`-sufficient for `x` (so `x ∈ A ∩ B`). -/
structure IsCoreInstance (V : Map) (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) :
    Prop where
  /-- The row witness is total. -/
  totalA : IsTotalProgram universalDecompressor pA
  /-- The row witness has length at most `e`. -/
  lenA : pA.length ≤ e
  /-- The column witness is total. -/
  totalB : IsTotalProgram universalDecompressor pB
  /-- The column witness has length at most `e`. -/
  lenB : pB.length ≤ e
  /-- The budget is at most the length. -/
  le_n : e ≤ n
  /-- `x` has length `n`. -/
  length_x : x.length = n
  /-- `pA(x) = A`. -/
  prodA : produces universalDecompressor pA x (canonicalFiniteSetCode A)
  /-- `pB(x) = B`. -/
  prodB : produces universalDecompressor pB x (canonicalFiniteSetCode B)
  /-- `A` is `e`-sufficient for `x`. -/
  sufA : IsSufficientModel V x A e
  /-- `B` is `e`-sufficient for `x`. -/
  sufB : IsSufficientModel V x B e

/-- The shape graph of an instance: witness outputs `progOut pA`, `progOut pB`, data length `n`
and floor size buckets `a = ⌊log₂ |A|⌋`, `b = ⌊log₂ |B|⌋`. -/
noncomputable def coreShape (pA pB : BitString) (n : ℕ) (A B : Finset BitString) : ShapeParams :=
  instShape pA pB n (Nat.log 2 A.card) (Nat.log 2 B.card)

/-- The component `C_0` of the actual string `x` in the shape graph of the instance. -/
noncomputable def instComponent (pA pB : BitString) (n : ℕ) (A B : Finset BitString)
    (x : BitString) : Finset BitString :=
  shapeComponent (coreShape pA pB n A B) (shapeEdges (coreShape pA pB n A B))
    (shapeSrc (coreShape pA pB n A B) x)

section Instance

variable {V : Map} {n e : ℕ} {pA pB x : BitString} {A B : Finset BitString}

/-- The row output of `x` is the code of `A`. -/
theorem IsCoreInstance.outA_eq (h : IsCoreInstance V n e pA pB x A B) :
    (coreShape pA pB n A B).outA x = canonicalFiniteSetCode A :=
  progOut_eq_of_mem h.prodA

/-- The column output of `x` is the code of `B`. -/
theorem IsCoreInstance.outB_eq (h : IsCoreInstance V n e pA pB x A B) :
    (coreShape pA pB n A B).outB x = canonicalFiniteSetCode B :=
  progOut_eq_of_mem h.prodB

/-- The actual string is an edge of the shape graph of the instance. -/
theorem IsCoreInstance.mem_shapeEdges (h : IsCoreInstance V n e pA pB x A B) :
    x ∈ shapeEdges (coreShape pA pB n A B) :=
  mem_shapeEdges_of _ h.length_x h.outA_eq h.outB_eq h.sufA.1 h.sufB.1 rfl rfl

end Instance

/-! ### The generic table machine -/

/-- The typed endpoint label of a side: a row (`false`) or a column (`true`). -/
def coreEnd (side : Bool) (w : BitString) : BitString ⊕ BitString :=
  if side then Sum.inr w else Sum.inl w

/-- Decode `m` numeric fields from the front of a packet; return them and the rest. -/
def coreFields : ℕ → BitString → List ℕ × BitString
  | 0, w => ([], w)
  | m + 1, w => ((numFieldDecode w).1 :: (coreFields m (numFieldDecode w).2).1,
      (coreFields m (numFieldDecode w).2).2)

/-- Decoding the fields of a numeric packet recovers them and the body. -/
theorem coreFields_numPacket (ks : List ℕ) (body : BitString) :
    coreFields ks.length (numPacket ks body) = (ks, body) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    unfold numPacket at ih ⊢
    simp only [List.length_cons, coreFields, List.foldr_cons, numFieldDecode_numField, ih]

/-- One step of field decoding with an accumulator: append the next field, keep the rest. -/
def coreFieldStep (st : List ℕ × BitString) : List ℕ × BitString :=
  (st.1 ++ [(numFieldDecode st.2).1], (numFieldDecode st.2).2)

/-- Iterating the accumulator step reads the fields in order. -/
theorem coreFieldStep_iterate (m : ℕ) : ∀ (acc : List ℕ) (w : BitString),
    coreFieldStep^[m] (acc, w) = (acc ++ (coreFields m w).1, (coreFields m w).2) := by
  induction m with
  | zero => intro acc w; simp [coreFields]
  | succ m ih =>
    intro acc w
    rw [Function.iterate_succ_apply, coreFieldStep, ih]
    simp [coreFields]

/-- **Field decoding is computable.**

Proof sketch: `coreFields m w` is the `m`-fold iteration of
`(acc, w) ↦ (acc ++ [(numFieldDecode w).1], (numFieldDecode w).2)` from `([], w)`
(induction on `m`, generalizing the accumulator); `Primrec.nat_iterate`/`Computable.nat_rec`
with `numFieldDecode_computable`, `Computable.list_append` (as E's `decodeFields_computable`). -/
theorem coreFields_computable : Computable₂ coreFields := by
  have hstep : Computable coreFieldStep :=
    (Primrec.list_append.to_comp.comp Computable.fst
      (Primrec.list_cons.to_comp.comp (Computable.fst.comp (numFieldDecode_computable.comp
        Computable.snd)) (Computable.const []))).pair
      (Computable.snd.comp (numFieldDecode_computable.comp Computable.snd))
  have hrec : Computable fun q : ℕ × BitString =>
      Nat.rec (motive := fun _ => List ℕ × BitString) ([], q.2)
        (fun _ IH => coreFieldStep IH) q.1 :=
    Computable.nat_rec Computable.fst ((Computable.const []).pair Computable.snd)
      (hstep.comp (Computable.snd.comp Computable.snd)).to₂
  refine hrec.of_eq fun q => ?_
  have hit : ∀ m : ℕ, ∀ st : List ℕ × BitString,
      Nat.rec (motive := fun _ => List ℕ × BitString) st (fun _ IH => coreFieldStep IH) m =
        coreFieldStep^[m] st := by
    intro m st
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ← ih]
  rw [hit, coreFieldStep_iterate]
  simp

/-- The packet of the core decoders: numeric fields `ks`, the two witness bodies and a tail. -/
def corePacket (ks : List ℕ) (pA pB tail : BitString) : BitString :=
  numPacket ks (totalProgramPairCode pA (totalProgramPairCode pB tail))

/-- The input of a decoder kernel: the two output tables, the numeric fields, the tail and the
condition. -/
abbrev CoreIn : Type :=
  (List (BitString × BitString) × List (BitString × BitString)) × List ℕ × BitString × BitString

/-- **The generic table machine.**  Decode `m` numeric fields (field `0` is the data length `n`),
the witness bodies and the tail; compute the output tables of both witnesses by complete runs;
apply the kernel.  It diverges only if a witness run diverges. -/
noncomputable def coreMachine (m : ℕ) (ker : CoreIn → Part BitString) : Map := fun q =>
  (runTable (decodeTotalProgramPairFirst (coreFields m q.1).2) ((coreFields m q.1).1.getD 0 0)).bind
    fun TA => (runTable (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond
      (coreFields m q.1).2)) ((coreFields m q.1).1.getD 0 0)).bind fun TB =>
        ker ((TA, TB), (coreFields m q.1).1,
          decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (coreFields m q.1).2), q.2)

/-- **The table machine is partial recursive** for a partial recursive kernel.

Proof sketch: `q ↦ coreFields m q.1` is computable (`coreFields_computable`); the bodies by
`decodeTotalProgramPairFirst_computable`/`…Second_computable`; `runTable_partrec` composed with
these (`Partrec₂.comp`); two `Partrec.bind`s; the kernel argument tuple is computable in
`(q, TA, TB)` (`Computable.pair`), so `hker.comp` gives the innermost step.  Prove the argument
tuples as typed `have`s before `.comp` (whnf pitfall of B2). -/
theorem coreMachine_partrec (m : ℕ) {ker : CoreIn → Part BitString} (hker : Partrec ker) :
    isDecompressor (coreMachine m ker) := by
  have hdf : Computable fun q : BitString × BitString => coreFields m q.1 :=
    coreFields_computable.comp (Computable.const m) Computable.fst
  have hks : Computable fun q : BitString × BitString => (coreFields m q.1).1 :=
    Computable.fst.comp hdf
  have hn : Computable fun q : BitString × BitString => (coreFields m q.1).1.getD 0 0 :=
    (Primrec.list_getD 0).to_comp.comp hks (Computable.const 0)
  have hpA : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairFirst (coreFields m q.1).2 :=
    decodeTotalProgramPairFirst_computable.comp (Computable.snd.comp hdf)
  have hpB : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (coreFields m q.1).2) :=
    decodeTotalProgramPairFirst_computable.comp
      (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf))
  have htail : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairSecond (decodeTotalProgramPairSecond (coreFields m q.1).2) :=
    decodeTotalProgramPairSecond_computable.comp
      (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf))
  have hargs : Computable fun r : ((BitString × BitString) × List (BitString × BitString)) ×
      List (BitString × BitString) =>
      (((r.1.2, r.2), (coreFields m r.1.1.1).1, decodeTotalProgramPairSecond
        (decodeTotalProgramPairSecond (coreFields m r.1.1.1).2), r.1.1.2) : CoreIn) :=
    ((Computable.snd.comp Computable.fst).pair Computable.snd).pair
      ((hks.comp (Computable.fst.comp Computable.fst)).pair
        ((htail.comp (Computable.fst.comp Computable.fst)).pair
          (Computable.snd.comp (Computable.fst.comp Computable.fst))))
  have hinner : Partrec₂ fun (p : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) =>
      ker ((p.2, TB), (coreFields m p.1.1).1, decodeTotalProgramPairSecond
        (decodeTotalProgramPairSecond (coreFields m p.1.1).2), p.1.2) :=
    hker.comp hargs
  have hmid : Partrec₂ fun (q : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (coreFields m q.1).2))
        ((coreFields m q.1).1.getD 0 0)).bind fun TB =>
          ker ((TA, TB), (coreFields m q.1).1, decodeTotalProgramPairSecond
            (decodeTotalProgramPairSecond (coreFields m q.1).2), q.2) :=
    Partrec.bind (runTable_partrec.comp (hpB.comp Computable.fst) (hn.comp Computable.fst)) hinner
  exact (Partrec.bind (runTable_partrec.comp hpA hn) hmid).of_eq fun q => rfl

/-- **Evaluation of the table machine on its packet.**  For total witnesses and `m = |ks|` fields,
the complete runs return tables `TA, TB` and the machine is the kernel on them, on every
condition.

Proof sketch: `runTable_dom` gives `TA := (runTable pA n).get _` and `TB`; unfold `coreMachine`,
rewrite `coreFields_numPacket`, `decodeTotalProgramPairFirst_pair`,
`decodeTotalProgramPairSecond_pair`, then `Part.eq_some_iff.mpr` and `Part.bind_some` twice. -/
theorem coreMachine_eval (m : ℕ) (ker : CoreIn → Part BitString) {ks : List ℕ}
    (hm : ks.length = m) {pA pB : BitString} (hA : IsTotalProgram universalDecompressor pA)
    (hB : IsTotalProgram universalDecompressor pB) (tail : BitString) :
    ∃ TA TB, TA ∈ runTable pA (ks.getD 0 0) ∧ TB ∈ runTable pB (ks.getD 0 0) ∧
      ∀ y, coreMachine m ker (corePacket ks pA pB tail, y) = ker ((TA, TB), ks, tail, y) := by
  subst hm
  obtain ⟨TA, hTA⟩ : ∃ TA, TA ∈ runTable pA (ks.getD 0 0) :=
    ⟨_, Part.get_mem (runTable_dom hA _)⟩
  obtain ⟨TB, hTB⟩ : ∃ TB, TB ∈ runTable pB (ks.getD 0 0) :=
    ⟨_, Part.get_mem (runTable_dom hB _)⟩
  refine ⟨TA, TB, hTA, hTB, fun y => ?_⟩
  simp only [coreMachine, corePacket, coreFields_numPacket, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair]
  rw [Part.eq_some_iff.mpr hTA, Part.bind_some, Part.eq_some_iff.mpr hTB, Part.bind_some]

/-- **Packet length.**  For at most `m` numeric fields, each at most `bf (n + 1)`, and witness
bodies of length at most `e ≤ n`: `|corePacket ks pA pB tail| ≤ |tail| + c H`, with `c` depending
only on `m` and `bf`.

Proof sketch: `length_numPacket_le m bf` bounds the fields by `c₀ ⌈log₂ (n + 2)⌉`;
`length_totalProgramPairCode` twice costs `|pA| + |pB| + 2 |bits |pA|| + 2 |bits |pB|| + 2`,
and `|bits k| = Nat.size k ≤ k` (`Nat.size_le`, `Nat.lt_two_pow_self`), so at most `6 e + 2`;
with `1 ≤ ⌈log₂ (n + 2)⌉` (`one_le_headerLog`) take `c = c₀ + 8`. -/
theorem length_corePacket_le (m bf : ℕ) :
    ∃ c : ℕ, ∀ (n e : ℕ) (ks : List ℕ) (pA pB tail : BitString), ks.length ≤ m →
      (∀ k ∈ ks, k ≤ bf * (n + 1)) → pA.length ≤ e → pB.length ≤ e → e ≤ n →
        (corePacket ks pA pB tail).length ≤ tail.length + c * baseBudget n e := by
  obtain ⟨c₀, hc₀⟩ := length_numPacket_le bf m
  refine ⟨c₀ + 8, fun n e ks pA pB tail hks hk hA hB hen => ?_⟩
  have h1 := hc₀ n ks (totalProgramPairCode pA (totalProgramPairCode pB tail)) hks hk
  have hs : ∀ k : ℕ, (Nat.bits k).length ≤ k := fun k => by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  have h2 := length_totalProgramPairCode pA (totalProgramPairCode pB tail)
  have h3 := length_totalProgramPairCode pB tail
  have h4 := hs pA.length
  have h5 := hs pB.length
  have hl := one_le_headerLog n
  unfold corePacket baseBudget
  nlinarith

/-- The table shape of a kernel input: `n, a, b` are the fields `0, 1, 2`. -/
def inShape (q : CoreIn) : ShapeParams :=
  tableShape q.1.1 q.1.2 (q.2.1.getD 0 0) (q.2.1.getD 1 0) (q.2.1.getD 2 0)

/-- The side of a kernel input: field `3` nonzero means the column side. -/
def inSide (q : CoreIn) : Bool :=
  decide (q.2.1.getD 3 0 ≠ 0)

/-- The budget of a kernel input: field `4`. -/
def inBudget (q : CoreIn) : ℕ :=
  q.2.1.getD 4 0

/-- The typed endpoint of a kernel input: the condition, typed by the side. -/
def inEnd (q : CoreIn) : BitString ⊕ BitString :=
  coreEnd (inSide q) q.2.2.2

/-- Reading the standard five fields `[n, a, b, side, s]`. -/
theorem inShape_mk (TA TB : List (BitString × BitString)) (n a b t s : ℕ) (tail y : BitString) :
    inShape ((TA, TB), [n, a, b, t, s], tail, y) = tableShape TA TB n a b :=
  rfl

/-- Reading the side field. -/
theorem inSide_mk (TA TB : List (BitString × BitString)) (n a b s : ℕ) (side : Bool)
    (tail y : BitString) : inSide ((TA, TB), [n, a, b, side.toNat, s], tail, y) = side := by
  cases side <;> rfl

/-- Reading the budget field. -/
theorem inBudget_mk (TA TB : List (BitString × BitString)) (n a b t s : ℕ) (tail y : BitString) :
    inBudget ((TA, TB), [n, a, b, t, s], tail, y) = s :=
  rfl

/-- **Selected cores read from tables are the instance's** (for strings of the data length). -/
theorem coreOf_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (s : ℕ) {z : BitString}
    (hz : z.length = P.n) : coreOf P s z = coreOf Q s z := by
  have hsrc : shapeSrc P z = shapeSrc Q z := by
    simp only [shapeSrc, (h.2.2.2 z hz).1]
  unfold coreOf
  rw [hsrc, (vertexCores_congr h s 0 (shapeSrc Q z)).2.1]

end Kolmogorov.StrongMerging.Upper
