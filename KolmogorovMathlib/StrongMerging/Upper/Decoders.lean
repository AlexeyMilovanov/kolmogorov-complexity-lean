import KolmogorovMathlib.StrongMerging.Upper.DecodersCore

/-!
# The total local-list decoder (blueprint H03, `UpperLocalBlockDecoder`)

`sublinear-merging.tex`, section "A canonical hierarchy of small subgraphs", eq. `local` (tex ~362),
and appendix "A literal total local-list decoder" (tex ~2475); blueprint `bp-upper-hierarchy`,
paragraph "One global local rank".

The decoder `localBlockDecoder` reads a packet `localPacket side n a b R L j pA pB s`: seven numeric
header fields `n, a, b, R, L, j, side`, the two total witness bodies `pA`, `pB` (length-framed),
and the local rank `s` in exactly `jL + 1` bits (`chunkAddress`, no delimiter: it is the rest of
the packet).  On any condition `w` it computes the two output tables by complete runs
(`runTable`), the complete depth-`j` list from the tables, filters the blocks incident to the
typed endpoint `(side, w)` and returns the code of the `s`-th one (default `∅`).  The whole finite
list is built before the rank is used, so nonvertices and out-of-range ranks return the default
and never cause divergence; the decoder is total on every packet whose witnesses are total.

`upperLocalBlockDecoder`: `CT(F | endpoint) ≤ jL + |p_A| + |p_B| + c (hdrCost + 1)`, where
`hdrCost [n, a, b, R, L, j, |p_A|, |p_B|]` is the logarithmic header cost; in the calibrated
instance this is the paper's `CT(F | A), CT(F | B) ≤ jL + c₃ H`.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### Packets -/

/-- Read `m` numeric fields (`numField`) from the front of a packet; returns the fields and the
rest of the packet. -/
def decodeFields : ℕ → BitString → List ℕ × BitString
  | 0, w => ([], w)
  | m + 1, w =>
    ((numFieldDecode w).1 :: (decodeFields m (numFieldDecode w).2).1,
      (decodeFields m (numFieldDecode w).2).2)

/-- Reading the fields of a numeric packet recovers the fields and the body. -/
theorem decodeFields_numPacket (ks : List ℕ) (body : BitString) :
    decodeFields ks.length (numPacket ks body) = (ks, body) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.length_cons, decodeFields, numPacket, List.foldr_cons,
      numFieldDecode_numField]
    simp only [numPacket] at ih
    rw [ih]

/-- One step of field decoding with an accumulator: append the next field, keep the rest. -/
def decodeFieldStep (st : List ℕ × BitString) : List ℕ × BitString :=
  (st.1 ++ [(numFieldDecode st.2).1], (numFieldDecode st.2).2)

/-- Iterating the accumulator step reads the fields in order. -/
theorem decodeFieldStep_iterate (m : ℕ) : ∀ (acc : List ℕ) (w : BitString),
    decodeFieldStep^[m] (acc, w) = (acc ++ (decodeFields m w).1, (decodeFields m w).2) := by
  induction m with
  | zero => intro acc w; simp [decodeFields]
  | succ m ih =>
    intro acc w
    rw [Function.iterate_succ_apply, decodeFieldStep, ih]
    simp [decodeFields]

/-- **Field decoding is computable** (the iteration of `numFieldDecode` by `Computable.nat_rec`). -/
theorem decodeFields_computable : Computable₂ decodeFields := by
  have hstep : Computable decodeFieldStep :=
    (Primrec.list_append.to_comp.comp Computable.fst
      (Primrec.list_cons.to_comp.comp (Computable.fst.comp (numFieldDecode_computable.comp
        Computable.snd)) (Computable.const []))).pair
      (Computable.snd.comp (numFieldDecode_computable.comp Computable.snd))
  have hrec : Computable fun q : ℕ × BitString =>
      Nat.rec (motive := fun _ => List ℕ × BitString) ([], q.2)
        (fun _ IH => decodeFieldStep IH) q.1 :=
    Computable.nat_rec Computable.fst ((Computable.const []).pair Computable.snd)
      (hstep.comp (Computable.snd.comp Computable.snd)).to₂
  refine hrec.of_eq fun q => ?_
  have hit : ∀ m : ℕ, ∀ st : List ℕ × BitString,
      Nat.rec (motive := fun _ => List ℕ × BitString) st (fun _ IH => decodeFieldStep IH) m =
        decodeFieldStep^[m] st := by
    intro m st
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ← ih]
  rw [hit, decodeFieldStep_iterate]
  simp

/-- The packet of the local block decoder: header fields `n, a, b, R, L, j, side`, the two
witness bodies, and the local rank `s` in exactly `jL + 1` bits. -/
def localPacket (side : Bool) (n a b R L j : ℕ) (pA pB : BitString) (s : ℕ) : BitString :=
  numPacket [n, a, b, R, L, j, side.toNat]
    (totalProgramPairCode pA (totalProgramPairCode pB (chunkAddress s (j * L + 1))))

/-- The binary length of `k` is at most `⌈log₂ (k + 2)⌉`. -/
private theorem bitsLen_le_headerLog (k : ℕ) : (Nat.bits k).length ≤ headerLog k := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  unfold headerLog
  exact Nat.lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (k + 2))

/-- A numeric packet costs at most four header units per field. -/
private theorem length_numPacket_le_four (ks : List ℕ) (body : BitString) :
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
    have h1 := bitsLen_le_headerLog k
    have h2 : (Nat.bits (Nat.bits k).length).length ≤ (Nat.bits k).length := by
      rw [Nat.size_eq_bits_len (Nat.bits k).length]
      exact Nat.size_le.2 Nat.lt_two_pow_self
    have h3 := one_le_headerLog k
    rw [hlen, hc]
    omega

/-- **Packet length** (tex ~2500): with `s < 2^(jL+1)` the local packet costs
`jL + 1` bits for the rank, the two bodies, and logarithmic headers. -/
theorem length_localPacket_le (side : Bool) (n a b R L j : ℕ) (pA pB : BitString) (s : ℕ)
    (hs : s < 2 ^ (j * L + 1)) :
    (localPacket side n a b R L j pA pB s).length ≤
      j * L + pA.length + pB.length + 4 * hdrCost [n, a, b, R, L, j, pA.length, pB.length] + 9 := by
  have hpair : ∀ p q : BitString,
      (totalProgramPairCode p q).length ≤ p.length + q.length + 3 * headerLog p.length := by
    intro p q
    rw [length_totalProgramPairCode]
    have h1 := bitsLen_le_headerLog p.length
    have h3 := one_le_headerLog p.length
    omega
  have htail : (chunkAddress s (j * L + 1)).length = j * L + 1 := chunkAddress_length s _ hs
  have hside : headerLog side.toNat ≤ 2 := by
    have h1 : side.toNat ≤ 1 := Bool.toNat_le side
    have h3 : headerLog 1 = 2 := by
      unfold headerLog
      decide
    have h2 : headerLog side.toNat ≤ headerLog 1 := Nat.clog_mono_right 2 (by omega)
    omega
  have hhdr := length_numPacket_le_four [n, a, b, R, L, j, side.toNat]
    (totalProgramPairCode pA (totalProgramPairCode pB (chunkAddress s (j * L + 1))))
  have h1 := hpair pA (totalProgramPairCode pB (chunkAddress s (j * L + 1)))
  have h2 := hpair pB (chunkAddress s (j * L + 1))
  have hc1 : hdrCost [n, a, b, R, L, j, side.toNat] = headerLog n + headerLog a +
      headerLog b + headerLog R + headerLog L + headerLog j + headerLog side.toNat := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  have hc2 : hdrCost [n, a, b, R, L, j, pA.length, pB.length] = headerLog n + headerLog a +
      headerLog b + headerLog R + headerLog L + headerLog j + headerLog pA.length +
        headerLog pB.length := by
    simp only [hdrCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  unfold localPacket
  omega

/-! ### The decoder -/

/-- The output of the local block decoder from decoded packet fields `ks = [n, a, b, R, L, j,
side]`, the two witness bodies, the rank `s` and the endpoint label `w`: complete runs of the two
witnesses at length `n`, then the local block read from the tables. -/
noncomputable def localBlockOut (ks : List ℕ) (pA pB : BitString) (s : ℕ) (w : BitString) :
    Part BitString :=
  (runTable pA (ks.getD 0 0)).bind fun TA => (runTable pB (ks.getD 0 0)).map fun TB =>
    canonicalFiniteSetCode (localBlock (tableShape TA TB (ks.getD 0 0) (ks.getD 1 0)
      (ks.getD 2 0)) (ks.getD 3 0) (ks.getD 4 0) (ks.getD 5 0) (decide (ks.getD 6 0 ≠ 0)) w s)

/-- **The total local-list decoder** `LocalBlock(Y; θ, j, side, s)` (tex ~2481), as a machine
reading the packet `localPacket` and the condition `w`. -/
noncomputable def localBlockDecoder : Map := fun q =>
  localBlockOut (decodeFields 7 q.1).1 (decodeTotalProgramPairFirst (decodeFields 7 q.1).2)
    (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (decodeFields 7 q.1).2))
    (bitsToNat (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond
      (decodeFields 7 q.1).2))) q.2

/-- The parameter tuple of the local block code read from a packet-and-condition `q` and the two
tables: `((TA, TB), (n, a, b), (R, L, j), side, w, s)`. -/
def lbTuple (q : BitString × BitString) (TA TB : List (BitString × BitString)) :
    (List (BitString × BitString) × List (BitString × BitString)) × (ℕ × ℕ × ℕ) ×
      (ℕ × ℕ × ℕ) × Bool × BitString × ℕ :=
  ((TA, TB), ((decodeFields 7 q.1).1.getD 0 0, (decodeFields 7 q.1).1.getD 1 0,
      (decodeFields 7 q.1).1.getD 2 0),
    ((decodeFields 7 q.1).1.getD 3 0, (decodeFields 7 q.1).1.getD 4 0,
      (decodeFields 7 q.1).1.getD 5 0),
    decide ((decodeFields 7 q.1).1.getD 6 0 ≠ 0), q.2,
    bitsToNat (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond
      (decodeFields 7 q.1).2)))

/-- The local block code as a function of the parameter tuple. -/
noncomputable def lbCode (q : (List (BitString × BitString) × List (BitString × BitString)) ×
    (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × Bool × BitString × ℕ) : BitString :=
  canonicalFiniteSetCode (localBlock (tableShape q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
    q.2.2.1.1 q.2.2.1.2.1 q.2.2.1.2.2 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)

/-- Packet parsing into the local block tuple is computable. -/
theorem lbTuple_computable :
    Computable fun x : ((BitString × BitString) × List (BitString × BitString)) ×
        List (BitString × BitString) => lbTuple x.1.1 x.1.2 x.2 := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 7 q.1 :=
    decodeFields_computable.comp (Computable.const 7) Computable.fst
  have hks : Computable fun q : BitString × BitString => (decodeFields 7 q.1).1 :=
    Computable.fst.comp hdf
  have hget : ∀ i : ℕ, Computable fun q : BitString × BitString =>
      (decodeFields 7 q.1).1.getD i 0 :=
    fun i => (Primrec.list_getD 0).to_comp.comp hks (Computable.const i)
  have hs : Computable fun q : BitString × BitString =>
      bitsToNat (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond
        (decodeFields 7 q.1).2)) :=
    bitsToNat_primrec.to_comp.comp (decodeTotalProgramPairSecond_computable.comp
      (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf)))
  have hside : Computable fun q : BitString × BitString =>
      decide ((decodeFields 7 q.1).1.getD 6 0 ≠ 0) :=
    (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp (hget 6)
      (Computable.const 0))).of_eq fun q => by simp
  have hpar : Computable fun q : BitString × BitString =>
      (((decodeFields 7 q.1).1.getD 0 0, (decodeFields 7 q.1).1.getD 1 0,
        (decodeFields 7 q.1).1.getD 2 0),
        ((decodeFields 7 q.1).1.getD 3 0, (decodeFields 7 q.1).1.getD 4 0,
          (decodeFields 7 q.1).1.getD 5 0),
        decide ((decodeFields 7 q.1).1.getD 6 0 ≠ 0), q.2,
        bitsToNat (decodeTotalProgramPairSecond (decodeTotalProgramPairSecond
          (decodeFields 7 q.1).2))) :=
    ((hget 0).pair ((hget 1).pair (hget 2))).pair (((hget 3).pair ((hget 4).pair (hget 5))).pair
      (hside.pair (Computable.snd.pair hs)))
  exact (((Computable.snd.comp Computable.fst).pair Computable.snd).pair
    (hpar.comp (Computable.fst.comp Computable.fst))).of_eq fun x => rfl

/-- **The local block decoder is partial recursive**: computable packet parsing
(`lbTuple_computable`), the two complete runs (`runTable_partrec`) by `Partrec.bind`/`Partrec.map`,
and the primitive recursive local block code `localBlockCode_primrec`. -/
theorem localBlockDecoder_partrec : isDecompressor localBlockDecoder := by
  have hdf : Computable fun q : BitString × BitString => decodeFields 7 q.1 :=
    decodeFields_computable.comp (Computable.const 7) Computable.fst
  have hn : Computable fun q : BitString × BitString => (decodeFields 7 q.1).1.getD 0 0 :=
    (Primrec.list_getD 0).to_comp.comp (Computable.fst.comp hdf) (Computable.const 0)
  have hpA : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairFirst (decodeFields 7 q.1).2 :=
    decodeTotalProgramPairFirst_computable.comp (Computable.snd.comp hdf)
  have hpB : Computable fun q : BitString × BitString =>
      decodeTotalProgramPairFirst (decodeTotalProgramPairSecond (decodeFields 7 q.1).2) :=
    decodeTotalProgramPairFirst_computable.comp
      (decodeTotalProgramPairSecond_computable.comp (Computable.snd.comp hdf))
  have hcode : Computable lbCode := localBlockCode_primrec.to_comp
  have hcore : Computable₂ fun (p : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) => lbCode (lbTuple p.1 p.2 TB) :=
    hcode.comp lbTuple_computable
  have hinner : Partrec₂ fun (q : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairFirst (decodeTotalProgramPairSecond
        (decodeFields 7 q.1).2)) ((decodeFields 7 q.1).1.getD 0 0)).map fun TB =>
        lbCode (lbTuple q TA TB) :=
    Partrec.map (runTable_partrec.comp (hpB.comp Computable.fst) (hn.comp Computable.fst)) hcore
  refine (Partrec.bind (runTable_partrec.comp hpA hn) hinner).of_eq fun q => ?_
  simp only [localBlockDecoder, localBlockOut, lbCode, lbTuple]

/-- **The decoder on its packet.**  For total witnesses, on every condition `w` the decoder halts
and returns the code of the local block of rank `s` at `(side, w)` in the instance's depth-`j`
list (the tables are complete runs, `runTable_dom`, read back by `localBlock_tableShape`). -/
theorem localBlockDecoder_spec (side : Bool) (n a b R L j : ℕ) (pA pB : BitString) (s : ℕ)
    (w : BitString) (hpA : IsTotalProgram universalDecompressor pA)
    (hpB : IsTotalProgram universalDecompressor pB) :
    localBlockDecoder (localPacket side n a b R L j pA pB s, w) =
      Part.some (canonicalFiniteSetCode
        (localBlock (instShape pA pB n a b) R L j side w s)) := by
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA n)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB n)
  have hTA' : runTable pA n = Part.some TA := Part.eq_some_iff.mpr hTA
  have hTB' : runTable pB n = Part.some TB := Part.eq_some_iff.mpr hTB
  have hfields : decodeFields 7 (localPacket side n a b R L j pA pB s) =
      ([n, a, b, R, L, j, side.toNat],
        totalProgramPairCode pA (totalProgramPairCode pB (chunkAddress s (j * L + 1)))) :=
    decodeFields_numPacket [n, a, b, R, L, j, side.toNat] _
  have hside : decide (side.toNat ≠ 0) = side := by
    cases side <;> rfl
  simp only [localBlockDecoder, localBlockOut, hfields, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair, List.getD_cons_zero, List.getD_cons_succ, hTA', hTB',
    Part.bind_some, Part.map_some, hside, bitsToNat_chunkAddress]
  rw [localBlock_tableShape hTA hTB]

/-! ### H03 -/

/-- **The total local-list decoder (blueprint H03, `UpperLocalBlockDecoder`).**  There is a
constant `c` such that for total witnesses `pA`, `pB`, every depth `j` with `jL ≤ a, b`, every
depth-`j` block `F` of the instance's hierarchy and every edge `z ∈ F`, on either side,
`CT(F | endpoint of z) ≤ jL + |p_A| + |p_B| + c (hdrCost [n, a, b, R, L, j, |p_A|, |p_B|] + 1)`.
The endpoint is `sideOut … side z` (the row output `progOut pA z` or the column output
`progOut pB z`); one global rank of `jL + 1` bits is used, not a path of ranks.

`sublinear-merging.tex`, eq. `local` (tex ~362) and appendix tex ~2475–2521. -/
theorem upperLocalBlockDecoder :
    ∃ c : ℕ, ∀ (pA pB : BitString) (n a b R L j : ℕ) (side : Bool) (F : Finset BitString)
      (z : BitString),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      j * L ≤ a → j * L ≤ b → F ∈ level (instShape pA pB n a b) R L j → z ∈ F →
      totalC (canonicalFiniteSetCode F) (sideOut (instShape pA pB n a b) side z) ≤
        j * L + pA.length + pB.length +
          c * (hdrCost [n, a, b, R, L, j, pA.length, pB.length] + 1) := by
  obtain ⟨c, hc⟩ := totalC_le_of_decoder localBlockDecoder localBlockDecoder_partrec
  refine ⟨c + 13, fun pA pB n a b R L j side F z hpA hpB ha hb hF hz => ?_⟩
  obtain ⟨s, hs, hsF⟩ := exists_localBlock_index (instShape pA pB n a b) R L j side ha hb hF hz
  have hspec := fun y => localBlockDecoder_spec side n a b R L j pA pB s y hpA hpB
  have htot : ∀ y, (localBlockDecoder (localPacket side n a b R L j pA pB s, y)).Dom := by
    intro y
    rw [hspec y]
    trivial
  have hmem : canonicalFiniteSetCode F ∈
      localBlockDecoder (localPacket side n a b R L j pA pB s,
        sideOut (instShape pA pB n a b) side z) := by
    rw [hspec, hsF]
    exact Part.mem_some _
  have h1 := hc _ htot _ _ hmem
  have h2 := length_localPacket_le side n a b R L j pA pB s hs
  generalize hdrCost [n, a, b, R, L, j, pA.length, pB.length] = H at h2 ⊢
  generalize (localPacket side n a b R L j pA pB s).length = m at h1 h2
  have h2' : (m : ℝ) ≤ (j : ℝ) * L + pA.length + pB.length + 4 * (H : ℝ) + 9 := by
    exact_mod_cast h2
  have hh : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hprod : (4 : ℝ) * (H : ℝ) + 9 + c ≤ ((c : ℝ) + 13) * ((H : ℝ) + 1) := by
    have := mul_nonneg hc0 hh
    linarith
  have hcast : ((c + 13 : ℕ) : ℝ) = (c : ℝ) + 13 := by norm_num
  rw [hcast]
  linarith

end Kolmogorov.StrongMerging.Upper
