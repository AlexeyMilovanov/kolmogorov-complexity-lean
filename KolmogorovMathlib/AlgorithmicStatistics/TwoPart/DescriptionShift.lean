import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Prefix.Properties

namespace Kolmogorov

open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution

/-- The size of a description chunk. -/
def descriptionChunkSize (S : Finset BitString) (s : ℕ) : ℕ := S.card / 2^s + 1

/-- The deterministic subset of `S` containing `x`, corresponding to a split into
`2^s` parts.  The split uses the canonical *computable* enumeration
`canonicalFinsetList S` (sorted by `Encodable` codes) rather than the
noncomputable `Finset.toList`, so the chunk is a computable function of `S` and
is reproducible by a decoder. -/
def descriptionChunk (S : Finset BitString) (x : BitString) (s : ℕ) : Finset BitString :=
  let L := canonicalFinsetList S
  let c := descriptionChunkSize S s
  let idx := L.findIdx (· == x)
  let start := (idx / c) * c
  (L.drop start |>.take c).toFinset

theorem descriptionChunkSize_pos (S : Finset BitString) (s : ℕ) :
    0 < descriptionChunkSize S s := Nat.add_pos_right _ (by decide)

theorem mem_descriptionChunk (S : Finset BitString) (x : BitString) (s : ℕ) (hx : x ∈ S) :
    x ∈ descriptionChunk S x s := by
  have hmem : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have h_findIdx : List.findIdx (fun y => y == x) (canonicalFinsetList S) <
      (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hmem, by simp⟩
  have h_findIdx_eq : ((canonicalFinsetList S).findIdx (fun y => y == x)) / descriptionChunkSize S
      s * descriptionChunkSize S s ≤ ((canonicalFinsetList S).findIdx (fun y => y == x)) ∧
          ((canonicalFinsetList S).findIdx (fun y => y == x)) <
              ((canonicalFinsetList S).findIdx (fun y => y == x)) / descriptionChunkSize S s *
                  descriptionChunkSize S s + descriptionChunkSize S s := by
    exact ⟨ Nat.div_mul_le_self _ _,
            by linarith
                [ Nat.div_add_mod ( List.findIdx ( fun y => y == x ) (canonicalFinsetList S) )
                    ( descriptionChunkSize S s ), Nat.mod_lt
                        ( List.findIdx ( fun y => y == x ) (canonicalFinsetList S) )
                            ( descriptionChunkSize_pos S s ) ] ⟩;
  convert List.mem_toFinset.mpr
      ( List.mem_iff_getElem.mpr ⟨ List.findIdx ( fun y => y == x ) (canonicalFinsetList S) -
                                   ( List.findIdx ( fun y => y == x ) (canonicalFinsetList S) /
                                       descriptionChunkSize S s
                                           ) * descriptionChunkSize S s, ?_, ?_ ⟩ ) using 1 <;>
                                             norm_num at *
  · exact ⟨ by omega, by omega ⟩
  · have h_idx : List.findIdx (fun x_1 => x_1 == x) (canonicalFinsetList S) /
          descriptionChunkSize S s *
          descriptionChunkSize S s +
        (List.findIdx (fun y => y == x) (canonicalFinsetList S) -
          List.findIdx (fun y => y == x) (canonicalFinsetList S) / descriptionChunkSize S s *
            descriptionChunkSize S s) = List.findIdx (fun y => y == x) (canonicalFinsetList S) :=
      by omega
    simp_rw [h_idx]
    exact eq_of_beq (List.findIdx_getElem (p := fun y => y == x) (w := by simpa using h_findIdx))

theorem descriptionChunk_subset (S : Finset BitString) (x : BitString) (s : ℕ) :
    descriptionChunk S x s ⊆ S := by
  intro y hy
  unfold descriptionChunk at hy
  simp only [List.mem_toFinset] at hy
  exact mem_canonicalFinsetList.mp (List.mem_of_mem_drop (List.mem_of_mem_take hy))

theorem descriptionChunk_nonempty (S : Finset BitString) (x : BitString) (s : ℕ) (hx : x ∈ S) :
    (descriptionChunk S x s).Nonempty :=
  ⟨x, mem_descriptionChunk S x s hx⟩

theorem card_descriptionChunk_le_pow (S : Finset BitString) (x : BitString) (s j : ℕ)
    (hcard : S.card ≤ 2 ^ j) (hs : s ≤ j) :
    (descriptionChunk S x s).card ≤ 2 ^ (j - s + 1) := by
  refine le_trans ?_ (show 2 ^ (j - s) + 1 ≤ 2 ^ (j - s + 1) from ?_)
  · refine le_trans ?_ (show S.card / 2 ^ s + 1 ≤ 2 ^ (j - s) + 1 from ?_)
    · refine le_trans ?_
        (show ((canonicalFinsetList S).drop (List.findIdx (fun x_1 => x_1 == x)
                                              (canonicalFinsetList S) /
          (S.card / 2 ^ s + 1) * (S.card / 2 ^ s + 1)) |>.take (S.card / 2 ^ s + 1)).toFinset.card ≤
          S.card / 2 ^ s + 1 from ?_)
      · unfold descriptionChunk; aesop
      · exact le_trans (List.toFinset_card_le _) (by simp)
    · exact Nat.succ_le_succ (Nat.div_le_of_le_mul <| by
        rw [← pow_add, Nat.add_sub_of_le hs]; linarith)
  · rw [pow_succ']; linarith [Nat.one_le_pow (j - s) 2 zero_lt_two]

/-! ### The explicit chunk encoder

Because the input already carries `S`'s uniform-distribution code, whose data
points are *exactly* `canonicalFinsetList S` (in sorted order), the chunk is a
contiguous sorted sublist of that list.  Hence the encoder needs no re-sorting:
it recovers `canonicalFinsetList S` from the decoded data, slices the requested
block, and re-encodes.  This makes the encoder a genuinely computable function. -/

/-- The data points of `codedUniformOn S hS` are exactly `canonicalFinsetList S`. -/
theorem dataPoints_codedUniformOn (S : Finset BitString) (hS : S.Nonempty) :
    (decodeDistributionData (codedUniformOn S hS).code).map CodedDistributionEntry.point
      = canonicalFinsetList S := by
  rw [show (codedUniformOn S hS).code = codedDistributionDataCode (codedUniformOn S hS).data from
       rfl,
    decodeDistributionData_code]
  change ((canonicalFinsetList S).map _).map CodedDistributionEntry.point = canonicalFinsetList S
  rw [List.map_map]; exact List.map_id'' (fun _ => rfl) _

/-- Appending high-order zero bits does not change the decoded value. -/
theorem bitsToNat_append_false (l : List Bool) (k : ℕ) :
    bitsToNat (l ++ List.replicate k false) = bitsToNat l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ n ih => rw [List.nil_append, List.replicate_succ] at *; unfold bitsToNat at *
                   simpa using ih
  | cons b l ih => simp only [List.cons_append]; unfold bitsToNat at *
                   simp only [List.foldr_cons, ih]

/-- The `s`-bit block address encoding the block index `blockIdx`. -/
def chunkAddress (blockIdx s : ℕ) : BitString :=
  Nat.bits blockIdx ++ List.replicate (s - (Nat.bits blockIdx).length) false

theorem chunkAddress_length (blockIdx s : ℕ) (h : blockIdx < 2 ^ s) :
    (chunkAddress blockIdx s).length = s := by
  have hle : (Nat.bits blockIdx).length ≤ s := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h
  simp [chunkAddress, hle]

theorem bitsToNat_chunkAddress (blockIdx s : ℕ) : bitsToNat (chunkAddress blockIdx s) = blockIdx :=
    by
  rw [chunkAddress, bitsToNat_append_false, bitsToNat_bits]

theorem chunkList_pairwise (L : List BitString) (h : L.Pairwise bitStringLE) (a b : ℕ) :
    ((L.drop a).take b).Pairwise bitStringLE :=
  h.sublist ((L.drop a).take_sublist b |>.trans (L.drop_sublist a))

theorem chunkList_nodup (L : List BitString) (h : L.Nodup) (a b : ℕ) :
    ((L.drop a).take b).Nodup :=
  h.sublist ((L.drop a).take_sublist b |>.trans (L.drop_sublist a))

/-- The block index of any present element fits in `s` bits. -/
theorem blockIdx_lt (S : Finset BitString) (x : BitString) (s : ℕ) (hx : x ∈ S) :
    (canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s < 2 ^ s := by
  have hmem : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have hidx : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hmem, by simp⟩
  rw [length_canonicalFinsetList] at hidx
  rw [Nat.div_lt_iff_lt_mul (descriptionChunkSize_pos S s), descriptionChunkSize]
  have h1 := Nat.div_add_mod S.card (2 ^ s)
  have h2 := Nat.mod_lt S.card (show 0 < 2 ^ s by positivity)
  nlinarith [hidx, h1, h2]

/-- The explicit, genuinely computable chunk encoder.  It decodes the uniform
code to recover `canonicalFinsetList S`, slices the block addressed by `z`
(reading the split parameter as `s = z.length`), and re-encodes the uniform
distribution on that contiguous (already sorted) slice. -/
def descriptionChunkUniformCode (t : BitString) : BitString :=
  let w := decodeFirst t
  let z := decodeSecond t
  let s := z.length
  let blockIdx := bitsToNat z
  let L := (decodeDistributionData w).map CodedDistributionEntry.point
  let c := L.length / 2 ^ s + 1
  let chunk := (L.drop (blockIdx * c)).take c
  codedDistributionDataCode (chunk.map fun x =>
    { point := x, mass := ratMassInvNat (max 1 chunk.length) (by positivity) })

/-- Correctness of the chunk encoder: with the block-address `chunkAddress` it
reproduces the canonical code of the uniform distribution on `descriptionChunk`. -/
theorem descriptionChunkUniformCode_eq (S : Finset BitString) (hS : S.Nonempty) (x : BitString)
    (s : ℕ) (hx : x ∈ S) :
    descriptionChunkUniformCode (pairCode (codedUniformOn S hS).code
        (chunkAddress ((canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s) s))
      = (codedUniformOn (descriptionChunk S x s) (descriptionChunk_nonempty S x s hx)).code := by
  have hblt : (canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s < 2 ^ s :=
    blockIdx_lt S x s hx
  have hlenz :
      (chunkAddress ((canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s) s).length
          = s :=
    chunkAddress_length _ s hblt
  have hbn : bitsToNat
      (chunkAddress ((canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s) s)
      = (canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s :=
          bitsToNat_chunkAddress _ _
  unfold descriptionChunkUniformCode
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, hlenz, hbn,
              dataPoints_codedUniformOn S hS,
    length_canonicalFinsetList]
  set chunk :=
      ((canonicalFinsetList S).drop (((canonicalFinsetList S).findIdx (· == x) /
                                       descriptionChunkSize S s) * (S.card / 2 ^ s +
                                                                     1))).take (S.card / 2 ^ s + 1)
                                                                         with hchunk
  have hDC : descriptionChunk S x s = chunk.toFinset := rfl
  have hnd : chunk.Nodup := chunkList_nodup _ (canonicalFinsetList_nodup S) _ _
  have hpw : chunk.Pairwise bitStringLE :=
      chunkList_pairwise _ (Finset.pairwise_sort S bitStringLE) _ _
  have hcanon : canonicalFinsetList chunk.toFinset = chunk :=
      canonicalFinsetList_of_sorted chunk hnd hpw
  have hxchunk : x ∈ chunk := by
    have := mem_descriptionChunk S x s hx; rw [hDC, List.mem_toFinset] at this; exact this
  have hlen : 0 < chunk.length := List.length_pos_of_mem hxchunk
  have hcard : chunk.toFinset.card = chunk.length := List.toFinset_card_of_nodup hnd
  have hmax : max 1 chunk.length = chunk.length := by omega
  rw [codedUniformOn_code_congr (descriptionChunk_nonempty S x s hx) (hDC ▸
                                                                       descriptionChunk_nonempty S
                                                                           x s hx) hDC,
      codedUniformOn_code_eq chunk.toFinset (hDC ▸ descriptionChunk_nonempty S x s hx)]
  refine congrArg codedDistributionDataCode ?_
  rw [hcanon]
  apply List.map_congr_left
  intro y _
  refine congrArg (fun m => ({point := y, mass := m} : CodedDistributionEntry)) ?_
  apply RatMass.code_injective
  simp only [RatMass.code, ratMassInvNat, hcard]
  rw [show (chunk).length = chunk.length from rfl, hmax]

/-- `codedDistributionDataCode` of a uniform map, written as a `foldr` that never
constructs a `CodedDistributionEntry` (only `BitString`s), which is convenient
for the computability proof. -/
theorem codedUniform_foldr (l : List BitString) (n : ℕ) (hn : 0 < n) :
    codedDistributionDataCode (l.map (fun x => ({point := x,
                                                  mass :=
                                                      ratMassInvNat n
                                                          hn} : CodedDistributionEntry)))
      = l.foldr (fun x acc => true :: pairCode (pairCode x (pairCode (natCode 1) (natCode n))) acc)
          [false] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, codedDistributionDataCode, List.foldr_cons, ih]; rfl

/-- `List.drop` on `List BitString` is primitive recursive in both arguments. -/
theorem primrec_listBitString_drop : Primrec₂ (fun (l : List BitString) (n : ℕ) => l.drop n) :=
  Primrec.list_drop

/-- `List.take` on `List BitString` is primitive recursive in both arguments. -/
theorem primrec_listBitString_take : Primrec₂ (fun (l : List BitString) (n : ℕ) => l.take n) :=
  Primrec.list_take

/-
The remaining genuine computability content of the description-shift bound,
isolated as a single local obligation: the explicit chunk encoder
`descriptionChunkUniformCode` is computable.  It is a composition of computable
decoders (`decodeFirst`, `decodeSecond`, `bitsToNat`, `decodeDistributionData`),
arithmetic, `List.drop`/`List.take`, and the computable encoder
`codedDistributionDataCode`; no sorting is required (the slice is already
sorted).
-/
theorem descriptionChunkUniformCode_computable : Computable descriptionChunkUniformCode := by
  have := @Kolmogorov.CodedFiniteDistribution.natCode_primrec;
  convert Primrec.to_comp _;
  convert Primrec.comp
      ( show Primrec ( fun t : List BitString => codedDistributionDataCode ( t.map fun x =>
        ( { point := x,
            mass := ratMassInvNat (max 1 (List.length t)) (by positivity)
          } : CodedDistributionEntry ) ) ) from ?_ )
      ( show Primrec ( fun t : BitString => ( ( decodeDistributionData ( decodeFirst t ) ).map
        CodedDistributionEntry.point |> fun L => ( L.drop ( bitsToNat ( decodeSecond t ) * (
          List.length L / 2 ^ ( List.length ( decodeSecond t ) ) + 1 ) ) |> fun chunk =>
            chunk.take ( List.length L / 2 ^ ( List.length ( decodeSecond t ) ) + 1 ) ) ) ) from
              ?_ ) using 1;
  · convert Primrec.of_eq _ _
    · exact fun l =>
        l.foldr
            ( fun x acc => true :: pairCode ( pairCode x ( pairCode ( natCode 1 ) ( natCode ( max 1
                l.length ) ) ) ) acc ) [ false ]
    · have h_pairCode_primrec : Primrec₂ (fun (x y : BitString) => pairCode x y) := pairCode_primrec
      exact Primrec.list_foldr (f := fun (l : List BitString) => l) (g := fun _ => [false])
        (h := fun l p => true :: pairCode (pairCode p.1 (pairCode (natCode 1)
          (natCode (max 1 l.length)))) p.2) Primrec.id (Primrec.const [false]) (
        by
          convert Primrec.list_cons.comp (Primrec.const true)
            (h_pairCode_primrec.comp (h_pairCode_primrec.comp (Primrec.fst.comp Primrec.snd)
              (h_pairCode_primrec.comp (this.comp (Primrec.const 1))
                (this.comp (Primrec.nat_max.comp (Primrec.const 1)
                  (Primrec.list_length.comp Primrec.fst))))) (Primrec.snd.comp Primrec.snd)) using 1
      )
    · intro n; exact (by
      convert codedUniform_foldr n ( max 1 n.length ) ( by positivity ) |> Eq.symm using 1)
  · convert Primrec.comp
      ( primrec_listBitString_take.comp ( primrec_listBitString_drop.comp ( show Primrec ( fun t :
          BitString => List.map CodedDistributionEntry.point
            ( decodeDistributionData ( decodeFirst t ) ) ) from ?_ )
        ( show Primrec ( fun t : BitString => bitsToNat ( decodeSecond t ) *
          ( List.length ( List.map CodedDistributionEntry.point ( decodeDistributionData
            ( decodeFirst t ) ) ) / 2 ^ List.length ( decodeSecond t ) + 1 ) ) from ?_ ) )
      ( show Primrec ( fun t : BitString => List.length ( List.map CodedDistributionEntry.point
        ( decodeDistributionData ( decodeFirst t ) ) ) / 2 ^ List.length ( decodeSecond t ) + 1 )
          from
          ?_ ) ) ( show Primrec ( fun t : BitString => t ) from ?_ ) using 1;
    · apply Primrec.list_map (decodeDistributionData_primrec.comp decodeFirst_primrec)
        (entry_point_primrec.comp Primrec.snd).to₂;
    · convert Primrec.nat_mul.comp ( bitsToNat_primrec.comp ( decodeSecond_primrec ) ) ( ?_ ) using
        1;
      convert Primrec.nat_add.comp
          ( Primrec.nat_div.comp ( show Primrec ( fun t : BitString => List.length ( List.map
              CodedDistributionEntry.point ( decodeDistributionData ( decodeFirst t ) )
                  ) ) from ?_ ) ( show Primrec ( fun t : BitString => 2 ^ List.length
                                                 ( decodeSecond t )
                                                     ) from ?_ ) ) ( show Primrec ( fun t :
                                                                                    BitString =>
                                                                                        1 ) from ?_
                                                                                            ) using
                                                                                                1;
      · convert Primrec.comp
          ( show Primrec ( fun t : List CodedDistributionEntry => List.length t ) from ?_ )
              ( show Primrec ( fun t : BitString => decodeDistributionData ( decodeFirst t ) ) from
                  ?_ ) using 1;
        · aesop;
        · exact Primrec.list_length;
        · convert decodeDistributionData_primrec.comp ( decodeFirst_primrec ) using 1;
      · convert twoPow_primrec.comp
          ( show Primrec ( fun t : BitString => List.length ( decodeSecond t ) ) from ?_ ) using 1;
        convert Primrec.list_length.comp ( decodeSecond_primrec ) using 1;
      · exact Primrec.const 1;
    · convert Primrec.nat_add.comp
        ( Primrec.nat_div.comp ( show Primrec ( fun t : BitString => ( List.map
                                                                       CodedDistributionEntry.point
                                                                           ( decodeDistributionData
                                                                               ( decodeFirst t )
                                                                                   ) ).length )
                                                                                       from
                                                  ?_ ) ( show Primrec
                                                         ( fun t : BitString => 2 ^ List.length
                                                             ( decodeSecond t )
                                                                 ) from ?_ ) ) ( Primrec.const 1 )
                                                                     using 1;
      · convert Primrec.comp
          ( show Primrec ( fun t : List CodedDistributionEntry => List.length t ) from ?_ )
              ( show Primrec ( fun t : BitString => decodeDistributionData ( decodeFirst t ) ) from
                  ?_ ) using 1;
        · aesop;
        · exact Primrec.list_length;
        · exact decodeDistributionData_primrec.comp decodeFirst_primrec;
      · exact twoPow_primrec.comp ( Primrec.list_length.comp ( decodeSecond_primrec ) );
    · exact Primrec.id

/--
Computable-encoder existence for the description-shift bound.  There is a fixed
computable map `f` sending the pair code of `S`'s uniform-distribution code
together with an `s`-bit *block address* `z` (of length exactly `s`) to the
canonical code of the uniform distribution on the chunk `descriptionChunk S x s`.

The crucial design choice is that the address `z` has length exactly `s`, so the
decoder recovers `s = z.length` for free: this is what makes the slack in
`descriptionShift_complexity` come out to `s + 2 * |bits s|` rather than
`s + 4 * |bits s|`.  The `2 * |bits s|` term is then precisely the
self-delimiting cost of the length prefix of `z` (`KPPlain_le_length_add_log`).
Assembled from the explicit encoder `descriptionChunkUniformCode`, its
computability `descriptionChunkUniformCode_computable`, and its correctness
`descriptionChunkUniformCode_eq` (with `z = chunkAddress (blockIndex) s`). -/
theorem exists_descriptionChunkUniformCode_computable :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ (S : Finset BitString) (_hS : S.Nonempty) (x : BitString) (s : ℕ) (hx : x ∈ S),
        ∃ z : BitString, z.length = s ∧
          f (pairCode (codedUniformOn S _hS).code z) =
            (codedUniformOn (descriptionChunk S x s)
              (descriptionChunk_nonempty S x s hx)).code := by
  refine ⟨descriptionChunkUniformCode, descriptionChunkUniformCode_computable, ?_⟩
  intro S hS x s hx
  exact ⟨chunkAddress ((canonicalFinsetList S).findIdx (· == x) / descriptionChunkSize S s) s,
    chunkAddress_length _ s (blockIdx_lt S x s hx),
    descriptionChunkUniformCode_eq S hS x s hx⟩

/-- The coding layer interface: the complexity of a description chunk exceeds the
complexity of `S` by at most `s + 2 * |bits s| + O(1)`.  This is fully reduced to
the computable-encoder existence `exists_descriptionChunkUniformCode_computable`;
the slack is the explicit accounting
`KPPair ≤ KPPlain S.code + KPPlain z + O(1)` together with
`KPPlain z ≤ z.length + 2 * |bits z.length| + O(1)` and `z.length = s`. -/
theorem descriptionShift_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ S hS x s (hx : x ∈ S),
      setComplexity U (descriptionChunk S x s) (descriptionChunk_nonempty S x s hx) ≤
      setComplexity U S hS + (s : ENat) + 2 * (Nat.bits s).length + c := by
  obtain ⟨f, hf_comp, hf_eq⟩ := exists_descriptionChunkUniformCode_computable
  obtain ⟨c_map, h_map⟩ := KPPlain_map_le U hU f hf_comp
  obtain ⟨c_pair, h_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_len, h_len⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c_map + c_pair + c_len, fun S hS x s hx => ?_⟩
  obtain ⟨z, hz_len, hz_eq⟩ := hf_eq S hS x s hx
  unfold setComplexity
  rw [← hz_eq]
  calc
    KPPlain U (f (pairCode (codedUniformOn S hS).code z))
        ≤ KPPlain U (pairCode (codedUniformOn S hS).code z) + (c_map : ENat) := h_map _
    _ = KPPair U (codedUniformOn S hS).code z + (c_map : ENat) := by
          rw [KPPlain_eq_KP, KPPair_eq_KP_pairCode]
    _ ≤ (KPPlain U (codedUniformOn S hS).code + KPPlain U z + (c_pair : ENat))
          + (c_map : ENat) := by
          gcongr
          exact h_pair _ _
    _ ≤ (KPPlain U (codedUniformOn S hS).code
            + (z.length + 2 * (Nat.bits z.length).length + (c_len : ENat)) + (c_pair : ENat))
          + (c_map : ENat) := by
          gcongr
          exact h_len z
    _ = KPPlain U (codedUniformOn S hS).code + (s : ENat) + 2 * (Nat.bits s).length
          + ((c_map + c_pair + c_len : ℕ) : ENat) := by
          rw [hz_len]
          push_cast
          ring

/-- **Portion observation** (honest, single-description form).  If `x` has an
`(i, j)`-description and `s ≤ j`, then `x` has an `(i + s + 2·|bits s| + c,
j - s + 1)`-description, obtained by slicing the description into `2^s`
contiguous chunks and keeping the chunk that contains `x`.  The complexity grows
by the explicit address cost `s + 2·|bits s| + c` (with `c` the fixed encoder
constant from `descriptionShift_complexity`) and the log-size drops by `s` (up to
the `+1` rounding term).  This is the size-reduction move on the description
profile; it underlies the deep "many-descriptions" improvements. -/
theorem inDescriptionProfile_portion (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (i j s : ℕ),
      InDescriptionProfile U x i j → s ≤ j →
      InDescriptionProfile U x (i + s + 2 * (Nat.bits s).length + c) (j - s + 1) := by
  obtain ⟨c, hc⟩ := descriptionShift_complexity U hU
  refine ⟨c, fun x i j s hprof hsj => ?_⟩
  obtain ⟨S, hS, hx, hcomp, hcard⟩ := hprof
  refine ⟨descriptionChunk S x s, descriptionChunk_nonempty S x s hx,
    mem_descriptionChunk S x s hx, ?_, ?_⟩
  · calc
      setComplexity U (descriptionChunk S x s) (descriptionChunk_nonempty S x s hx)
          ≤ setComplexity U S hS + (s : ENat) + 2 * (Nat.bits s).length + c := hc S hS x s hx
      _ ≤ (i : ENat) + (s : ENat) + 2 * (Nat.bits s).length + c := by gcongr
      _ = ((i + s + 2 * (Nat.bits s).length + c : ℕ) : ENat) := by push_cast; ring
  · exact card_descriptionChunk_le_pow S x s j hcard hsj

end Kolmogorov
