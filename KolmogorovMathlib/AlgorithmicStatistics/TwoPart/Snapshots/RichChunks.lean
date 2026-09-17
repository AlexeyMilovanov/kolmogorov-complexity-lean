import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ImprovingDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Snapshots.Snapshot

/-!
# Rich descriptions and their chunks

A description is *rich* for `x` when many descriptions of the same parameters contain the
element it selects.  `inDescriptionProfile_of_many` is the reduction this module proves: if
`x` belongs to at least `2 ^ k` distinct `(i, j)`-descriptions, then the set of rich elements
is itself a description of `x` with a better parameter pair.

The witness is `richSelectorFn`, which waits for the stage matching the advised halting count
and outputs the uniform code of the rich set; it is partial recursive
(`partrec_richSelectorFn`), its input fields are read back by `selNat_richInput`,
`selAlpha_richInput`, `selMaxK_richInput`, `selH_richInput`, and `richInput_KPPlain_le` and
`setComplexity_richDescriptionElements_le` bound its complexity by `i + 1` plus logarithmic
slack.

The second half is the chunking used by `Part02` and `Part03`:
`emittedHalfRichChunksStep` and `emittedHalfRichChunksList` distribute the newly emitted
half-rich elements into chunks stage by stage, primitive recursively.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- The complexity coordinate is read back from a rich-selector input. -/
@[simp] theorem selNat_richInput (i j k h : ℕ) :
    selNat (richInput i j k h) = i := by
  simp [richInput]

/-- The size coordinate is read back from a rich-selector input. -/
@[simp] theorem selAlpha_richInput (i j k h : ℕ) :
    selAlpha (richInput i j k h) = j := by
  simp [richInput]

/-- The third parameter is read back from a rich-selector input. -/
@[simp] theorem selMaxK_richInput (i j k h : ℕ) :
    selMaxK (richInput i j k h) = k := by
  simp [richInput]

/-- The halting-count advice is read back from a rich-selector input. -/
@[simp] theorem selH_richInput (i j k h : ℕ) :
    selH (richInput i j k h) = h := by
  simp [richInput]

/-- The selector that waits for the stage matching the advised halting count and
outputs the uniform-distribution code of the rich description elements at that
stage. -/
noncomputable def richSelectorFn (c : Code) : BitString →. BitString := fun s =>
  (Nat.rfind (fun t => Part.some (decide (countHalts c (selNat s) t = selH s)))).bind
    (fun t => Part.some
      (codedDistributionDataCode ((canonicalFinsetList
        (snapshotRichElements c (selNat s) (selAlpha s) (selMaxK s) t)).map fun x =>
          { point := x,
            mass := ratMassInvNat (max 1 (canonicalFinsetList
              (snapshotRichElements c (selNat s)
                (selAlpha s) (selMaxK s) t)).length)
                (by positivity) })))

/-- The rich selector is a partial recursive function of its input. -/
theorem partrec_richSelectorFn (c : Code) : Partrec (richSelectorFn c) := by
  -- Ordinal selector computability for the snapshot rich-element stream.
  have h_eq : Computable (fun p : ℕ × ℕ => decide (p.1 = p.2)) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.fst Primrec.snd)).to_comp
  have h_check : Computable₂ (fun (s : BitString) (t : ℕ) =>
      decide (countHalts c (selNat s) t = selH s)) :=
    (h_eq.comp (Computable.pair
      ((countHalts_computable c).comp
        (Computable.pair (selNat_computable.comp Computable.fst) Computable.snd))
      (selH_computable.comp Computable.fst))).to₂
  have h_args : Primrec (fun p : BitString × ℕ =>
      ((selNat p.1, selAlpha p.1), selMaxK p.1, p.2)) :=
    Primrec.pair
      (Primrec.pair (selNat_primrec.comp Primrec.fst) (selAlpha_primrec.comp Primrec.fst))
      (Primrec.pair (selMaxK_primrec.comp Primrec.fst) Primrec.snd)
  have h_body := (codedUniformEncoder_primrec.comp
    ((snapshotRichElements_primrec c).comp h_args)).to_comp.to₂
  exact (Partrec.bind (Partrec.rfind h_check.partrec₂) h_body.partrec₂).of_eq
    (fun _ => rfl)

/-- There is a partial recursive map which, on the input coding `(i, j, k)` and the
right advice below `2 ^ (i + 1)`, outputs the canonical uniform code of the set
of rich description elements. -/
theorem exists_partrec_richSet_code (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ i j k (hne : (richDescriptionElements U i j k).Nonempty),
        ∃ h < 2 ^ (i + 1), f (richInput i j k h) = Part.some
            ((codedUniformOn (richDescriptionElements U i j k) hne).code) := by
  obtain ⟨c, hcRaw⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  have hc : IsCodeFor c U := by
    exact hcRaw
  refine ⟨ richSelectorFn c, partrec_richSelectorFn c, ?_ ⟩;
  intro i j k hne
  obtain ⟨t_star, hmax⟩ := exists_max_countHalts c i
  set h := countHalts c i t_star
  have h_lt : h < 2 ^ (i + 1) := by
    exact lt_of_le_of_lt ( countHalts_le_length c i t_star ) ( length_boundedPrograms_lt i )
  set t₀ := Nat.find (⟨t_star, rfl⟩ : ∃ t, countHalts c i t = h)
  have ht0 : countHalts c i t₀ = h := by
    exact Nat.find_spec ( ⟨ t_star, rfl ⟩ : ∃ t, countHalts c i t = h )
  have ht0_min : ∀ m < t₀, countHalts c i m ≠ h := by
    exact fun m mn => fun hm => mn.not_ge <| Nat.find_min' _ hm
  have hmax0 : ∀ t', countHalts c i t' ≤ countHalts c i t₀ := by
    grind
  use h, h_lt;
  convert Part.eq_some_iff.mpr _ using 1;
  unfold richSelectorFn
  simp +decide only [selNat_richInput, selH_richInput, selAlpha_richInput, selMaxK_richInput,
    length_canonicalFinsetList, Part.mem_bind_iff, Part.mem_some_iff]
  use t₀
  simp_all +decide only [ne_eq, implies_true,
    snapshotRichElements_eq_richDescriptionElements hc i j k t₀ hmax0, Finset.one_le_card,
    sup_of_le_right]
  convert codedUniformOn_code_eq _ hne using 1
  apply and_iff_right
  let test : PFun Nat Bool := fun t => Part.some (decide (countHalts c i t = h))
  change t₀ ∈ Nat.rfind test
  rw [Nat.mem_rfind]
  constructor
  · simp [test, ht0]
  · intro m hm
    simp [test, ht0_min m hm]

/-- The rich-selector input has prefix complexity at most `i + 1` plus logarithmic
slack in `i + j + k`, even after adding a fixed constant. -/
theorem richInput_KPPlain_le (U : Map) (hU : IsOptimalPrefixConditional U) (c_partrec : ℕ) :
    ∃ c : ℕ, ∀ i j k h, h < 2 ^ (i + 1) →
      KPPlain U (richInput i j k h) + (c_partrec : ENat) ≤
        (i + 1 : ENat) + logSlack c (i + j + k) := by
  -- Let `c₀` be the constant from `KPPlain_le_length_add_log U hU` (gives `KPPlain U s ≤ s.length +
  --   2*(Nat.bits s.length).length + c₀`).
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU;
  refine ⟨ 19 + c₀ + c_partrec, fun i j k h hh => le_trans (add_le_add (hc₀ _) le_rfl) ?_⟩
  norm_cast; simp +decide only [richInput]
  -- Let `L := (Nat.bits (i+j+k)).length`.
  set L := (Nat.bits (i + j + k)).length with hL_def
  have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
      (Nat.bits h).length ≤ i + 1 ∧ i < 2 ^ L := by
    have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L := by
      have hL : ∀ a b : ℕ, a ≤ b → (Nat.bits a).length ≤ (Nat.bits b).length := by
        intros a b hab
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
        exact Nat.size_le_size hab
      exact ⟨ hL _ _ ( by linarith ), hL _ _ ( by linarith ), hL _ _ ( by linarith ) ⟩;
    exact ⟨hL.1, hL.2.1, hL.2.2, length_natBits_lt_pow hh,
      lt_two_pow_length_natBits i |> lt_of_lt_of_le <| Nat.pow_le_pow_right (by decide) hL.1⟩
  -- Then `(selectorInput i j k h).length ≤ 6*L + i + 4`.
  have h_selectorInput_length : (selectorInput i j k h).length ≤ 6 * L + i + 4 := by
    unfold selectorInput
    simp +decide only [pairCode, pack4, List.append_assoc, List.length_append, length_natCode]
    linarith
  -- Then `(Nat.bits (selectorInput i j k h).length).length ≤ L + 4`.
  have h_bits_length : (Nat.bits (selectorInput i j k h).length).length ≤ L + 4 := by
    have h_bits_length : (selectorInput i j k h).length < 2 ^ (L + 4) := by
      rw [pow_add]
      nlinarith [Nat.pow_le_pow_right two_pos (show L ≥ 0 by positivity),
        show L ≤ 2 ^ L by
          exact Nat.recOn L (by norm_num) fun n ihn => by
            rw [pow_succ']; linarith [Nat.one_le_pow n 2 zero_lt_two]]
    exact length_natBits_lt_pow h_bits_length;
  -- Abstract the (large) `selectorInput` length as an opaque atom before running
  -- `nlinarith`, so the arithmetic solver does not repeatedly `whnf` the `richInput`
  -- definition.
  unfold logSlack
  set P := (selectorInput i j k h).length with hP
  clear_value P
  clear hP
  rw [← hL_def]
  nlinarith

/-- The set of rich description elements has set complexity at most `i + 1` plus
logarithmic slack in `i + j + k`. -/
theorem setComplexity_richDescriptionElements_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ i j k (hne : (richDescriptionElements U i j k).Nonempty),
      setComplexity U (richDescriptionElements U i j k) hne ≤ (i + 1 : ENat) + logSlack c
          (i + j + k) := by
  obtain ⟨f, hf, hf_spec⟩ := exists_partrec_richSet_code U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c₄, hc₄⟩ := richInput_KPPlain_le U hU c₃
  refine ⟨c₄, fun i j k hne => ?_⟩
  obtain ⟨h, hh₁, hh₂⟩ := hf_spec i j k hne
  have hmem : (codedUniformOn (richDescriptionElements U i j k) hne).code ∈
      f (richInput i j k h) := by
    rw [hh₂]; exact Part.mem_some _
  exact le_trans (hc₃ _ _ hmem) (hc₄ i j k h hh₁)

/-- **Rich-set reduction.**  If `x` belongs to at least `2^k` distinct
`(i,j)`-descriptions, then the computable rich set witnesses a description of
`x` of complexity `(i+1) + logSlack c (i+j+k)` and log-size `i + 1 + j - k`.

This is the honest consequence of the selector bridge: it combines
`mem_richDescriptionElements_of_many` (membership), the selector complexity
bound `setComplexity_richDescriptionElements_le`, and the double-counting
cardinality bound `card_richDescriptionElements_le`.  It is *not* yet either half
of the improving-descriptions proposition (the rich set has log-size `i+1+j-k`,
which still carries the extra `i+1` from the description-count bound), but it is
the single combinatorial+coding witness those halves are built from. -/
theorem inDescriptionProfile_of_many (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (i j k : ℕ), ManyIJDescriptions U x i j k →
      InDescriptionProfile U x ((i + 1) + logSlack c (i + j + k)) (i + 1 + j - k) := by
  obtain ⟨c, hc⟩ := setComplexity_richDescriptionElements_le U hU
  refine ⟨c, fun x i j k hmany => ?_⟩
  have hx : x ∈ richDescriptionElements U i j k :=
    mem_richDescriptionElements_of_many U x i j k hmany
  have hne : (richDescriptionElements U i j k).Nonempty := ⟨x, hx⟩
  refine ⟨richDescriptionElements U i j k, hne, hx, ?_, ?_⟩
  · refine le_trans (hc i j k hne) (le_of_eq ?_)
    push_cast
    ring
  · exact card_richDescriptionElements_le U i j k

/-!
### Size-Portion Selector Decomposition

The size-improvement half is carried by a single, honestly-stated selector
obligation `richSizePortion_selector_spec`.  It bundles, for one shared coding
constant `c` and one shared selected-portion family `S`, the three facts that the
article's portion/batch construction must deliver:

* membership and nonemptiness of the selected portion (the witness must contain
  `x`);
* the complexity bound `setComplexity ≤ i + logSlack c (n+i+j)` (to be discharged
  via the snapshot selector machinery: `exists_partrec_richSet_code`,
  `KPPlain_partrec_map_le`, `richInput_KPPlain_le`);
* the cardinality bound `card ≤ 2^(j-k+logSlack c (n+i+j))` (the half-rich
  portion count).

Bundling into one existential is deliberate: the three bounds all constrain the
*same* selected set, so splitting them across separate lemmas about a post-hoc
`Classical.choose` would make each individually unprovable (nothing would pin the
chosen witness).  The assembled interface `exists_richSizePortion_logSlack` is a
thin projection of this obligation.
-/

/-
Logarithmic-slack absorption: an additive `+1` together with a doubling of
the slack argument is absorbed by enlarging the slack constant.  If `A ≤ 2 * B`
then `1 + logSlack c₄ A ≤ logSlack (2 * c₄ + 1) B`.  This is the arithmetic that
lets the coding-wrapper lemmas replace the raw selector slack argument
`i + j + k` (or `i + j + k + m`) by the visible-parameter slack `n + i + j`.
-/
theorem logSlack_one_add_le_two_mul (c₄ A B : ℕ) (h : A ≤ 2 * B) :
    1 + logSlack c₄ A ≤ logSlack (2 * c₄ + 1) B := by
  unfold logSlack; ring_nf;
  have h_bits : (Nat.bits A).length ≤ (Nat.bits (2 * B)).length := by
    rw [ Nat.size_eq_bits_len, Nat.size_eq_bits_len ] ; exact Nat.size_le_size h;
  rcases B with ( _ | B ) <;> simp_all +decide;
  · linarith;
  · nlinarith

/-
Logarithmic-slack absorption with an additive `+4` and a slack argument bounded
by `2 * B + 3`.  This is the complexity-portion analogue of
`logSlack_one_add_le_two_mul`: the raw selector slack argument
`i + j + k + (i - k + 3)` is at most `2 * (n + i + j) + 3` (using `k ≤ i`), and the
additive `+4` (one from the address `(i-k)+1` rounding, three absorbed) is paid for
by enlarging the slack constant to `4 * c₄ + 4`.
-/
theorem logSlack_four_add_le (c₄ A B : ℕ) (h : A ≤ 2 * B + 3) :
    4 + logSlack c₄ A ≤ logSlack (4 * c₄ + 4) B := by
  have h_bits : (Nat.bits A).length ≤ (Nat.bits B).length + 2 := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
    calc A ≤ 2 * B + 3 := h
      _ < 4 * 2 ^ Nat.size B := by nlinarith [Nat.lt_size_self B]
      _ = 2 ^ (Nat.size B + 2) := by rw [pow_add]; ring
  unfold logSlack
  have hmul : c₄ * (Nat.bits A).length ≤ c₄ * ((Nat.bits B).length + 2) := by gcongr
  nlinarith [hmul, Nat.zero_le (c₄ * (Nat.bits B).length),
    Nat.zero_le ((Nat.bits B).length), Nat.zero_le c₄]

/-
Address-parameterized refinement of `richInput_KPPlain_le`.  When the batch
address `h` is bounded by `2 ^ (m + 1)` (with `m` possibly much smaller than
`i`, as for the complexity portion where `m = i - k`), the plain complexity of
`richInput i j k h` is controlled by `m + 1` plus a logarithmic slack in all
visible parameters `i + j + k + m`.  The original `richInput_KPPlain_le` is the
special case `m = i`.
-/
theorem richInput_KPPlain_le_addr (U : Map) (hU : IsOptimalPrefixConditional U) (c_partrec : ℕ) :
    ∃ c : ℕ, ∀ (i j k h m : ℕ), h < 2 ^ (m + 1) →
      KPPlain U (richInput i j k h) + (c_partrec : ENat)
        ≤ ((m : ENat) + 1) + logSlack c (i + j + k + m) := by
  -- Set `c₀` from `KPPlain_le_length_add_log U hU`.
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU;
  refine ⟨19 + c₀ + c_partrec, fun i j k h m hlt => le_trans (add_le_add (hc₀ _) le_rfl) ?_⟩
  set L := (Nat.bits (i + j + k + m)).length with hL_def
  have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
      (Nat.bits m).length ≤ L ∧ (Nat.bits h).length ≤ m + 1 ∧ m < 2 ^ L := by
    have hL : (Nat.bits i).length ≤ L ∧ (Nat.bits j).length ≤ L ∧ (Nat.bits k).length ≤ L ∧
        (Nat.bits m).length ≤ L := by
      have hL : ∀ a b : ℕ, a ≤ b → (Nat.bits a).length ≤ (Nat.bits b).length := by
        intros a b hab
        rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
        exact Nat.size_le_size hab
      exact ⟨hL _ _ (by linarith), hL _ _ (by linarith),
        hL _ _ (by linarith), hL _ _ (by linarith)⟩
    exact ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2, length_natBits_lt_pow hlt,
      lt_two_pow_length_natBits m |> lt_of_lt_of_le <| Nat.pow_le_pow_right (by decide) hL.2.2.2⟩
  unfold logSlack; norm_cast; simp +arith +decide only [ge_iff_le]
  -- By definition of `selectorInput`, we have:
  have h_selectorInput_length : (selectorInput i j k h).length ≤ 6 * L + m + 4 := by
    unfold selectorInput
    simp +decide only [pairCode, pack4, List.append_assoc, List.length_append, length_natCode]
    linarith
  have h_bits_length : (Nat.bits (selectorInput i j k h).length).length ≤ L + 4 := by
    have h_bits_length : (selectorInput i j k h).length < 2 ^ (L + 4) := by
      rw [pow_add]
      nlinarith [Nat.pow_le_pow_right two_pos (show L ≥ 0 by positivity),
        show L ≤ 2 ^ L by
          exact Nat.recOn L (by norm_num) fun n ihn => by
            rw [pow_succ']; linarith [Nat.one_le_pow n 2 zero_lt_two]]
    exact length_natBits_lt_pow h_bits_length;
  have h_richInput_length : (richInput i j k h).length ≤ 6 * L + m + 4 := by
    simpa only [richInput] using h_selectorInput_length
  have h_richInput_bits_length : (Nat.bits (richInput i j k h).length).length ≤ L + 4 := by
    simpa only [richInput] using h_bits_length
  -- Abstract the (large) `richInput` length as an opaque atom before running
  -- `nlinarith`, so the arithmetic solver does not repeatedly `whnf` the `richInput`
  -- definition.
  clear h_selectorInput_length h_bits_length
  set P := (richInput i j k h).length with hP
  clear_value P
  clear hP
  rw [← hL_def]
  nlinarith [Nat.zero_le (c₀ * L), Nat.zero_le (c_partrec * L)]

/-
**List chunking membership.**  If a list `L` of length at most `a * b`
contains `x` and the chunk size `b` is positive, then `x` lies in one of the `a`
consecutive length-`b` chunks `(L.drop (h * b)).take b`, indexed by some `h < a`.

This is the pure combinatorial ingredient of the size-portion (half-rich) batch
construction: the rich set has at most `2^(i+1+j-k)` elements, so cutting its
canonical list into chunks of size `2^(j-k)` yields at most `2^(i+1)` batches,
and the batch containing `x` is selected by an address `h < 2^(i+1)`.
-/
theorem mem_listChunk_of_mem {α : Type*} (L : List α) (a b : ℕ)
    (hb : 0 < b) {x : α} (hx : x ∈ L) (hlen : L.length ≤ a * b) :
    ∃ h < a, x ∈ (L.drop (h * b)).take b := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
  refine ⟨k / b, ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul <| by linarith [Fin.is_lt k]
  · rw [← hk, List.mem_iff_get]
    refine ⟨⟨k % b, ?_⟩, ?_⟩
    · simp only [List.length_take, List.length_drop, lt_inf_iff]
      exact ⟨Nat.mod_lt _ hb,
        lt_tsub_iff_left.mpr (by linarith [Nat.mod_add_div k b, k.2])⟩
    · simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
      exact getElem_congr rfl (Nat.div_add_mod' k b) _

/-- `emittedHalfRichChunksFoldStep` processes a single new rich element `x`.
If `x` is already placed, it does nothing. Otherwise, it extracts the currently
unplaced half-rich elements, forms a new chunk of size at most `2^j` with `x` at
the head, and appends it to the emitted chunks list. -/
def emittedHalfRichChunksFoldStep (j : ℕ) (half_rich : List BitString)
    (chunks : List (List BitString)) (x : BitString) : List (List BitString) :=
  bif decide (x ∈ chunks.flatten) then
    chunks
  else
    let unplaced_half := half_rich.filter (fun y =>
      bif decide (y ∈ chunks.flatten) then false else true)
    let new_chunk := (x :: unplaced_half.filter (fun y =>
      bif decide (y = x) then false else true)).take (2 ^ j)
    chunks ++ [new_chunk]

/-- The fold step that distributes new elements into half-rich chunks is primitive
recursive. -/
theorem emittedHalfRichChunks_fold_step_primrec :
    Primrec₂ (fun (p : ℕ × List BitString × List (List BitString)) (x : BitString) =>
      emittedHalfRichChunksFoldStep p.1 p.2.1 p.2.2 x) := by
  have hj : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hhalf : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hchunks : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString => q.2) :=
    Primrec.snd
  have hflat : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        q.1.2.2.flatten) :=
    Primrec.list_flatten.comp hchunks
  have hplaced : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        decide (q.2 ∈ q.1.2.2.flatten)) :=
    bitString_mem_primrec.comp hx hflat
  have hnotPlaced : Primrec₂
      (fun (q : (ℕ × (List BitString × List (List BitString))) × BitString)
        (y : BitString) =>
        bif decide (y ∈ q.1.2.2.flatten) then false else true) := by
    have hmem : Primrec
        (fun z : ((ℕ × (List BitString × List (List BitString))) × BitString) × BitString =>
          decide (z.2 ∈ z.1.1.2.2.flatten)) :=
      bitString_mem_primrec.comp Primrec.snd (hflat.comp Primrec.fst)
    exact (Primrec.cond hmem (Primrec.const false) (Primrec.const true)).to₂
  have hunplaced : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        q.1.2.1.filter (fun y =>
          bif decide (y ∈ q.1.2.2.flatten) then false else true)) :=
    list_filter_primrec hhalf hnotPlaced
  have hnotEq : Primrec₂
      (fun (q : (ℕ × (List BitString × List (List BitString))) × BitString)
        (y : BitString) =>
        bif decide (y = q.2) then false else true) := by
    have heq : Primrec
        (fun z : ((ℕ × (List BitString × List (List BitString))) × BitString) × BitString =>
          decide (z.2 = z.1.2)) :=
      PrimrecPred.decide
        (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
    exact (Primrec.cond heq (Primrec.const false) (Primrec.const true)).to₂
  have hwithoutX : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        (q.1.2.1.filter (fun y =>
          bif decide (y ∈ q.1.2.2.flatten) then false else true)).filter
            (fun y => bif decide (y = q.2) then false else true)) :=
    list_filter_primrec hunplaced hnotEq
  have hcons : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        q.2 :: (q.1.2.1.filter (fun y =>
          bif decide (y ∈ q.1.2.2.flatten) then false else true)).filter
            (fun y => bif decide (y = q.2) then false else true)) :=
    Primrec.list_cons.comp hx hwithoutX
  have hpow : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString => 2 ^ q.1.1) :=
    primrec_two_pow_aux.comp hj
  have hnewChunk : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        (q.2 :: (q.1.2.1.filter (fun y =>
          bif decide (y ∈ q.1.2.2.flatten) then false else true)).filter
            (fun y => bif decide (y = q.2) then false else true)).take (2 ^ q.1.1)) :=
    Primrec.list_take.comp hpow hcons
  have hsingleton : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        [(q.2 :: (q.1.2.1.filter (fun y =>
          bif decide (y ∈ q.1.2.2.flatten) then false else true)).filter
            (fun y => bif decide (y = q.2) then false else true)).take (2 ^ q.1.1)]) :=
    Primrec.list_cons.comp hnewChunk (Primrec.const [])
  have happend : Primrec
      (fun q : (ℕ × (List BitString × List (List BitString))) × BitString =>
        q.1.2.2 ++
          [(q.2 :: (q.1.2.1.filter (fun y =>
            bif decide (y ∈ q.1.2.2.flatten) then false else true)).filter
              (fun y => bif decide (y = q.2) then false else true)).take (2 ^ q.1.1)]) :=
    Primrec.list_append.comp hchunks hsingleton
  simpa only [emittedHalfRichChunksFoldStep] using
    (Primrec.cond hplaced hchunks happend).to₂
/-
General `foldl` combinator: a left fold with a primitive-recursive step
function, initial accumulator, and list, all primitive recursive in the input,
is primitive recursive.
-/
theorem list_foldl_primrec {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ → β → σ}
    (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec (fun p : (α × σ) × β => h p.1.1 p.1.2 p.2)) :
    Primrec (fun a => (f a).foldl (h a) (g a)) := by
  refine Primrec.list_foldl hf hg
    (show Primrec₂ (fun (a : α) (p : σ × β) => h a p.1 p.2) from ?_)
  exact hh.comp (Primrec.pair (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd))

/-- One stage of the chunking: extend the current chunks by the elements emitted at
stage `t`. -/
def emittedHalfRichChunksStep (c : Code) (i j k : ℕ) (t : ℕ) (chunks : List (List BitString)) :
    List (List BitString) :=
  let rich := (snapshotRichElementsList c i j k t).eraseDups
  let half_rich := (snapshotRichElementsList c i j (k - 1) t).eraseDups
  rich.foldl (emittedHalfRichChunksFoldStep j half_rich) chunks

/-- One chunking stage is primitive recursive in its parameters. -/
theorem emittedHalfRichChunks_step_primrec (c : Code) :
    Primrec (fun p : ((ℕ × ℕ) × ℕ) × ℕ × List (List BitString) =>
      emittedHalfRichChunksStep c p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2) := by
  -- Compose the primitive-recursive rich and half-rich snapshot lists with the
  -- fold step.
  apply list_foldl_primrec;
  · have h_eraseDups_primrec : Primrec (fun (l : List BitString) => l.eraseDups) :=
      eraseDups_bitstring_primrec
    exact h_eraseDups_primrec.comp (
        snapshotRichElementsList_primrec c |> Primrec.comp <| Primrec.pair ( Primrec.pair (
            Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ( Primrec.snd.comp (
              Primrec.fst.comp ( Primrec.fst ) ) ) ) ( Primrec.pair ( Primrec.snd.comp (
                Primrec.fst ) ) ( Primrec.fst.comp ( Primrec.snd ) ) ) );
  · exact Primrec.snd.comp ( Primrec.snd );
  · convert emittedHalfRichChunks_fold_step_primrec.comp _ _ using 1;
    rotate_left;
    · exact fun p => ( p.1.1.1.1.2, ( snapshotRichElementsList c p.1.1.1.1.1 p.1.1.1.1.2 (
        p.1.1.1.2 - 1 ) p.1.1.2.1 ).eraseDups, p.1.2 );
    · exact fun p => p.2;
    · apply Primrec₂.comp;
      · exact Primrec.pair Primrec.fst Primrec.snd;
      · exact Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp (
          Primrec.fst ) ) ) );
      · apply Primrec.pair;
        · have h_eraseDups_primrec : Primrec (fun (L : List BitString) => L.eraseDups) := by
            grind +suggestions;
          convert h_eraseDups_primrec.comp _ using 1;
          convert snapshotRichElementsList_primrec c |> Primrec.comp <| _ using 1;
          rotate_left;
          · exact fun p => ( p.1.1.1.1, p.1.1.1.2 - 1, p.1.1.2.1 );
          · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp (
              Primrec.fst ) ) ) ) ( Primrec.pair ( Primrec.nat_sub.comp ( Primrec.snd.comp (
                Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) ( Primrec.const 1 ) ) (
                  Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) );
          · grind;
        · exact Primrec.snd.comp ( Primrec.fst );
    · exact Primrec.snd;
    · rfl

/-- The chunk lists after `t` stages of the chunking. -/
def emittedHalfRichChunksList (c : Code) (i j k : ℕ) : ℕ → List (List BitString)
| 0 => emittedHalfRichChunksStep c i j k 0 []
| t + 1 => emittedHalfRichChunksStep c i j k (t + 1) (emittedHalfRichChunksList c i j k t)

/-- The chunk lists are primitive recursive in the parameters and the stage. -/
theorem emittedHalfRichChunksList_primrec (c : Code) :
    Primrec (fun p : ((
        ℕ × ℕ) × ℕ) × ℕ => emittedHalfRichChunksList c p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  -- Primitive recursion over time for the emitted online chunk stream.
  apply Primrec.of_eq;
  rotate_right;
  · exact fun p => ( List.foldl (
      fun chunks t => emittedHalfRichChunksStep c p.1.1.1 p.1.1.2 p.1.2 ( t + 1 ) chunks ) (
        emittedHalfRichChunksStep c p.1.1.1 p.1.1.2 p.1.2 0 [ ] ) ( List.range p.2 ) );
  · apply list_foldl_primrec;
    · exact Primrec.list_range.comp ( Primrec.snd );
    · convert emittedHalfRichChunks_step_primrec c |> Primrec.comp <| _ using 1;
      rotate_left;
      · exact fun p => ( p.1, 0, [ ] );
      · exact Primrec.pair ( Primrec.fst ) ( Primrec.pair ( Primrec.const 0 ) ( Primrec.const [
        ] ) );
      · grind;
    · convert emittedHalfRichChunks_step_primrec c |> Primrec.comp <| _ using 1;
      rotate_left;
      · exact fun p => ( p.1.1.1, p.2 + 1, p.1.2 );
      · exact Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.succ.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      · grind;
  · intro n; induction n.2 <;> simp_all +decide [ List.range_succ ] ;
    · rfl;
    · rfl

/-- The chunks after `t` stages, as finite sets. -/
def emittedHalfRichChunks (c : Code) (i j k : ℕ) (t : ℕ) : List (Finset BitString) :=
  (emittedHalfRichChunksList c i j k t).map List.toFinset

end Kolmogorov
