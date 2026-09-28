import KolmogorovMathlib.AlgorithmicStatistics.BoundedLists.OmegaPrefix
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.Restricted.EffectiveSelection.Part01

/-!
# VS40 Section 4, Milestone B5: position invariance and tail monotonicity

The public coordinate is the completed suffix *including* `x`.  This avoids
taking a logarithm of zero when `x` is the final output.  The proofs below use
one uniform reconstruction selector.  Given a high prefix of the first Omega
count, it waits for the last full dyadic block containing `x`, waits until that
whole block has appeared in the second enumeration, and uses the exact number
of still-missing outputs as short advice to reconstruct the second Omega count.

`boundedOutputEnumeration c m` is only a convenience wrapper for a *fixed*
bound.  No uniform complexity theorem below is obtained from that wrapper:
such a theorem could have a constant depending on `m`.  The reconstruction
selector instead treats both bounds as explicit data and is fixed before all
varying bounds and strings.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The bounded complexity list at bound `m`, packaged as a staged enumeration: its stages are
the `boundedOutputStage c m t`, which are computable and increase by prefixes. -/
def boundedOutputEnumeration (c : Code) (m : ℕ) : StagedEnumeration where
  enum t := boundedOutputStage c m t
  computable := (boundedOutputStage_computable c).comp
    (Computable.pair (Computable.const m) Computable.id)
  mono t := boundedOutputStage_prefix c m t

/-- The suffix coordinate of `x` in the completed bound-`m` enumeration. -/
noncomputable def suffixCoordinate (c : Code) (m : ℕ) (x : BitString) : ℕ :=
  suffixCountIncluding (completedBoundedOutput c m) x

/-- The suffix coordinate of `x` at bound `m` is positive exactly when the plain
complexity of `x` is at most `m`. -/
theorem suffixCoordinate_pos_iff_plainK_le
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    (m : ℕ) (x : BitString) :
    0 < suffixCoordinate c m x ↔ plainK V x ≤ (m : ENat) := by
  unfold suffixCoordinate
  rw [suffixCountIncluding_pos_iff_mem]
  exact mem_completedBoundedOutput_iff_plainK_le hc m x

/-- The suffix count of an element is at most the length of the list. -/
theorem suffixCountIncluding_le_length
    {α : Type*} [DecidableEq α] (L : List α) (x : α) :
    suffixCountIncluding L x ≤ L.length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
      unfold suffixCountIncluding
      split_ifs
      · exact le_rfl
      · exact ih.trans (Nat.le_succ _)

/-- The suffix coordinate at bound `m` is at most `omegaCount c m`. -/
theorem suffixCoordinate_le_omegaCount
    (c : Code) (m : ℕ) (x : BitString) :
    suffixCoordinate c m x ≤ omegaCount c m := by
  exact suffixCountIncluding_le_length _ _

/-- If `x` does not occur in `P`, its suffix count in `P ++ x :: S` is `|S| + 1`. -/
theorem suffixCountIncluding_append_cons_of_not_mem
    {α : Type*} [DecidableEq α]
    (P S : List α) (x : α) (hxP : x ∉ P) :
    suffixCountIncluding (P ++ x :: S) x = S.length + 1 := by
  induction P with
  | nil => simp [suffixCountIncluding]
  | cons y P ih =>
      simp only [List.mem_cons, not_or] at hxP
      unfold suffixCountIncluding
      simp only [List.cons_append]
      rw [if_neg (Ne.symm hxP.1)]
      exact ih hxP.2

/-- The dyadic block used by the position selector really contains `x`.
The list is duplicate-free, `T` is the lower endpoint determined by a high
Omega prefix, and `Q` is the corresponding dyadic quantum. -/
theorem mem_recentBlock_of_suffix_bracket
    {α : Type*} [DecidableEq α]
    {L : List α} {x : α} (hL : L.Nodup) (hx : x ∈ L)
    {T Q : ℕ}
    (hTle : T ≤ L.length) (hlenLt : L.length < T + Q)
    (hQle : Q ≤ suffixCountIncluding L x)
    (hlt2Q : suffixCountIncluding L x < 2 * Q) :
    x ∈ (L.take T).drop (T - 2 * Q) := by
  obtain ⟨P, S, hdecomp⟩ := List.mem_iff_append.mp hx
  have hxP : x ∉ P := by
    rw [hdecomp, List.nodup_append] at hL
    intro hxP
    exact hL.2.2 x hxP x (by simp) rfl
  have hsuffix :
      suffixCountIncluding L x = S.length + 1 := by
    rw [hdecomp]
    exact suffixCountIncluding_append_cons_of_not_mem P S x hxP
  have hlen :
      L.length = P.length + suffixCountIncluding L x := by
    calc
      L.length = P.length + (S.length + 1) := by
        rw [hdecomp, List.length_append, List.length_cons]
      _ = P.length + suffixCountIncluding L x := by rw [hsuffix]
  have hPlt : P.length < T := by omega
  have hstart : T - 2 * Q ≤ P.length := by omega
  rw [List.mem_drop_iff_getElem]
  let j := P.length - (T - 2 * Q)
  have hjstart : (T - 2 * Q) + j = P.length := by
    dsimp [j]
    omega
  have htakeLen : (L.take T).length = T := by
    simp [List.length_take, Nat.min_eq_left hTle]
  refine ⟨j, ?_, ?_⟩
  · rw [htakeLen]
    omega
  · have hidx : T - 2 * Q + j = P.length := hjstart
    have hidxT : T - 2 * Q + j < T := by omega
    have hopt :
        (L.take T)[T - 2 * Q + j]? = some x := by
      rw [List.getElem?_take, if_pos hidxT, hidx, hdecomp]
      simp
    exact (List.getElem?_eq_some_iff.mp hopt).2

/-! ## Uniform reconstruction input -/

/-- The short self-delimiting header carries the source bound, target bound,
and the width of the high Omega prefix. -/
def positionReconstructionHeader (m n k : ℕ) : BitString :=
  pairCode (Nat.bits m) (pairCode (Nat.bits n) (Nat.bits k))

/-- Input to the position reconstruction selector.  The long fields are kept
undoubled in the payload: a high prefix of `Ω_m`, followed by a fixed-width
code for the number of target outputs still missing. -/
def positionReconstructionInput
    (m n k : ℕ) (omegaPrefix : BitString) (remaining remainingWidth : ℕ) :
    BitString :=
  pairCode (positionReconstructionHeader m n k)
    (omegaPrefix ++ fixedWidthNatCode remaining remainingWidth)

/-- The source bound read off a position-reconstruction input. -/
def positionReconstructionM (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeFirst z))

/-- The target bound read off a position-reconstruction input. -/
def positionReconstructionN (z : BitString) : ℕ :=
  bitsToNat (decodeFirst (decodeSecond (decodeFirst z)))

/-- The width of the high `Ω` prefix, read off a position-reconstruction input. -/
def positionReconstructionK (z : BitString) : ℕ :=
  bitsToNat (decodeSecond (decodeSecond (decodeFirst z)))

/-- The payload block of a position-reconstruction input. -/
def positionReconstructionPayload (z : BitString) : BitString :=
  decodeSecond z

/-- The high `Ω` prefix carried by a position-reconstruction input. -/
def positionReconstructionPrefix (z : BitString) : BitString :=
  (positionReconstructionPayload z).take (positionReconstructionK z)

/-- The number of still-missing target outputs, read off a position-reconstruction
input. -/
def positionReconstructionRemaining (z : BitString) : ℕ :=
  decodeFixedWidthNatCode
    ((positionReconstructionPayload z).drop (positionReconstructionK z))

/-- The block size `2 ^ (m + 1 - k)` determined by the source bound and the prefix
width. -/
def positionReconstructionQuantum (z : BitString) : ℕ :=
  2 ^ (positionReconstructionM z + 1 - positionReconstructionK z)

/-- The stage threshold determined by the high prefix: the prefix value times the
block size. -/
def positionReconstructionThreshold (z : BitString) : ℕ :=
  decodeFixedWidthNatCode (positionReconstructionPrefix z) *
    positionReconstructionQuantum z

/-- The last two source blocks before the high-prefix threshold.  When the
block size `Q` satisfies `Q ≤ suffix(x) < 2Q`, this list contains `x`. -/
def positionReconstructionBlock
    (c : Code) (z : BitString) (t : ℕ) : List BitString :=
  let threshold := positionReconstructionThreshold z
  let quantum := positionReconstructionQuantum z
  ((boundedOutputStage c (positionReconstructionM z) t).take threshold).drop
    (threshold - 2 * quantum)

/-- A computable Boolean test that every element of `xs` occurs in `ys`. -/
def positionBlockSeen (xs ys : List BitString) : Bool :=
  xs.all (fun x => decide (x ∈ ys))

/-- Uniform reconstruction of the target Omega count. -/
noncomputable def positionReconstructionSelector
    (c₁ c₂ : Code) : BitString →. BitString := fun z =>
  (Nat.rfind (fun t => Part.some (decide
      (positionReconstructionThreshold z ≤
        (boundedOutputStage c₁ (positionReconstructionM z) t).length)))).bind
    (fun t₁ =>
      (Nat.rfind (fun t => Part.some
          (positionBlockSeen
            (positionReconstructionBlock c₁ z t₁)
            (boundedOutputStage c₂ (positionReconstructionN z) t)))).bind
        (fun t₂ => Part.some (Nat.bits
          ((boundedOutputStage c₂
            (positionReconstructionN z) t₂).length +
              positionReconstructionRemaining z))))

/-- The exact length of a position-reconstruction input in terms of the prefix
width, the remainder width and the three header parameters. -/
theorem positionReconstructionInput_length
    {m n k remaining remainingWidth : ℕ} {omegaPrefix : BitString}
    (hprefix : omegaPrefix.length = k)
    (hremaining : remaining < 2 ^ remainingWidth) :
    (positionReconstructionInput m n k omegaPrefix remaining remainingWidth).length =
      k + remainingWidth +
        4 * (Nat.bits m).length +
        4 * (Nat.bits n).length +
        2 * (Nat.bits k).length + 5 := by
  unfold positionReconstructionInput positionReconstructionHeader
  rw [length_pairCode, length_pairCode, length_pairCode,
    List.length_append, fixedWidthNatCode_length hremaining, hprefix]
  omega

/-- The source bound is read back from an assembled input. -/
@[simp] theorem positionReconstructionM_input
    (m n k remaining remainingWidth : ℕ) (omegaPrefix : BitString) :
    positionReconstructionM
      (positionReconstructionInput m n k omegaPrefix remaining remainingWidth) = m := by
  unfold positionReconstructionM positionReconstructionInput
  rw [decodeFirst_pairCode]
  unfold positionReconstructionHeader
  rw [decodeFirst_pairCode, bitsToNat_bits]

/-- The target bound is read back from an assembled input. -/
@[simp] theorem positionReconstructionN_input
    (m n k remaining remainingWidth : ℕ) (omegaPrefix : BitString) :
    positionReconstructionN
      (positionReconstructionInput m n k omegaPrefix remaining remainingWidth) = n := by
  unfold positionReconstructionN positionReconstructionInput
  rw [decodeFirst_pairCode]
  unfold positionReconstructionHeader
  rw [decodeSecond_pairCode, decodeFirst_pairCode, bitsToNat_bits]

/-- The prefix width is read back from an assembled input. -/
@[simp] theorem positionReconstructionK_input
    (m n k remaining remainingWidth : ℕ) (omegaPrefix : BitString) :
    positionReconstructionK
      (positionReconstructionInput m n k omegaPrefix remaining remainingWidth) = k := by
  unfold positionReconstructionK positionReconstructionInput
  rw [decodeFirst_pairCode]
  unfold positionReconstructionHeader
  rw [decodeSecond_pairCode, decodeSecond_pairCode, bitsToNat_bits]

/-- The high `Ω` prefix is read back from an assembled input. -/
theorem positionReconstructionPrefix_input
    {m n k remaining remainingWidth : ℕ} {omegaPrefix : BitString}
    (hprefix : omegaPrefix.length = k) :
    positionReconstructionPrefix
      (positionReconstructionInput m n k omegaPrefix remaining remainingWidth) = omegaPrefix := by
  unfold positionReconstructionPrefix positionReconstructionPayload
  rw [positionReconstructionK_input]
  unfold positionReconstructionInput
  rw [decodeSecond_pairCode]
  rw [← hprefix, List.take_left]

/-- The remainder count is read back from an assembled input. -/
theorem positionReconstructionRemaining_input
    {m n k remaining remainingWidth : ℕ} {omegaPrefix : BitString}
    (hprefix : omegaPrefix.length = k) :
    positionReconstructionRemaining
      (positionReconstructionInput m n k omegaPrefix remaining remainingWidth) = remaining := by
  unfold positionReconstructionRemaining positionReconstructionPayload
  rw [positionReconstructionK_input]
  unfold positionReconstructionInput
  rw [decodeSecond_pairCode]
  rw [← hprefix, List.drop_left, decodeFixedWidthNatCode_encode]

/-- Pure computability plumbing for the fixed two-bound reconstruction. -/
theorem positionReconstructionSelector_partrec (c₁ c₂ : Code) :
    Partrec (positionReconstructionSelector c₁ c₂) := by
  have hm : Primrec positionReconstructionM :=
    bitsToNat_primrec.comp
      (CodedFiniteDistribution.decodeFirst_primrec.comp CodedFiniteDistribution.decodeFirst_primrec)
  have hn : Primrec positionReconstructionN :=
    bitsToNat_primrec.comp
      (CodedFiniteDistribution.decodeFirst_primrec.comp
        (CodedFiniteDistribution.decodeSecond_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec))
  have hk : Primrec positionReconstructionK :=
    bitsToNat_primrec.comp
      (CodedFiniteDistribution.decodeSecond_primrec.comp
        (CodedFiniteDistribution.decodeSecond_primrec.comp
          CodedFiniteDistribution.decodeFirst_primrec))
  have hpayload : Primrec positionReconstructionPayload :=
    CodedFiniteDistribution.decodeSecond_primrec
  have hprefix : Primrec positionReconstructionPrefix := by
    unfold positionReconstructionPrefix
    exact Primrec.list_take.comp hpayload hk
  have hremaining : Primrec positionReconstructionRemaining := by
    unfold positionReconstructionRemaining
    exact decodeFixedWidthNatCode_primrec.comp
      (Primrec.list_drop.comp hpayload hk)
  have hquantum : Primrec positionReconstructionQuantum := by
    unfold positionReconstructionQuantum
    exact Kolmogorov.primrec_two_pow_aux.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_add.comp hm (Primrec.const 1)) hk)
  have hthreshold : Primrec positionReconstructionThreshold := by
    unfold positionReconstructionThreshold
    exact Primrec.nat_mul.comp
      (decodeFixedWidthNatCode_primrec.comp hprefix) hquantum
  have hm₁ : Primrec (fun q : BitString × ℕ =>
      positionReconstructionM q.1) :=
    hm.comp Primrec.fst
  have hstage₁ : Primrec (fun q : BitString × ℕ =>
      boundedOutputStage c₁ (positionReconstructionM q.1) q.2) :=
    (boundedOutputStage_primrec c₁).comp
      (Primrec.pair hm₁ Primrec.snd)
  have hthreshold₁ : Primrec (fun q : BitString × ℕ =>
      positionReconstructionThreshold q.1) :=
    hthreshold.comp Primrec.fst
  have hcheck₁ : Computable₂ (fun (z : BitString) (t : ℕ) =>
      decide (positionReconstructionThreshold z ≤
        (boundedOutputStage c₁
          (positionReconstructionM z) t).length)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hthreshold₁
        (Primrec.list_length.comp hstage₁))).to_comp.to₂
  have hsearch₁ : Partrec (fun z : BitString =>
      Nat.rfind (fun t => Part.some (decide
        (positionReconstructionThreshold z ≤
          (boundedOutputStage c₁
            (positionReconstructionM z) t).length)))) :=
    Partrec.rfind hcheck₁.partrec₂
  have htwiceQuantum : Primrec (fun z : BitString =>
      2 * positionReconstructionQuantum z) :=
    Primrec.nat_mul.comp (Primrec.const 2) hquantum
  have hstart : Primrec (fun z : BitString =>
      positionReconstructionThreshold z -
        2 * positionReconstructionQuantum z) :=
    Primrec.nat_sub.comp hthreshold htwiceQuantum
  have hblock : Primrec (fun q : BitString × ℕ =>
      positionReconstructionBlock c₁ q.1 q.2) := by
    unfold positionReconstructionBlock
    exact Primrec.list_drop.comp
      (Primrec.list_take.comp hstage₁ hthreshold₁)
      (hstart.comp Primrec.fst)
  have hn₂ : Primrec (fun q : (BitString × ℕ) × ℕ =>
      positionReconstructionN q.1.1) :=
    hn.comp (Primrec.fst.comp Primrec.fst)
  have hstage₂ : Primrec (fun q : (BitString × ℕ) × ℕ =>
      boundedOutputStage c₂ (positionReconstructionN q.1.1) q.2) :=
    (boundedOutputStage_primrec c₂).comp
      (Primrec.pair hn₂ Primrec.snd)
  have hblock₂ : Primrec (fun q : (BitString × ℕ) × ℕ =>
      positionReconstructionBlock c₁ q.1.1 q.1.2) :=
    hblock.comp Primrec.fst
  have hseen : Primrec (fun q : (BitString × ℕ) × ℕ =>
      positionBlockSeen
        (positionReconstructionBlock c₁ q.1.1 q.1.2)
        (boundedOutputStage c₂ (positionReconstructionN q.1.1) q.2)) := by
    have hpred : Primrec₂
        (fun (q : (BitString × ℕ) × ℕ) (x : BitString) =>
          decide (x ∈ boundedOutputStage c₂
            (positionReconstructionN q.1.1) q.2)) :=
      (bitString_mem_primrec.comp Primrec.snd
        (hstage₂.comp Primrec.fst)).to₂
    unfold positionBlockSeen
    exact list_all_primrec hblock₂ hpred
  have hcheck₂ : Computable₂
      (fun (q : BitString × ℕ) (t : ℕ) =>
        positionBlockSeen
          (positionReconstructionBlock c₁ q.1 q.2)
          (boundedOutputStage c₂ (positionReconstructionN q.1) t)) :=
    hseen.to_comp.to₂
  have hsearch₂ : Partrec (fun q : BitString × ℕ =>
      Nat.rfind (fun t => Part.some
        (positionBlockSeen
          (positionReconstructionBlock c₁ q.1 q.2)
          (boundedOutputStage c₂
            (positionReconstructionN q.1) t)))) :=
    Partrec.rfind hcheck₂.partrec₂
  have hout : Computable₂
      (fun (q : BitString × ℕ) (t : ℕ) =>
        Nat.bits
          ((boundedOutputStage c₂
            (positionReconstructionN q.1) t).length +
              positionReconstructionRemaining q.1)) := by
    have hstageOut : Primrec (fun q : (BitString × ℕ) × ℕ =>
        boundedOutputStage c₂
          (positionReconstructionN q.1.1) q.2) :=
      hstage₂
    have hremainingOut : Primrec (fun q : (BitString × ℕ) × ℕ =>
        positionReconstructionRemaining q.1.1) :=
      hremaining.comp (Primrec.fst.comp Primrec.fst)
    exact (primrec_natBits.comp
      (Primrec.nat_add.comp
        (Primrec.list_length.comp hstageOut)
        hremainingOut)).to_comp.to₂
  have hafter : Partrec₂
      (fun (z : BitString) (t₁ : ℕ) =>
        (Nat.rfind (fun t => Part.some
          (positionBlockSeen
            (positionReconstructionBlock c₁ z t₁)
            (boundedOutputStage c₂
              (positionReconstructionN z) t)))).bind
          (fun t₂ => Part.some (Nat.bits
            ((boundedOutputStage c₂
              (positionReconstructionN z) t₂).length +
                positionReconstructionRemaining z)))) :=
    (Partrec.bind hsearch₂
      ((Partrec.comp Partrec.some hout).to₂)).to₂
  exact (Partrec.bind hsearch₁ hafter).of_eq (fun _ => rfl)

/-! ### Pieces of the reconstruction argument -/

/-- The least stage at which a Boolean test succeeds is a value of `Nat.rfind` on that
test: this is the bridge between the two ways the selector's searches are described,
`Nat.find` in the argument and `Nat.rfind` in the partial function. -/
private lemma nat_find_mem_rfind {f : ℕ → Bool} (h : ∃ t, f t = true) :
    Nat.find h ∈ Nat.rfind (fun t => Part.some (f t)) := by
  rw [Nat.mem_rfind]
  refine ⟨by simpa using Nat.find_spec h, ?_⟩
  intro u hu
  simpa using Nat.find_min h hu

/-- The decidable-predicate form of `nat_find_mem_rfind`: the least stage at which a
decidable property holds is a value of `Nat.rfind` on its decision procedure. -/
private lemma nat_find_mem_rfind_decide {p : ℕ → Prop} [DecidablePred p] (h : ∃ t, p t) :
    Nat.find h ∈ Nat.rfind (fun t => Part.some (decide (p t))) := by
  rw [Nat.mem_rfind]
  refine ⟨by simpa using Nat.find_spec h, ?_⟩
  intro u hu
  simpa using Nat.find_min h hu

/-- **The source-side block.**  If the threshold `T` and the quantum `Q` bracket the Omega
count of the source enumeration and `x`'s suffix coordinate lies in `[Q, 2Q)`, then `x` is
one of the last `2Q` of the first `T` completed source outputs. -/
private lemma positionReconstruction_mem_recentBlock (c₁ : Code) {m T Q : ℕ} {x : BitString}
    (hx : x ∈ completedBoundedOutput c₁ m)
    (hTle : T ≤ omegaCount c₁ m) (homegaLt : omegaCount c₁ m < T + Q)
    (hQle : Q ≤ suffixCoordinate c₁ m x)
    (hlt2Q : suffixCoordinate c₁ m x < 2 * Q) :
    x ∈ ((completedBoundedOutput c₁ m).take T).drop (T - 2 * Q) := by
  apply mem_recentBlock_of_suffix_bracket
  · unfold completedBoundedOutput
    exact boundedOutputStage_nodup c₁ m _
  · exact hx
  · simpa [omegaCount] using hTle
  · simpa [omegaCount] using homegaLt
  · simpa [suffixCoordinate] using hQle
  · simpa [suffixCoordinate] using hlt2Q

/-- **The target-side search.**  If every element of the block is a completed target
output, then the target enumeration has seen the whole block at some stage; at the first
such stage the outputs still missing are fewer than `x`'s target suffix coordinate. -/
private lemma positionReconstruction_exists_seen_stage (c₂ : Code) {n : ℕ} {x : BitString}
    (block : List BitString) (hxblock : x ∈ block)
    (hblockSubset : ∀ y, y ∈ block → y ∈ completedBoundedOutput c₂ n) :
    ∃ t₂ : ℕ, ∃ rest : List BitString,
      t₂ ∈ Nat.rfind (fun t => Part.some
        (positionBlockSeen block (boundedOutputStage c₂ n t))) ∧
      boundedOutputStage c₂ n t₂ ++ rest = completedBoundedOutput c₂ n ∧
      rest.length < suffixCoordinate c₂ n x := by
  have hseenAtCompletion :
      positionBlockSeen block
        (boundedOutputStage c₂ n (boundedOutputCompletionTime c₂ n)) = true := by
    unfold positionBlockSeen
    rw [List.all_eq_true]
    intro y hy
    rw [decide_eq_true_eq, boundedOutputStage_eq_completed_at_completion]
    exact hblockSubset y hy
  have hex : ∃ t, positionBlockSeen block (boundedOutputStage c₂ n t) = true :=
    ⟨boundedOutputCompletionTime c₂ n, hseenAtCompletion⟩
  refine ⟨Nat.find hex, ?_⟩
  have hspec : positionBlockSeen block
      (boundedOutputStage c₂ n (Nat.find hex)) = true := Nat.find_spec hex
  have hxTargetStage : x ∈ boundedOutputStage c₂ n (Nat.find hex) := by
    unfold positionBlockSeen at hspec
    rw [List.all_eq_true] at hspec
    have hxSeen := hspec x hxblock
    rwa [decide_eq_true_eq] at hxSeen
  obtain ⟨rest, hrest⟩ :=
    boundedOutputStage_prefix_completed c₂ n (Nat.find hex)
  refine ⟨rest, nat_find_mem_rfind hex, hrest, ?_⟩
  have hsuffixPos :
      0 < suffixCountIncluding (boundedOutputStage c₂ n (Nat.find hex)) x :=
    suffixCountIncluding_pos_iff_mem.mpr hxTargetStage
  have hsuffix :
      suffixCoordinate c₂ n x =
        suffixCountIncluding (boundedOutputStage c₂ n (Nat.find hex)) x + rest.length := by
    unfold suffixCoordinate
    rw [← hrest, suffixCountIncluding_append_of_mem hxTargetStage]
  omega

/-- Correctness of the concrete reconstruction selector.  The hypotheses say
that the source suffix lies in the dyadic bracket `[Q,2Q)` and that every
completed source output is a completed target output.  The selector then needs
strictly fewer than `suffixCoordinate c₂ n x` possible values for the final
missing-count advice. -/
theorem positionReconstructionSelector_recovers
    (c₁ c₂ : Code) {m n k : ℕ} {x : BitString}
    (hk : k ≤ m + 1)
    (hx : x ∈ completedBoundedOutput c₁ m)
    (hQle :
      2 ^ (m + 1 - k) ≤ suffixCoordinate c₁ m x)
    (hlt2Q :
      suffixCoordinate c₁ m x < 2 * 2 ^ (m + 1 - k))
    (hsubset :
      ∀ y, y ∈ completedBoundedOutput c₁ m →
        y ∈ completedBoundedOutput c₂ n) :
    ∃ remaining : ℕ,
      remaining < suffixCoordinate c₂ n x ∧
      Nat.bits (omegaCount c₂ n) ∈
        positionReconstructionSelector c₁ c₂
          (positionReconstructionInput m n k
            ((omegaFixedCode c₁ m).take k) remaining
            (Nat.log 2 (suffixCoordinate c₂ n x) + 1)) := by
  let omegaPrefix := (omegaFixedCode c₁ m).take k
  let remainingWidth := Nat.log 2 (suffixCoordinate c₂ n x) + 1
  have hprefix : omegaPrefix.length = k := by
    dsimp [omegaPrefix]
    rw [List.length_take, omegaFixedCode_length, Nat.min_eq_left hk]
  have hinterval :
      decodeFixedWidthNatCode omegaPrefix * 2 ^ (m + 1 - k) ≤
          omegaCount c₁ m ∧
        omegaCount c₁ m <
          (decodeFixedWidthNatCode omegaPrefix + 1) * 2 ^ (m + 1 - k) := by
    simpa [omegaPrefix] using
      fixedWidthNatCode_take_interval
        (omegaCount_lt_two_pow_succ c₁ m) k
  let threshold :=
    decodeFixedWidthNatCode omegaPrefix * 2 ^ (m + 1 - k)
  let quantum := 2 ^ (m + 1 - k)
  have hthresholdLe : threshold ≤ omegaCount c₁ m := by
    simpa [threshold, quantum] using hinterval.1
  have homegaLt : omegaCount c₁ m < threshold + quantum := by
    calc
      omegaCount c₁ m <
          (decodeFixedWidthNatCode omegaPrefix + 1) *
            2 ^ (m + 1 - k) := hinterval.2
      _ = threshold + quantum := by
        dsimp [threshold, quantum]
        ring
  let z₀ :=
    positionReconstructionInput m n k omegaPrefix 0 remainingWidth
  have hz₀Threshold :
      positionReconstructionThreshold z₀ = threshold := by
    unfold positionReconstructionThreshold
    rw [positionReconstructionPrefix_input hprefix]
    simp [z₀, threshold, positionReconstructionQuantum]
  have hz₀Quantum :
      positionReconstructionQuantum z₀ = quantum := by
    simp [z₀, quantum, positionReconstructionQuantum]
  have hex₁ :
      ∃ t, positionReconstructionThreshold z₀ ≤
        (boundedOutputStage c₁ (positionReconstructionM z₀) t).length := by
    refine ⟨boundedOutputCompletionTime c₁ m, ?_⟩
    rw [positionReconstructionM_input, hz₀Threshold]
    simpa [omegaCount] using hthresholdLe.trans_eq
      (boundedOutputCompletionTime_spec c₁ m).symm
  let t₁ := Nat.find hex₁
  have ht₁Spec :
      positionReconstructionThreshold z₀ ≤
        (boundedOutputStage c₁ (positionReconstructionM z₀) t₁).length :=
    Nat.find_spec hex₁
  have ht₁Mem :
      t₁ ∈ Nat.rfind (fun t => Part.some (decide
        (positionReconstructionThreshold z₀ ≤
          (boundedOutputStage c₁
            (positionReconstructionM z₀) t).length))) :=
    nat_find_mem_rfind_decide hex₁
  have ht₁Spec' :
      threshold ≤ (boundedOutputStage c₁ m t₁).length := by
    simpa [z₀, hz₀Threshold] using ht₁Spec
  have htake :
      (boundedOutputStage c₁ m t₁).take threshold =
        (completedBoundedOutput c₁ m).take threshold := by
    obtain ⟨sourceRest, hsourceRest⟩ :=
      boundedOutputStage_prefix_completed c₁ m t₁
    rw [← hsourceRest, List.take_append_of_le_length ht₁Spec']
  have hblockMem :
      x ∈ positionReconstructionBlock c₁ z₀ t₁ := by
    unfold positionReconstructionBlock
    dsimp only
    rw [positionReconstructionM_input, hz₀Threshold, hz₀Quantum, htake]
    exact positionReconstruction_mem_recentBlock c₁ hx hthresholdLe homegaLt
      (by simpa [quantum] using hQle) (by simpa [quantum] using hlt2Q)
  have hblockSubset :
      ∀ y, y ∈ positionReconstructionBlock c₁ z₀ t₁ →
        y ∈ completedBoundedOutput c₂ n := by
    intro y hy
    apply hsubset y
    apply (boundedOutputStage_prefix_completed c₁ m t₁).sublist.subset
    unfold positionReconstructionBlock at hy
    rw [positionReconstructionM_input] at hy
    exact List.mem_of_mem_take (List.mem_of_mem_drop hy)
  obtain ⟨t₂, targetRest, ht₂Mem, htargetRest, hremainingLt⟩ :=
    positionReconstruction_exists_seen_stage c₂
      (positionReconstructionBlock c₁ z₀ t₁) hblockMem hblockSubset
  let z :=
    positionReconstructionInput m n k omegaPrefix
      targetRest.length remainingWidth
  have hzThreshold :
      positionReconstructionThreshold z = threshold := by
    unfold positionReconstructionThreshold
    rw [positionReconstructionPrefix_input hprefix]
    simp [z, threshold, positionReconstructionQuantum]
  have ht₁Mem' :
      t₁ ∈ Nat.rfind (fun t => Part.some (decide
        (positionReconstructionThreshold z ≤
          (boundedOutputStage c₁
            (positionReconstructionM z) t).length))) := by
    simpa [z, z₀, hzThreshold, hz₀Threshold] using ht₁Mem
  have hblockEq :
      positionReconstructionBlock c₁ z t₁ =
        positionReconstructionBlock c₁ z₀ t₁ := by
    unfold positionReconstructionBlock
    simp [z, z₀, hzThreshold, hz₀Threshold,
      positionReconstructionQuantum]
  have ht₂Mem' :
      t₂ ∈ Nat.rfind (fun t => Part.some
        (positionBlockSeen
          (positionReconstructionBlock c₁ z t₁)
          (boundedOutputStage c₂ (positionReconstructionN z) t))) := by
    simpa [z, hblockEq] using ht₂Mem
  have hlengthAdd :
      (boundedOutputStage c₂ n t₂).length + targetRest.length =
        omegaCount c₂ n := by
    calc
      (boundedOutputStage c₂ n t₂).length + targetRest.length =
          (boundedOutputStage c₂ n t₂ ++ targetRest).length := by simp
      _ = (completedBoundedOutput c₂ n).length :=
        congrArg List.length htargetRest
      _ = omegaCount c₂ n := rfl
  refine ⟨targetRest.length, hremainingLt, ?_⟩
  change Nat.bits (omegaCount c₂ n) ∈
    positionReconstructionSelector c₁ c₂ z
  unfold positionReconstructionSelector
  rw [Part.mem_bind_iff]
  refine ⟨t₁, ht₁Mem', ?_⟩
  rw [Part.mem_bind_iff]
  refine ⟨t₂, ht₂Mem', ?_⟩
  rw [positionReconstructionN_input,
    positionReconstructionRemaining_input hprefix, hlengthAdd]
  exact Part.mem_some _

/-! ## The uniform position-growth core -/

/-- **The dyadic bracket of a suffix coordinate.**  The binary logarithm of a suffix
coordinate of a completed bound-`m` output is at most `m`, and its quantum brackets the
coordinate: the coordinate lies in `[2 ^ q, 2 ^ (q + 1))` for `q` that logarithm.  Read at
`k = m + 1 - q` this is the bracket hypothesis of
`positionReconstructionSelector_recovers`. -/
private lemma suffixCoordinate_dyadic_bracket (c₁ : Code) {m : ℕ} {x : BitString}
    (hx : x ∈ completedBoundedOutput c₁ m) :
    Nat.log 2 (suffixCoordinate c₁ m x) < m + 1 ∧
      2 ^ Nat.log 2 (suffixCoordinate c₁ m x) ≤ suffixCoordinate c₁ m x ∧
      suffixCoordinate c₁ m x < 2 * 2 ^ Nat.log 2 (suffixCoordinate c₁ m x) := by
  have haPos : 0 < suffixCoordinate c₁ m x := by
    dsimp [suffixCoordinate]
    exact suffixCountIncluding_pos_iff_mem.2 hx
  have haPow : suffixCoordinate c₁ m x < 2 ^ (m + 1) :=
    lt_of_le_of_lt (suffixCoordinate_le_omegaCount c₁ m x)
      (omegaCount_lt_two_pow_succ c₁ m)
  refine ⟨Nat.log_lt_of_lt_pow haPos.ne' haPow, Nat.pow_log_le_self 2 haPos.ne', ?_⟩
  rw [show 2 * 2 ^ Nat.log 2 (suffixCoordinate c₁ m x)
      = 2 ^ (Nat.log 2 (suffixCoordinate c₁ m x) + 1) by rw [pow_succ]; omega]
  exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- **The growth bound in arithmetic form.**  A number below `2 ^ (q + 1)` scaled by `2 ^ d`
stays below a positive `b` scaled by `2 ^ s`, as soon as the exponents satisfy
`q + 1 + d ≤ log₂ b + s`. -/
private lemma mul_two_pow_le_of_log_le {a b q d s : ℕ} (hb : 0 < b)
    (ha : a < 2 ^ (q + 1)) (hlog : q + 1 + d ≤ Nat.log 2 b + s) :
    a * 2 ^ d ≤ b * 2 ^ s :=
  le_of_lt <| calc
    a * 2 ^ d < 2 ^ (q + 1) * 2 ^ d :=
      Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ = 2 ^ (q + 1 + d) := (pow_add 2 (q + 1) d).symm
    _ ≤ 2 ^ (Nat.log 2 b + s) := Nat.pow_le_pow_right (by decide) hlog
    _ = 2 ^ Nat.log 2 b * 2 ^ s := by rw [pow_add]
    _ ≤ b * 2 ^ s := by
        gcongr
        exact Nat.pow_log_le_self 2 hb.ne'

/-- If the completed source set at budget `m` is included in the completed
target set at budget `n`, then the target suffix grows by the expected
`2^(n-m)` factor up to uniform logarithmic slack. -/
theorem suffixCoordinate_growth_of_subset
    (V : Map) (hV : isOptimalConditional V)
    (c₁ c₂ : Code) (hc₂ : IsCodeFor c₂ V) :
    ∃ C : ℕ, ∀ (m n : ℕ) (x : BitString),
      m ≤ n →
      x ∈ completedBoundedOutput c₁ m →
      (∀ y, y ∈ completedBoundedOutput c₁ m →
        y ∈ completedBoundedOutput c₂ n) →
      suffixCoordinate c₁ m x * 2 ^ (n - m) ≤
        suffixCoordinate c₂ n x * 2 ^ logSlack C n := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV
      (positionReconstructionSelector c₁ c₂)
      (positionReconstructionSelector_partrec c₁ c₂)
  obtain ⟨Clen, hlen⟩ := plainK_le_length V hV
  obtain ⟨Clower, hlower⟩ :=
    plainKNat_omegaCount_lower V hV c₂ hc₂
  let C := Clower + Cmap + Clen + 24
  refine ⟨C, fun m n x hmn hx hsubset => ?_⟩
  let a := suffixCoordinate c₁ m x
  let b := suffixCoordinate c₂ n x
  have haPos : 0 < a := by
    dsimp [a, suffixCoordinate]
    exact (suffixCountIncluding_pos_iff_mem).2 hx
  have hbMem : x ∈ completedBoundedOutput c₂ n := hsubset x hx
  have hbPos : 0 < b := by
    dsimp [b, suffixCoordinate]
    exact (suffixCountIncluding_pos_iff_mem).2 hbMem
  obtain ⟨hqLt, hQle0, hlt2Q0⟩ := suffixCoordinate_dyadic_bracket c₁ hx
  let q := Nat.log 2 a
  let k := m + 1 - q
  have hqLt' : q < m + 1 := hqLt
  have hk : k ≤ m + 1 := Nat.sub_le _ _
  have hmk : m + 1 - k = q := Nat.sub_sub_self (by omega)
  have hkq : k + q = m + 1 := Nat.sub_add_cancel (by omega)
  have hQle : 2 ^ (m + 1 - k) ≤ a := by rw [hmk]; exact hQle0
  have hlt2Q : a < 2 * 2 ^ (m + 1 - k) := by rw [hmk]; exact hlt2Q0
  obtain ⟨remaining, hremainingB, hselector⟩ :=
    positionReconstructionSelector_recovers c₁ c₂ hk hx hQle hlt2Q hsubset
  let remainingWidth := Nat.log 2 b + 1
  let omegaPrefix := (omegaFixedCode c₁ m).take k
  let input :=
    positionReconstructionInput m n k omegaPrefix remaining remainingWidth
  have hbPow : b < 2 ^ remainingWidth := by
    dsimp [remainingWidth]
    exact Nat.lt_pow_succ_log_self (by norm_num) b
  have hremainingPow : remaining < 2 ^ remainingWidth :=
    lt_trans hremainingB hbPow
  have hprefixLength : omegaPrefix.length = k := by
    dsimp [omegaPrefix]
    rw [List.length_take, omegaFixedCode_length, Nat.min_eq_left hk]
  have hinputLength :
      input.length =
        k + remainingWidth +
          4 * (Nat.bits m).length +
          4 * (Nat.bits n).length +
          2 * (Nat.bits k).length + 5 := by
    exact positionReconstructionInput_length hprefixLength hremainingPow
  have hselector' :
      Nat.bits (omegaCount c₂ n) ∈
        positionReconstructionSelector c₁ c₂ input := by
    simpa [input, omegaPrefix, remainingWidth] using hselector
  have hcomplexity :
      plainKNat V (omegaCount c₂ n) ≤
        (input.length : ENat) + (Clen : ENat) + (Cmap : ENat) := by
    calc
      plainKNat V (omegaCount c₂ n)
          ≤ plainK V input + (Cmap : ENat) :=
        hmap input _ hselector'
      _ ≤ ((input.length : ENat) + (Clen : ENat)) + (Cmap : ENat) := by
        gcongr
        exact hlen input
  have hnENat :
      (n : ENat) ≤
        (input.length : ENat) +
          (Clen : ENat) + (Cmap : ENat) + (Clower : ENat) := by
    calc
      (n : ENat) ≤
          plainKNat V (omegaCount c₂ n) + (Clower : ENat) :=
        hlower n
      _ ≤ ((input.length : ENat) + (Clen : ENat) + (Cmap : ENat)) +
          (Clower : ENat) := by
        gcongr
  have hn :
      n ≤ input.length + Clen + Cmap + Clower := by
    exact_mod_cast hnENat
  have hkN : k ≤ n + 1 := by
    dsimp [k]
    omega
  have hkBits :
      (Nat.bits k).length ≤ (Nat.bits n).length + 2 := by
    calc
      (Nat.bits k).length ≤ (Nat.bits (n + 1)).length :=
        length_natBits_mono hkN
      _ ≤ (Nat.bits n).length + (Nat.bits 1).length + 1 :=
        length_natBits_add_le n 1
      _ = (Nat.bits n).length + 2 := by norm_num
  have hmBits :
      (Nat.bits m).length ≤ (Nat.bits n).length :=
    length_natBits_mono hmn
  have hlog :
      q + 1 + (n - m) ≤
        Nat.log 2 b + logSlack C n := by
    have hraw :
        q + 1 + (n - m) ≤
          Nat.log 2 b +
            (10 * (Nat.bits n).length +
              Clen + Cmap + Clower + 12) := by
      rw [hinputLength] at hn
      dsimp [remainingWidth] at hn
      omega
    have habsorb :
        10 * (Nat.bits n).length +
            Clen + Cmap + Clower + 12 ≤
          logSlack C n := by
      have hbits : 10 * (Nat.bits n).length ≤ C * (Nat.bits n).length :=
        Nat.mul_le_mul_right _ (by
          dsimp [C]
          omega)
      have hconst : Clen + Cmap + Clower + 12 ≤ C := by
        dsimp [C]
        omega
      dsimp [logSlack]
      omega
    omega
  exact mul_two_pow_le_of_log_le hbPos (Nat.lt_pow_succ_log_self (by norm_num) a) hlog

/-! ## Paper-facing B5 endpoints -/

/-- Between two optimal machines the suffix coordinate is preserved up to a shift of
the bound and a factor `2 ^ logSlack C (m + d)`. -/
theorem prop_pos_def_shift
    (V₁ V₂ : Map)
    (hV₁ : isOptimalConditional V₁) (hV₂ : isOptimalConditional V₂)
    (c₁ c₂ : Code) (hc₁ : IsCodeFor c₁ V₁) (hc₂ : IsCodeFor c₂ V₂) :
    ∃ d C : ℕ, ∀ (m : ℕ) x, plainK V₁ x ≤ (m : ENat) →
      suffixCoordinate c₁ m x ≤
        suffixCoordinate c₂ (m + d) x * 2 ^ logSlack C (m + d) := by
  obtain ⟨d, hd⟩ := hV₂.2 V₁ hV₁.1
  obtain ⟨C, hgrowth⟩ :=
    suffixCoordinate_growth_of_subset V₂ hV₂ c₁ c₂ hc₂
  refine ⟨d, C, fun m x hx => ?_⟩
  have hxmem : x ∈ completedBoundedOutput c₁ m :=
    (mem_completedBoundedOutput_iff_plainK_le hc₁ m x).2 hx
  have hsubset :
      ∀ y, y ∈ completedBoundedOutput c₁ m →
        y ∈ completedBoundedOutput c₂ (m + d) := by
    intro y hy
    apply (mem_completedBoundedOutput_iff_plainK_le hc₂ (m + d) y).2
    have hyK : plainK V₁ y ≤ (m : ENat) :=
      (mem_completedBoundedOutput_iff_plainK_le hc₁ m y).1 hy
    calc
      plainK V₂ y ≤ plainK V₁ y + (d : ENat) := hd y []
      _ ≤ (m : ENat) + (d : ENat) := by gcongr
      _ = ((m + d : ℕ) : ENat) := by rw [Nat.cast_add]
  have hgrowth :=
    hgrowth m (m + d) x (Nat.le_add_right m d) hxmem hsubset
  calc
    suffixCoordinate c₁ m x
        ≤ suffixCoordinate c₁ m x * 2 ^ ((m + d) - m) := by
      exact Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ suffixCoordinate c₂ (m + d) x *
          2 ^ logSlack C (m + d) := hgrowth

/-- Two codes for the same optimal machine give suffix coordinates that agree up to
a factor `2 ^ logSlack C m` in both directions. -/
theorem prop_pos_def
    (V : Map) (hV : isOptimalConditional V)
    (c₁ c₂ : Code) (hc₁ : IsCodeFor c₁ V) (hc₂ : IsCodeFor c₂ V) :
    ∃ C : ℕ, ∀ (m : ℕ) x, plainK V x ≤ (m : ENat) →
      suffixCoordinate c₁ m x ≤
          suffixCoordinate c₂ m x * 2 ^ logSlack C m ∧
      suffixCoordinate c₂ m x ≤
          suffixCoordinate c₁ m x * 2 ^ logSlack C m := by
  obtain ⟨C₁, h₁⟩ :=
    suffixCoordinate_growth_of_subset V hV c₁ c₂ hc₂
  obtain ⟨C₂, h₂⟩ :=
    suffixCoordinate_growth_of_subset V hV c₂ c₁ hc₁
  let C := max C₁ C₂
  refine ⟨C, fun m x hx => ?_⟩
  have hx₁ : x ∈ completedBoundedOutput c₁ m :=
    (mem_completedBoundedOutput_iff_plainK_le hc₁ m x).2 hx
  have hx₂ : x ∈ completedBoundedOutput c₂ m :=
    (mem_completedBoundedOutput_iff_plainK_le hc₂ m x).2 hx
  have hsubset₁ :
      ∀ y, y ∈ completedBoundedOutput c₁ m →
        y ∈ completedBoundedOutput c₂ m := by
    intro y hy
    exact (mem_completedBoundedOutput_iff_plainK_le hc₂ m y).2
      ((mem_completedBoundedOutput_iff_plainK_le hc₁ m y).1 hy)
  have hsubset₂ :
      ∀ y, y ∈ completedBoundedOutput c₂ m →
        y ∈ completedBoundedOutput c₁ m := by
    intro y hy
    exact (mem_completedBoundedOutput_iff_plainK_le hc₁ m y).2
      ((mem_completedBoundedOutput_iff_plainK_le hc₂ m y).1 hy)
  have hforward := h₁ m m x le_rfl hx₁ hsubset₁
  have hbackward := h₂ m m x le_rfl hx₂ hsubset₂
  constructor
  · calc
      suffixCoordinate c₁ m x
          ≤ suffixCoordinate c₂ m x * 2 ^ logSlack C₁ m := by
        simpa using hforward
      _ ≤ suffixCoordinate c₂ m x * 2 ^ logSlack C m := by
        exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
            (logSlack_mono_left (le_max_left C₁ C₂) m)
  · calc
      suffixCoordinate c₂ m x
          ≤ suffixCoordinate c₁ m x * 2 ^ logSlack C₂ m := by
        simpa using hbackward
      _ ≤ suffixCoordinate c₁ m x * 2 ^ logSlack C m := by
        exact Nat.mul_le_mul_left _ <|
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
            (logSlack_mono_left (le_max_right C₁ C₂) m)

/-- Raising the bound by `d` multiplies the suffix coordinate by at least `2 ^ d`,
up to a factor `2 ^ logSlack C (m + d)`. -/
theorem prop_tail_monotonicity
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ (m d : ℕ) x, plainK V x ≤ (m : ENat) →
      suffixCoordinate c m x * 2 ^ d ≤
        suffixCoordinate c (m + d) x * 2 ^ logSlack C (m + d) := by
  obtain ⟨C, hgrowth⟩ :=
    suffixCoordinate_growth_of_subset V hV c c hc
  refine ⟨C, fun m d x hx => ?_⟩
  have hxmem : x ∈ completedBoundedOutput c m :=
    (mem_completedBoundedOutput_iff_plainK_le hc m x).2 hx
  have hsubset :
      ∀ y, y ∈ completedBoundedOutput c m →
        y ∈ completedBoundedOutput c (m + d) := by
    intro y hy
    apply (mem_completedBoundedOutput_iff_plainK_le hc (m + d) y).2
    have hyK :=
      (mem_completedBoundedOutput_iff_plainK_le hc m y).1 hy
    exact hyK.trans (by
      exact_mod_cast Nat.le_add_right m d)
  simpa using
    hgrowth m (m + d) x (Nat.le_add_right m d) hxmem hsubset

end Kolmogorov
