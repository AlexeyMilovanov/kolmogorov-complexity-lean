import KolmogorovMathlib.StrongMerging.Upper.DecodersCore
import KolmogorovMathlib.StoppingComplexity.CeilLog

/-!
# The total point selector (blueprint H05, `UpperHierarchySelector`)

`sublinear-merging.tex`, section "Residual compression and stopping" (tex ~430–478) and appendix
"A literal total point selector" (tex ~2523); blueprint `bp-upper-hierarchy`, paragraph "Point
selector and score".

* `selectModelAt c₂ R pA pB e z`: the selected model at input `z` for an explicit shrink exponent
  `R`: `{z}` if `|z| ≤ 1` or a witness output does not contain `z`; in the small-degree branch
  `min a b ≤ JL` the model of the larger bucket (ties to `B`); otherwise the parent of the first
  residual along `z`'s path (`firstResidualBlock`), with `L = c₂ H`, `H = e + ⌈log₂ (n + 2)⌉`,
  `J = ⌊n / R⌋ + 1`, `n = |z|` and the buckets `a, b` of the two outputs.
* `selectModel c₂ ρ pA pB e z`: the same with `R = clipR n (ρ n e)` given by a rule.
* `selectModelAt_of_le`, `selectModelAt_of_lt`: the selection at the calibrated instance.
* `selectModelAtT`: the same selection read from two output tables (`tableOut`), the version the
  selector program computes; `selectModelAtT_eq`: on complete runs it is `selectModelAt`.
* `selectorDecoder c₂ ρ`: the literal selector program.  It reads the packet
  `selPacket h e pA pB = numField h (pointPacket e pA pB)`, computes the two output tables at length
  `|z|` by complete runs (`runTable`) and returns the code of `selectModelAtT`.
* `upperHierarchySelector` (H05): for every computable rule `ρ n e h` (`h` an extra packet number:
  `ρ n e h = h` hardwires `R`, a rule ignoring `h` is a fixed rule) there is `c` such that for
  total witnesses of length `≤ e` and every input `z`,
  `CT(selectModel … z | z) ≤ 7 (e + 1) + 4 ⌈log₂ (h + 2)⌉ + c`.  The selector is total on every
  input; its totality uses only witness totality and finite searches, never sufficiency.
-/

namespace Kolmogorov.StrongMerging.Upper

/-- Clip a requested shrink exponent into `[1, n]`: `min n (max 1 r)`. -/
def clipR (n r : ℕ) : ℕ :=
  min n (max 1 r)

/-- **The semantic point selector at shrink exponent `R`** (`Select(z; p_A, p_B, e, parent)`,
tex ~2530).  `n = |z|`, the outputs are `A_z = parseModel (progOut pA z)`,
`B_z = parseModel (progOut pB z)`, `a, b` their floor buckets, `L = c₂ H`, `J = ⌊n / R⌋ + 1`. -/
noncomputable def selectModelAt (c₂ R : ℕ) (pA pB : BitString) (e : ℕ) (z : BitString) :
    Finset BitString :=
  if z.length ≤ 1 ∨ z ∉ parseModel (progOut pA z) ∨ z ∉ parseModel (progOut pB z) then {z}
  else if min (Nat.log 2 (parseModel (progOut pA z)).card)
      (Nat.log 2 (parseModel (progOut pB z)).card) ≤
      (z.length / R + 1) * (c₂ * baseBudget z.length e) then
    (if Nat.log 2 (parseModel (progOut pA z)).card ≤ Nat.log 2 (parseModel (progOut pB z)).card
      then parseModel (progOut pB z) else parseModel (progOut pA z))
  else ((firstResidualBlock (instShape pA pB z.length (Nat.log 2 (parseModel (progOut pA z)).card)
      (Nat.log 2 (parseModel (progOut pB z)).card)) R (c₂ * baseBudget z.length e)
      (z.length / R + 1) z).map Prod.snd).getD {z}

/-- **The semantic point selector with a rule**: `R = clipR n (ρ n e)` at `n = |z|`. -/
noncomputable def selectModel (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ) (pA pB : BitString) (e : ℕ)
    (z : BitString) : Finset BitString :=
  selectModelAt c₂ (clipR z.length (ρ z.length e)) pA pB e z

/-- A hardwired exponent in `[1, n]` is unchanged by clipping. -/
theorem clipR_of_le {n R : ℕ} (h1 : 1 ≤ R) (h2 : R ≤ n) : clipR n R = R := by
  unfold clipR
  omega

/-- Clipping lands in `[1, n]` when `n ≥ 1`. -/
theorem one_le_clipR {n r : ℕ} (hn : 1 ≤ n) : 1 ≤ clipR n r ∧ clipR n r ≤ n := by
  unfold clipR
  omega

/-- **Selection in the small-degree branch** (tex ~322).  At the calibrated instance (the witnesses
output the codes of `A, B ∋ x`, `|x| ≥ 2`), if `min a b ≤ JL` the selector returns the model of the
larger bucket, ties to `B`. -/
theorem selectModelAt_of_le {c₂ R e : ℕ} {pA pB x : BitString} {A B : Finset BitString}
    (hx : 2 ≤ x.length) (hA : progOut pA x = canonicalFiniteSetCode A)
    (hB : progOut pB x = canonicalFiniteSetCode B) (hxA : x ∈ A) (hxB : x ∈ B)
    (hsmall : min (Nat.log 2 A.card) (Nat.log 2 B.card) ≤
      (x.length / R + 1) * (c₂ * baseBudget x.length e)) :
    selectModelAt c₂ R pA pB e x = if Nat.log 2 A.card ≤ Nat.log 2 B.card then B else A := by
  unfold selectModelAt
  rw [hA, hB, parseModel_canonicalFiniteSetCode, parseModel_canonicalFiniteSetCode]
  have hne : ¬ (x.length ≤ 1 ∨ x ∉ A ∨ x ∉ B) := by
    simp only [not_or, not_le, not_not]
    exact ⟨by omega, hxA, hxB⟩
  rw [ite_eq_right hne, ite_eq_left hsmall]

/-- **Selection in the hierarchy branch** (tex ~436).  At the calibrated instance, if
`JL < a, b` and the first residual along `x` is that of the depth-`j` block `F`, the selector
returns `F`. -/
theorem selectModelAt_of_lt {c₂ R e : ℕ} {pA pB x : BitString} {A B : Finset BitString}
    (hx : 2 ≤ x.length) (hA : progOut pA x = canonicalFiniteSetCode A)
    (hB : progOut pB x = canonicalFiniteSetCode B) (hxA : x ∈ A) (hxB : x ∈ B)
    (hbig : (x.length / R + 1) * (c₂ * baseBudget x.length e) <
      min (Nat.log 2 A.card) (Nat.log 2 B.card)) {j : ℕ} {F : Finset BitString}
    (hsel : firstResidualBlock (instShape pA pB x.length (Nat.log 2 A.card) (Nat.log 2 B.card)) R
      (c₂ * baseBudget x.length e) (x.length / R + 1) x = some (j, F)) :
    selectModelAt c₂ R pA pB e x = F := by
  unfold selectModelAt
  rw [hA, hB, parseModel_canonicalFiniteSetCode, parseModel_canonicalFiniteSetCode]
  have hne : ¬ (x.length ≤ 1 ∨ x ∉ A ∨ x ∉ B) := by
    simp only [not_or, not_le, not_not]
    exact ⟨by omega, hxA, hxB⟩
  rw [ite_eq_right hne, ite_eq_right (not_le.mpr hbig), hsel]
  rfl

/-! ### The selection read from output tables -/

/-- **The point selector read from two output tables.**  The same selection as `selectModelAt`,
with the witness outputs at the input `z` and the shape graph read from the tables `TA`, `TB`
(`tableOut`, `tableShape`).  This is the finite total computation inside the selector program
(tex ~2531–2575). -/
noncomputable def selectModelAtT (c₂ R e : ℕ) (TA TB : List (BitString × BitString))
    (z : BitString) : Finset BitString :=
  if z.length ≤ 1 ∨ z ∉ parseModel (tableOut TA z) ∨ z ∉ parseModel (tableOut TB z) then {z}
  else if min (Nat.log 2 (parseModel (tableOut TA z)).card)
      (Nat.log 2 (parseModel (tableOut TB z)).card) ≤
      (z.length / R + 1) * (c₂ * baseBudget z.length e) then
    (if Nat.log 2 (parseModel (tableOut TA z)).card ≤ Nat.log 2 (parseModel (tableOut TB z)).card
      then parseModel (tableOut TB z) else parseModel (tableOut TA z))
  else ((firstResidualBlock (tableShape TA TB z.length (Nat.log 2 (parseModel (tableOut TA z)).card)
      (Nat.log 2 (parseModel (tableOut TB z)).card)) R (c₂ * baseBudget z.length e)
      (z.length / R + 1) z).map Prod.snd).getD {z}

/-- **Tables of complete runs give the semantic selection**, on every input `z` (including
`|z| ≤ 1` and invalid or noncontaining outputs): the outputs at `z` are read back by
`tableOut_of_mem_runTable`, and the residual search agrees by `firstResidualBlock_congr` and
`tableShape_agreeOn`. -/
theorem selectModelAtT_eq {pA pB z : BitString} {TA TB : List (BitString × BitString)}
    (hA : TA ∈ runTable pA z.length) (hB : TB ∈ runTable pB z.length) (c₂ R e : ℕ) :
    selectModelAtT c₂ R e TA TB z = selectModelAt c₂ R pA pB e z := by
  have hoA : tableOut TA z = progOut pA z := tableOut_of_mem_runTable hA rfl
  have hoB : tableOut TB z = progOut pB z := tableOut_of_mem_runTable hB rfl
  unfold selectModelAtT selectModelAt
  rw [hoA, hoB, firstResidualBlock_congr (tableShape_agreeOn hA hB)]

/-! #### Primitive recursive pieces of the table selection -/

/-- The canonical code of a parsed model is primitive recursive in the word. -/
theorem parseModel_code_primrec :
    Primrec fun w : BitString => canonicalFiniteSetCode (parseModel w) :=
  (canonicalFiniteSetCode_toFinset_primrec.comp canonicalPointListOfCode_primrec).of_eq
    fun _ => rfl

/-- The floor bucket `⌊log₂ |parseModel w|⌋` is primitive recursive in the word. -/
theorem parseModel_logCard_primrec :
    Primrec fun w : BitString => Nat.log 2 (parseModel w).card :=
  (primrec_natLogTwo.comp (Primrec.list_length.comp
    (dedup_primrec.comp canonicalPointListOfCode_primrec))).of_eq fun w => by
    rw [parseModel, List.card_toFinset]

/-- Membership in a parsed model is primitive recursive. -/
theorem parseModel_mem_primrec :
    Primrec₂ fun (z w : BitString) => decide (z ∈ parseModel w) :=
  (bitString_mem_primrec.comp Primrec.fst
    (canonicalPointListOfCode_primrec.comp Primrec.snd)).of_eq fun p => by
    simp [parseModel]

/-- The base budget `H = e + ⌈log₂ (n + 2)⌉` is primitive recursive. -/
theorem baseBudget_primrec : Primrec₂ baseBudget :=
  (Primrec.nat_add.comp Primrec.snd
    (primrec_clogTwo.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)))).of_eq
    fun _ => rfl

/-- The code of a singleton model is primitive recursive. -/
theorem singleton_code_primrec :
    Primrec fun z : BitString => canonicalFiniteSetCode ({z} : Finset BitString) :=
  (canonicalFiniteSetCode_toFinset_primrec.comp
    (Primrec.list_cons.comp Primrec.id (Primrec.const []))).of_eq fun z => by simp

/-- Pushing the canonical code through the residual-branch default. -/
theorem code_getD_map_snd (o : Option (ℕ × Finset BitString)) (z : BitString) :
    ((o.map fun p => (p.1, canonicalFiniteSetCode p.2)).map fun p => p.2).getD
        (canonicalFiniteSetCode {z}) = canonicalFiniteSetCode ((o.map Prod.snd).getD {z}) := by
  cases o <;> rfl

/-- **The residual branch is primitive recursive in the tables**: the code of the parent block
selected by `firstResidualBlock` on the table shape (default `{z}`), from B's
`firstResidualBlock_primrec` with `fA T z = tableOut T.1 z`, `fB T z = tableOut T.2 z`. -/
theorem selectResidualCode_primrec :
    Primrec fun q : ((List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) × BitString =>
      canonicalFiniteSetCode (((firstResidualBlock (tableShape q.1.1.1 q.1.1.2 q.1.2.1.1
        q.1.2.1.2.1 q.1.2.1.2.2) q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2).map Prod.snd).getD
          {q.2}) := by
  have hA : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.1 z :=
    tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hB : Primrec₂ fun (T : List (BitString × BitString) × List (BitString × BitString))
      (z : BitString) => tableOut T.2 z :=
    tableOut_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hF := firstResidualBlock_primrec _ _ hA hB
  exact (Primrec.option_getD.comp (Primrec.option_map hF (Primrec.snd.comp Primrec.snd).to₂)
    (singleton_code_primrec.comp Primrec.snd)).of_eq fun q => code_getD_map_snd _ q.2

/-- **The selection is primitive recursive in the tables.**  The canonical code of
`selectModelAtT c₂ R e TA TB z` is a primitive recursive function of `(c₂, R, e)`, the two tables
and `z` (tex ~2531–2575: a finite computation with no unknown end time). -/
theorem selectModelAtT_code_primrec :
    Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) × List (BitString × BitString)) ×
        BitString =>
      canonicalFiniteSetCode (selectModelAtT q.1.1 q.1.2.1 q.1.2.2 q.2.1.1 q.2.1.2 q.2.2) := by
  have hz : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.2.2 := Primrec.snd.comp Primrec.snd
  have hT : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.2.1 := Primrec.fst.comp Primrec.snd
  have hoA := tableOut_primrec.comp (Primrec.fst.comp hT) hz
  have hoB := tableOut_primrec.comp (Primrec.snd.comp hT) hz
  have hn := Primrec.list_length.comp hz
  have ha := parseModel_logCard_primrec.comp hoA
  have hb := parseModel_logCard_primrec.comp hoB
  have hc : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.1 := Primrec.fst.comp Primrec.fst
  have hR : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have he : Primrec fun q : (ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString)) × BitString => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hL := Primrec.nat_mul.comp hc (baseBudget_primrec.comp hn he)
  have hJ := Primrec.succ.comp (Primrec.nat_div.comp hn hR)
  have hmemA := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoA)
  have hmemB := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoB)
  have hguard := (Primrec.nat_le.comp hn (Primrec.const 1)).or (hmemA.not.or hmemB.not)
  have hsmall := Primrec.nat_le.comp (Primrec.nat_min.comp ha hb) (Primrec.nat_mul.comp hJ hL)
  have hab := Primrec.nat_le.comp ha hb
  have hres := selectResidualCode_primrec.comp
    ((hT.pair ((hn.pair (ha.pair hb)).pair (hR.pair (hL.pair hJ)))).pair hz)
  refine (Primrec.ite hguard (singleton_code_primrec.comp hz)
    (Primrec.ite hsmall (Primrec.ite hab (parseModel_code_primrec.comp hoB)
      (parseModel_code_primrec.comp hoA)) hres)).of_eq fun q => ?_
  unfold selectModelAtT
  split_ifs <;> simp_all

/-- `clipR` is primitive recursive. -/
theorem clipR_primrec : Primrec₂ clipR :=
  Primrec.nat_min.comp Primrec.fst (Primrec.nat_max.comp (Primrec.const 1) Primrec.snd)

/-! ### The literal selector program -/

/-- The packet of the point selector: the extra number `h` (the hardwired exponent, or `0` for a
fixed rule) in front of the point packet `(e, p_A, p_B)`. -/
def selPacket (h e : ℕ) (pA pB : BitString) : BitString :=
  numField h (pointPacket e pA pB)

/-- **Selector packet length** (tex ~2394–2410): with witness bodies of length at most `e`, the
packet costs at most `7 (e + 1) + 4 ⌈log₂ (h + 2)⌉` bits. -/
theorem length_selPacket_le (h e : ℕ) (pA pB : BitString) (hA : pA.length ≤ e)
    (hB : pB.length ≤ e) : (selPacket h e pA pB).length ≤ 7 * (e + 1) + 4 * headerLog h := by
  have hpt := length_pointPacket_le e pA pB hA hB
  have hsize : Nat.size h ≤ headerLog h := by
    unfold headerLog
    rw [Nat.size_le]
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_pow_clog one_lt_two (h + 2))
  have hss : (Nat.bits (Nat.bits h).length).length ≤ (Nat.bits h).length := by
    rw [Nat.size_eq_bits_len (Nat.bits h).length]
    exact Nat.size_le.2 Nat.lt_two_pow_self
  have hl1 := one_le_headerLog h
  rw [← Nat.size_eq_bits_len] at hsize
  unfold selPacket numField
  rw [length_totalProgramPairCode]
  omega

/-- The output of the selector program from its decoded packet `(h, e, p_A, p_B)` on the input
`z`: complete runs of both witnesses at length `|z|`, then the table selection with the clipped
exponent `R = clipR |z| (ρ |z| e h)`. -/
noncomputable def selOut (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) (h e : ℕ) (pA pB z : BitString) :
    Part BitString :=
  (runTable pA z.length).bind fun TA => (runTable pB z.length).map fun TB =>
    canonicalFiniteSetCode (selectModelAtT c₂ (clipR z.length (ρ z.length e h)) e TA TB z)

/-- **The literal total point selector** `Select(z; p_A, p_B, e, parent)` (tex ~2531), for the
hierarchy step `c₂` and the rule `ρ`, as a machine reading `selPacket h e pA pB` and the input
`z`. -/
noncomputable def selectorDecoder (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) : Map := fun q =>
  selOut c₂ ρ (numFieldDecode q.1).1 (numFieldDecode (numFieldDecode q.1).2).1
    (decodeTotalProgramPairFirst (numFieldDecode (numFieldDecode q.1).2).2)
    (decodeTotalProgramPairSecond (numFieldDecode (numFieldDecode q.1).2).2) q.2

/-- **The selector program is partial recursive** for a computable rule: computable packet
parsing, the two complete runs (`runTable_partrec`) combined by `Partrec.bind` and `Partrec.map`,
and the primitive recursive table selection `selectModelAtT_code_primrec` at the clipped
exponent given by the computable rule. -/
theorem selectorDecoder_partrec (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ)
    (hρ : Computable fun q : ℕ × ℕ × ℕ => ρ q.1 q.2.1 q.2.2) :
    isDecompressor (selectorDecoder c₂ ρ) := by
  have hrest : Computable fun q : BitString × BitString => (numFieldDecode q.1).2 :=
    Computable.snd.comp (numFieldDecode_computable.comp Computable.fst)
  have hh : Computable fun q : BitString × BitString => (numFieldDecode q.1).1 :=
    Computable.fst.comp (numFieldDecode_computable.comp Computable.fst)
  have he : Computable fun q : BitString × BitString =>
      (numFieldDecode (numFieldDecode q.1).2).1 :=
    Computable.fst.comp (numFieldDecode_computable.comp hrest)
  have hbody : Computable fun q : BitString × BitString =>
      (numFieldDecode (numFieldDecode q.1).2).2 :=
    Computable.snd.comp (numFieldDecode_computable.comp hrest)
  have hpA := decodeTotalProgramPairFirst_computable.comp hbody
  have hpB := decodeTotalProgramPairSecond_computable.comp hbody
  have hlen : Computable fun q : BitString × BitString => q.2.length :=
    (Primrec.list_length.comp Primrec.snd).to_comp
  have hfst : Computable fun r : (BitString × BitString) × List (BitString × BitString) => r.1 :=
    Computable.fst
  have hR : Computable fun q : BitString × BitString =>
      clipR q.2.length (ρ q.2.length (numFieldDecode (numFieldDecode q.1).2).1
        (numFieldDecode q.1).1) :=
    clipR_primrec.to_comp.comp hlen (hρ.comp (hlen.pair (he.pair hh)))
  have hfinal : Computable₂ fun (r : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) =>
      canonicalFiniteSetCode (selectModelAtT c₂ (clipR r.1.2.length (ρ r.1.2.length
        (numFieldDecode (numFieldDecode r.1.1).2).1 (numFieldDecode r.1.1).1))
        (numFieldDecode (numFieldDecode r.1.1).2).1 r.2 TB r.1.2) :=
    (selectModelAtT_code_primrec.to_comp.comp
      (((Computable.const c₂).pair ((hR.comp (Computable.fst.comp Computable.fst)).pair
        (he.comp (Computable.fst.comp Computable.fst)))).pair
        (((Computable.snd.comp Computable.fst).pair Computable.snd).pair
          (Computable.snd.comp (Computable.fst.comp Computable.fst))))).of_eq fun _ => rfl
  have hinner : Partrec₂ fun (r : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairSecond (numFieldDecode (numFieldDecode r.1).2).2)
        r.2.length).map fun TB =>
        canonicalFiniteSetCode (selectModelAtT c₂ (clipR r.2.length (ρ r.2.length
          (numFieldDecode (numFieldDecode r.1).2).1 (numFieldDecode r.1).1))
          (numFieldDecode (numFieldDecode r.1).2).1 TA TB r.2) :=
    Partrec.map (runTable_partrec.comp (hpB.comp hfst) (hlen.comp hfst)) hfinal
  exact (Partrec.bind (runTable_partrec.comp hpA hlen) hinner).of_eq fun q => rfl

/-- **The selector program on its packet** (totality and correctness on every input).  For total
witnesses the program halts on every input `z` and returns the code of the semantic selection
`selectModel c₂ (ρ · · h) pA pB e z`.  Totality uses only witness totality (`runTable_dom`) and
finite searches, never sufficiency. -/
theorem selectorDecoder_spec (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ) (h e : ℕ) (pA pB z : BitString)
    (hpA : IsTotalProgram universalDecompressor pA)
    (hpB : IsTotalProgram universalDecompressor pB) :
    selectorDecoder c₂ ρ (selPacket h e pA pB, z) =
      Part.some (canonicalFiniteSetCode (selectModel c₂ (fun n e => ρ n e h) pA pB e z)) := by
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA z.length)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB z.length)
  have hsel := selectModelAtT_eq hTA hTB c₂ (clipR z.length (ρ z.length e h)) e
  unfold selectorDecoder selOut
  simp only [selPacket, pointPacket, numFieldDecode_numField, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨TA, hTA, ?_⟩
  rw [Part.mem_map_iff]
  refine ⟨TB, hTB, ?_⟩
  rw [hsel]
  rfl

/-- **The total point selector (blueprint H05, `UpperHierarchySelector`).**  Fix the hierarchy
step constant `c₂` and a computable rule `ρ n e h`.  There is a constant `c` such that for all
total witnesses `pA, pB` of length at most `e`, every packet number `h` and every input `z`,
`CT(selectModel c₂ (ρ · · h) pA pB e z | z) ≤ 7 (e + 1) + 4 ⌈log₂ (h + 2)⌉ + c`.  The selector
program carries only `p_A, p_B, e, h`; it derives `n = |z|` and the buckets from its input, and it
halts on every input.  With `ρ n e h = h` this is the hardwired-`R` cost `O(e + log n)`, with a rule
ignoring `h` (and `h = 0`) the cost `O(e + 1)`; the constant is quantified before the witnesses
and `e`.

`sublinear-merging.tex`, tex ~456–466 and appendix tex ~2394–2410, ~2523–2592. -/
theorem upperHierarchySelector (c₂ : ℕ) (ρ : ℕ → ℕ → ℕ → ℕ)
    (hρ : Computable fun q : ℕ × ℕ × ℕ => ρ q.1 q.2.1 q.2.2) :
    ∃ c : ℕ, ∀ (pA pB : BitString) (e h : ℕ) (z : BitString),
      IsTotalProgram universalDecompressor pA → IsTotalProgram universalDecompressor pB →
      pA.length ≤ e → pB.length ≤ e →
      pointTotalC (selectModel c₂ (fun n e => ρ n e h) pA pB e z) z ≤
        7 * (e + 1) + 4 * headerLog h + c := by
  obtain ⟨c, hc⟩ := totalC_le_of_decoder (selectorDecoder c₂ ρ) (selectorDecoder_partrec c₂ ρ hρ)
  refine ⟨c, fun pA pB e h z hpA hpB hA hB => ?_⟩
  have hspec := fun y => selectorDecoder_spec c₂ ρ h e pA pB y hpA hpB
  have htot : ∀ y, (selectorDecoder c₂ ρ (selPacket h e pA pB, y)).Dom := by
    intro y
    rw [hspec y]
    trivial
  have hmem : canonicalFiniteSetCode (selectModel c₂ (fun n e => ρ n e h) pA pB e z) ∈
      selectorDecoder c₂ ρ (selPacket h e pA pB, z) := by
    rw [hspec z]
    exact Part.mem_some _
  have h1 := hc _ htot _ _ hmem
  have h2 := length_selPacket_le h e pA pB hA hB
  generalize (selPacket h e pA pB).length = m at h1 h2
  have h2' : (m : ℝ) ≤ 7 * ((e : ℝ) + 1) + 4 * (headerLog h : ℝ) := by
    exact_mod_cast h2
  change totalC _ z ≤ _
  linarith

end Kolmogorov.StrongMerging.Upper
