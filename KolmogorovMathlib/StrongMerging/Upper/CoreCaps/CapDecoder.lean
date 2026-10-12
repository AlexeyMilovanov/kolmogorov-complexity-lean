import KolmogorovMathlib.StrongMerging.Upper.CoreDecoders
import KolmogorovMathlib.StrongMerging.Upper.Profiles

/-!
# The cap decoder of the core caps

The enumeration of short descriptions in a residual, the acquisition rules and the cap
decoder that the caps M04-M08 are read from.

Part of `KolmogorovMathlib.StrongMerging.Upper.CoreCaps`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Upper

open Nat.Partrec (Code)

/-! ### The enumeration of short descriptions in a residual -/

/-- **The dovetailed enumeration** of the residual edges with descriptions of length `≤ K` given
`P`: step `i = ⟪t, k⟫` runs the `k`-th program of length `≤ K` for `t` stages of the code `cV` on
the condition `P` and emits its output if it lies in `U`. -/
def coreEnum (cV : Code) (U : Finset BitString) (P : BitString) (K : ℕ) (i : ℕ) :
    Option BitString :=
  ((boundedPrograms K)[(Nat.unpair i).2]?).bind fun p =>
    (conditionalRunOut cV (Nat.unpair i).1 p P).filter fun z => decide (z ∈ U)

/-- **Soundness of the enumeration**: every arrival lies in `U` and has `C(z | P) ≤ K`. -/
theorem mem_arrivals_coreEnum {V : Map} {cV : Code} (hcV : IsCodeFor cV V)
    {U : Finset BitString} {P : BitString} {K s : ℕ} {z : BitString}
    (hz : z ∈ arrivals (coreEnum cV U P K) s) : z ∈ U ∧ condC V z P ≤ K := by
  obtain ⟨i, -, hi⟩ := (mem_arrivals_iff _ s z).mp hz
  unfold coreEnum at hi
  rw [Option.bind_eq_some_iff] at hi
  obtain ⟨p, hp, hz'⟩ := hi
  cases hrun : conditionalRunOut cV (Nat.unpair i).1 p P with
  | none =>
    rw [hrun] at hz'
    simp at hz'
  | some y =>
    rw [hrun] at hz'
    simp only [Option.filter_some, decide_eq_true_eq] at hz'
    split_ifs at hz' with hy
    obtain rfl : y = z := Option.some_inj.mp hz'
    refine ⟨hy, ?_⟩
    have hpK : p.length ≤ K := (mem_boundedPrograms_iff p K).mp (List.mem_of_getElem? hp)
    have hprod := conditionalRunOut_sound hcV hrun
    have h1 : condK V y P ≤ (p.length : ℕ∞) :=
      (condK_le_iff V y P p.length).2 ⟨p, le_rfl, hprod⟩
    have h2 : (condK V y P).toNat ≤ K := (toNat_le_of_le_natCast h1).trans hpK
    unfold condC
    exact_mod_cast h2

/-- **Completeness of the enumeration**: an edge of `U` printed from `P` by a program of length
`≤ K` eventually arrives. -/
theorem exists_mem_arrivals_coreEnum {V : Map} {cV : Code} (hcV : IsCodeFor cV V)
    {U : Finset BitString} {P : BitString} {K : ℕ} {z p : BitString} (hz : z ∈ U)
    (hp : p.length ≤ K) (hprod : produces V p P z) :
    ∃ s, z ∈ arrivals (coreEnum cV U P K) s := by
  obtain ⟨t, ht⟩ := conditionalRunOut_complete hcV hprod
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp ((mem_boundedPrograms_iff p K).mpr hp)
  refine ⟨Nat.pair t k + 1, (mem_arrivals_iff _ _ _).mpr ⟨Nat.pair t k, Nat.lt_succ_self _, ?_⟩⟩
  simp [coreEnum, Nat.unpair_pair, hk, ht, hz]

/-! ### The acquisition rules and the cap decoder -/

/-- **How the cap decoder obtains the condition object `P` from an endpoint `y`** (on the side
`side`): mode `0` returns the constant `[]` (the unconditional enumeration); mode `1` runs the
ordinary program `aux` on `y` under `V` (a common factor, possibly partial); otherwise it returns
the core of local rank `decodeBits aux` at the budget `s₀` among the cores incident to the typed
endpoint (default `∅`; the adjacent cap). -/
noncomputable def acquire (V : Map) (P : ShapeParams) (mode s₀ : ℕ) (side : Bool)
    (aux y : BitString) : Part BitString :=
  if mode = 0 then Part.some []
  else if mode = 1 then V (aux, y)
  else Part.some (canonicalFiniteSetCode ((incidentCores P (vertexCores P s₀ (coreEnd side y))
    (coreEnd side y)).getD (decodeBits aux) ∅))

/-- **The cap kernel.**  Fields `[n, a, b, side, s, K, mode, s₀]`; the tail is the pair
`(aux, bits r)`.  Acquire `P`, enumerate the edges of the capped residual (budget `s`, cap
`2^(K+1)`) of the endpoint's component with `C(z | P) ≤ K`, and decode the edge of rank `r` owned
by the typed endpoint in the online orientation with the budget-`s` capacities.  Partial. -/
noncomputable def capKer (V : Map) (cV : Code) (q : CoreIn) : Part BitString :=
  (acquire V (inShape q) (q.2.1.getD 6 0) (q.2.1.getD 7 0) (inSide q)
      (decodeTotalProgramPairFirst q.2.2.1) q.2.2.2).bind fun Pobj =>
    decodeOwned (shapeSrc (inShape q)) (shapeTgt (inShape q)) (coreCap (inShape q) (inBudget q))
      (coreEnum cV (vertexResidual (inShape q) (inBudget q) (2 ^ (q.2.1.getD 5 0 + 1)) (inEnd q))
        Pobj (q.2.1.getD 5 0))
      (inEnd q) (decodeBits (decodeTotalProgramPairSecond q.2.2.1))

/-- The decoding step of the cap kernel once the object `P` has been acquired. -/
noncomputable def capDecode (cV : Code) (q : CoreIn) (Pobj : BitString) : Part BitString :=
  decodeOwned (shapeSrc (inShape q)) (shapeTgt (inShape q)) (coreCap (inShape q) (inBudget q))
    (coreEnum cV (vertexResidual (inShape q) (inBudget q) (2 ^ (q.2.1.getD 5 0 + 1)) (inEnd q))
      Pobj (q.2.1.getD 5 0))
    (inEnd q) (decodeBits (decodeTotalProgramPairSecond q.2.2.1))

/-- The cap kernel is acquisition followed by the decoding step. -/
theorem capKer_eq (V : Map) (cV : Code) (q : CoreIn) :
    capKer V cV q = (acquire V (inShape q) (q.2.1.getD 6 0) (q.2.1.getD 7 0) (inSide q)
      (decodeTotalProgramPairFirst q.2.2.1) q.2.2.2).bind (capDecode cV q) :=
  rfl

/-- **Acquisition is partial recursive.**

Proof sketch: split on the mode field (`Partrec` of an `if` on a computable Boolean, e.g. via
`Partrec.cond`/`Computable.cond` after rewriting the nested `if` as `bif`): mode `0` is the constant
`Part.some []`; mode `1` is `hV.1 : Partrec V` composed with the computable pair
`(decodeTotalProgramPairFirst q.2.2.1, q.2.2.2)`; otherwise the value is total and computable from
`vertexCores_codes_primrec` (at `(tables, (n, a, b), s₀, inEnd q)`), a `List.filter` of codes by
incidence to the typed endpoint, `List.getD` and `decodeBits_computable`, as in
`localCoreKer_partrec`. -/
theorem acquire_partrec {V : Map} (hV : isOptimalConditional V) :
    Partrec fun q : CoreIn => acquire V (inShape q) (q.2.1.getD 6 0) (q.2.1.getD 7 0) (inSide q)
      (decodeTotalProgramPairFirst q.2.2.1) q.2.2.2 := by
  -- the mode-2 value: the core of a local rank at the earlier budget `s₀`
  have hq : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.1 := Primrec.fst
  have hv : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hs : Primrec fun r : CoreIn × (BitString ⊕ BitString) × ℕ => r.1.2.1.getD 7 0 :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 7)
  have hpar := Primrec.pair (Primrec.fst.comp hq)
    (Primrec.pair (inNAB_primrec.comp hq) (Primrec.pair hs hv))
  have hcodes := vertexCores_codes_primrec.comp hpar
  have hA : Primrec fun x : ((CoreIn × (BitString ⊕ BitString) × ℕ) × BitString) × BitString =>
      decide ((Sum.inl (tableOut x.1.1.1.1.1 x.2) : BitString ⊕ BitString) = x.1.1.2.1) :=
    Primrec.eq.decide.comp (Primrec.sumInl.comp (tableOut_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hB : Primrec fun x : ((CoreIn × (BitString ⊕ BitString) × ℕ) × BitString) × BitString =>
      decide ((Sum.inr (tableOut x.1.1.1.1.2 x.2) : BitString ⊕ BitString) = x.1.1.2.1) :=
    Primrec.eq.decide.comp (Primrec.sumInr.comp (tableOut_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hor := Primrec.or.comp hA hB
  have htest : Primrec₂ fun (r : CoreIn × (BitString ⊕ BitString) × ℕ) (w : BitString) =>
      (canonicalPointListOfCode w).any fun z =>
        decide ((Sum.inl (tableOut r.1.1.1 z) : BitString ⊕ BitString) = r.2.1) ||
          decide ((Sum.inr (tableOut r.1.1.2 z) : BitString ⊕ BitString) = r.2.1) :=
    list_any_primrec (canonicalPointListOfCode_primrec.comp Primrec.snd) hor
  have hfil := primrec_list_filter hcodes htest
  have hget := (Primrec.list_getD (canonicalFiniteSetCode (∅ : Finset BitString))).comp hfil hi
  have harg : Computable fun q : CoreIn =>
      (q, inEnd q, decodeBits (decodeTotalProgramPairFirst q.2.2.1)) :=
    Computable.pair Computable.id (Computable.pair inEnd_computable
      (decodeBits_computable.comp (decodeTotalProgramPairFirst_computable.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))))
  have h2 : Computable fun q : CoreIn => canonicalFiniteSetCode ((incidentCores (inShape q)
      (vertexCores (inShape q) (q.2.1.getD 7 0) (inEnd q)) (inEnd q)).getD
        (decodeBits (decodeTotalProgramPairFirst q.2.2.1)) ∅) := by
    refine (hget.to_comp.comp harg).of_eq fun q => ?_
    have hpred : ∀ T : Finset BitString, ((canonicalFinsetList T).any fun z =>
        decide ((Sum.inl (tableOut q.1.1 z) : BitString ⊕ BitString) = inEnd q) ||
          decide ((Sum.inr (tableOut q.1.2 z) : BitString ⊕ BitString) = inEnd q)) =
        decide (∃ z ∈ T, shapeSrc (inShape q) z = inEnd q ∨ shapeTgt (inShape q) z = inEnd q) := by
      intro T
      rw [Bool.eq_iff_iff]
      simp [List.any_eq_true, mem_canonicalFinsetList, shapeSrc, shapeTgt, inShape, tableShape]
    simp only [incidentCores, List.filter_map, List.getD_map, Function.comp_def,
      canonicalPointListOfCode_canonicalFiniteSetCode, hpred]
    rfl
  -- the mode-1 value: the ordinary program run by `V`
  have h1 : Partrec fun q : CoreIn => V (decodeTotalProgramPairFirst q.2.2.1, q.2.2.2) :=
    hV.1.comp (Computable.pair (decodeTotalProgramPairFirst_computable.comp
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
      (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hm : Computable fun q : CoreIn => q.2.1.getD 6 0 :=
    (Primrec.list_getD 0).to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 6)
  have hc0 : Computable fun q : CoreIn => decide (q.2.1.getD 6 0 = 0) :=
    Primrec.eq.decide.to_comp.comp hm (Computable.const 0)
  have hc1 : Computable fun q : CoreIn => decide (q.2.1.getD 6 0 = 1) :=
    Primrec.eq.decide.to_comp.comp hm (Computable.const 1)
  have hall := Partrec.cond hc0 (Computable.const ([] : BitString)).partrec
    (Partrec.cond hc1 h1 h2.partrec)
  refine hall.of_eq fun q => ?_
  unfold acquire
  by_cases h0 : q.2.1.getD 6 0 = 0
  · rw [decide_eq_true h0, Bool.cond_true, ite_eq_left h0]
    rfl
  · by_cases h1' : q.2.1.getD 6 0 = 1
    · rw [decide_eq_false h0, Bool.cond_false, decide_eq_true h1', Bool.cond_true, ite_eq_right h0,
        ite_eq_left h1']
    · rw [decide_eq_false h0, Bool.cond_false, decide_eq_false h1', Bool.cond_false,
        ite_eq_right h0, ite_eq_right h1']
      rfl

/-- The row endpoint map of the table shape is computable in the parameters. -/
theorem capSrc_computable :
    Computable₂ fun (p : CoreIn × BitString) (z : BitString) => shapeSrc (inShape p.1) z := by
  have h : Computable fun r : (CoreIn × BitString) × BitString => tableOut r.1.1.1.1 r.2 :=
    tableOut_primrec.to_comp.comp
      (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      Computable.snd
  exact (Computable.sumInl.comp h).of_eq fun r => rfl

/-- The column endpoint map of the table shape is computable in the parameters. -/
theorem capTgt_computable :
    Computable₂ fun (p : CoreIn × BitString) (z : BitString) => shapeTgt (inShape p.1) z := by
  have h : Computable fun r : (CoreIn × BitString) × BitString => tableOut r.1.1.1.2 r.2 :=
    tableOut_primrec.to_comp.comp
      (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      Computable.snd
  exact (Computable.sumInr.comp h).of_eq fun r => rfl

/-- **The budget-`s` capacities are computable in the parameters.**

Proof sketch: `coreCap P s v` is `Sum.elim` of the constants `2^(a - s)`, `2^(b - s)`
(`Computable.sumCasesOn` with `shapePR_pow_primrec`, `Primrec.nat_sub` and `Primrec.list_getD`
on the fields); conclude with `of_eq` after `cases v`. -/
theorem capCap_computable :
    Computable₂ fun (p : CoreIn × BitString) (v : BitString ⊕ BitString) =>
      coreCap (inShape p.1) (inBudget p.1) v := by
  have hl : Primrec fun r : (CoreIn × BitString) × (BitString ⊕ BitString) => r.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hs : Primrec fun r : (CoreIn × BitString) × (BitString ⊕ BitString) =>
      r.1.1.2.1.getD 4 0 :=
    (Primrec.list_getD 0).comp hl (Primrec.const 4)
  have ha : Primrec fun r : (CoreIn × BitString) × (BitString ⊕ BitString) =>
      2 ^ (r.1.1.2.1.getD 1 0 - r.1.1.2.1.getD 4 0) :=
    shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp ((Primrec.list_getD 0).comp hl (Primrec.const 1)) hs)
  have hb : Primrec fun r : (CoreIn × BitString) × (BitString ⊕ BitString) =>
      2 ^ (r.1.1.2.1.getD 2 0 - r.1.1.2.1.getD 4 0) :=
    shapePR_pow_primrec.comp (Primrec.const 2)
      (Primrec.nat_sub.comp ((Primrec.list_getD 0).comp hl (Primrec.const 2)) hs)
  have h := Computable.sumCasesOn
    (f := fun r : (CoreIn × BitString) × (BitString ⊕ BitString) => r.2)
    Computable.snd (ha.to_comp.comp Computable.fst).to₂ (hb.to_comp.comp Computable.fst).to₂
  refine h.of_eq fun r => ?_
  rcases r with ⟨p, v⟩
  cases v <;> rfl

/-- A filter of a computable option by a computable test is computable. -/
theorem mc_computable_option_filter {α : Type} [Primcodable α] {o : α → Option BitString}
    {t : α → BitString → Bool} (ho : Computable o) (ht : Computable₂ t) :
    Computable fun a => (o a).filter (t a) := by
  refine (Computable.option_bind ho (Computable.cond ht (Computable.option_some.comp Computable.snd)
    (Computable.const none)).to₂).of_eq fun a => ?_
  rcases o a with _ | z
  · rfl
  · simp [Option.filter]

/-- **The residual enumeration is computable in the parameters.**

Proof sketch: the residual code is primitive recursive (`vertexCappedCodes_primrec`, second
component, at `(tables, (n, a, b), (s, 2^(K+1)), inEnd q)` with `inNAB_primrec`,
`inEnd_computable`, `shapePR_pow_primrec`), and `z ∈ U ↔ z ∈ canonicalPointListOfCode (code U)`
(`canonicalPointListOfCode_canonicalFiniteSetCode`, `mem_canonicalFinsetList`); `coreEnum` is then
`Primrec.option_bind` of `Primrec.list_getElem?` on `boundedPrograms` (primitive recursive in `K`)
with `conditionalRunOut_computable cV` and an `Option.filter` by `bitString_mem_primrec`
(E's `computable_option_filter` pattern). -/
theorem capEnum_computable (cV : Code) :
    Computable₂ fun (p : CoreIn × BitString) (i : ℕ) =>
      coreEnum cV (vertexResidual (inShape p.1) (inBudget p.1) (2 ^ (p.1.2.1.getD 5 0 + 1))
        (inEnd p.1)) p.2 (p.1.2.1.getD 5 0) i := by
  have hl : Computable fun p : CoreIn × BitString => p.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hK : Computable fun p : CoreIn × BitString => p.1.2.1.getD 5 0 :=
    (Primrec.list_getD 0).to_comp.comp hl (Computable.const 5)
  have hs : Computable fun p : CoreIn × BitString => p.1.2.1.getD 4 0 :=
    (Primrec.list_getD 0).to_comp.comp hl (Computable.const 4)
  have hM : Computable fun p : CoreIn × BitString => 2 ^ (p.1.2.1.getD 5 0 + 1) :=
    shapePR_pow_primrec.to_comp.comp (Computable.const 2)
      (Primrec.nat_add.to_comp.comp hK (Computable.const 1))
  have hpar : Computable fun p : CoreIn × BitString =>
      ((p.1.1, (p.1.2.1.getD 0 0, p.1.2.1.getD 1 0, p.1.2.1.getD 2 0),
        (p.1.2.1.getD 4 0, 2 ^ (p.1.2.1.getD 5 0 + 1)), inEnd p.1) : FamParams) :=
    (Computable.fst.comp Computable.fst).pair ((inNAB_primrec.to_comp.comp Computable.fst).pair
      ((hs.pair hM).pair (inEnd_computable.comp Computable.fst)))
  have hRcode : Computable fun p : CoreIn × BitString => canonicalFiniteSetCode
      (vertexResidual (inShape p.1) (inBudget p.1) (2 ^ (p.1.2.1.getD 5 0 + 1)) (inEnd p.1)) :=
    (Computable.snd.comp (vertexCappedCodes_primrec.to_comp.comp hpar)).of_eq fun p => rfl
  have hmem : Computable₂ fun (p : CoreIn × BitString) (z : BitString) => decide (z ∈
      vertexResidual (inShape p.1) (inBudget p.1) (2 ^ (p.1.2.1.getD 5 0 + 1)) (inEnd p.1)) :=
    (bitString_mem_primrec.to_comp.comp Computable.snd
      (canonicalPointListOfCode_primrec.to_comp.comp (hRcode.comp Computable.fst))).of_eq
        fun x => by simp [canonicalPointListOfCode_canonicalFiniteSetCode]
  have hf : Computable fun x : (CoreIn × BitString) × ℕ =>
      (boundedPrograms (x.1.1.2.1.getD 5 0))[(Nat.unpair x.2).2]? :=
    Primrec.list_getElem?.to_comp.comp (primrec_boundedPrograms.to_comp.comp
      (hK.comp Computable.fst)) (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hrun := Lower.conditionalRunOut_computable cV
  have htup : Computable fun x : ((CoreIn × BitString) × ℕ) × BitString =>
      ((Nat.unpair x.1.2).1, x.2, x.1.1.2) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))).to_comp.pair
      (Computable.snd.pair (Computable.snd.comp (Computable.fst.comp Computable.fst)))
  have ho : Computable fun x : ((CoreIn × BitString) × ℕ) × BitString =>
      conditionalRunOut cV (Nat.unpair x.1.2).1 x.2 x.1.1.2 :=
    Computable.comp (f := fun q : ℕ × BitString × BitString => conditionalRunOut cV q.1 q.2.1 q.2.2)
      (g := fun x : ((CoreIn × BitString) × ℕ) × BitString => ((Nat.unpair x.1.2).1, x.2, x.1.1.2))
      hrun htup
  have ht : Computable₂ fun (x : ((CoreIn × BitString) × ℕ) × BitString) (z : BitString) =>
      decide (z ∈ vertexResidual (inShape x.1.1.1) (inBudget x.1.1.1)
        (2 ^ (x.1.1.1.2.1.getD 5 0 + 1)) (inEnd x.1.1.1)) :=
    hmem.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hg : Computable₂ fun (x : (CoreIn × BitString) × ℕ) (prog : BitString) =>
      (conditionalRunOut cV (Nat.unpair x.2).1 prog x.1.2).filter fun z =>
        decide (z ∈ vertexResidual (inShape x.1.1) (inBudget x.1.1) (2 ^ (x.1.1.2.1.getD 5 0 + 1))
          (inEnd x.1.1)) :=
    mc_computable_option_filter (o := fun x : ((CoreIn × BitString) × ℕ) × BitString =>
      conditionalRunOut cV (Nat.unpair x.1.2).1 x.2 x.1.1.2)
      (t := fun (x : ((CoreIn × BitString) × ℕ) × BitString) (z : BitString) =>
        decide (z ∈ vertexResidual (inShape x.1.1.1) (inBudget x.1.1.1)
          (2 ^ (x.1.1.1.2.1.getD 5 0 + 1)) (inEnd x.1.1.1))) ho ht
  exact (Computable.option_bind hf hg).of_eq fun x => rfl

/-- **The decoder's query is computable**: the parameters, the typed endpoint and the rank read
from the tail.

Proof sketch: `Computable.pair` of `Computable.id`, `inEnd_computable.comp Computable.fst` and
`decodeBits_computable.comp (decodeTotalProgramPairSecond_computable.comp …)` with the projection
`r.1.2.2.1`. -/
theorem capTup_computable :
    Computable fun r : CoreIn × BitString =>
      (r, inEnd r.1, decodeBits (decodeTotalProgramPairSecond r.1.2.2.1)) := by
  have htail : Computable fun r : CoreIn × BitString => r.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  exact Computable.pair Computable.id (Computable.pair (inEnd_computable.comp Computable.fst)
    (decodeBits_computable.comp (decodeTotalProgramPairSecond_computable.comp htail)))

/-- **The decoding step is partial recursive** (`decodeOwned_partrec` of B2, proved). -/
theorem capDecode_partrec (cV : Code) : Partrec₂ (capDecode cV) := by
  have hdo := decodeOwned_partrec
    (fun (p : CoreIn × BitString) (z : BitString) => shapeSrc (inShape p.1) z)
    (fun (p : CoreIn × BitString) (z : BitString) => shapeTgt (inShape p.1) z)
    (fun (p : CoreIn × BitString) (v : BitString ⊕ BitString) =>
      coreCap (inShape p.1) (inBudget p.1) v)
    (fun (p : CoreIn × BitString) (i : ℕ) =>
      coreEnum cV (vertexResidual (inShape p.1) (inBudget p.1) (2 ^ (p.1.2.1.getD 5 0 + 1))
        (inEnd p.1)) p.2 (p.1.2.1.getD 5 0) i)
    capSrc_computable capTgt_computable capCap_computable (capEnum_computable cV)
  exact (hdo.comp capTup_computable).of_eq fun r => rfl

/-- **The cap kernel is partial recursive**: acquisition (`acquire_partrec`) bound to the decoding
step (`capDecode_partrec`). -/
theorem capKer_partrec {V : Map} (hV : isOptimalConditional V) {cV : Code}
    (_hcV : IsCodeFor cV V) : Partrec (capKer V cV) :=
  (Partrec.bind (acquire_partrec hV) (capDecode_partrec cV)).of_eq fun q => (capKer_eq V cV q).symm

/-- **Congruence of the owner-rank decoder.**  `decodeOwned` only evaluates the endpoint maps on
enumerated edges.

Proof sketch: every element of `arrivals en s` is a value of `en` (`mem_arrivals_iff`); the run
`orient` over a list only evaluates `src`, `tgt` on its elements (induction on the list,
`orientStep`, `chooseOwner`), so `ownedHit` agrees at every stage, and so do `Nat.rfind` and the
final `Part.bind`. -/
theorem decodeOwned_congr {α V' : Type*} [DecidableEq α] [DecidableEq V']
    {src tgt src' tgt' : α → V'} (d : V' → ℕ) (en : ℕ → Option α)
    (h : ∀ i z, en i = some z → src z = src' z ∧ tgt z = tgt' z) (v : V') (r : ℕ) :
    decodeOwned src tgt d en v r = decodeOwned src' tgt' d en v r := by
  have hQ : ∀ s, ∀ z ∈ arrivals en s, src z = src' z ∧ tgt z = tgt' z := by
    intro s z hz
    obtain ⟨i, -, hi⟩ := (mem_arrivals_iff en s z).mp hz
    exact h i z hi
  have hfold : ∀ (L t : List α), (∀ z ∈ L, src z = src' z ∧ tgt z = tgt' z) →
      (∀ z ∈ t, z ∈ L) → ∀ (st st' : OrientState α V'), st.load = st'.load →
        st.rank = st'.rank → (∀ z ∈ L, st.owner z = st'.owner z) →
          (t.foldl (orientStep src tgt d) st).load = (t.foldl (orientStep src' tgt' d) st').load ∧
          (t.foldl (orientStep src tgt d) st).rank = (t.foldl (orientStep src' tgt' d) st').rank ∧
          ∀ z ∈ L, (t.foldl (orientStep src tgt d) st).owner z =
            (t.foldl (orientStep src' tgt' d) st').owner z := by
    intro L t hL ht
    induction t with
    | nil => intro st st' h1 h2 h3; exact ⟨h1, h2, h3⟩
    | cons e t ih =>
      intro st st' h1 h2 h3
      have heL : e ∈ L := ht e List.mem_cons_self
      have hc : chooseOwner src tgt d st.load e = chooseOwner src' tgt' d st'.load e := by
        unfold chooseOwner
        rw [h1, (hL e heL).1, (hL e heL).2]
      simp only [List.foldl_cons]
      apply ih (fun z hz => ht z (List.mem_cons_of_mem _ hz))
      · change Function.update st.load (chooseOwner src tgt d st.load e)
            (st.load (chooseOwner src tgt d st.load e) + 1) =
          Function.update st'.load (chooseOwner src' tgt' d st'.load e)
            (st'.load (chooseOwner src' tgt' d st'.load e) + 1)
        rw [hc, h1]
      · change Function.update st.rank e (st.load (chooseOwner src tgt d st.load e)) =
          Function.update st'.rank e (st'.load (chooseOwner src' tgt' d st'.load e))
        rw [hc, h1, h2]
      · intro z hz
        change Function.update st.owner e (chooseOwner src tgt d st.load e) z =
          Function.update st'.owner e (chooseOwner src' tgt' d st'.load e) z
        rw [hc]
        by_cases hze : z = e
        · subst hze
          simp
        · rw [Function.update_of_ne hze, Function.update_of_ne hze]
          exact h3 z hz
  have horient : ∀ s, ∀ e ∈ arrivals en s,
      (orient src tgt d (arrivals en s)).owner e =
          (orient src' tgt' d (arrivals en s)).owner e ∧
        (orient src tgt d (arrivals en s)).rank e =
          (orient src' tgt' d (arrivals en s)).rank e := by
    intro s e he
    have := hfold (arrivals en s) (arrivals en s) (hQ s) (fun z hz => hz) (orientInit src)
      (orientInit src') rfl rfl (fun z hz => (hQ s z hz).1)
    exact ⟨this.2.2 e he, congrFun this.2.1 e⟩
  have hhit : ∀ s, ownedHit src tgt d en v r s = ownedHit src' tgt' d en v r s := by
    intro s
    unfold ownedHit
    apply find?_congr_of_mem
    intro e he
    rw [(horient s e he).1, (horient s e he).2]
  unfold decodeOwned
  simp only [hhit]

/-- The full residual of the component of either endpoint of `x` is the same. -/
theorem vertexResidual_tgt_eq_src {P : ShapeParams} (s M : ℕ) {x : BitString}
    (hx : x ∈ shapeEdges P) :
    vertexResidual P s M (shapeTgt P x) = vertexResidual P s M (shapeSrc P x) := by
  unfold vertexResidual
  rw [shapeComponent_src_eq_tgt hx]

/-- **Incidence of family members only reads outputs at the data length.** -/
theorem incidentCores_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (s : ℕ)
    (v : BitString ⊕ BitString) :
    incidentCores P (vertexCores Q s v) v = incidentCores Q (vertexCores Q s v) v := by
  unfold incidentCores
  apply List.filter_congr
  intro T hT
  have hlen : ∀ z ∈ T, z.length = Q.n := by
    intro z hz
    have hsub := (coreRunAux_mem _ s _ _ _ T hT).2.1
    exact (mem_stringsOfLength _ _).mp
      (Finset.mem_filter.mp (shapeComponent_subset _ _ _ (hsub hz))).1
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨z, hz, hzv⟩
    refine ⟨z, hz, ?_⟩
    obtain ⟨h1, h2⟩ := h.2.2.2 z ((hlen z hz).trans h.1.symm)
    simpa only [shapeSrc, shapeTgt, h1, h2] using hzv
  · rintro ⟨z, hz, hzv⟩
    refine ⟨z, hz, ?_⟩
    obtain ⟨h1, h2⟩ := h.2.2.2 z ((hlen z hz).trans h.1.symm)
    simpa only [shapeSrc, shapeTgt, h1, h2] using hzv

/-- **Acquisition only reads outputs at the data length.** -/
theorem acquire_congr {P Q : ShapeParams} (h : P.AgreeOn Q) (V : Map) (mode s₀ : ℕ)
    (side : Bool) (aux y : BitString) :
    acquire V P mode s₀ side aux y = acquire V Q mode s₀ side aux y := by
  unfold acquire
  split_ifs
  · rfl
  · rfl
  · rw [(vertexCores_congr h s₀ 0 _).2.1, incidentCores_congr h s₀]

/-- The values of the residual enumeration lie in the residual. -/
theorem coreEnum_mem {cV : Code} {U : Finset BitString} {P : BitString} {K i : ℕ} {z : BitString}
    (hi : coreEnum cV U P K i = some z) : z ∈ U := by
  unfold coreEnum at hi
  rw [Option.bind_eq_some_iff] at hi
  obtain ⟨p, -, hz'⟩ := hi
  cases hrun : conditionalRunOut cV (Nat.unpair i).1 p P with
  | none =>
    rw [hrun] at hz'
    simp at hz'
  | some y =>
    rw [hrun] at hz'
    simp only [Option.filter_some, decide_eq_true_eq] at hz'
    split_ifs at hz' with hy
    obtain rfl : y = z := Option.some_inj.mp hz'
    exact hy

/-- **Specification of the cap decoder on its packet.**  At a qualifying instance, if `P` is
acquired from the endpoint `y` of the side `side`, `U` is the capped residual at that endpoint and
`x` has arrived in the enumeration of `U` at stage `t` with owner the typed endpoint, then the
machine returns `x` from the packet with fields `[n, a, b, side, s, K, mode, s₀]` and tail
`(aux, bits r)`, `r` the rank of `x` in the orientation of the arrivals.

Proof sketch: `coreMachine_eval` with complete-run tables `TA, TB`; the table shape agrees with the
instance (`tableShape_agreeOn`), so the acquired object (`vertexCores_congr`, the endpoint test of
`incidentCores` reads outputs of strings of length `n` only), the residual (`vertexCores_congr`)
and the capacities (same `a, b`) agree; the endpoint maps agree on every enumerated edge (edges of
`U` have length `n`), so `decodeOwned_congr` replaces the table shape by the instance shape; then
`Part.mem_bind_iff` with the acquisition and `upperOrientationStream` at stage `t`. -/
theorem capMachine_spec {V : Map} {cV : Code} {n e : ℕ} {pA pB x : BitString}
    {A B : Finset BitString} (h : IsCoreInstance V n e pA pB x A B) (s K mode s₀ : ℕ)
    (side : Bool) (aux Pobj y : BitString) (U : Finset BitString)
    (hU : vertexResidual (coreShape pA pB n A B) s (2 ^ (K + 1)) (coreEnd side y) = U)
    (hacq : Pobj ∈ acquire V (coreShape pA pB n A B) mode s₀ side aux y) (t : ℕ)
    (hxt : x ∈ arrivals (coreEnum cV U Pobj K) t)
    (howner : (orient (shapeSrc (coreShape pA pB n A B)) (shapeTgt (coreShape pA pB n A B))
      (coreCap (coreShape pA pB n A B) s) (arrivals (coreEnum cV U Pobj K) t)).owner x =
        coreEnd side y) :
    x ∈ coreMachine 8 (capKer V cV)
      (corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s, K, mode, s₀] pA pB
        (totalProgramPairCode aux (Nat.bits ((orient (shapeSrc (coreShape pA pB n A B))
          (shapeTgt (coreShape pA pB n A B)) (coreCap (coreShape pA pB n A B) s)
            (arrivals (coreEnum cV U Pobj K) t)).rank x))), y) := by
  obtain ⟨TA, TB, hTA, hTB, heval⟩ := coreMachine_eval 8 (capKer V cV)
    (ks := [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s, K, mode, s₀]) rfl h.totalA
    h.totalB (totalProgramPairCode aux (Nat.bits ((orient (shapeSrc (coreShape pA pB n A B))
      (shapeTgt (coreShape pA pB n A B)) (coreCap (coreShape pA pB n A B) s)
        (arrivals (coreEnum cV U Pobj K) t)).rank x)))
  have hag : (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)).AgreeOn
      (coreShape pA pB n A B) := tableShape_agreeOn (n := n) hTA hTB
  rw [heval y, capKer_eq, Part.mem_bind_iff]
  have hside : inSide ((TA, TB), [n, Nat.log 2 A.card, Nat.log 2 B.card, side.toNat, s, K, mode,
      s₀], totalProgramPairCode aux (Nat.bits ((orient (shapeSrc (coreShape pA pB n A B))
        (shapeTgt (coreShape pA pB n A B)) (coreCap (coreShape pA pB n A B) s)
          (arrivals (coreEnum cV U Pobj K) t)).rank x)), y) = side := by
    cases side <;> rfl
  refine ⟨Pobj, ?_, ?_⟩
  · simp only [inShape, hside, List.getD_cons_succ, List.getD_cons_zero,
      decodeTotalProgramPairFirst_pair]
    rw [acquire_congr hag]
    exact hacq
  · unfold capDecode inEnd
    simp only [inShape, inBudget, hside, List.getD_cons_succ, List.getD_cons_zero,
      decodeTotalProgramPairSecond_pair, decodeBits_natBits]
    rw [(vertexCores_congr hag s (2 ^ (K + 1)) _).2.2.2, hU]
    have hval : ∀ i z, coreEnum cV U Pobj K i = some z →
        shapeSrc (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) z =
            shapeSrc (coreShape pA pB n A B) z ∧
          shapeTgt (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) z =
            shapeTgt (coreShape pA pB n A B) z := by
      intro i z hi
      have hzU := coreEnum_mem hi
      rw [← hU] at hzU
      have hzC := ((mem_coreResidual_iff _ s _ _ z).mp hzU).1
      have hzG := shapeComponent_subset _ _ _ hzC
      have hzn : z.length = n := (mem_stringsOfLength _ _).mp (Finset.mem_filter.mp hzG).1
      obtain ⟨h1, h2⟩ := hag.2.2.2 z hzn
      exact ⟨by simp only [shapeSrc, h1], by simp only [shapeTgt, h2]⟩
    have hcap : coreCap (tableShape TA TB n (Nat.log 2 A.card) (Nat.log 2 B.card)) s =
        coreCap (coreShape pA pB n A B) s := rfl
    rw [hcap, decodeOwned_congr _ _ hval]
    have hstream := upperOrientationStream (src := shapeSrc (coreShape pA pB n A B))
      (tgt := shapeTgt (coreShape pA pB n A B)) (d := coreCap (coreShape pA pB n A B) s)
      (coreEnum cV U Pobj K) hxt
    rw [howner] at hstream
    exact hstream

/-- **Tail length of the cap decoder.**  If `|aux| ≤ 3 n + bsize + 1`, `L ≤ 3 n + 1 + bsize` and
`r < 3 (L + 1) 2^d`, then `|(aux, bits r)| ≤ |aux| + d + c ⌈log₂ (n + 2)⌉`, with `c` depending
only on `bsize`.

Proof sketch: `length_totalProgramPairCode` gives `|aux| + |bits r| + 2 |bits |aux|| + 1`.
`|bits r| = Nat.size r ≤ d + Nat.size (3 (L + 1))` since `r < 2^(Nat.size (3 (L + 1))) 2^d`
(`Nat.size_le`, `Nat.lt_size_self`), and `Nat.size m ≤ ⌈log₂ (m + 2)⌉`; finally
`⌈log₂ (9 n + 6 + 3 bsize + 2)⌉` and `⌈log₂ (3 n + bsize + 3)⌉` are at most
`c' ⌈log₂ (n + 2)⌉` (`Nat.clog` of a product/sum, or `logb_linear_le_headerLog` and
`Nat.clog`/`Real.logb` bridges). -/
theorem length_capTail_le (bsize : ℕ) :
    ∃ c : ℕ, ∀ (n d L r : ℕ) (aux : BitString), aux.length ≤ 3 * n + bsize + 1 →
      L ≤ 3 * n + 1 + bsize → r < 3 * (L + 1) * 2 ^ d →
        (totalProgramPairCode aux (Nat.bits r)).length ≤ aux.length + d + c * headerLog n := by
  refine ⟨3 * Nat.size (9 + 3 * bsize) + 4, fun n d L r aux haux hL hr => ?_⟩
  have hl1 := one_le_headerLog n
  have hpow : n + 2 ≤ 2 ^ headerLog n := Nat.le_pow_clog one_lt_two (n + 2)
  have hK2 : 9 + 3 * bsize < 2 ^ Nat.size (9 + 3 * bsize) := Nat.lt_size_self _
  have hsz : ∀ m, m ≤ (9 + 3 * bsize) * (n + 2) →
      Nat.size m ≤ Nat.size (9 + 3 * bsize) + headerLog n := by
    intro m hm
    rw [Nat.size_le, pow_add]
    calc m ≤ (9 + 3 * bsize) * (n + 2) := hm
      _ ≤ (9 + 3 * bsize) * 2 ^ headerLog n := Nat.mul_le_mul_left _ hpow
      _ < 2 ^ Nat.size (9 + 3 * bsize) * 2 ^ headerLog n :=
        Nat.mul_lt_mul_of_pos_right hK2 (by positivity)
  have h3L : 3 * (L + 1) < 2 ^ (Nat.size (9 + 3 * bsize) + headerLog n) :=
    Nat.size_le.mp (hsz (3 * (L + 1)) (by nlinarith))
  have hr' : r < 2 ^ (Nat.size (9 + 3 * bsize) + headerLog n + d) := by
    calc r < 3 * (L + 1) * 2 ^ d := hr
      _ ≤ 2 ^ (Nat.size (9 + 3 * bsize) + headerLog n) * 2 ^ d := Nat.mul_le_mul_right _ h3L.le
      _ = 2 ^ (Nat.size (9 + 3 * bsize) + headerLog n + d) := (pow_add _ _ _).symm
  have hbr : (Nat.bits r).length ≤ Nat.size (9 + 3 * bsize) + headerLog n + d := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact hr'
  have hba : (Nat.bits aux.length).length ≤ Nat.size (9 + 3 * bsize) + headerLog n := by
    rw [Nat.size_eq_bits_len]
    exact hsz _ (by nlinarith)
  rw [length_totalProgramPairCode]
  nlinarith

/-- `⌈log₂ (n + 2)⌉ ≤ n + 1`. -/
theorem mc_headerLog_le_add_one (n : ℕ) : headerLog n ≤ n + 1 := by
  unfold headerLog
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h1 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

/-- `1 ≤ H`. -/
theorem mc_one_le_baseBudget (n e : ℕ) : (1 : ℝ) ≤ baseBudget n e := by
  have := one_le_headerLog n
  unfold baseBudget
  exact_mod_cast (by omega : 1 ≤ e + headerLog n)

/-- `⌈log₂ (n + 2)⌉ ≤ H`. -/
theorem mc_headerLog_le_baseBudget (n e : ℕ) : (headerLog n : ℝ) ≤ baseBudget n e := by
  unfold baseBudget
  push_cast
  linarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)]

/-- A field bounded by `2 n + c + 2` is at most `(c + 3) (n + 1)`. -/
theorem mc_le_mul_succ {k n c : ℕ} (hk : k ≤ 2 * n + c + 2) : k ≤ (c + 3) * (n + 1) := by
  nlinarith

end Kolmogorov.StrongMerging.Upper
