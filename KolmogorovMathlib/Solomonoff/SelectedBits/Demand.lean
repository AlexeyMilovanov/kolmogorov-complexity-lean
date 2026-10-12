import KolmogorovMathlib.MonotoneComplexity.Omega.LscBasic
import KolmogorovMathlib.Solomonoff.Domination.IndexedMeasures
import KolmogorovMathlib.Solomonoff.SelectedBits.DepthMajorant

/-!
# Certified demands of a tree index

The effective part of the selected-bit argument (blueprint nodes E10–E12).  An arbitrary
numerical index `e` is read as a candidate membership test: at stage `s` the code
`Denumerable.ofNat Nat.Partrec.Code e` is run with `Nat.Partrec.Code.evaln s` on the encoding of
a word, and the outputs `0` and `1` are read as the Boolean answers (`queryAnswer`); everything
else is unresolved.  A word `x` is *certified* at stage `s` (`certified`) when every prefix of
`x` is answered `true` and both children of every strict prefix are resolved.  The *demand*

  `demand G q e s x = q s x / 2 ^ s * ∏_{i < |x|} certFactor G q e s (x.take i) x[i]`

is emitted only for certified words (and is `0` otherwise); the factor of a prefix is the gain
at the stage ratio of numerators `natRatio` when the sibling is answered `false`.  The demand is
a genuinely computable rational function of `(e, s, x)` (`computable_demand`).

*Soundness* (`demand_le_stageDemand`): for every index the demands are bounded by the stage
demands of the possibly empty, noncomputable prefix-closed set `indexTree e` of the words all of
whose prefixes are accepted, so the masses `demandMass G q e x = ⨆ s, demand G q e s x` have
total at most `1` on every finite prefix-free set (`sum_demandMass_le_one`).  *Completeness*
(`eventually_demand_eq_stageDemand`): when `e` decides `T`, the demand of every word is
eventually the stage demand for `T`.  *Uniformity*
(`isUniformlyLowerSemicomputableTreeFamily_demandMass`): the running maxima of the demands,
floored to dyadic values, form one jointly computable approximation of the whole family.
-/

namespace Kolmogorov.SelectedBits

open Filter
open scoped ENNReal

/-! ### Bounded queries and certification -/

/-- The Boolean reading of a raw output: `0` is `false`, `1` is `true`, every other output is
unresolved. -/
def boolOfNat (n : ℕ) : Option Bool :=
  if n = 0 then some false else if n = 1 then some true else none

/-- The answer of the index `e` at stage `s` on the word `y`: the Boolean reading of
`evaln s (ofNat Code e) (encode y)`, `none` if the bounded evaluation does not halt or returns
a non-Boolean output. -/
def queryAnswer (e s : ℕ) (y : BitString) : Option Bool :=
  (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) (Encodable.encode y)).bind
    boolOfNat

/-- The word `x` is **certified** for the index `e` at stage `s`: every prefix `x.take i`,
`i ≤ |x|`, is answered `true`, and the sibling `x.take i ++ [!x[i]]` of the next prefix is
answered (`true` or `false`) for every `i < |x|`. -/
def certified (e s : ℕ) (x : BitString) : Bool :=
  (List.range (x.length + 1)).all (fun i => decide (queryAnswer e s (x.take i) = some true)) &&
    (List.range x.length).all
      (fun i => (queryAnswer e s (x.take i ++ [!(x.getD i false)])).isSome)

/-- The factor of the node `z` on the way to `z ++ [b]`, read from the answers: the gain at the
numerator ratio of the two children when the sibling `z ++ [!b]` is answered `false`, and `1`
otherwise. -/
def certFactor (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ) (z : BitString)
    (b : Bool) : ℚ :=
  if queryAnswer e s (z ++ [!b]) = some false then
    G.gain s (natRatio (q s (z ++ [b])) (q s (z ++ [!b])))
  else 1

/-- The **certified demand** of the word `x` for the index `e` at stage `s`: the stage mass
`q s x / 2 ^ s` times the certified factors of the strict prefixes of `x` when `x` is
certified, and `0` otherwise. -/
def demand (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ) (x : BitString) : ℚ :=
  if certified e s x then
    qStage q s x * ∏ i ∈ Finset.range x.length, certFactor G q e s (x.take i) (x.getD i false)
  else 0

/-- Every certified factor is at least `1`. -/
theorem one_le_certFactor (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ) (z : BitString)
    (b : Bool) : 1 ≤ certFactor G q e s z b := by
  unfold certFactor
  split_ifs
  · exact G.one_le _ _
  · exact le_rfl

/-- Certified demands are nonnegative. -/
theorem demand_nonneg (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ) (x : BitString) :
    0 ≤ demand G q e s x := by
  unfold demand
  split_ifs
  · refine mul_nonneg (qStage_nonneg q s x) (Finset.prod_nonneg fun i _ => ?_)
    exact zero_le_one.trans (one_le_certFactor G q e s _ _)
  · exact le_rfl

/-- The stage ratio of the rational stages is the ratio of the numerators: the common
denominator `2 ^ s` cancels. -/
theorem childRatio_qStage (q : ℕ → BitString → ℕ) (s : ℕ) (z : BitString) (b : Bool) :
    childRatio (qStage q) s z b = natRatio (q s (z ++ [b])) (q s (z ++ [!b])) := by
  rw [childRatio, qStage, qStage, ← add_div,
    div_div_div_cancel_right₀ (pow_ne_zero s two_ne_zero), natRatio]

/-! ### Computability -/

/-- The Boolean reading of raw outputs is primitive recursive. -/
theorem primrec_boolOfNat : Primrec boolOfNat :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const _)
      (Primrec.const _))

/-- The bounded answers are primitive recursive jointly in the index, the stage and the word:
`Nat.Partrec.Code.primrec_evaln` composed with `Primrec.ofNat Nat.Partrec.Code` and
`Primrec.encode`, then bound through the primitive recursive `boolOfNat`. -/
theorem primrec_queryAnswer :
    Primrec (fun p : ℕ × ℕ × BitString => queryAnswer p.1 p.2.1 p.2.2) := by
  have hev : Primrec (fun p : ℕ × ℕ × BitString =>
      Nat.Partrec.Code.evaln p.2.1 (Denumerable.ofNat Nat.Partrec.Code p.1)
        (Encodable.encode p.2.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.snd)
        ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst))
        (Primrec.encode.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.option_bind hev (primrec_boolOfNat.comp Primrec.snd).to₂

/-- The answers at primitive recursive indices, stages and words are primitive recursive:
`primrec_queryAnswer` composed with the data. -/
theorem primrec_queryAnswer_comp {α : Type*} [Primcodable α] {e s : α → ℕ}
    {w : α → BitString} (he : Primrec e) (hs : Primrec s) (hw : Primrec w) :
    Primrec (fun a => queryAnswer (e a) (s a) (w a)) :=
  primrec_queryAnswer.comp (Primrec.pair he (Primrec.pair hs hw))

/-- Certification is primitive recursive jointly in the index, the stage and the word: both
conjunctions are `List.all` over `List.range` (`list_all_primrec`) of answers at prefixes
(`Primrec.list_take`) and at siblings (`Primrec.list_getD`, `Primrec.list_append`). -/
theorem primrec_certified :
    Primrec (fun p : ℕ × ℕ × BitString => certified p.1 p.2.1 p.2.2) := by
  have he : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have htake : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ => a.1.2.2.take a.2) :=
    Primrec.list_take.comp Primrec.snd hx
  have hsib : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ =>
      a.1.2.2.take a.2 ++ [!(a.1.2.2.getD a.2 false)]) :=
    Primrec.list_append.comp htake (Primrec.list_cons.comp
      (Primrec.not.comp ((Primrec.list_getD false).comp hx Primrec.snd)) (Primrec.const []))
  have hlen : Primrec (fun p : ℕ × ℕ × BitString => p.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have h1 : Primrec (fun p : ℕ × ℕ × BitString =>
      (List.range (p.2.2.length + 1)).all
        (fun i => decide (queryAnswer p.1 p.2.1 (p.2.2.take i) = some true))) :=
    list_all_primrec (Primrec.list_range.comp (Primrec.succ.comp hlen))
      (Primrec.eq.decide.comp (primrec_queryAnswer_comp he hs htake)
        (Primrec.const (some true))).to₂
  have h2 : Primrec (fun p : ℕ × ℕ × BitString =>
      (List.range p.2.2.length).all
        (fun i => (queryAnswer p.1 p.2.1 (p.2.2.take i ++ [!(p.2.2.getD i false)])).isSome)) :=
    list_all_primrec (Primrec.list_range.comp hlen)
      (Primrec.option_isSome.comp (primrec_queryAnswer_comp he hs hsib)).to₂
  exact Primrec.and.comp h1 h2

/-- Certification is computable jointly in the index, the stage and the word. -/
theorem computable_certified :
    Computable (fun p : ℕ × ℕ × BitString => certified p.1 p.2.1 p.2.2) :=
  primrec_certified.to_comp

/-- The rational stages of a computable numerator approximation are computable. -/
theorem computable_qStage {q : ℕ → BitString → ℕ}
    (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    Computable (fun p : ℕ × BitString => qStage q p.1 p.2) := by
  refine computable_of_num_den (N := fun p : ℕ × BitString => (q p.1 p.2 : ℤ))
    (D := fun p : ℕ × BitString => 2 ^ p.1)
    (ComputableReals.primrec_natCastInt.to_comp.comp hq) (Computable.pow2.comp Computable.fst)
    (fun p => pow_pos (by norm_num) _) (fun p => ?_)
  simp [qStage]

/-- The certified factors are computable jointly in the index, the stage, the node and the
bit: a `Computable.cond` on the primitive recursive test whether the sibling is answered
`false`, with the gain (`GainFamily.computable`) at the computable ratio of numerators
(`computable₂_natRatio`) in the forced case. -/
theorem computable_certFactor (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    Computable (fun p : (ℕ × ℕ) × BitString × Bool =>
      certFactor G q p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hsib : Primrec (fun p : (ℕ × ℕ) × BitString × Bool => p.2.1 ++ [!p.2.2]) :=
    Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.not.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const []))
  have hchild : Primrec (fun p : (ℕ × ℕ) × BitString × Bool => p.2.1 ++ [p.2.2]) :=
    Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
  have hc : Computable (fun p : (ℕ × ℕ) × BitString × Bool =>
      decide (queryAnswer p.1.1 p.1.2 (p.2.1 ++ [!p.2.2]) = some false)) :=
    (Primrec.eq.decide.comp (primrec_queryAnswer_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst) hsib) (Primrec.const (some false))).to_comp
  have hs : Computable (fun p : (ℕ × ℕ) × BitString × Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hg : Computable (fun p : (ℕ × ℕ) × BitString × Bool =>
      G.gain p.1.2 (natRatio (q p.1.2 (p.2.1 ++ [p.2.2])) (q p.1.2 (p.2.1 ++ [!p.2.2])))) :=
    G.computable.comp hs (computable₂_natRatio.comp (hq.comp (hs.pair hchild.to_comp))
      (hq.comp (hs.pair hsib.to_comp)))
  refine (Computable.cond hc hg (Computable.const 1)).of_eq fun p => ?_
  simp only [certFactor, Bool.cond_decide]

/-- The product `∏ i ∈ range n, f i` is the `Nat.rec` accumulation of the factors. -/
theorem natRec_mul_eq_prod_range (f : ℕ → ℚ) (n : ℕ) :
    Nat.rec (motive := fun _ => ℚ) 1 (fun i acc => acc * f i) n =
      ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ← ih]

/-- The products of the certified factors along a word are computable jointly in the index,
the stage and the word, as a `Nat.rec` accumulation over the prefix lengths. -/
theorem computable_prod_certFactor (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    Computable (fun p : ℕ × ℕ × BitString => ∏ i ∈ Finset.range p.2.2.length,
      certFactor G q p.1 p.2.1 (p.2.2.take i) (p.2.2.getD i false)) := by
  have hx : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ => a.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ => a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hpair : Computable (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ =>
      ((a.1.1, a.1.2.1), a.1.2.2.take a.2.1, a.1.2.2.getD a.2.1 false)) :=
    Computable.pair (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp Computable.fst)))
      (Computable.pair (Primrec.list_take.comp hi hx).to_comp
        ((Primrec.list_getD false).comp hx hi).to_comp)
  have hf : Computable (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ =>
      certFactor G q a.1.1 a.1.2.1 (a.1.2.2.take a.2.1) (a.1.2.2.getD a.2.1 false)) :=
    ((computable_certFactor G hq).comp hpair).of_eq fun _ => rfl
  have hstep : Computable₂ (fun (p : ℕ × ℕ × BitString) (r : ℕ × ℚ) =>
      r.2 * certFactor G q p.1 p.2.1 (p.2.2.take r.1) (p.2.2.getD r.1 false)) :=
    computable₂_ratMul.comp (Computable.snd.comp Computable.snd) hf
  refine (Computable.nat_rec
    (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.snd))
    (Computable.const 1) hstep).of_eq fun p => ?_
  exact natRec_mul_eq_prod_range
    (fun i => certFactor G q p.1 p.2.1 (p.2.2.take i) (p.2.2.getD i false)) _

/-- **The certified demands are computable** jointly in the index, the stage and the word: a
`Computable.cond` on `computable_certified` with the product of the computable stage
(`computable_qStage`) and the computable product of the certified factors. -/
theorem computable_demand (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    Computable (fun p : ℕ × ℕ × BitString => demand G q p.1 p.2.1 p.2.2) := by
  have hm : Computable (fun p : ℕ × ℕ × BitString => qStage q p.2.1 p.2.2 *
      ∏ i ∈ Finset.range p.2.2.length,
        certFactor G q p.1 p.2.1 (p.2.2.take i) (p.2.2.getD i false)) :=
    computable₂_ratMul.comp ((computable_qStage hq).comp Computable.snd)
      (computable_prod_certFactor G hq)
  refine (Computable.cond computable_certified hm (Computable.const 0)).of_eq fun p => ?_
  cases h : certified p.1 p.2.1 p.2.2 <;> simp [demand, h]

/-! ### Soundness for arbitrary indices -/

/-- The **tree of an index**: the words all of whose prefixes are accepted, i.e. on whose
encodings the code with index `e` halts with output `1`.  It is prefix closed, possibly empty,
and in general not computable. -/
def indexTree (e : ℕ) : Set BitString :=
  {x | ∀ y, y <+: x →
    (1 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode y)}

/-- The tree of an index is prefix closed. -/
theorem prefixClosed_indexTree (e : ℕ) : PrefixClosed (indexTree e) :=
  fun _ _ hxy hy z hz => hy z (hz.trans hxy)

/-- The Boolean reading of `n` is `some b` exactly when `n = if b then 1 else 0`. -/
theorem boolOfNat_eq_some_iff {n : ℕ} {b : Bool} :
    boolOfNat n = some b ↔ n = if b then 1 else 0 := by
  unfold boolOfNat
  cases b <;> split_ifs <;> simp_all

/-- A Boolean answer of the index at some stage is an output of the code with index `e` on the
encoding of the word (`Nat.Partrec.Code.evaln_sound`). -/
theorem mem_eval_of_queryAnswer_eq_some {e s : ℕ} {y : BitString} {b : Bool}
    (h : queryAnswer e s y = some b) :
    (if b then 1 else 0 : ℕ) ∈
      (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode y) := by
  obtain ⟨n, hn, hb⟩ := Option.bind_eq_some_iff.mp h
  rw [boolOfNat_eq_some_iff] at hb
  subst hb
  exact Nat.Partrec.Code.evaln_sound hn

/-- When the code with index `e` outputs the Boolean `b` on the encoding of `y`, the index
answers `b` at every large stage (`Nat.Partrec.Code.evaln_complete`,
`Nat.Partrec.Code.evaln_mono`). -/
theorem eventually_queryAnswer_eq_some {e : ℕ} {y : BitString} {b : Bool}
    (h : (if b then 1 else 0 : ℕ) ∈
      (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode y)) :
    ∀ᶠ s in atTop, queryAnswer e s y = some b := by
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h
  filter_upwards [eventually_ge_atTop k] with s hs
  rw [queryAnswer, Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hs hk), Option.bind_some]
  exact boolOfNat_eq_some_iff.mpr rfl

/-- Certification unpacked: every prefix `x.take i`, `i ≤ |x|`, is answered `true`, and the
sibling `x.take i ++ [!x[i]]` of the next prefix is answered for every `i < |x|`. -/
theorem certified_eq_true_iff {e s : ℕ} {x : BitString} :
    certified e s x = true ↔
      (∀ i ≤ x.length, queryAnswer e s (x.take i) = some true) ∧
        ∀ i < x.length, (queryAnswer e s (x.take i ++ [!(x.getD i false)])).isSome := by
  simp [certified, List.all_eq_true, List.mem_range]

/-- A certified word belongs to the tree of the index: each of its prefixes `y = x.take |y|` is
answered `true`, hence accepted. -/
theorem mem_indexTree_of_certified {e s : ℕ} {x : BitString}
    (hcert : certified e s x = true) : x ∈ indexTree e := by
  intro y hy
  have h := (certified_eq_true_iff.mp hcert).1 y.length hy.length_le
  rw [← List.prefix_iff_eq_take.mp hy] at h
  simpa using mem_eval_of_queryAnswer_eq_some h

/-- At a certified word, the certified factor of every strict prefix is the node factor of the
tree of the index for the rational stages `qStage q`: a sibling answered `false` outputs `0`, so
it is not accepted (`Part.mem_unique`) and leaves the tree; a sibling answered `true` is
accepted, and so are all its proper prefixes, which are prefixes of the word. -/
theorem certFactor_eq_nodeFactor_of_certified (G : GainFamily) (q : ℕ → BitString → ℕ)
    {e s : ℕ} {x : BitString} (hcert : certified e s x = true) {i : ℕ} (hi : i < x.length) :
    certFactor G q e s (x.take i) (x.getD i false) =
      nodeFactor G (indexTree e) (qStage q) s (x.take i) (x.getD i false) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((certified_eq_true_iff.mp hcert).2 i hi)
  have hout := mem_eval_of_queryAnswer_eq_some hc
  cases c with
  | false =>
    have hnot : x.take i ++ [!(x.getD i false)] ∉ indexTree e := fun hmem => by
      have h1 := hmem _ List.prefix_rfl
      exact absurd (Part.mem_unique hout h1) (by simp)
    rw [certFactor, ite_eq_left hc, nodeFactor, ite_eq_right hnot, childRatio_qStage]
  | true =>
    have hmem : x.take i ++ [!(x.getD i false)] ∈ indexTree e := by
      intro y hy
      rcases List.prefix_concat_iff.mp hy with rfl | hy
      · simpa using hout
      · exact mem_indexTree_of_certified hcert y (hy.trans (List.take_prefix i x))
    rw [certFactor, ite_eq_right (by rw [hc]; simp), nodeFactor, ite_eq_left hmem]

/-- **Soundness of a certified demand.**  A demand emitted at a certified word is the stage
demand of the tree of the index with the stages `qStage q`: the word is in `indexTree e`
(`mem_indexTree_of_certified`), and the certified factors are the node factors of
`indexTree e` (`certFactor_eq_nodeFactor_of_certified`). -/
theorem demand_eq_stageDemand_of_certified (G : GainFamily) (q : ℕ → BitString → ℕ)
    {e s : ℕ} {x : BitString} (hcert : certified e s x = true) :
    demand G q e s x = stageDemand G (indexTree e) (qStage q) s x := by
  rw [demand, stageDemand, ite_eq_left hcert, ite_eq_left (mem_indexTree_of_certified hcert),
    forcedGainProd, List.length_nil, ← Finset.range_eq_Ico]
  congr 1
  exact Finset.prod_congr rfl fun i hi =>
    certFactor_eq_nodeFactor_of_certified G q hcert (Finset.mem_range.mp hi)

/-- Every certified demand is either `0` or the stage demand of the tree of the index. -/
theorem demand_eq_zero_or_eq_stageDemand (G : GainFamily) (q : ℕ → BitString → ℕ)
    (e s : ℕ) (x : BitString) :
    demand G q e s x = 0 ∨ demand G q e s x = stageDemand G (indexTree e) (qStage q) s x := by
  by_cases hcert : certified e s x = true
  · exact Or.inr (demand_eq_stageDemand_of_certified G q hcert)
  · left
    simp [demand, hcert]

/-- **Soundness.**  For every index, every certified demand is at most the stage demand of the
tree of the index. -/
theorem demand_le_stageDemand (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ)
    (x : BitString) : demand G q e s x ≤ stageDemand G (indexTree e) (qStage q) s x := by
  rcases demand_eq_zero_or_eq_stageDemand G q e s x with h | h
  · rw [h]
    exact stageDemand_nonneg G _ (qStage_nonneg q) s x
  · exact h.le

/-- The **mass of the demands** of the index `e` at the word `x`: the supremum over the stages
of the certified demands. -/
noncomputable def demandMass (G : GainFamily) (q : ℕ → BitString → ℕ) (e : ℕ)
    (x : BitString) : ℝ≥0∞ :=
  ⨆ s, ENNReal.ofReal (demand G q e s x : ℝ)

/-- **The antichain budget for every index.**  For the stages of a simple tree approximation,
the demand masses of every index have total at most `1` on every finite prefix-free set. -/
theorem sum_demandMass_le_one (G : GainFamily) {a : BitString → ℝ≥0∞}
    {q : ℕ → BitString → ℕ} (hq : IsSimpleTreeApproximation a q) (e : ℕ)
    (S : Finset BitString) (hS : IsPrefixFree (S : Set BitString)) :
    ∑ x ∈ S, demandMass G q e x ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun x _ => iSup_mono fun s => ?_)
    (sum_iSup_stageDemand_le G (prefixClosed_indexTree e) (isCoherentStages_qStage hq)
      (fun s => (qStage_root hq s).le) S hS)
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast demand_le_stageDemand G q e s x)

/-! ### Completeness for deciding indices -/

/-- The tree of an index deciding `T` is `T`: the output on `y` is `1` exactly when `y ∈ T`,
and `T` is prefix closed. -/
theorem indexTree_eq_of_decidesTree {e : ℕ} {T : Set BitString} (h : DecidesTree e T) :
    indexTree e = T := by
  obtain ⟨⟨_, hT⟩, hdec⟩ := h
  have key : ∀ y, (1 : ℕ) ∈ (Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode y) ↔
      y ∈ T := by
    intro y
    obtain ⟨b, hb, hbT⟩ := hdec y
    constructor
    · intro h1
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hb
        exact absurd (Part.mem_unique hb h1) (by norm_num)
      | true => exact hbT.mp rfl
    · intro hy
      obtain rfl : b = true := hbT.mpr hy
      simpa using hb
  ext x
  simp only [indexTree, Set.mem_ofPred_eq, key]
  exact ⟨fun h => h x List.prefix_rfl, fun hx y hy => hT hy hx⟩

/-- Every word of the tree of a deciding index is eventually certified: the finitely many
queries (the prefixes of `x`, which are in `T`, and the siblings of the next prefixes) all halt
with Boolean outputs, so each is answered from some stage on (`eventually_queryAnswer_eq_some`),
and `Filter.eventually_all_finset` combines them. -/
theorem eventually_certified {e : ℕ} {T : Set BitString} (h : DecidesTree e T)
    {x : BitString} (hx : x ∈ T) : ∀ᶠ s in atTop, certified e s x = true := by
  have hans : ∀ y, ∃ b : Bool, (b = true ↔ y ∈ T) ∧
      ∀ᶠ s in atTop, queryAnswer e s y = some b := fun y => by
    obtain ⟨b, hb, hbT⟩ := h.2 y
    exact ⟨b, hbT, eventually_queryAnswer_eq_some hb⟩
  have hpre : ∀ i ∈ Finset.range (x.length + 1),
      ∀ᶠ s in atTop, queryAnswer e s (x.take i) = some true := fun i _ => by
    obtain ⟨b, hbT, hev⟩ := hans (x.take i)
    rwa [hbT.mpr (h.1.2 (List.take_prefix i x) hx)] at hev
  have hsib : ∀ i ∈ Finset.range x.length,
      ∀ᶠ s in atTop, (queryAnswer e s (x.take i ++ [!(x.getD i false)])).isSome := fun i _ => by
    obtain ⟨b, -, hev⟩ := hans (x.take i ++ [!(x.getD i false)])
    filter_upwards [hev] with s hs
    rw [hs]
    rfl
  filter_upwards [(Filter.eventually_all_finset _).mpr hpre,
    (Filter.eventually_all_finset _).mpr hsib] with s h1 h2
  exact certified_eq_true_iff.mpr ⟨fun i hi => h1 i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)),
    fun i hi => h2 i (Finset.mem_range.mpr hi)⟩

/-- **Completeness.**  When `e` decides `T`, the certified demand of every word is eventually
the stage demand for `T` with the stages `qStage q`. -/
theorem eventually_demand_eq_stageDemand (G : GainFamily) (q : ℕ → BitString → ℕ) {e : ℕ}
    {T : Set BitString} (h : DecidesTree e T) (x : BitString) :
    ∀ᶠ s in atTop, demand G q e s x = stageDemand G T (qStage q) s x := by
  by_cases hx : x ∈ T
  · filter_upwards [eventually_certified h hx] with s hs
    rw [demand_eq_stageDemand_of_certified G q hs, indexTree_eq_of_decidesTree h]
  · refine Filter.Eventually.of_forall fun s => ?_
    have h1 := demand_le_stageDemand G q e s x
    have h2 : stageDemand G T (qStage q) s x = 0 := by simp [stageDemand, hx]
    rw [indexTree_eq_of_decidesTree h, h2] at h1
    rw [h2]
    exact le_antisymm h1 (demand_nonneg G q e s x)

/-! ### Uniform lower semicomputability -/

/-- The running maximum over the stages `t ≤ s` of the certified demands. -/
def demandRunMax (G : GainFamily) (q : ℕ → BitString → ℕ) (e s : ℕ) (x : BitString) : ℚ :=
  ratRunMax (fun t => demand G q e t x) s

/-- The running maxima of the certified demands are computable jointly in the index, the stage
and the word: `Computable.nat_rec` on the stage with the step `max acc (demand …)`
(`computable₂_ratMax`, `computable_demand`), as in `computable_ratRunMaxP`. -/
theorem computable_demandRunMax (G : GainFamily) {q : ℕ → BitString → ℕ}
    (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    Computable (fun p : ℕ × ℕ × BitString => demandRunMax G q p.1 p.2.1 p.2.2) := by
  have hd := computable_demand G hq
  have hstage : Computable (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ =>
      (a.1.1, a.2.1 + 1, a.1.2.2)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.succ.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hnext : Computable (fun a : (ℕ × ℕ × BitString) × ℕ × ℚ =>
      demand G q a.1.1 (a.2.1 + 1) a.1.2.2) :=
    (hd.comp hstage).of_eq fun _ => rfl
  have hstep : Computable₂ (fun (p : ℕ × ℕ × BitString) (r : ℕ × ℚ) =>
      max r.2 (demand G q p.1 (r.1 + 1) p.2.2)) :=
    computable₂_ratMax.comp (Computable.snd.comp Computable.snd) hnext
  have hbase : Computable (fun p : ℕ × ℕ × BitString => demand G q p.1 0 p.2.2) :=
    (hd.comp (Computable.pair Computable.fst (Computable.pair (Computable.const 0)
      (Computable.snd.comp Computable.snd)))).of_eq fun _ => rfl
  refine (Computable.nat_rec (Computable.fst.comp Computable.snd) hbase hstep).of_eq
    fun p => ?_
  obtain ⟨e, s, x⟩ := p
  dsimp only
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [demandRunMax, ratRunMax_succ, ← demandRunMax, ← ih]

/-- The running maxima have the same suprema as the demands. -/
theorem iSup_ofReal_demandRunMax (G : GainFamily) (q : ℕ → BitString → ℕ) (e : ℕ)
    (x : BitString) :
    ⨆ s, ENNReal.ofReal (demandRunMax G q e s x : ℝ) = demandMass G q e x := by
  unfold demandMass
  apply le_antisymm
  · refine iSup_le fun s => ?_
    obtain ⟨t, ht⟩ : ∃ t, demandRunMax G q e s x = demand G q e t x := by
      induction s with
      | zero => exact ⟨0, rfl⟩
      | succ s ih =>
        obtain ⟨t, ht⟩ := ih
        simp only [demandRunMax, ratRunMax_succ] at ht ⊢
        rcases max_cases (ratRunMax (fun t => demand G q e t x) s) (demand G q e (s + 1) x)
          with ⟨h, _⟩ | ⟨h, _⟩
        · exact ⟨t, h.trans ht⟩
        · exact ⟨s + 1, h⟩
    rw [ht]
    exact le_iSup (fun s => ENNReal.ofReal (demand G q e s x : ℝ)) t
  · refine iSup_le fun s => le_trans ?_
      (le_iSup (fun s => ENNReal.ofReal (demandRunMax G q e s x : ℝ)) s)
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast le_ratRunMax (fun t => demand G q e t x) s)

/-- **Uniform lower semicomputability of the demand masses.**  For a computable numerator
approximation `q`, the family `demandMass G q` is lower semicomputable uniformly in the index:
the witness is the dyadic floor `ratDyadicFloor (demandRunMax G q e s x) s`. -/
theorem isUniformlyLowerSemicomputableTreeFamily_demandMass (G : GainFamily)
    {q : ℕ → BitString → ℕ} (hq : Computable (fun p : ℕ × BitString => q p.1 p.2)) :
    IsUniformlyLowerSemicomputableTreeFamily (demandMass G q) := by
  refine ⟨fun e s x => ratDyadicFloor (demandRunMax G q e s x) s, fun e s x => ?_,
    fun e x => ?_, ?_⟩
  · exact dyadicValue_ratDyadicFloor_mono_of_le
      (monotone_ratRunMax (fun t => demand G q e t x) (Nat.le_succ s)) s
  · change (⨆ s, dyadicValue (ratDyadicFloor (demandRunMax G q e s x) s) s) = _
    rw [iSup_dyadicValue_ratDyadicFloor (show Monotone fun s => demandRunMax G q e s x from
      monotone_ratRunMax (fun t => demand G q e t x))]
    exact iSup_ofReal_demandRunMax G q e x
  · exact computable_ratDyadicFloor.comp (computable_demandRunMax G hq)
      (Computable.fst.comp Computable.snd)

end Kolmogorov.SelectedBits
