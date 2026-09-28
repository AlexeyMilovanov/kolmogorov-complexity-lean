import KolmogorovMathlib.AlgorithmicRandomness.EffectiveNull
import KolmogorovMathlib.AlgorithmicRandomness.Disjointify
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.AlgorithmicRandomness.Enumeration


namespace Kolmogorov

open MeasureTheory Topology

/-! ## Computable finite snapshots of an enumeration -/

/-- The values emitted during the first `s` stages of an `Option`-valued
enumeration, in their original order. -/
def enumValues (f : ℕ → Option BitString) : ℕ → List BitString
  | 0 => []
  | s + 1 => enumValues f s ++ (f s).toList

/-- No value has been emitted before stage zero. -/
@[simp] lemma enumValues_zero (f : ℕ → Option BitString) : enumValues f 0 = [] := rfl

/-- The list of values emitted before stage `s + 1` extends the one before stage `s` by the
emission at stage `s`. -/
@[simp] lemma enumValues_succ (f : ℕ → Option BitString) (s : ℕ) :
    enumValues f (s + 1) = enumValues f s ++ (f s).toList := rfl

/-- The list of values emitted before a stage is computable. -/
lemma computable_enumValues {α : Type*} [Primcodable α]
    {f : α → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable (fun p : α × ℕ => enumValues (f p.1) p.2) := by
  have hstep : Computable₂ (fun (a : α × ℕ) (q : ℕ × List BitString) =>
      q.2 ++ (f a.1 q.1).toList) := by
    have hfa : Computable (fun r : (α × ℕ) × (ℕ × List BitString) => f r.1.1 r.2.1) :=
      hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)
    have htail : Computable (fun r : (α × ℕ) × (ℕ × List BitString) =>
        (f r.1.1 r.2.1).toList) :=
      Primrec.optionToList.to_comp.comp hfa
    exact (Computable.list_append.comp (Computable.snd.comp Computable.snd) htail).to₂
  refine (Computable.nat_rec Computable.snd (Computable.const []) hstep).of_eq ?_
  intro p
  induction p.2 with
  | zero => rfl
  | succ s ih => simp [enumValues_succ, ih]

/-- The emitted values only grow from one stage to the next. -/
lemma enumValues_prefix_succ (f : ℕ → Option BitString) (s : ℕ) :
    enumValues f s <+: enumValues f (s + 1) := by
  rw [enumValues_succ]
  exact List.prefix_append _ _

/-- The emitted values only grow with the stage. -/
lemma enumValues_prefix_of_le (f : ℕ → Option BitString) {s t : ℕ} (hst : s ≤ t) :
    enumValues f s <+: enumValues f t := by
  induction hst with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (enumValues_prefix_succ f _)

/-- A string has been emitted before stage `s` exactly when the enumeration emits it at some
index below `s`. -/
lemma mem_enumValues_iff (f : ℕ → Option BitString) (s : ℕ) (x : BitString) :
    x ∈ enumValues f s ↔ ∃ i < s, f i = some x := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [enumValues_succ, List.mem_append, ih]
      constructor
      · rintro (⟨i, hi, hfi⟩ | hx)
        · exact ⟨i, by omega, hfi⟩
        · cases hfs : f s with
          | none => revert hx; rw [hfs]; simp
          | some y =>
              revert hx
              rw [hfs]
              simp only [Option.toList_some, List.mem_singleton]
              rintro rfl
              exact ⟨s, by omega, hfs⟩
      · rintro ⟨i, hi, hfi⟩
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with his | rfl
        · exact Or.inl ⟨i, his, hfi⟩
        · right
          simp [hfi]

/-- Stage-`s` approximation to the compacted enumeration: its `i`-th value is
the `i`-th interval emitted before stage `s`, when that value already exists. -/
def compactStage (f : ℕ → Option BitString) (i s : ℕ) : Option BitString :=
  (enumValues f s)[i]?

/-- The compacted stagewise enumeration is computable. -/
lemma computable_compactStage {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable (fun q : (ℕ × ℕ) × ℕ => compactStage (f q.1.1) q.1.2 q.2) := by
  have houter : Computable (fun q : (ℕ × ℕ) × ℕ => q.1) := Computable.fst
  have hleft : Computable (fun q : ℕ × ℕ => q.1) := Computable.fst
  have hn : Computable (fun q : (ℕ × ℕ) × ℕ => q.1.1) :=
    hleft.comp houter
  have harg : Computable (fun q : (ℕ × ℕ) × ℕ => (q.1.1, q.2)) :=
    hn.pair Computable.snd
  have hvalues0 : Computable (fun q : ℕ × ℕ => enumValues (f q.1) q.2) :=
    computable_enumValues hf
  have hvalues : Computable (fun q : (ℕ × ℕ) × ℕ => enumValues (f q.1.1) q.2) :=
    hvalues0.comp harg
  have hright : Computable (fun q : ℕ × ℕ => q.2) := Computable.snd
  have hidx : Computable (fun q : (ℕ × ℕ) × ℕ => q.1.2) := hright.comp houter
  exact Computable.list_getElem?.comp hvalues
    hidx

/-- Once the compacted enumeration has emitted a value at an index, it keeps emitting it at all
later stages. -/
lemma compactStage_stable (f : ℕ → Option BitString) {i s t : ℕ} {x : BitString}
    (hst : s ≤ t) (h : compactStage f i s = some x) :
    compactStage f i t = some x := by
  rw [compactStage, List.getElem?_eq_some_iff] at h ⊢
  obtain ⟨hi, hix⟩ := h
  have hp := enumValues_prefix_of_le f hst
  refine ⟨lt_of_lt_of_le hi hp.length_le, ?_⟩
  rw [← hix]
  exact (hp.getElem hi).symm

/-- The set of indices at which the compacted enumeration has emitted is an initial segment. -/
lemma compactStage_domain_downward (f : ℕ → Option BitString) {i j s : ℕ}
    (hij : i ≤ j) (h : (compactStage f j s).isSome) :
    (compactStage f i s).isSome := by
  rw [Option.isSome_iff_exists] at h ⊢
  obtain ⟨x, hx⟩ := h
  rw [compactStage, List.getElem?_eq_some_iff] at hx
  obtain ⟨hj, -⟩ := hx
  have hi : i < (enumValues f s).length := lt_of_le_of_lt hij hj
  exact ⟨(enumValues f s)[i], List.getElem?_eq_getElem hi⟩

/-- The open set represented by all values of a staged partial enumeration. -/
def stagedCover (f : ℕ → ℕ → Option BitString) : Set CantorSeq :=
  ⋃ i, ⋃ s, (f i s).elim ∅ cantorCylinder

/-- Compacting an enumeration does not change the open set it covers. -/
lemma stagedCover_compactStage (f : ℕ → Option BitString) :
    stagedCover (compactStage f) = ⋃ i, (f i).elim ∅ cantorCylinder := by
  ext w
  simp only [stagedCover, Set.mem_iUnion]
  constructor
  · rintro ⟨i, s, his⟩
    cases hcis : compactStage f i s with
    | none => simp [hcis] at his
    | some x =>
        have hxmem : x ∈ enumValues f s := by
          rw [compactStage, List.getElem?_eq_some_iff] at hcis
          obtain ⟨hi, hix⟩ := hcis
          rw [← hix]
          exact List.getElem_mem hi
        obtain ⟨j, hj, hfj⟩ := (mem_enumValues_iff f s x).1 hxmem
        exact ⟨j, by simpa [hcis, hfj] using his⟩
  · rintro ⟨j, hj⟩
    cases hfj : f j with
    | none => simp [hfj] at hj
    | some x =>
        have hxmem : x ∈ enumValues f (j + 1) :=
          (mem_enumValues_iff f (j + 1) x).2 ⟨j, by omega, hfj⟩
        obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hxmem
        refine ⟨i, j + 1, ?_⟩
        have hc : compactStage f i (j + 1) = some x := by
          rw [compactStage, List.getElem?_eq_some_iff]
          exact ⟨hi, hix⟩
        simpa [hc, hfj] using hj

/-! ## Turning an enumerable cylinder family into a decidable one -/

/-- Boolean prefix test used by the bounded-stage cover. -/
def normalFormIsPrefixB (y x : BitString) : Bool := decide (x.take y.length = y)

/-- The boolean prefix test is correct. -/
lemma normalFormIsPrefixB_iff (y x : BitString) :
    normalFormIsPrefixB y x = true ↔ y <+: x := by
  rw [normalFormIsPrefixB, decide_eq_true_iff, List.prefix_iff_eq_take]
  exact eq_comm

/-- The boolean prefix test is primitive recursive in both arguments. -/
lemma primrec₂_normalFormIsPrefixB : Primrec₂ normalFormIsPrefixB := by
  have h : Primrec (fun p : BitString × BitString =>
      decide (p.2.take p.1.length = p.1)) :=
    Primrec₂.comp (Primrec.eq (α := BitString)).decide
      (Primrec₂.comp (f := fun (l : BitString) (n : ℕ) => l.take n)
        Primrec.list_take Primrec.snd
        (Primrec.list_length.comp Primrec.fst))
      Primrec.fst
  exact h

/-- Whether an optional emission is a string that is a prefix of `x`, i.e. whether the emitted
cylinder contains the cylinder of `x`. -/
def emissionCovers (o : Option BitString) (x : BitString) : Bool :=
  (o.map fun y => normalFormIsPrefixB y x).getD false

/-- Whether one of the first `s` emitted intervals is a prefix of `x`. -/
def prefixSeen (f : ℕ → Option BitString) (x : BitString) : ℕ → Bool
  | 0 => false
  | s + 1 => prefixSeen f x s || emissionCovers (f s) x

/-- The bounded search succeeds exactly when some emission before stage `s` is a prefix
of `x`. -/
lemma prefixSeen_spec (f : ℕ → Option BitString) (x : BitString) (s : ℕ) :
    prefixSeen f x s = true ↔ ∃ i < s, ∃ y, f i = some y ∧ y <+: x := by
  induction s with
  | zero => simp [prefixSeen]
  | succ s ih =>
      rw [prefixSeen, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, y, hfy, hyx⟩ | hs)
        · exact ⟨i, by omega, y, hfy, hyx⟩
        · cases hfs : f s with
          | none => simp [hfs, emissionCovers] at hs
          | some y =>
              have hyx : y <+: x :=
                (normalFormIsPrefixB_iff y x).1 (by simpa [hfs, emissionCovers] using hs)
              exact ⟨s, by omega, y, hfs, hyx⟩
      · rintro ⟨i, hi, y, hfy, hyx⟩
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with his | rfl
        · exact Or.inl ⟨i, his, y, hfy, hyx⟩
        · exact Or.inr (by simp [hfy, emissionCovers, (normalFormIsPrefixB_iff y x).2 hyx])

/-- The covering test on emissions is computable. -/
lemma computable₂_emissionCovers : Computable₂ emissionCovers := by
  have hpref : Computable₂ normalFormIsPrefixB := primrec₂_normalFormIsPrefixB.to_comp
  have hbranch : Computable₂ (fun (r : Option BitString × BitString) (y : BitString) =>
      normalFormIsPrefixB y r.2) :=
    hpref.comp Computable.snd (Computable.snd.comp Computable.fst)
  have hmap : Computable (fun r : Option BitString × BitString =>
      r.1.map (fun y => normalFormIsPrefixB y r.2)) :=
    Computable.option_map Computable.fst hbranch
  exact (Computable.option_getD hmap (Computable.const false)).to₂

/-- The bounded search for a covering emission is computable. -/
lemma computable_prefixSeen {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable (fun q : (ℕ × BitString) × ℕ => prefixSeen (f q.1.1) q.1.2 q.2) := by
  have hstep : Computable₂ (fun (a : (ℕ × BitString) × ℕ)
      (q : ℕ × Bool) => q.2 || emissionCovers (f a.1.1 q.1) a.1.2) := by
    have hfstep : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) =>
        f r.1.1.1 r.2.1) := by
      have hra : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) => r.1) :=
        Computable.fst
      have ha : Computable (fun a : (ℕ × BitString) × ℕ => a.1) := Computable.fst
      have hn0 : Computable (fun a : ℕ × BitString => a.1) := Computable.fst
      have hn : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) => r.1.1.1) := by
        exact hn0.comp (ha.comp hra)
      exact hf.comp hn (Computable.fst.comp Computable.snd)
    have hcover : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) =>
        emissionCovers (f r.1.1.1 r.2.1) r.1.1.2) := by
      have hra : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) => r.1) :=
        Computable.fst
      have ha : Computable (fun a : (ℕ × BitString) × ℕ => a.1) := Computable.fst
      have hx0 : Computable (fun a : ℕ × BitString => a.2) := Computable.snd
      have hx : Computable (fun r : ((ℕ × BitString) × ℕ) × (ℕ × Bool) => r.1.1.2) := by
        exact hx0.comp (ha.comp hra)
      exact computable₂_emissionCovers.comp hfstep hx
    exact (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd) hcover).to₂
  refine (Computable.nat_rec Computable.snd (Computable.const false) hstep).of_eq ?_
  intro q
  induction q.2 with
  | zero => rfl
  | succ s ih =>
      change (Nat.rec false
        (fun y IH => IH || emissionCovers (f q.1.1 y) q.1.2) s ||
          emissionCovers (f q.1.1 s) q.1.2) = _
      rw [ih]
      rfl

/-- A decidable family whose cylinders have the same union as an enumerated
family.  A string `x` is selected if an interval emitted by stage `|x|` is a
prefix of `x`. -/
def decidableCover (f : ℕ → Option BitString) (x : BitString) : Bool :=
  prefixSeen f x (x.length + 1)

/-- The decidable covering predicate of a computable family of enumerations is computable. -/
lemma computable_decidableCover {f : ℕ → ℕ → Option BitString} (hf : Computable₂ f) :
    Computable₂ (fun n x => decidableCover (f n) x) := by
  have hseen := computable_prefixSeen hf
  have harg : Computable (fun p : ℕ × BitString =>
      (((p.1, p.2), p.2.length + 1) : (ℕ × BitString) × ℕ)) := by
    have hlen : Computable (fun p : ℕ × BitString => p.2.length + 1) :=
      Computable.succ.comp (Computable.list_length.comp Computable.snd)
    exact (Computable.fst.pair Computable.snd).pair hlen
  exact (hseen.comp harg).to₂

/-- The cylinders selected by the covering predicate cover the same open set as the original
enumeration. -/
lemma decidableCover_iUnion (f : ℕ → Option BitString) :
    (⋃ x, if decidableCover f x then cantorCylinder x else (∅ : Set CantorSeq)) =
      ⋃ i, (f i).elim ∅ cantorCylinder := by
  ext w
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx⟩
    by_cases hp : decidableCover f x = true
    · have hwx : w ∈ cantorCylinder x := by simpa [hp] using hx
      obtain ⟨i, hi, y, hfy, hyx⟩ :=
        (prefixSeen_spec f x (x.length + 1)).1 hp
      exact ⟨i, by
        rw [hfy]
        exact cantorCylinder_subset_of_prefix hyx hwx⟩
    · simp [hp] at hx
  · rintro ⟨i, hi⟩
    cases hfi : f i with
    | none => simp [hfi] at hi
    | some y =>
        have hwy : IsCantorPrefix y w := by simpa [hfi] using hi
        let L := max y.length i
        let x := cantorPrefix w L
        have hwx : w ∈ cantorCylinder x := mem_cantorCylinder_cantorPrefix w L
        have hyx : y <+: x :=
          prefix_of_isCantorPrefix hwy hwx (by simp [x, L])
        have hp : decidableCover f x = true :=
          (prefixSeen_spec f x (x.length + 1)).2 (by
            have hi : i < x.length + 1 := by simp [x, L]
            exact ⟨i, hi, y, hfi, hyx⟩)
        exact ⟨x, by simp [hp, hwx]⟩

/-- Enumerate a decidable family by traversing the canonical enumeration of
bit strings and retaining exactly the selected members. -/
def decidableFamilyEnum (p : BitString → Bool) (i : ℕ) : Option BitString :=
  (Encodable.decode₂ BitString i).bind fun x => bif p x then some x else none

/-- The enumeration attached to a computable family of string predicates is computable. -/
lemma computable_decidableFamilyEnum {p : ℕ → BitString → Bool} (hp : Computable₂ p) :
    Computable₂ (fun n i => decidableFamilyEnum (p n) i) := by
  have hx : Computable (fun q : ℕ × ℕ => Encodable.decode₂ BitString q.2) :=
    (Primrec.decode₂.comp Primrec.snd).to_comp
  have hbranch : Computable₂ (fun (q : ℕ × ℕ) (x : BitString) =>
      bif p q.1 x then some x else none) := by
    have htest : Computable (fun r : (ℕ × ℕ) × BitString => p r.1.1 r.2) :=
      hp.comp (Computable.fst.comp Computable.fst) Computable.snd
    exact (Computable.cond htest (Computable.option_some.comp Computable.snd)
      (Computable.const none)).to₂
  exact (Computable.option_bind hx hbranch).to₂

/-- The enumeration attached to a string predicate covers exactly the union of the cylinders it
selects. -/
lemma decidableFamilyEnum_iUnion (p : BitString → Bool) :
    (⋃ i, (decidableFamilyEnum p i).elim ∅ cantorCylinder) =
      ⋃ x, (if p x then cantorCylinder x else (∅ : Set CantorSeq)) := by
  ext w
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    unfold decidableFamilyEnum at hi
    cases hdec : Encodable.decode₂ BitString i with
    | none => simp [hdec] at hi
    | some x =>
        by_cases hp : p x = true
        · exact ⟨x, by simpa [hdec, hp] using hi⟩
        · simp [hdec, hp] at hi
  · rintro ⟨x, hx⟩
    refine ⟨Encodable.encode x, ?_⟩
    unfold decidableFamilyEnum
    rw [Encodable.encodek₂]
    by_cases hp : p x = true
    · simpa [hp] using hx
    · simp [hp] at hx

/-- The sequence of rationals `2^{-n}` is computable. -/
lemma computable_pow_half : Computable (fun (n : ℕ) => (2 : ℚ)⁻¹ ^ n) := by
  have hnat : Primrec (fun n : ℕ => 2 ^ n) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id
  refine computable_of_num_den (f := fun n : ℕ => (2 : ℚ)⁻¹ ^ n)
    (N := fun _ : ℕ => 1) (D := fun n : ℕ => 2 ^ n)
    (Computable.const 1) (hnat.to_comp)
    (fun _ => by positivity) (fun n => by push_cast; exact one_div (2^n : ℚ) ▸ inv_pow (2 : ℚ) n)

/-- The extended-real image of the rational `2^{-n}` is the dyadic value of numerator one. -/
lemma ofReal_pow_half_eq_dyadicValue (n : ℕ) :
    ENNReal.ofReal ((((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ)) = dyadicValue 1 n := by
  simp only [dyadicValue, Nat.cast_one]
  have hcast : ((((2 : ℚ)⁻¹ ^ n : ℚ) : ℝ)) = 1 / (2 : ℝ) ^ n := by
    push_cast
    exact one_div ((2 : ℝ) ^ n) ▸ inv_pow (2 : ℝ) n
  rw [hcast, ENNReal.ofReal_div_of_pos (by positivity)]
  simp

/-- A positive rational is at least `2^{-d}`, where `d` is its denominator. -/
lemma inv_two_pow_den_le_rat {q : ℚ} (hq : 0 < q) :
    1 / (2 : ℝ) ^ q.den ≤ (q : ℝ) := by
  have hnum : (1 : ℤ) ≤ q.num := by
    have : 0 < q.num := Rat.num_pos.mpr hq
    omega
  have hden : (0 : ℝ) < q.den := by positivity
  have hpow : ((q.den : ℕ) : ℝ) ≤ (2 : ℝ) ^ q.den := by
    exact_mod_cast (Nat.lt_two_pow_self (n := q.den)).le
  have hfrac : (1 : ℝ) / q.den ≤ (q.num : ℝ) / q.den := by
    gcongr
    exact_mod_cast hnum
  rw [Rat.cast_def]
  exact le_trans (one_div_le_one_div_of_le hden hpow) hfrac

/-- Every positive rational dominates the dyadic value `2^{-d}` given by its denominator, which
turns rational bounds into dyadic ones. -/
lemma dyadicValue_den_le_rat {q : ℚ} (hq : 0 < q) :
    dyadicValue 1 q.den ≤ ENNReal.ofReal (q : ℝ) := by
  have hdyadic : dyadicValue 1 q.den = ENNReal.ofReal (1 / (2 : ℝ) ^ q.den) := by
    simp only [dyadicValue, Nat.cast_one]
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp
  rw [hdyadic, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact inv_two_pow_den_le_rat hq

/-- One interval-enumeration program, uniform in a rational error parameter.
Only positive parameters are used in the effective-null normal form. -/
def IsRationallyUniformlyEffectiveOpen (U : ℚ → Set CantorSeq) : Prop :=
  ∃ f : ℚ → ℕ → Option BitString,
    Computable (fun p : ℚ × ℕ => f p.1 p.2) ∧
    ∀ q, U q = ⋃ i, (f q i).elim ∅ cantorCylinder

/-- Shifting a uniformly effectively open family by one keeps it uniformly effectively open. -/
lemma IsUniformlyEffectiveOpen.succ {U : ℕ → Set CantorSeq} (h : IsUniformlyEffectiveOpen U) :
    IsUniformlyEffectiveOpen (fun n => U (n + 1)) := by
  rcases h with ⟨f, hcomp, hU⟩
  refine ⟨fun n k => f (n + 1) k, ?_, fun n => hU (n + 1)⟩
  exact Computable.comp hcomp ((Primrec.succ.to_comp.comp Computable.fst).pair Computable.snd)

/-- Shifting the index by one turns the bounds `μ (U n) ≤ 2^{-n}` into strict ones. -/
lemma measure_shift_strict_bound {μ : Measure CantorSeq} {U : ℕ → Set CantorSeq}
    (h_bound : ∀ n, μ (U n) ≤ dyadicValue 1 n) (n : ℕ) :
    μ (U (n + 1)) < dyadicValue 1 n := by
  calc μ (U (n + 1)) ≤ dyadicValue 1 (n + 1) := h_bound (n + 1)
       _ < dyadicValue 1 n := by
          have h1 : dyadicValue 1 (n + 1) = ENNReal.ofReal (1 / (2 : ℝ) ^ (n + 1)) := by
            simp only [dyadicValue, Nat.cast_one]
            rw [ENNReal.ofReal_div_of_pos (by positivity)]
            simp
          have h2 : dyadicValue 1 n = ENNReal.ofReal (1 / (2 : ℝ) ^ n) := by
            simp only [dyadicValue, Nat.cast_one]
            rw [ENNReal.ofReal_div_of_pos (by positivity)]
            simp
          rw [h1, h2, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          rw [one_div_lt_one_div (by positivity) (by positivity)]
          apply pow_lt_pow_right₀ (by norm_num) (by linarith)

-- Problem 69: arbitrary positive rational bounds and the strict dyadic form
/-- Effective nullity may be tested with an effectively open family indexed by positive rationals
whose member for `q` has measure at most `q`. -/
lemma isEffectivelyNull_iff_rational_bound (μ : Measure CantorSeq) (A : Set CantorSeq) :
    IsEffectivelyNull μ A ↔
    ∃ U : ℚ → Set CantorSeq, IsRationallyUniformlyEffectiveOpen U ∧
      (∀ q : ℚ, 0 < q → A ⊆ U q) ∧
      ∀ q : ℚ, 0 < q → μ (U q) ≤ ENNReal.ofReal (q : ℝ) := by
  constructor
  · rintro ⟨U, ⟨f, hf, hUf⟩, hA, hbound⟩
    refine ⟨fun q => U q.den, ?_, ?_, ?_⟩
    · refine ⟨fun q i => f q.den i, ?_, fun q => hUf q.den⟩
      have hden : Computable (fun p : ℚ × ℕ => p.1.den) :=
        computable_ratDen.comp Computable.fst
      exact hf.comp hden Computable.snd
    · intro q hq
      exact fun w hw => Set.mem_iInter.1 (hA hw) q.den
    · intro q hq
      exact (hbound q.den).trans (dyadicValue_den_le_rat hq)
  · rintro ⟨U, ⟨f, hf, hUf⟩, hA, hbound⟩
    refine ⟨fun n => U ((2 : ℚ)⁻¹ ^ n), ?_, ?_, ?_⟩
    · refine ⟨fun n i => f ((2 : ℚ)⁻¹ ^ n) i, ?_, fun n => hUf _⟩
      have hq : Computable (fun p : ℕ × ℕ => (2 : ℚ)⁻¹ ^ p.1) :=
        computable_pow_half.comp Computable.fst
      exact hf.comp (hq.pair Computable.snd)
    · intro w hw
      exact Set.mem_iInter.2 fun n => hA _ (by positivity) hw
    · intro n
      have hb := hbound ((2 : ℚ)⁻¹ ^ n) (by positivity)
      rw [ofReal_pow_half_eq_dyadicValue] at hb
      exact hb

/-- Effective nullity may be tested with strict measure bounds `μ (U n) < 2^{-n}`. -/
lemma isEffectivelyNull_iff_strict_bound (μ : Measure CantorSeq) (A : Set CantorSeq) :
    IsEffectivelyNull μ A ↔
    ∃ U : ℕ → Set CantorSeq, IsUniformlyEffectiveOpen U ∧
      A ⊆ ⋂ n, U n ∧ ∀ n, μ (U n) < dyadicValue 1 n := by
  constructor
  · rintro ⟨U, hU, hA, h_bound⟩
    refine ⟨fun n => U (n + 1), ?_, ?_, ?_⟩
    · exact hU.succ
    · intro w hw
      exact Set.mem_iInter.2 fun n => Set.mem_iInter.1 (hA hw) (n + 1)
    · exact measure_shift_strict_bound h_bound
  · rintro ⟨U, hU, hA, h_bound⟩
    exact ⟨U, hU, hA, fun n => le_of_lt (h_bound n)⟩

/-- A uniform computable stage approximation to partial interval enumerations.
The stability clause makes every pair `(n,i)` approximate one partial-function
value.  The final clause says that the convergence domain in `i` is downward
closed, equivalently an initial segment of `ℕ` or all of `ℕ`. -/
def IsUniformlyInitialSegmentEnumeration
    (f : ℕ → ℕ → ℕ → Option BitString) : Prop :=
  Computable (fun q : (ℕ × ℕ) × ℕ => f q.1.1 q.1.2 q.2) ∧
  (∀ n i s t x, s ≤ t → f n i s = some x → f n i t = some x) ∧
  ∀ n {i j}, i ≤ j → (∃ s, (f n j s).isSome) → ∃ s, (f n i s).isSome

-- Problem 70: initial-segment domains of the partial interval enumerations
/-- Effective nullity may be tested with enumerations whose emissions are stable and indexed by an
initial segment. -/
lemma isEffectivelyNull_iff_initial_segment (μ : Measure CantorSeq) (A : Set CantorSeq) :
    IsEffectivelyNull μ A ↔
    ∃ f : ℕ → ℕ → ℕ → Option BitString, IsUniformlyInitialSegmentEnumeration f ∧
      A ⊆ ⋂ n, stagedCover (f n) ∧
      ∀ n, μ (stagedCover (f n)) ≤ dyadicValue 1 n := by
  constructor
  · rintro ⟨U, ⟨g, hg, hUg⟩, hA, hbound⟩
    refine ⟨fun n => compactStage (g n), ?_, ?_, ?_⟩
    · refine ⟨computable_compactStage hg, ?_, ?_⟩
      · intro n i s t x hst hx
        exact compactStage_stable (g n) hst hx
      · intro n i j hij
        rintro ⟨s, hjs⟩
        exact ⟨s, compactStage_domain_downward (g n) hij hjs⟩
    · intro w hw
      exact Set.mem_iInter.2 fun n => by
        rw [stagedCover_compactStage, ← hUg n]
        exact Set.mem_iInter.1 (hA hw) n
    · intro n
      rw [stagedCover_compactStage, ← hUg n]
      exact hbound n
  · rintro ⟨f, ⟨hf, hstable, hdom⟩, hA, hbound⟩
    refine ⟨fun n => stagedCover (f n), ?_, hA, hbound⟩
    refine ⟨fun n k => f n (Nat.unpair k).1 (Nat.unpair k).2, ?_, ?_⟩
    · have hargs : Computable (fun p : ℕ × ℕ =>
          (((p.1, (Nat.unpair p.2).1), (Nat.unpair p.2).2) : (ℕ × ℕ) × ℕ)) := by
        exact ((Primrec.fst.pair
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp
      exact hf.comp hargs
    · intro n
      ext w
      simp only [stagedCover, Set.mem_iUnion]
      constructor
      · rintro ⟨i, s, his⟩
        exact ⟨Nat.pair i s, by simpa [Nat.unpair_pair] using his⟩
      · rintro ⟨k, hk⟩
        exact ⟨(Nat.unpair k).1, (Nat.unpair k).2, hk⟩

-- Problem 71: Decidable covering families
/-- Effective nullity may be tested with a computable family of decidable string predicates in
place of enumerations. -/
lemma isEffectivelyNull_iff_decidable (μ : Measure CantorSeq) (A : Set CantorSeq) :
    IsEffectivelyNull μ A ↔
    ∃ p : ℕ → BitString → Bool, Computable₂ p ∧
      A ⊆ ⋂ n, ⋃ x, (if p n x then cantorCylinder x else (∅ : Set CantorSeq)) ∧
      ∀ n, μ (⋃ x, (if p n x then cantorCylinder x else (∅ : Set CantorSeq))) ≤
        dyadicValue 1 n := by
  constructor
  · rintro ⟨U, ⟨f, hf, hUf⟩, hA, hbound⟩
    refine ⟨fun n x => decidableCover (f n) x, computable_decidableCover hf, ?_, ?_⟩
    · intro w hw
      exact Set.mem_iInter.2 fun n => by
        rw [decidableCover_iUnion, ← hUf n]
        exact Set.mem_iInter.1 (hA hw) n
    · intro n
      rw [decidableCover_iUnion, ← hUf n]
      exact hbound n
  · rintro ⟨p, hp, hA, hbound⟩
    refine ⟨fun n => ⋃ x, (if p n x then cantorCylinder x else (∅ : Set CantorSeq)),
      ?_, hA, hbound⟩
    refine ⟨fun n i => decidableFamilyEnum (p n) i,
      computable_decidableFamilyEnum hp, ?_⟩
    intro n
    exact (decidableFamilyEnum_iUnion (p n)).symm

end Kolmogorov
