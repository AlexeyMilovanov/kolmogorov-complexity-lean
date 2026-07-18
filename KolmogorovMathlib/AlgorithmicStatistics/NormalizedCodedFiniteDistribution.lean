import KolmogorovMathlib.AlgorithmicStatistics.Stochasticity
import KolmogorovMathlib.Prefix.Properties

/-!
# Normalized coded finite rational distributions

This file adds an extensional layer above `CodedFiniteDistribution`.  The raw
layer remains the canonical list-code representation: repeated points are
allowed there and model complexity is the complexity of that exact list code.

The normalized layer records the usual canonicality conditions for finite
rational models: one entry per point and no zero-mass entries.  The actual
normalizer below combines repeated points by exact rational addition and removes
zero masses, but does not sort the result; it follows the order supplied by
`List.eraseDups` on the list of points.
-/

namespace Kolmogorov

namespace RatMass

/-- The rational mass `0`. -/
def zero : RatMass where
  num := 0
  den := 1
  den_pos := by decide

/-- Exact addition of two represented non-negative rational masses. -/
def add (q r : RatMass) : RatMass where
  num := q.num * r.den + r.num * q.den
  den := q.den * r.den
  den_pos := Nat.mul_pos q.den_pos r.den_pos

@[simp] theorem zero_value : zero.value = 0 := by
  simp [zero, value]

/-- The represented value of exact rational-mass addition. -/
theorem add_value (q r : RatMass) :
    (q.add r).value = q.value + r.value := by
  have hb : (q.den : ENNReal) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hbt : (q.den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hd : (r.den : ENNReal) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  have hdt : (r.den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  unfold RatMass.add RatMass.value
  push_cast
  rw [ENNReal.add_div, mul_comm (r.num : ENNReal) (q.den : ENNReal),
    ENNReal.mul_div_mul_left _ _ hb hbt, ENNReal.mul_div_mul_right _ _ hd hdt]

@[simp] theorem add_num_eq_zero {q r : RatMass} :
    (q.add r).num = 0 ↔ q.num = 0 ∧ r.num = 0 := by
  simp [add, Nat.pos_iff_ne_zero.mp q.den_pos, Nat.pos_iff_ne_zero.mp r.den_pos]

end RatMass

namespace CodedFiniteDistribution

/-- A raw entry has nonzero rational mass when its numerator is nonzero. -/
def EntryNonzero (e : CodedDistributionEntry) : Prop :=
  e.mass.num ≠ 0

/-- No zero-mass entries occur in the raw list. -/
def NoZeroMassEntries (P : CodedFiniteDistribution) : Prop :=
  ∀ e ∈ P.data, EntryNonzero e

/-- The projected point list has no duplicates. -/
def NoDuplicatePoints (P : CodedFiniteDistribution) : Prop :=
  (P.data.map CodedDistributionEntry.point).Nodup

/-- Structural normalization: no duplicate point entries and no zero-mass entries.

Probability normalization is kept as the separate predicate `P.IsProbability`,
so the same structural normal form can also be used for finite semimeasures or
intermediate exact rational mass lists. -/
def Normalized (P : CodedFiniteDistribution) : Prop :=
  P.NoDuplicatePoints ∧ P.NoZeroMassEntries

/-- A normalized probability model is a structurally normalized coded model whose
finite rational masses sum to one. -/
structure NormalizedFiniteDistribution where
  toCoded : CodedFiniteDistribution
  normalized : toCoded.Normalized
  isProbability : toCoded.IsProbability

namespace NormalizedFiniteDistribution

instance : Coe NormalizedFiniteDistribution CodedFiniteDistribution where
  coe P := P.toCoded

/-- The canonical code is still the raw list code of the normalized data. -/
def code (P : NormalizedFiniteDistribution) : BitString :=
  P.toCoded.code

/-- Complexity of a normalized model, measured by its canonical normalized list code. -/
noncomputable def complexity (U : Map) (P : NormalizedFiniteDistribution) : ENat :=
  P.toCoded.complexity U

/-- The mass function exposed by a normalized model. -/
noncomputable def mass (P : NormalizedFiniteDistribution) (x : BitString) : ENNReal :=
  P.toCoded.mass x

theorem isProbability_coe (P : NormalizedFiniteDistribution) :
    (P : CodedFiniteDistribution).IsProbability :=
  P.isProbability

theorem normalized_coe (P : NormalizedFiniteDistribution) :
    (P : CodedFiniteDistribution).Normalized :=
  P.normalized

/-- A normalized probability model can be used anywhere the stochasticity layer
expects a raw coded finite distribution. -/
theorem isStochastic_of_deficiencyLe (U : Map) (x : BitString)
    (P : NormalizedFiniteDistribution) (alpha beta : Nat)
    (hcomp : P.complexity U ≤ (alpha : ENat))
    (hdef : Kolmogorov.DeficiencyLe U (P : CodedFiniteDistribution) x beta) :
    IsStochastic U x alpha beta :=
  isStochastic_of_model U x (P : CodedFiniteDistribution) alpha beta
    P.isProbability hcomp hdef

end NormalizedFiniteDistribution

/-! ### Normalization construction -/

/-- Sum all rational masses in `data` whose point is `x`. -/
def combinePointMass (x : BitString) :
    List CodedDistributionEntry → RatMass
  | [] => RatMass.zero
  | e :: es =>
      if e.point = x then e.mass.add (combinePointMass x es)
      else combinePointMass x es

/-
The represented value of `combinePointMass x data` equals the total mass at
`x` recorded by the raw list.
-/
theorem combinePointMass_value (x : BitString) (data : List CodedDistributionEntry) :
    (combinePointMass x data).value =
      data.foldr (fun e acc => (if e.point = x then e.mass.value else 0) + acc) 0 := by
  induction data with
  | nil => exact RatMass.zero_value
  | cons e data ih =>
    by_cases h : e.point = x <;> simp +decide [h]
    · convert RatMass.add_value e.mass ( combinePointMass x data ) using 1
      · exact congr_arg RatMass.value
          ( by rw [ show combinePointMass x ( e :: data ) = e.mass.add ( combinePointMass x data )
                    from if_pos h ] )
      · rw [ ih ]
    · grind +locals

/-- The mass at `x` equals the combined-mass value of the raw data. -/
theorem mass_eq_combinePointMass (P : CodedFiniteDistribution) (x : BitString) :
    P.mass x = (combinePointMass x P.data).value :=
  (combinePointMass_value x P.data).symm

/-- Build the single normalized entry for `x`, unless the combined mass is zero. -/
def normalizedEntry? (data : List CodedDistributionEntry) (x : BitString) :
    Option CodedDistributionEntry :=
  let q := combinePointMass x data
  if q.num = 0 then none else some { point := x, mass := q }

/-- Combine repeated points by exact rational addition and remove zero-mass
entries.  No sorting is performed. -/
def normalizeData (data : List CodedDistributionEntry) :
    List CodedDistributionEntry :=
  ((data.map CodedDistributionEntry.point).eraseDups).filterMap
    (normalizedEntry? data)

/-- Normalize a raw coded finite distribution by combining repeated points and
dropping zero-mass entries. -/
def normalize (P : CodedFiniteDistribution) : CodedFiniteDistribution where
  data := normalizeData P.data

@[simp] theorem normalize_data (P : CodedFiniteDistribution) :
    P.normalize.data = normalizeData P.data := rfl

/-
Normalization removes duplicate point entries.
-/
theorem normalize_noDuplicatePoints (P : CodedFiniteDistribution) :
    P.normalize.NoDuplicatePoints := by
  -- Let's unfold the definition of `normalizeNoDuplicatePoints`.
  unfold NoDuplicatePoints at *; simp_all +decide [ normalizeData ] ;
  rw [ List.nodup_map_iff_inj_on ];
  · unfold normalizedEntry?; aesop;
  · apply List.Nodup.filterMap;
    · unfold normalizedEntry?; aesop;
    · -- By definition of `List.eraseDupsBy.loop`, the resulting list is nodup.
      have h_loop_nodup : ∀ (l : List BitString) (acc : List BitString), List.Nodup acc →
          List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
        intros l acc hacc
        induction l generalizing acc with
        | nil => simp_all +decide [ List.eraseDupsBy.loop ]
        | cons hd tl ih =>
          simp_all +decide [ List.eraseDupsBy.loop ]
          cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide
          exact ih _ ( List.nodup_cons.mpr ⟨ fun hx => h _ hx rfl, hacc ⟩ )
      exact h_loop_nodup _ _ ( by simp +decide )

/-
Normalization removes entries whose exact rational mass is zero.
-/
theorem normalize_noZeroMassEntries (P : CodedFiniteDistribution) :
    P.normalize.NoZeroMassEntries := by
  intro e he; unfold CodedFiniteDistribution.normalize at he; simp_all +decide;
  unfold normalizeData at he; simp_all +decide [ List.mem_filterMap ] ;
  unfold normalizedEntry? at he; aesop;

/-- The output of `normalize` is structurally normalized. -/
theorem normalize_normalized (P : CodedFiniteDistribution) :
    P.normalize.Normalized :=
  ⟨P.normalize_noDuplicatePoints, P.normalize_noZeroMassEntries⟩

/-
Combining repeated entries preserves the represented mass at every point.
-/
theorem normalize_mass (P : CodedFiniteDistribution) (x : BitString) :
    P.normalize.mass x = P.mass x := by
  unfold CodedFiniteDistribution.mass;
  have h_foldr_eq : ∀ (l : List BitString), List.foldr
      (fun y acc => (if y = x then (combinePointMass x P.data).value else 0) + acc) 0
          (List.eraseDups l) = (if x ∈ l then (combinePointMass x P.data).value else 0) := by
    intro l;
    induction l using List.reverseRecOn with
    | nil => simp_all +decide
    | append_singleton l ih _ =>
      simp_all +decide [ List.eraseDups_append ]
      simp_all +decide [ List.removeAll ]
      by_cases h : ih ∈ l <;> simp_all +decide
      · grind
      · simp_all +decide [ List.eraseDups_cons ]
        split_ifs at * <;> simp_all +decide
        convert congr_arg ( fun y => y + ( combinePointMass x P.data ).value ) ‹List.foldr
            ( fun y acc => ( if y = x then ( combinePointMass x P.data ).value else 0 ) + acc ) 0
                l.eraseDups = 0› using 1
        · induction l.eraseDups <;> simp +decide [ * ]
          rw [ add_assoc ]
        · rw [ zero_add ]
  convert h_foldr_eq ( P.data.map CodedDistributionEntry.point ) using 1;
  · rw [ CodedFiniteDistribution.normalize_data, normalizeData ];
    have h_filterMap_eq : ∀ (l : List BitString), List.foldr
        (fun y acc => (if y = x then (combinePointMass x P.data).value else 0) + acc) 0 l =
            List.foldr (fun e acc => (if e.point = x then e.mass.value else 0) + acc) 0
                (List.filterMap (normalizedEntry? P.data) l) := by
      intro l; induction l <;> simp +decide [ * ] ;
      simp +decide [ List.filterMap_cons, normalizedEntry? ];
      split_ifs <;> simp_all +decide [ RatMass.value ];
    grind;
  · rw [ ← combinePointMass_value ];
    split_ifs <;> simp_all +decide [ List.mem_map ];
    have h_combine_zero : ∀ (l : List CodedDistributionEntry), (∀ e ∈ l,
                                                                 e.point ≠
                                                                     x) → combinePointMass x l =
                                                                         RatMass.zero := by
      intros l hl; induction l <;> simp_all +decide [ combinePointMass ] ;
    rw [ h_combine_zero _ ‹_›, RatMass.zero_value ]

/-
Normalization preserves the probability condition.
-/
theorem normalize_isProbability {P : CodedFiniteDistribution}
    (hP : P.IsProbability) : P.normalize.IsProbability := by
  refine Eq.trans ?_ hP;
  rw [ Finset.sum_subset ( show P.normalize.support ⊆ P.support from ?_ ) ?_ ];
  · exact Finset.sum_congr rfl fun x hx => normalize_mass P x;
  · intro x hx; simp_all +decide [ mem_support_iff ] ;
    obtain ⟨ a, ha, rfl ⟩ := hx;
    have h_mem : a.point ∈ P.data.map CodedDistributionEntry.point := by
      have h_mem : a.point ∈ (P.data.map CodedDistributionEntry.point).eraseDups := by
        unfold normalizeData at ha; simp_all +decide [ List.mem_filterMap ] ;
        unfold normalizedEntry? at ha; aesop;
      have h_mem : ∀ (l : List BitString), a.point ∈ List.eraseDups l → a.point ∈ l := by
        intros l hl
        induction l using List.reverseRecOn <;> simp_all +decide [ List.eraseDups_append ] ;
        simp_all +decide [ List.removeAll ];
        grind;
      exact h_mem _ ‹_›;
    aesop;
  · intros x hx hx';
    contrapose! hx';
    convert mem_support_iff _ _ |>.2 _;
    contrapose! hx';
    convert mass_eq_combinePointMass _ _ using 1;
    have h_combine_zero : ∀ (l : List CodedDistributionEntry), (∀ e ∈ l,
                                                                 e.point ≠
                                                                     x) → combinePointMass x l =
                                                                         RatMass.zero := by
      intros l hl; induction l <;> simp_all +decide [ combinePointMass ] ;
    rw [ h_combine_zero _ fun e he => by aesop ] ; norm_num [ RatMass.zero_value ]

/-- Package a raw probability model as a normalized probability model. -/
def normalizedFiniteDistributionOfProbability (P : CodedFiniteDistribution)
    (hP : P.IsProbability) : NormalizedFiniteDistribution where
  toCoded := P.normalize
  normalized := normalize_normalized P
  isProbability := normalize_isProbability hP

/-- Deficiency bounds are unchanged by normalization, provided the conditional
program complexity is compared against the normalized code explicitly. -/
theorem deficiencyLe_normalize_of_mass_preserved (U : Map)
    (P : CodedFiniteDistribution) (x : BitString) (beta : Nat)
    (hKP :
      complexityWeight (KP U x P.normalize.code) ≤
        complexityWeight (KP U x P.code))
    (hdef : Kolmogorov.DeficiencyLe U P x beta) :
    Kolmogorov.DeficiencyLe U P.normalize x beta := by
  unfold Kolmogorov.DeficiencyLe CodedFiniteDistribution.DeficiencyLe at *
  rw [normalize_mass P x]
  exact le_trans hKP hdef

/-- A raw stochasticity witness can be replaced by its normalized mass-equivalent
model once the normalized model satisfies the requested complexity and
conditional-code bounds. -/
theorem isStochastic_normalize_of_model (U : Map) (x : BitString)
    (P : CodedFiniteDistribution) (alpha beta : Nat)
    (hprob : P.IsProbability)
    (hcomp : P.normalize.complexity U ≤ (alpha : ENat))
    (hKP :
      complexityWeight (KP U x P.normalize.code) ≤
        complexityWeight (KP U x P.code))
    (hdef : Kolmogorov.DeficiencyLe U P x beta) :
    IsStochastic U x alpha beta :=
  isStochastic_of_model U x P.normalize alpha beta
    (normalize_isProbability hprob) hcomp
    (deficiencyLe_normalize_of_mass_preserved U P x beta hKP hdef)

def decodeNatCode (z : BitString) : Nat := (z.takeWhile id).length

@[simp] lemma decodeNatCode_natCode (n : Nat) : decodeNatCode (natCode n) = n := by
  simp [decodeNatCode, natCode]

def decodeRatMass (w : BitString) : RatMass :=
  { num := decodeNatCode (decodeFirst w),
    den := max 1 (decodeNatCode (decodeSecond w)),
    den_pos := by omega }

def decodeDistributionEntry (w : BitString) : CodedDistributionEntry :=
  { point := decodeFirst w,
    mass := decodeRatMass (decodeSecond w) }

def decodeDistributionDataAux : Nat → BitString → List CodedDistributionEntry
  | 0, _ => []
  | _, [] => []
  | _, false :: _ => []
  | n + 1, true :: w =>
      decodeDistributionEntry (decodeFirst w) :: decodeDistributionDataAux n (decodeSecond w)

def decodeDistributionData (w : BitString) : List CodedDistributionEntry :=
  decodeDistributionDataAux w.length w

def decodeCodedFiniteDistribution (w : BitString) : CodedFiniteDistribution :=
  { data := decodeDistributionData w }

theorem decodeRatMass_code (q : RatMass) : decodeRatMass (RatMass.code q) = q := by
  cases q with
  | mk num den den_pos =>
      simp [decodeRatMass, RatMass.code, decodeFirst_pairCode, decodeSecond_pairCode,
        Nat.max_eq_right (Nat.succ_le_of_lt den_pos)]

theorem decodeDistributionEntry_code (e : CodedDistributionEntry) :
    decodeDistributionEntry (CodedDistributionEntry.code e) = e := by
  cases e with
  | mk point mass =>
      simp [decodeDistributionEntry, CodedDistributionEntry.code, decodeFirst_pairCode,
        decodeSecond_pairCode, decodeRatMass_code]

theorem decodeDistributionDataAux_code (data : List CodedDistributionEntry) (k : Nat) :
    decodeDistributionDataAux ((codedDistributionDataCode data).length + k)
      (codedDistributionDataCode data) = data := by
  induction data generalizing k with
  | nil =>
      simp [decodeDistributionDataAux, codedDistributionDataCode]
  | cons e es ih =>
      rw [show (codedDistributionDataCode (e :: es)).length + k =
          (e.code.length + 1 + e.code.length + (codedDistributionDataCode es).length + k) + 1 by
        simp [codedDistributionDataCode, pairCode]
        omega]
      unfold decodeDistributionDataAux
      simp [codedDistributionDataCode, decodeFirst_pairCode, decodeSecond_pairCode,
        decodeDistributionEntry_code]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (e.code.length + 1 + e.code.length + k)

theorem decodeDistributionData_code (data : List CodedDistributionEntry) :
    decodeDistributionData (codedDistributionDataCode data) = data := by
  simpa [decodeDistributionData] using decodeDistributionDataAux_code data 0

theorem decodeCodedFiniteDistribution_code (P : CodedFiniteDistribution) :
    decodeCodedFiniteDistribution P.code = P := by
  cases P
  simp [decodeCodedFiniteDistribution, code, decodeDistributionData_code]

/-! ### Computability of the code-level normalizer

We prove `normalizeCode` is computable by showing each stage is primitive
recursive and converting with `Primrec.to_comp`.  Recall
`normalizeCode = codedDistributionDataCode ∘ normalizeData ∘ decodeDistributionData`. -/

/-- The unary natural-number decoder `(z.takeWhile id).length` is primitive recursive. -/
theorem decodeNatCode_primrec : Primrec decodeNatCode :=
  Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)

/-- The first-component decoder is primitive recursive. -/
theorem decodeFirst_primrec : Primrec decodeFirst := by
  have hlen : Primrec (fun z : BitString => (z.takeWhile id).length) :=
    Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)
  have hdrop : Primrec (fun z : BitString => z.drop ((z.takeWhile id).length + 1)) :=
    primrec_list_drop.comp Primrec.id (Primrec.succ.comp hlen)
  exact (primrec_list_take.comp hdrop hlen).of_eq (fun _ => rfl)

/-- The second-component decoder is primitive recursive. -/
theorem decodeSecond_primrec : Primrec decodeSecond := by
  have hlen : Primrec (fun z : BitString => (z.takeWhile id).length) :=
    Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)
  have hdrop : Primrec
      (fun z : BitString => z.drop (((z.takeWhile id).length + 1) + (z.takeWhile id).length)) :=
    primrec_list_drop.comp Primrec.id (Primrec.nat_add.comp (Primrec.succ.comp hlen) hlen)
  exact hdrop.of_eq (fun _ => rfl)

/-
Exact rational-mass addition is primitive recursive.
-/
theorem ratMass_add_primrec : Primrec₂ RatMass.add := by
  have h_add : Primrec (fun p : RatMass × RatMass => ⟨(p.1.num * p.2.den + p.2.num * p.1.den,
                                                        p.1.den * p.2.den), by
    exact Nat.mul_pos p.1.den_pos p.2.den_pos⟩ : RatMass × RatMass → {p : ℕ × ℕ // 0 < p.2}) := by
    refine Primrec.subtype_mk ?_
    exact Primrec.pair
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (ratMass_num_primrec.comp Primrec.fst)
          (ratMass_den_primrec.comp Primrec.snd))
        (Primrec.nat_mul.comp (ratMass_num_primrec.comp Primrec.snd)
          (ratMass_den_primrec.comp Primrec.fst)))
      (Primrec.nat_mul.comp (ratMass_den_primrec.comp Primrec.fst)
        (ratMass_den_primrec.comp Primrec.snd))
  generalize_proofs at *
  convert Primrec.of_equiv_symm.comp h_add using 1

/-
The rational-mass decoder is primitive recursive.
-/
theorem decodeRatMass_primrec : Primrec decodeRatMass := by
  refine Primrec.of_eq (f := fun w => ⟨ decodeNatCode ( decodeFirst w ),
                                        max 1 ( decodeNatCode ( decodeSecond w ) ), by positivity
                                            ⟩) ?_ ?_
  · convert Primrec.of_equiv_symm.comp _ using 1;
    rotate_left;
    exact fun w =>
        ⟨ ( decodeNatCode ( decodeFirst w ), max 1 ( decodeNatCode ( decodeSecond w ) ) ),
            by simp +decide ⟩;
    · refine Primrec.subtype_mk ?_;
      exact Primrec.pair ( decodeNatCode_primrec.comp decodeFirst_primrec )
          ( Primrec.nat_max.comp ( Primrec.const 1 ) ( decodeNatCode_primrec.comp
                                                       decodeSecond_primrec ) );
    · exact funext fun _ => rfl;
  · aesop

/-
The entry decoder is primitive recursive.
-/
theorem decodeDistributionEntry_primrec : Primrec decodeDistributionEntry := by
  refine Primrec.of_eq (f := fun w => ⟨ decodeFirst w, decodeRatMass ( decodeSecond w ) ⟩) ?_ ?_
  · convert Primrec.of_equiv_symm.comp
      ( Primrec.pair ( decodeFirst_primrec ) ( decodeRatMass_primrec.comp decodeSecond_primrec ) )
          using 1;
  · aesop

/-- One forward step of the fuelled list decoder: consume one `true`-led entry
and append it to the accumulator, otherwise stop (identity). -/
def ddStep (s : BitString × List CodedDistributionEntry) :
    BitString × List CodedDistributionEntry :=
  match s.1 with
  | true :: w' => (decodeSecond w', s.2 ++ [decodeDistributionEntry (decodeFirst w')])
  | _ => s

/-
The fuelled list decoder equals the second component of `ddStep` iterated
`n` times from `(w, acc)`.
-/
theorem decodeDistributionDataAux_eq_iter (n : Nat) (w : BitString)
    (acc : List CodedDistributionEntry) :
    (Nat.rec (motive := fun _ => BitString × List CodedDistributionEntry) (w, acc)
        (fun _ s => ddStep s) n).2 = acc ++ decodeDistributionDataAux n w := by
          induction n generalizing w acc with
          | zero => simp +decide [ decodeDistributionDataAux ]
          | succ n ih =>
            convert ih ( ddStep ( w, acc ) |>.1 ) ( ddStep ( w, acc ) |>.2 ) using 1
            · congr! 1
              exact Nat.recOn n rfl fun n ih => by aesop
            · cases w <;> simp +decide [ ddStep ]
              · cases n <;> rfl
              · cases ‹Bool› <;> simp +decide [ decodeDistributionDataAux ]
                cases n <;> rfl

/-- The list decoder as a `Nat.rec` iteration suitable for `Primrec.nat_rec'`. -/
theorem decodeDistributionData_eq_iter (w : BitString) :
    decodeDistributionData w =
      (Nat.rec (motive := fun _ => BitString × List CodedDistributionEntry) (w, [])
        (fun _ s => ddStep s) w.length).2 := by
  have := decodeDistributionDataAux_eq_iter w.length w []
  rw [List.nil_append] at this
  rw [decodeDistributionData, this]

/-
One forward decoding step is primitive recursive.
-/
theorem ddStep_primrec : Primrec ddStep := by
  refine Primrec.of_eq
      (f := fun s => if s.1 = [] then s else if s.1.head? = some true then ( decodeSecond
                                                                             ( s.1.tail! ), s.2 ++
          [ decodeDistributionEntry ( decodeFirst ( s.1.tail! ) ) ] ) else s) ?_ ?_
  · refine Primrec.of_eq
      (f := fun s => if s.1 = [] then s else if s.1.head? = some true then ( decodeSecond
                                                                             ( s.1.tail! ), s.2 ++
          [ decodeDistributionEntry ( decodeFirst ( s.1.tail! ) ) ] ) else s) ?_ ?_
    · refine Primrec.ite ?_ ?_ ?_;
      · convert Primrec.eq.comp ( Primrec.fst ) ( Primrec.const [] ) using 1;
      · exact Primrec.id;
      · refine Primrec.ite ?_ ?_ ?_;
        · convert Primrec.eq.comp ( Primrec.list_head? |> Primrec.comp <| Primrec.fst )
            ( Primrec.const ( some true ) ) using 1;
        · refine Primrec.pair ?_ ?_;
          · convert decodeSecond_primrec.comp ( Primrec.list_tail.comp ( Primrec.fst ) ) using 1;
          · refine Primrec.list_append.comp ?_ ?_;
            · exact Primrec.snd;
            · exact Primrec.list_cons.comp
                ( decodeDistributionEntry_primrec.comp ( decodeFirst_primrec.comp
                                                         ( Primrec.list_tail.comp ( Primrec.fst ) )
                                                             ) ) ( Primrec.const [] );
        · exact Primrec.id;
    · exact fun _ => rfl;
  · -- By definition of `ddStep`, we can split into cases based on the first element of the pair.
    intro n
    obtain ⟨w, l⟩ := n
    rcases w with _ | ⟨b, w'⟩
    · rfl
    · cases b <;> rfl

/-
The full list decoder is primitive recursive.
-/
theorem decodeDistributionData_primrec : Primrec decodeDistributionData := by
  rw [ show decodeDistributionData = _ from funext fun w => decodeDistributionData_eq_iter w ];
  refine Primrec.snd.comp ?_;
  convert Primrec.nat_rec' _ _ _ using 1;
  rotate_left;
  exact fun w => List.length w;
  exact fun w => ( w, [] );
  exact fun w p => ddStep p.2;
  · exact Primrec.list_length;
  · exact Primrec.pair Primrec.id ( Primrec.const [] );
  · exact ddStep_primrec.comp ( Primrec.snd.comp Primrec.snd );
  · rfl

/-
Combining the masses at a fixed point is primitive recursive.
-/
theorem combinePointMass_primrec :
    Primrec₂ (fun x data => combinePointMass x data) := by
      convert Primrec.list_rec _ _ _ using 1;
      rotate_left;
      exact BitString × List CodedDistributionEntry;
      exact CodedDistributionEntry;
      exact RatMass;
      all_goals try infer_instance;
      exact fun p => p.2;
      exact fun p => RatMass.zero;
      exact fun p q => if q.1.point = p.1 then q.1.mass.add q.2.2 else q.2.2;
      · exact Primrec.snd;
      · exact Primrec.const RatMass.zero;
      · refine Primrec.ite ?_ ?_ ?_;
        · convert Primrec.eq.comp ( entry_point_primrec.comp ( Primrec.fst.comp ( Primrec.snd ) ) )
            ( Primrec.fst.comp ( Primrec.fst ) ) using 1;
        · exact ratMass_add_primrec.comp
            ( entry_mass_primrec.comp ( Primrec.fst.comp ( Primrec.snd ) ) )
                ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) );
        · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) );
      · constructor <;> intro h;
        · convert h.comp ( Primrec.fst ) ( Primrec.snd ) using 1;
          ext ⟨x, data⟩; induction data <;> simp +decide [ *, combinePointMass ] ;
        · convert h using 1;
          constructor <;> intro h <;> rw [ Primrec₂ ] at *;
          · assumption;
          · convert h using 1;
            ext ⟨x, data⟩; induction data <;> simp +decide [ *, combinePointMass ] ;

/-
`eraseDups` on bit-string lists, written as a left fold.
-/
theorem eraseDups_bitstring_eq_foldl (l : List BitString) :
    l.eraseDups = l.foldl (fun acc a => if a ∈ acc then acc else acc ++ [a]) [] := by
      induction l using List.reverseRecOn with
      | nil => simp +decide [ * ]
      | append_singleton l ih _ =>
        simp +decide [ *, List.eraseDups_append ]
        simp +decide [ List.removeAll ]
        split_ifs <;> simp_all +decide [ List.filter_cons ]
        · have h_foldl : ∀ (l : List BitString) (acc : List BitString), ih ∈ List.foldl
            (fun acc a => if a ∈ acc then acc else acc ++ [a]) acc l → ih ∈ acc ∨ ih ∈ l := by
            intros l acc h; induction l using List.reverseRecOn <;> aesop
          grind
        · split_ifs <;> simp_all +decide [ List.eraseDups_cons ]
          rename_i h₁ h₂ h₃
          have h_foldl : ∀ (l : List BitString) (acc : List BitString), ih ∈ l → ih ∈ List.foldl
              (fun acc a => if a ∈ acc then acc else acc ++ [a]) acc l := by
            intros l acc h; induction l using List.reverseRecOn <;> aesop
          exact h₂ <| h_foldl _ _ h₃

/-
List membership of bit strings is a primitive-recursive predicate.
-/
theorem mem_bitstring_primrec :
    PrimrecPred (fun p : BitString × List BitString => p.1 ∈ p.2) := by
      refine ⟨ ?_, ?_ ⟩;
      exact fun _ => inferInstance;
      have h_mem : Primrec (fun p : BitString × List BitString => List.idxOf p.1 p.2) := by
        convert Primrec.list_idxOf.comp ( Primrec.fst ) ( Primrec.snd ) using 1;
        convert rfl;
        infer_instance;
      convert Primrec.nat_lt.comp ( h_mem ) ( Primrec.list_length.comp ( Primrec.snd ) ) using 1;
      simp +decide [ PrimrecPred, List.idxOf_lt_length_iff ]

/-
`eraseDups` on bit-string lists is primitive recursive.
-/
theorem eraseDups_bitstring_primrec :
    Primrec (fun l : List BitString => l.eraseDups) := by
      rw [ show ( fun l : List BitString => l.eraseDups ) = fun l => l.foldl ( fun acc a => if a ∈
                                                                               acc then acc else
                                                                                   acc ++ [ a ]
                                                                                       ) [ ] from
                                                                                           funext
                                                                                 fun l =>
                                                                                     eraseDups_bitstring_eq_foldl l ];
      convert Primrec.list_foldl ( Primrec.id ) ( Primrec.const [] ) _ using 1;
      rotate_left;
      exact fun l p => if p.2 ∈ p.1 then p.1 else p.1 ++ [ p.2 ];
      · convert Primrec.ite _ _ _ using 1;
        · convert mem_bitstring_primrec.comp
            ( Primrec.snd.comp ( Primrec.snd ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd )
                ) using 1;
        · exact Primrec.fst.comp ( Primrec.snd );
        · exact Primrec.list_append.comp ( Primrec.fst.comp ( Primrec.snd ) )
            ( Primrec.list_cons.comp ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.const [] ) );
      · rfl

/-
Building the normalized entry at a point is primitive recursive.
-/
theorem normalizedEntry?_primrec :
    Primrec₂ (fun data x => normalizedEntry? data x) := by
      have h_swap : Primrec₂ (fun data x => combinePointMass x data) := by
        convert combinePointMass_primrec.comp ( Primrec.snd ) ( Primrec.fst ) using 1;
      convert Primrec.ite _ _ _ using 1;
      · convert Primrec.eq.comp
          ( ratMass_num_primrec.comp ( h_swap.comp ( Primrec.fst ) ( Primrec.snd ) ) )
              ( Primrec.const 0 ) using 1;
      · exact Primrec.const none;
      · convert Primrec.option_some.comp
          ( Primrec.of_equiv_symm.comp ( Primrec.pair ( Primrec.snd ) ( h_swap ) ) ) using 1

/-
The list normalizer is primitive recursive.
-/
theorem normalizeData_primrec : Primrec normalizeData := by
  have h_swap : Primrec₂ (fun data x => normalizedEntry? data x) := normalizedEntry?_primrec
  convert Primrec.listFilterMap _ h_swap using 1;
  convert eraseDups_bitstring_primrec.comp
      ( Primrec.list_map Primrec.id ( entry_point_primrec.comp ( Primrec.snd ) |> Primrec.to₂ ) )
          using 1

/-- The bitstring transformer induced by normalization on canonical codes.  On
non-distribution codes the value is arbitrary; the complexity theorem only uses
it on codes of actual `CodedFiniteDistribution`s. -/
def normalizeCode (w : BitString) : BitString :=
  (decodeCodedFiniteDistribution w).normalize.code

theorem normalizeCode_code (P : CodedFiniteDistribution) :
    normalizeCode P.code = P.normalize.code := by
  unfold normalizeCode
  rw [decodeCodedFiniteDistribution_code]

/-- `normalizeCode` is primitive recursive. -/
theorem normalizeCode_primrec : Primrec normalizeCode :=
  (codedDistributionDataCode_primrec.comp
    (normalizeData_primrec.comp decodeDistributionData_primrec)).of_eq (fun _ => rfl)

/-- The code-level normalizer is computable.  Mathematically, this is the
effective parser/normalizer for canonical finite rational distribution codes:
decode the raw list, combine equal points by exact rational arithmetic, remove
zero masses, and re-encode the normalized list. -/
theorem normalizeCode_computable : Computable normalizeCode :=
  normalizeCode_primrec.to_comp

/-- Normalization changes model complexity by at most an additive constant for
an optimal prefix machine. -/
theorem normalize_complexity_le_add_const (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P : CodedFiniteDistribution,
      P.normalize.complexity U ≤ P.complexity U + (c : ENat) := by
  obtain ⟨c, hc⟩ := KPPlain_map_le U hU normalizeCode normalizeCode_computable
  refine ⟨c, ?_⟩
  intro P
  unfold complexity
  rw [← normalizeCode_code P]
  exact hc P.code

/-- Every raw coded finite probability model has a normalized representative
with the same mass function and only `O(1)` extra model complexity. -/
theorem exists_normalized_probability_complexity_le_add_const (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : Nat, ∀ P : CodedFiniteDistribution, P.IsProbability →
      ∃ Q : NormalizedFiniteDistribution,
        (∀ x : BitString, Q.mass x = P.mass x) ∧
        Q.complexity U ≤ P.complexity U + (c : ENat) := by
  obtain ⟨c, hc⟩ := normalize_complexity_le_add_const U hU
  refine ⟨c, ?_⟩
  intro P hP
  refine ⟨normalizedFiniteDistributionOfProbability P hP, ?_, ?_⟩
  · intro x
    exact normalize_mass P x
  · exact hc P

end CodedFiniteDistribution

end Kolmogorov
