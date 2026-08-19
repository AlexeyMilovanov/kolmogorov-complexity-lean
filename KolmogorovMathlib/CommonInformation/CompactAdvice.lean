import KolmogorovMathlib.CommonInformation.ConditionalCounting

/-!
# Common Information: the compact two-parameter conditional-description stream

SUV Theorem 223 needs, as the third advice list, the family of encoded pairs
`(z, v)` with `C(z) < α` and `C(v | z) < β`.  In the space of *encoded* pairs
this family has only about `2^(α+β)` elements — the "descriptive volume" — which
is what yields the sharp `C(x,y) ≤ 3n + O(log n)` bound.  This is strictly
smaller (exponent `α + β + 2` rather than `3τ`) than the three-parameter
`commonWitnessPairsLe` relation of `Counting.lean`, which counts pairs `(x, y)`
and must **not** be used as the compact advice object.

This file provides:

* the noncomputable semantic finset `conditionalDescriptionPairsLe`, with exact
  membership `mem_conditionalDescriptionPairsLe_iff` and the decisive cardinality
  bound `card_conditionalDescriptionPairsLe_lt`;
* a prefix-monotone, nodup, computable staged enumeration
  `conditionalDescriptionPairsStage` with exact eventual semantics
  `mem_conditionalDescriptionPairsStage_eventually_iff`;
* a generic finite-completion lemma `exists_stage_toFinset_eq` and its
  instantiation `exists_conditionalDescriptionPairsStage_complete`, giving a
  finite stage whose `toFinset` is exactly the semantic relation.

Everything is a two-level analogue of the three-parameter common-witness
enumeration in `ConditionalCounting.lean`, reusing `conditionalOutputSnapshot`,
its soundness/completeness/monotonicity, and the primitive-recursive list
combinators.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### The semantic finset and its cardinality -/

/-- The semantic relation of encoded pairs `pairCode z v` with `C(z) ≤ α` and
`C(v | z) ≤ β`. -/
noncomputable def conditionalDescriptionPairsLe
    (V : Map) (α β : Nat) : Finset BitString :=
  (compressibleWords V [] α).biUnion fun z =>
    (compressibleWords V z β).image fun v => pairCode z v

/-- Exact semantic membership in `conditionalDescriptionPairsLe`. -/
theorem mem_conditionalDescriptionPairsLe_iff
    (V : Map) (α β : Nat) (w : BitString) :
    w ∈ conditionalDescriptionPairsLe V α β ↔
      ∃ z v, w = pairCode z v ∧
        plainK V z ≤ (α : ENat) ∧ condK V v z ≤ (β : ENat) := by
  rw [conditionalDescriptionPairsLe, Finset.mem_biUnion]
  constructor
  · rintro ⟨z, hz, hw⟩
    rw [Finset.mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨z, v, rfl, (mem_compressibleWords_iff V [] z α).mp hz,
      (mem_compressibleWords_iff V z v β).mp hv⟩
  · rintro ⟨z, v, rfl, hz, hv⟩
    refine ⟨z, (mem_compressibleWords_iff V [] z α).mpr hz, ?_⟩
    rw [Finset.mem_image]
    exact ⟨v, (mem_compressibleWords_iff V z v β).mpr hv, rfl⟩

/-- **The decisive `2τ` cardinality bound.** The compact relation has fewer than
`2^((α+1)+(β+1))` elements — exponent `α + β + 2`, not `3τ`. -/
theorem card_conditionalDescriptionPairsLe_lt
    (V : Map) (α β : Nat) :
    (conditionalDescriptionPairsLe V α β).card <
      2 ^ ((α + 1) + (β + 1)) := by
  unfold conditionalDescriptionPairsLe
  have hα := cardCompressibleWordsLt V [] α
  have hEach :
      ∀ z ∈ compressibleWords V [] α,
        ((compressibleWords V z β).image fun v => pairCode z v).card ≤
          2 ^ (β + 1) := by
    intro z _
    calc ((compressibleWords V z β).image fun v => pairCode z v).card
        ≤ (compressibleWords V z β).card := Finset.card_image_le
      _ ≤ 2 ^ (β + 1) := (cardCompressibleWordsLt V z β).le
  calc
    ((compressibleWords V [] α).biUnion fun z =>
        (compressibleWords V z β).image fun v => pairCode z v).card
        ≤ ∑ z ∈ compressibleWords V [] α,
            ((compressibleWords V z β).image fun v => pairCode z v).card :=
      Finset.card_biUnion_le
    _ ≤ (compressibleWords V [] α).card * 2 ^ (β + 1) :=
      Finset.sum_le_card_nsmul _ _ _ hEach
    _ < 2 ^ (α + 1) * 2 ^ (β + 1) :=
      Nat.mul_lt_mul_of_pos_right hα (Nat.pow_pos (by norm_num))
    _ = 2 ^ ((α + 1) + (β + 1)) := by rw [← pow_add]

/-! ### The staged computable enumeration -/

/-- At one finite stage, enumerate every encoded pair `pairCode z v` for a
currently visible `z` (via an `α`-bounded unconditional program) and a currently
visible `v` (via a `β`-bounded program conditional on that `z`). -/
def conditionalDescriptionPairsSnapshot
    (c : Code) (α β t : Nat) : List BitString :=
  (conditionalOutputSnapshot c [] α t).flatMap fun z =>
    (conditionalOutputSnapshot c z β t).map fun v => pairCode z v

/-- Prefix-monotone accumulation of the finite snapshots, with duplicates
removed so that a finite semantic range forces eventual stabilization. -/
def conditionalDescriptionPairsStage
    (c : Code) (α β : Nat) : Nat → List BitString
  | 0 => (conditionalDescriptionPairsSnapshot c α β 0).eraseDups
  | t + 1 =>
      (conditionalDescriptionPairsStage c α β t ++
        conditionalDescriptionPairsSnapshot c α β (t + 1)).eraseDups

theorem conditionalDescriptionPairsStage_nodup
    (c : Code) (α β t : Nat) :
    (conditionalDescriptionPairsStage c α β t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

theorem conditionalDescriptionPairsStage_prefix
    (c : Code) (α β t : Nat) :
    conditionalDescriptionPairsStage c α β t <+:
      conditionalDescriptionPairsStage c α β (t + 1) := by
  rw [conditionalDescriptionPairsStage]
  exact prefix_eraseDups_append_of_nodup _ _
    (conditionalDescriptionPairsStage_nodup c α β t)

/-- Compact-advice stages are prefix-monotone between any two ordered times. -/
theorem conditionalDescriptionPairsStage_prefix_of_le
    (c : Code) (α β : Nat) {s t : Nat} (hst : s ≤ t) :
    conditionalDescriptionPairsStage c α β s <+:
      conditionalDescriptionPairsStage c α β t := by
  induction hst with
  | refl => exact List.prefix_refl _
  | step _ ih =>
      exact ih.trans (conditionalDescriptionPairsStage_prefix c α β _)

/-! ### Soundness -/

theorem mem_conditionalDescriptionPairsSnapshot_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {α β t : Nat} {w : BitString}
    (hw : w ∈ conditionalDescriptionPairsSnapshot c α β t) :
    ∃ z v, w = pairCode z v ∧
      plainK V z ≤ (α : ENat) ∧
      condK V v z ≤ (β : ENat) := by
  unfold conditionalDescriptionPairsSnapshot at hw
  simp only [List.mem_flatMap, List.mem_map] at hw
  obtain ⟨z, hz, v, hv, rfl⟩ := hw
  unfold conditionalOutputSnapshot at hz hv
  rw [List.mem_filterMap] at hz hv
  obtain ⟨pz, hpz, hpzRun⟩ := hz
  obtain ⟨pv, hpv, hpvRun⟩ := hv
  refine ⟨z, v, rfl, ?_, ?_⟩
  · apply (condKLeIff V z [] α).2
    exact ⟨pz, (mem_boundedPrograms_iff pz α).1 hpz,
      conditionalRunOut_sound hc hpzRun⟩
  · apply (condKLeIff V v z β).2
    exact ⟨pv, (mem_boundedPrograms_iff pv β).1 hpv,
      conditionalRunOut_sound hc hpvRun⟩

theorem mem_conditionalDescriptionPairsStage_sound
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    {α β t : Nat} {w : BitString}
    (hw : w ∈ conditionalDescriptionPairsStage c α β t) :
    ∃ z v, w = pairCode z v ∧
      plainK V z ≤ (α : ENat) ∧
      condK V v z ≤ (β : ENat) := by
  induction t with
  | zero =>
      exact mem_conditionalDescriptionPairsSnapshot_sound hc
        (by simpa [conditionalDescriptionPairsStage,
          mem_eraseDups_bitString] using hw)
  | succ t ih =>
      have hw' :
          w ∈ conditionalDescriptionPairsStage c α β t ∨
            w ∈ conditionalDescriptionPairsSnapshot c α β (t + 1) := by
        simpa [conditionalDescriptionPairsStage,
          mem_eraseDups_bitString] using hw
      exact hw'.elim ih (mem_conditionalDescriptionPairsSnapshot_sound hc)

theorem conditionalDescriptionPairsSnapshot_mem_stage
    (c : Code) (α β t : Nat) {w : BitString}
    (hw : w ∈ conditionalDescriptionPairsSnapshot c α β t) :
    w ∈ conditionalDescriptionPairsStage c α β t := by
  cases t with
  | zero =>
      simpa [conditionalDescriptionPairsStage,
        mem_eraseDups_bitString] using hw
  | succ t =>
      simp only [conditionalDescriptionPairsStage, mem_eraseDups_bitString,
        List.mem_append]
      exact Or.inr hw

/-! ### Computability -/

/-- One compact-advice snapshot is primitive recursive uniformly in both program
bounds and the finite stage. -/
theorem conditionalDescriptionPairsSnapshot_primrec (c : Code) :
    Primrec
      (fun q : (Nat × Nat) × Nat =>
        conditionalDescriptionPairsSnapshot c q.1.1 q.1.2 q.2) := by
  unfold conditionalDescriptionPairsSnapshot
  have hα : Primrec (fun q : (Nat × Nat) × Nat => q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hβ : Primrec (fun q : (Nat × Nat) × Nat => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun q : (Nat × Nat) × Nat => q.2) := Primrec.snd
  have hOuter : Primrec (fun q : (Nat × Nat) × Nat =>
      conditionalOutputSnapshot c [] q.1.1 q.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair (Primrec.const []) hα) ht)
  have hInner : Primrec (fun r : ((Nat × Nat) × Nat) × BitString =>
      conditionalOutputSnapshot c r.2 r.1.1.2 r.1.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair Primrec.snd (hβ.comp Primrec.fst))
        (ht.comp Primrec.fst))
  have hbody : Primrec₂ (fun (q : (Nat × Nat) × Nat) (z : BitString) =>
      (conditionalOutputSnapshot c z q.1.2 q.2).map fun v => pairCode z v) :=
    (map_pairCode_primrec.comp (Primrec.pair Primrec.snd hInner)).to₂
  exact Primrec.list_flatMap hOuter hbody

/-- The compact-advice stages are primitive recursive uniformly in both program
bounds and the stage number, for each fixed decompressor code. -/
theorem conditionalDescriptionPairsStage_primrec (c : Code) :
    Primrec
      (fun q : (Nat × Nat) × Nat =>
        conditionalDescriptionPairsStage c q.1.1 q.1.2 q.2) := by
  have hSnapshot := conditionalDescriptionPairsSnapshot_primrec c
  have hbase :
      Primrec
        (fun p : (Nat × Nat) × Nat =>
          (conditionalDescriptionPairsSnapshot c p.1.1 p.1.2 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (hSnapshot.comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep :
      Primrec₂
        (fun (p : (Nat × Nat) × Nat) (z : Nat × List BitString) =>
          (z.2 ++ conditionalDescriptionPairsSnapshot c
            p.1.1 p.1.2 (z.1 + 1)).eraseDups) :=
    (eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp
        (Primrec.snd.comp Primrec.snd)
        (hSnapshot.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.succ.comp
              (Primrec.fst.comp Primrec.snd)))))).to₂
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  rintro ⟨⟨α, β⟩, t⟩
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [conditionalDescriptionPairsStage]
      rw [← ih]

/-- The compact-advice stages are computable uniformly in both program bounds and
the stage number, for each fixed decompressor code. -/
theorem conditionalDescriptionPairsStage_computable (c : Code) :
    Computable
      (fun q : (Nat × Nat) × Nat =>
        conditionalDescriptionPairsStage c q.1.1 q.1.2 q.2) :=
  (conditionalDescriptionPairsStage_primrec c).to_comp

/-! ### Exact eventual semantics -/

/-- A pair `pairCode z v` eventually appears in the compact stream iff `z` has an
`α`-bit unconditional program and `v` a `β`-bit program conditional on `z`.  The
non-strict `≤` matches `conditionalDescriptionPairsLe`; source-level strict
thresholds are obtained by decrementing positive integer bounds. -/
theorem mem_conditionalDescriptionPairsStage_eventually_iff
    {V : Map} {c : Code} (hc : IsCodeFor c V)
    (α β : Nat) (z v : BitString) :
    (∃ t, pairCode z v ∈ conditionalDescriptionPairsStage c α β t) ↔
      plainK V z ≤ (α : ENat) ∧ condK V v z ≤ (β : ENat) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨z', v', hpair, hz, hv⟩ :=
      mem_conditionalDescriptionPairsStage_sound hc ht
    have hzv : (z', v') = (z, v) := pairCode_injective hpair.symm
    cases hzv
    exact ⟨hz, hv⟩
  · rintro ⟨hz, hv⟩
    obtain ⟨pz, hpzLen, hpz⟩ := (condKLeIff V z [] α).1 hz
    obtain ⟨pv, hpvLen, hpv⟩ := (condKLeIff V v z β).1 hv
    obtain ⟨tz, htz⟩ := conditionalRunOut_complete hc hpz
    obtain ⟨tv, htv⟩ := conditionalRunOut_complete hc hpv
    let T := max tz tv
    have hzT : z ∈ conditionalOutputSnapshot c [] α T :=
      mem_conditionalOutputSnapshot_of_run hpzLen
        (conditionalRunOut_mono c (le_max_left _ _) htz)
    have hvT : v ∈ conditionalOutputSnapshot c z β T :=
      mem_conditionalOutputSnapshot_of_run hpvLen
        (conditionalRunOut_mono c (le_max_right _ _) htv)
    refine ⟨T, conditionalDescriptionPairsSnapshot_mem_stage c α β T ?_⟩
    unfold conditionalDescriptionPairsSnapshot
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨z, hzT, v, hvT, rfl⟩

/-! ### Finite completion -/

/-- Generic finite completion: a prefix-monotone, sound, eventually-complete
staged list has a finite stage whose `toFinset` is exactly the target finite
set. -/
theorem exists_stage_toFinset_eq
    {γ : Type*} [DecidableEq γ]
    {L : Nat → List γ} {F : Finset γ}
    (hmono : ∀ t, L t <+: L (t + 1))
    (hsound : ∀ t w, w ∈ L t → w ∈ F)
    (hcomplete : ∀ w ∈ F, ∃ t, w ∈ L t) :
    ∃ T, (L T).toFinset = F := by
  classical
  have hpre : ∀ {s t : Nat}, s ≤ t → L s <+: L t := by
    intro s t hst
    induction hst with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (hmono _)
  have hmono_fin : ∀ {s t : Nat}, s ≤ t →
      (L s).toFinset ⊆ (L t).toFinset := by
    intro s t hst w hw
    exact List.mem_toFinset.mpr ((hpre hst).subset (List.mem_toFinset.mp hw))
  have key : ∀ G : Finset γ, (∀ w ∈ G, ∃ t, w ∈ L t) →
      ∃ T, G ⊆ (L T).toFinset := by
    intro G
    refine Finset.induction_on G (fun _ => ⟨0, Finset.empty_subset _⟩) ?_
    intro w G' _ ih hcomp
    obtain ⟨T', hT'⟩ := ih (fun v hv => hcomp v (Finset.mem_insert_of_mem hv))
    obtain ⟨tw, htw⟩ := hcomp w (Finset.mem_insert_self w G')
    refine ⟨max T' tw, ?_⟩
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact hmono_fin (le_max_right _ _) (List.mem_toFinset.mpr htw)
    · exact hmono_fin (le_max_left _ _) (hT' hv)
  obtain ⟨T, hT⟩ := key F hcomplete
  refine ⟨T, Finset.Subset.antisymm ?_ hT⟩
  intro w hw
  exact hsound T w (List.mem_toFinset.mp hw)

/-- Once a prefix-monotone sound enumeration has reached its entire semantic
finset, every later sound stage still represents exactly that finset. -/
theorem complete_stage_persists
    {γ : Type*} [DecidableEq γ]
    {L : Nat → List γ} {F : Finset γ} {T t : Nat}
    (_hTt : T ≤ t)
    (hprefix : L T <+: L t)
    (hcomplete : (L T).toFinset = F)
    (hsound : (L t).toFinset ⊆ F) :
    (L t).toFinset = F := by
  apply Finset.Subset.antisymm hsound
  rw [← hcomplete]
  intro w hw
  exact List.mem_toFinset.mpr
    (hprefix.subset (List.mem_toFinset.mp hw))

/-- Three componentwise bounds that saturate their sum are each tight.  Used to
turn a merged total-count equality into completeness of every constituent list
during the eventual selector recovery. -/
theorem three_eq_of_le_and_sum_eq {a b c A B C : Nat}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (hsum : a + b + c = A + B + C) : a = A ∧ b = B ∧ c = C := by
  omega

/-- A nodup list contained in a finite set of the same cardinality has that set
as its `toFinset`.  Combined with `three_eq_of_le_and_sum_eq`, this recovers each
completed semantic list from the merged total count. -/
theorem toFinset_eq_of_subset_card {γ : Type*} [DecidableEq γ]
    {l : List γ} {F : Finset γ}
    (hnodup : l.Nodup) (hsub : l.toFinset ⊆ F) (hcard : l.length = F.card) :
    l.toFinset = F := by
  apply Finset.eq_of_subset_of_card_le hsub
  rw [List.toFinset_card_of_nodup hnodup]
  exact hcard.ge

/-- There is a finite stage of the compact stream whose `toFinset` equals the
semantic relation `conditionalDescriptionPairsLe`. -/
theorem exists_conditionalDescriptionPairsStage_complete
    {V : Map} {c : Code} (hc : IsCodeFor c V) (α β : Nat) :
    ∃ T, (conditionalDescriptionPairsStage c α β T).toFinset =
      conditionalDescriptionPairsLe V α β := by
  refine exists_stage_toFinset_eq
    (L := fun t => conditionalDescriptionPairsStage c α β t)
    (F := conditionalDescriptionPairsLe V α β)
    (fun t => conditionalDescriptionPairsStage_prefix c α β t) ?_ ?_
  · intro t w hw
    obtain ⟨z, v, rfl, hz, hv⟩ := mem_conditionalDescriptionPairsStage_sound hc hw
    exact (mem_conditionalDescriptionPairsLe_iff V α β (pairCode z v)).mpr
      ⟨z, v, rfl, hz, hv⟩
  · intro w hw
    obtain ⟨z, v, rfl, hz, hv⟩ :=
      (mem_conditionalDescriptionPairsLe_iff V α β w).mp hw
    exact (mem_conditionalDescriptionPairsStage_eventually_iff hc α β z v).mpr ⟨hz, hv⟩

end Kolmogorov
