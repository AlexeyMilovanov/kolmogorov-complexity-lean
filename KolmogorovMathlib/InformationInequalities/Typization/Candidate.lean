import KolmogorovMathlib.InformationInequalities.AlmostUniform
import KolmogorovMathlib.InformationInequalities.Easy
import KolmogorovMathlib.Complexity.Tuples.OneTerm
import KolmogorovMathlib.CommonInformation.CompactAdvice
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry

/-!
# Typization candidates: the set `A(x)` of tuples with dominated complexity profile

SUV Section 10.6, p. 326, first half of the proof of Theorem 211.

For a tuple `x` of strings of complexity at most `N`, the set
`A(x) = {y : κ(y) ≤ κ(x) componentwise}` — the tuples whose vector `κ` of conditional
complexities `C(y_J | y_I)` of disjoint subtuples is dominated by that of `x` — is presented over
a finite alphabet.  It contains `x`; it is enumerable from the profile `κ(x)`, which costs only
`O(log N)` bits, so `log |A(x)| ≥ C(x) − O(log N)`; and each of its sections has fewer than
`2^{C(x_J | x_I) + 1}` elements.  The definition `IsTypizationCandidate` collects these
properties, and `exists_isTypizationCandidate` proves that such a set exists.
-/

namespace Kolmogorov

open Finset
open Kolmogorov.CodedFiniteDistribution

variable {n : ℕ}

/-- A **typization candidate** for the tuple `x` at complexity budget `N`, with slack constant
`c`: a non-empty set `A` of tuples over a finite alphabet with `log |A| ≥ C(x) − O(log N)` and
`log m_A(J | I) ≤ C(x_J | x_I) + O(log N)` for all disjoint `I, J`.  The set `A(x)` of the
proof of Theorem 211 is one. -/
def IsTypizationCandidate (D : Map) (x : Fin n → BitString) (N c : ℕ)
    {m : ℕ} (A : Finset (Fin n → Fin m)) : Prop :=
  A.Nonempty ∧
    ((tupleCondK D x Finset.univ ∅).toNat : ℝ) - (logSlack c N : ℝ)
        ≤ Real.logb 2 A.card ∧
      ∀ I J : Finset (Fin n), Disjoint I J →
        Real.logb 2 (maxSection A J I)
          ≤ ((tupleCondK D x J I).toNat : ℝ) + (logSlack c N : ℝ)

/- The componentwise ordering on the full vector of conditional complexities used in the
definition `A(x) = {y : κ(y) ≤ κ(x)}` in the proof of Theorem 211. -/
private def HasDominatedConditionalProfile (D : Map) (y x : Fin n → BitString) : Prop :=
  ∀ I J : Finset (Fin n), Disjoint I J → tupleCondK D y J I ≤ tupleCondK D x J I

/- A finite alphabet presentation of the whole set `A(x)`.  Completeness says that every
tuple with dominated profile is represented over the alphabet; the last clause says that the
finite set consists of exactly those represented tuples. -/
private def IsConditionalProfileModel (D : Map) (x : Fin n → BitString) {m : ℕ}
    (A : Finset (Fin n → Fin m)) : Prop :=
  ∃ decode : Fin m → BitString,
    Function.Injective decode ∧
      (∀ y, HasDominatedConditionalProfile D y x → ∀ i, ∃ a, decode a = y i) ∧
      ∀ a, a ∈ A ↔ HasDominatedConditionalProfile D (decode ∘ a) x

/- Finiteness of the bounded-program sets makes the full dominated complexity profile into a
finite set after injectively coding all strings which occur in it by one finite alphabet. -/
private lemma exists_conditionalProfileModel (D : Map) (hD : isOptimalConditional D)
    (x : Fin n → BitString) :
    ∃ (m : ℕ) (A : Finset (Fin n → Fin m)), IsConditionalProfileModel D x A := by
  classical
  let S : Set BitString :=
    {z | ∃ y, HasDominatedConditionalProfile D y x ∧ ∃ i, y i = z}
  let encodeSingleton : BitString → BitString := fun z => listCode [z]
  have hmem_compressible (z : BitString) (k : ℕ)
      (hz : condK D z [] ≤ (k : ℕ∞)) : z ∈ compressibleWords D [] k := by
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, hz⟩
    obtain ⟨p, hpLen, hp⟩ := (condK_le_iff D z [] k).mp hz
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, mem_programsLe k p hpLen, progToOut_eq_some.mpr hp⟩
  have hS : S.Finite := by
    apply Set.Finite.of_finite_image (f := encodeSingleton)
    · refine (Finset.finite_toSet (Finset.univ.biUnion fun i =>
          compressibleWords D [] (tupleCondK D x {i} ∅).toNat)).subset ?_
      rintro z ⟨w, ⟨y, hy, i, rfl⟩, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨i, hmem_compressible _ _ ?_⟩
      have hbound := hy ∅ {i} (by simp)
      have hfinite := tupleCondK_ne_top D hD x {i} ∅
      rw [ENat.natCast_toNat hfinite]
      simpa [encodeSingleton, tupleCondK, subtupleCode] using hbound
    · intro z hz w hw hzw
      exact List.singleton_injective (listCode_injective hzw)
  let : Fintype S := hS.fintype
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let decode : Fin (Fintype.card S) → BitString := fun a => (e.symm a).1
  let A : Finset (Fin n → Fin (Fintype.card S)) :=
    Finset.univ.filter fun a => HasDominatedConditionalProfile D (decode ∘ a) x
  refine ⟨Fintype.card S, A, decode, ?_, ?_, ?_⟩
  · intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  · intro y hy i
    have hyi : y i ∈ S := ⟨y, hy, i, rfl⟩
    refine ⟨e ⟨y i, hyi⟩, ?_⟩
    simp [decode]
  · intro a
    simp [A]

/- The original tuple belongs to its own dominated-profile set. -/
private lemma conditionalProfileModel_nonempty {D : Map} {x : Fin n → BitString} {m : ℕ}
    {A : Finset (Fin n → Fin m)} (hA : IsConditionalProfileModel D x A) : A.Nonempty := by
  classical
  obtain ⟨decode, _, hcomplete, hmem⟩ := hA
  have hprofile : HasDominatedConditionalProfile D x x := by
    intro I J hIJ
    exact le_rfl
  have hrepresent : ∀ i, ∃ a, decode a = x i := hcomplete x hprofile
  choose a ha using hrepresent
  refine ⟨a, (hmem a).2 ?_⟩
  intro I J hIJ
  have htuple : decode ∘ a = x := by
    funext i
    exact ha i
  rw [htuple]

/- Fixing the `I`-coordinates of a profile tuple leaves fewer than
`2^(C(x_J | x_I)+1)` possible `J`-subtuples.  This is the conditional-program counting step
in the source proof. -/
private lemma maxSection_conditionalProfileModel_lt_two_pow
    (D : Map) (hD : isOptimalConditional D) (x : Fin n → BitString) {m : ℕ}
    (A : Finset (Fin n → Fin m)) (hA : IsConditionalProfileModel D x A)
    (I J : Finset (Fin n)) (hIJ : Disjoint I J) :
    maxSection A J I < 2 ^ ((tupleCondK D x J I).toNat + 1) := by
  classical
  obtain ⟨decode, hdecode, _, hmem⟩ := hA
  let k := (tupleCondK D x J I).toNat
  have hk : tupleCondK D x J I = (k : ℕ∞) := by
    exact (ENat.natCast_toNat (tupleCondK_ne_top D hD x J I)).symm
  have code_eq_of_restrict : ∀ (K : Finset (Fin n)) (a b : Fin n → Fin m),
      restrictTo K a = restrictTo K b →
        subtupleCode (decode ∘ a) K = subtupleCode (decode ∘ b) K := by
    intro K a b hab
    unfold subtupleCode
    apply congrArg listCode
    apply List.map_congr_left
    intro i hi
    exact congrArg decode (congrFun hab ⟨i, (Finset.mem_sort _).1 hi⟩)
  rw [maxSection]
  apply (Finset.sup_lt_iff (by positivity)).2
  intro p _
  let S := sectionOver A J I p
  change S.card < 2 ^ (k + 1)
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    have hwitness : ∀ s : {s // s ∈ S},
        ∃ a ∈ A.filter fun a => restrictTo I a = p, restrictTo J a = s.1 := by
      intro s
      apply Finset.mem_image.mp
      simpa only [S, sectionOver] using s.property
    let lift : {s // s ∈ S} → (Fin n → Fin m) := fun s => (hwitness s).choose
    have hlift (s : {s // s ∈ S}) :
        (lift s ∈ A.filter fun a => restrictTo I a = p) ∧ restrictTo J (lift s) = s.1 := by
      exact (hwitness s).choose_spec
    let sBase : {s // s ∈ S} := ⟨s₀, hs₀⟩
    let f : {s // s ∈ S} → BitString := fun s => subtupleCode (decode ∘ lift s) J
    have hf : Function.Injective f := by
      intro s t hst
      apply Subtype.ext
      have hlists :
          (J.sort (· ≤ ·)).map (decode ∘ lift s) =
            (J.sort (· ≤ ·)).map (decode ∘ lift t) := by
        apply listCode_injective
        exact hst
      have hrestrict : restrictTo J (lift s) = restrictTo J (lift t) := by
        funext j
        apply hdecode
        exact (List.map_inj_left.mp hlists) j.1 ((Finset.mem_sort _).2 j.2)
      exact (hlift s).2.symm.trans (hrestrict.trans (hlift t).2)
    let C := compressibleWords D (subtupleCode (decode ∘ lift sBase) I) k
    have hmaps : Set.MapsTo f (↑S.attach) (↑C) := by
      intro s _
      have hsA : lift s ∈ A := (Finset.mem_filter.mp (hlift s).1).1
      have hsI : restrictTo I (lift s) = restrictTo I (lift sBase) :=
        (Finset.mem_filter.mp (hlift s).1).2.trans
          (Finset.mem_filter.mp (hlift sBase).1).2.symm
      have hprofile := (hmem (lift s)).1 hsA I J hIJ
      have hcomplex :
          condK D (f s) (subtupleCode (decode ∘ lift sBase) I) ≤ (k : ℕ∞) := by
        dsimp only [f]
        rw [← code_eq_of_restrict I (lift s) (lift sBase) hsI]
        exact hprofile.trans_eq hk
      change f s ∈ compressibleWords D (subtupleCode (decode ∘ lift sBase) I) k
      rw [compressibleWords, Finset.mem_filter]
      refine ⟨?_, hcomplex⟩
      obtain ⟨q, hqLen, hq⟩ := (condK_le_iff D _ _ k).mp hcomplex
      rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨q, mem_programsLe k q hqLen, progToOut_eq_some.mpr hq⟩
    have hcard := Finset.card_le_card_of_injOn f hmaps hf.injOn
    rw [Finset.card_attach] at hcard
    exact hcard.trans_lt
      (card_compressibleWordsLt D (subtupleCode (decode ∘ lift sBase) I) k)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

private def typFinsets (n : ℕ) : List (Finset (Fin n)) :=
  (exactLengthPrograms n).map fun w => Finset.univ.filter fun i => w.getD i.1 false

private def typProfilePairs : List (Finset (Fin n) × Finset (Fin n)) :=
  ((typFinsets n).flatMap fun I => (typFinsets n).map fun J => (I, J)).filter
    fun q => decide (Disjoint q.1 q.2)

private def typSubtupleFromCode (I : Finset (Fin n)) (w : BitString) : BitString :=
  listCode ((I.sort (· ≤ ·)).map fun i => (decodeListCode w).getD i.1 [])

private def typTupleFromCode (w : BitString) : BitString :=
  listCode ((List.range n).map fun i => (decodeListCode w).getD i [])

private def typProfileBound (profile : BitString) (r : ℕ) : ℕ :=
  bitsToNat ((decodeListCode profile).getD r [])

private def typProfileAccept (c : Nat.Partrec.Code) (profile : BitString) (t : ℕ)
    (w : BitString) : List (Finset (Fin n) × Finset (Fin n)) → ℕ → Bool
  | [], _ => true
  | q :: qs, r =>
      decide (typSubtupleFromCode q.2 w ∈
        conditionalOutputSnapshot c (typSubtupleFromCode q.1 w)
          (typProfileBound profile
            ((typProfilePairs (n := n)).findIdx (· == q))) t) &&
        typProfileAccept c profile t w qs (r + 1)

private def typProfileSnapshot (c : Nat.Partrec.Code) (profile : BitString) (t : ℕ) :
    List BitString :=
  let full := ((∅ : Finset (Fin n)), Finset.univ)
  let r := (typProfilePairs (n := n)).findIdx (· == full)
  ((conditionalOutputSnapshot c [] (typProfileBound profile r) t).map
      (typTupleFromCode (n := n))).filter fun w =>
    typProfileAccept c profile t w (typProfilePairs (n := n)) 0

private def typProfileStage (c : Nat.Partrec.Code) (profile : BitString) : ℕ → List BitString
  | 0 => (typProfileSnapshot (n := n) c profile 0).eraseDups
  | t + 1 =>
      (typProfileStage c profile t ++
        typProfileSnapshot (n := n) c profile (t + 1)).eraseDups

private lemma typProfileMapGetD_primrec (idxs : List ℕ) :
    Primrec (fun w : BitString => idxs.map fun i => (decodeListCode w).getD i []) := by
  induction idxs with
  | nil => exact Primrec.const []
  | cons i is ih =>
      exact Primrec.list_cons.comp
        ((Primrec.list_getD []).comp decodeListCode_primrec (Primrec.const i)) ih

private lemma typSubtupleFromCode_primrec (I : Finset (Fin n)) :
    Primrec (typSubtupleFromCode I) := by
  unfold typSubtupleFromCode
  exact (listCode_primrec.comp
    (typProfileMapGetD_primrec ((I.sort (· ≤ ·)).map fun i => i.1))).of_eq
      (by
        intro w
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        rfl)

private lemma typTupleFromCode_primrec : Primrec (typTupleFromCode (n := n)) := by
  unfold typTupleFromCode
  exact listCode_primrec.comp (typProfileMapGetD_primrec (List.range n))

private lemma typProfileBound_primrec :
    Primrec (fun p : BitString × ℕ => typProfileBound p.1 p.2) := by
  exact bitsToNat_primrec.comp
    ((Primrec.list_getD []).comp (decodeListCode_primrec.comp Primrec.fst) Primrec.snd)

private lemma typProfileAccept_primrec (c : Nat.Partrec.Code)
    (qs : List (Finset (Fin n) × Finset (Fin n))) (r : ℕ) :
    Primrec (fun p : (BitString × ℕ) × BitString =>
      typProfileAccept c p.1.1 p.1.2 p.2 qs r) := by
  induction qs generalizing r with
  | nil => exact Primrec.const true
  | cons q qs ih =>
      have hI : Primrec (fun p : (BitString × ℕ) × BitString =>
          typSubtupleFromCode q.1 p.2) :=
        (typSubtupleFromCode_primrec q.1).comp Primrec.snd
      have hJ : Primrec (fun p : (BitString × ℕ) × BitString =>
          typSubtupleFromCode q.2 p.2) :=
        (typSubtupleFromCode_primrec q.2).comp Primrec.snd
      let rq := (typProfilePairs (n := n)).findIdx (· == q)
      have hb : Primrec (fun p : (BitString × ℕ) × BitString =>
          typProfileBound p.1.1 rq) :=
        typProfileBound_primrec.comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const rq))
      have hs : Primrec (fun p : (BitString × ℕ) × BitString =>
          conditionalOutputSnapshot c (typSubtupleFromCode q.1 p.2)
            (typProfileBound p.1.1 rq) p.1.2) :=
        (conditionalOutputSnapshot_primrec c).comp
          (Primrec.pair (Primrec.pair hI hb) (Primrec.snd.comp Primrec.fst))
      have hm : Primrec (fun p : (BitString × ℕ) × BitString =>
          decide (typSubtupleFromCode q.2 p.2 ∈
            conditionalOutputSnapshot c (typSubtupleFromCode q.1 p.2)
              (typProfileBound p.1.1 rq) p.1.2)) :=
        bitString_mem_primrec.comp hJ hs
      exact (Primrec.and.comp hm (ih (r + 1))).of_eq fun _ => rfl

private lemma typProfileSnapshot_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : BitString × ℕ => typProfileSnapshot (n := n) c p.1 p.2) := by
  let full : Finset (Fin n) × Finset (Fin n) := (∅, Finset.univ)
  let r := (typProfilePairs (n := n)).findIdx (· == full)
  have hb : Primrec (fun p : BitString × ℕ => typProfileBound p.1 r) :=
    typProfileBound_primrec.comp (Primrec.pair Primrec.fst (Primrec.const r))
  have hs : Primrec (fun p : BitString × ℕ =>
      conditionalOutputSnapshot c [] (typProfileBound p.1 r) p.2) :=
    (conditionalOutputSnapshot_primrec c).comp
      (Primrec.pair (Primrec.pair (Primrec.const []) hb) Primrec.snd)
  have hm : Primrec (fun p : BitString × ℕ =>
      (conditionalOutputSnapshot c [] (typProfileBound p.1 r) p.2).map
        (typTupleFromCode (n := n))) :=
    Primrec.list_map hs ((typTupleFromCode_primrec (n := n)).comp Primrec.snd).to₂
  have hp : Primrec₂ (fun (p : BitString × ℕ) (w : BitString) =>
      typProfileAccept c p.1 p.2 w (typProfilePairs (n := n)) 0) :=
    (typProfileAccept_primrec c (typProfilePairs (n := n)) 0).to₂
  exact (list_filter_primrec hm hp).of_eq fun p => by
    simp only [typProfileSnapshot]
    rfl

private lemma typProfileStage_primrec (c : Nat.Partrec.Code) :
    Primrec (fun p : BitString × ℕ => typProfileStage (n := n) c p.1 p.2) := by
  have hs := typProfileSnapshot_primrec (n := n) c
  have hbase : Primrec (fun p : BitString × ℕ =>
      (typProfileSnapshot (n := n) c p.1 0).eraseDups) :=
    eraseDups_bitstring_primrec.comp
      (hs.comp (Primrec.pair Primrec.fst (Primrec.const 0)))
  have hstep : Primrec₂ (fun (p : BitString × ℕ) (z : ℕ × List BitString) =>
      (z.2 ++ typProfileSnapshot (n := n) c p.1 (z.1 + 1)).eraseDups) :=
    (eraseDups_bitstring_primrec.comp
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (hs.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))))).to₂
  refine (Primrec.nat_rec' Primrec.snd hbase hstep).of_eq ?_
  intro p
  induction p.2 with
  | zero => rfl
  | succ t ih => simp only [typProfileStage]; rw [← ih]

private lemma typProfileStage_nodup (c : Nat.Partrec.Code) (profile : BitString) (t : ℕ) :
    (typProfileStage (n := n) c profile t).Nodup := by
  cases t <;> exact nodup_eraseDups_bitString _

private lemma typProfileStage_prefix (c : Nat.Partrec.Code) (profile : BitString) (t : ℕ) :
    typProfileStage (n := n) c profile t <+:
      typProfileStage (n := n) c profile (t + 1) := by
  rw [typProfileStage]
  exact prefix_eraseDups_append_of_nodup _ _ (typProfileStage_nodup c profile t)

/-- The list code of at most `n` strings of complexity at most `N` has complexity `O(N)`. -/
lemma exists_listCode_complexity_linear (D : Map) (hD : isOptimalConditional D) :
    ∃ a b : ℕ, ∀ (N : ℕ) (l : List BitString), l.length ≤ n →
      (∀ z ∈ l, plainK D z ≤ (N : ℕ∞)) →
      plainK D (listCode l) ≤ ((a * N + b : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ := plainK_pair_le_two_mul D hD
  obtain ⟨e, he⟩ := plainK_le_length D hD
  induction n with
  | zero =>
      refine ⟨0, e, fun N l hl _ => ?_⟩
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)
      subst l
      simpa using he []
  | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨2 * (a + 1), 2 * b + k + e, fun N l hl hall => ?_⟩
      cases l with
      | nil =>
          have hempty : plainK D [] ≤ (e : ℕ∞) := by simpa [programLength] using he []
          exact hempty.trans (by norm_cast; omega)
      | cons z zs =>
          have hzs : zs.length ≤ n := by simp at hl; omega
          have hz : plainK D z ≤ (N : ℕ∞) := hall z (by simp)
          have htail : plainK D (listCode zs) ≤ ((a * N + b : ℕ) : ℕ∞) :=
            hab N zs hzs (fun w hw => hall w (by simp [hw]))
          have hz' : plainK D z ≤ ((a * N + b + N : ℕ) : ℕ∞) :=
            hz.trans (by norm_cast; omega)
          have htail' : plainK D (listCode zs) ≤
              ((a * N + b + N : ℕ) : ℕ∞) := htail.trans (by norm_cast; omega)
          have hp := hk (a * N + b + N) z (listCode zs) hz' htail'
          have hle : 2 * (a * N + b + N) + k ≤ 2 * (a + 1) * N + (2 * b + k + e) := by
            ring_nf; omega
          simpa [listCode, cPair] using hp.trans (Nat.cast_le.mpr hle)

/-- Every conditional complexity `C(x_J | x_I)` of a tuple of strings of complexity at most `N`
is `O(N)`: the entries of the complexity profile are linearly bounded. -/
lemma exists_profile_component_linear_bound
    (D : Map) (hD : isOptimalConditional D) :
    ∃ a b : ℕ, ∀ (N : ℕ) (x : Fin n → BitString),
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ I J : Finset (Fin n), (tupleCondK D x J I).toNat ≤ a * N + b := by
  obtain ⟨a, b, hab⟩ := exists_listCode_complexity_linear (n := n) D hD
  obtain ⟨d, hd⟩ := condK_le_plainK D hD
  refine ⟨a, b + d, fun N x hx I J => ?_⟩
  have hplain : plainK D (subtupleCode x J) ≤ ((a * N + b : ℕ) : ℕ∞) := by
    apply hab N ((J.sort (· ≤ ·)).map x)
    · simpa using Finset.card_le_univ J
    · intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨i, _, rfl⟩ := hz
      exact hx i
  have hcond : tupleCondK D x J I ≤ ((a * N + (b + d) : ℕ) : ℕ∞) := by
    calc
      tupleCondK D x J I ≤ plainK D (subtupleCode x J) + (d : ℕ∞) := hd _ _
      _ ≤ ((a * N + b : ℕ) : ℕ∞) + (d : ℕ∞) := by gcongr
      _ = ((a * N + (b + d) : ℕ) : ℕ∞) := by push_cast; ring
  have h := ENat.toNat_le_toNat hcond (ENat.natCast_ne_top _)
  rwa [ENat.toNat_natCast] at h

private noncomputable def typProfileCode (D : Map) (x : Fin n → BitString) : BitString :=
  listCode ((typProfilePairs (n := n)).map fun q =>
    Nat.bits (tupleCondK D x q.2 q.1).toNat)

private lemma mem_typFinsets (I : Finset (Fin n)) : I ∈ typFinsets n := by
  let w : BitString := List.ofFn fun i : Fin n => decide (i ∈ I)
  have hwlen : w.length = n := by simp [w]
  have hw : w ∈ exactLengthPrograms n := by
    rw [← hwlen]
    exact mem_exactLengthPrograms_self w
  rw [typFinsets, List.mem_map]
  refine ⟨w, hw, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : i.1 < w.length := by simp [w]
  rw [List.getD_eq_getElem _ _ hi]
  simp [w]

private lemma mem_typProfilePairs {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    (I, J) ∈ typProfilePairs (n := n) := by
  rw [typProfilePairs, List.mem_filter]
  refine ⟨?_, by simpa⟩
  rw [List.mem_flatMap]
  exact ⟨I, mem_typFinsets I, by
    rw [List.mem_map]
    exact ⟨J, mem_typFinsets J, rfl⟩⟩

private lemma typProfileBound_code (D : Map) (x : Fin n → BitString)
    {q : Finset (Fin n) × Finset (Fin n)} (hq : q ∈ typProfilePairs (n := n)) :
    typProfileBound (typProfileCode D x)
        ((typProfilePairs (n := n)).findIdx (· == q)) =
      (tupleCondK D x q.2 q.1).toNat := by
  let L := typProfilePairs (n := n)
  have hi : L.findIdx (· == q) < L.length :=
    List.findIdx_lt_length_of_exists ⟨q, hq, by simp⟩
  have hget : L.getD (L.findIdx (· == q)) (∅, ∅) = q := by
    rw [List.getD_eq_getElem _ _ hi]
    simpa using List.findIdx_getElem (w := hi) (p := (· == q)) (xs := L)
  unfold typProfileBound typProfileCode
  rw [decodeListCode_listCode]
  have himap : L.findIdx (· == q) <
      (L.map fun q => Nat.bits (tupleCondK D x q.2 q.1).toNat).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ himap, List.getElem_map]
  have hget' : L[L.findIdx (· == q)] = q := by
    simpa using List.findIdx_getElem (w := hi) (p := (· == q)) (xs := L)
  rw [hget', bitsToNat_bits]

private lemma typSubtupleFromCode_tupleCode (x : Fin n → BitString)
    (I : Finset (Fin n)) : typSubtupleFromCode I (tupleCode x) = subtupleCode x I := by
  unfold typSubtupleFromCode tupleCode subtupleCode
  rw [decodeListCode_listCode]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hil : i.1 < (List.ofFn x).length := by simp
  rw [List.getD_eq_getElem _ _ hil]
  simp

private lemma typTupleFromCode_tupleCode (x : Fin n → BitString) :
    typTupleFromCode (n := n) (tupleCode x) = tupleCode x := by
  unfold typTupleFromCode tupleCode
  rw [decodeListCode_listCode]
  congr 1
  apply List.ext_get
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp [hi]

private lemma exists_mem_typProfileSnapshot {D : Map} {c : Nat.Partrec.Code}
    (hc : IsCodeFor c D) (hD : isOptimalConditional D) (x : Fin n → BitString) :
    ∃ t, tupleCode x ∈ typProfileSnapshot (n := n) c (typProfileCode D x) t := by
  classical
  have hfinite (q : Finset (Fin n) × Finset (Fin n)) :
      tupleCondK D x q.2 q.1 = ((tupleCondK D x q.2 q.1).toNat : ℕ∞) :=
    (ENat.natCast_toNat (tupleCondK_ne_top D hD x q.2 q.1)).symm
  have hle (q : Finset (Fin n) × Finset (Fin n)) :
      condK D (subtupleCode x q.2) (subtupleCode x q.1) ≤
        ((tupleCondK D x q.2 q.1).toNat : ℕ∞) := by
    change tupleCondK D x q.2 q.1 ≤ _
    exact le_of_eq (hfinite q)
  choose p hpLen hp using fun q =>
    (condK_le_iff D (subtupleCode x q.2) (subtupleCode x q.1)
      (tupleCondK D x q.2 q.1).toNat).mp (hle q)
  choose s hs using fun q => conditionalRunOut_complete hc (hp q)
  let T := Finset.univ.sup s
  have hout (q : Finset (Fin n) × Finset (Fin n)) :
      subtupleCode x q.2 ∈ conditionalOutputSnapshot c (subtupleCode x q.1)
        (tupleCondK D x q.2 q.1).toNat T := by
    exact mem_conditionalOutputSnapshot_of_run (hpLen q)
      (conditionalRunOut_mono c (Finset.le_sup (Finset.mem_univ q)) (hs q))
  have haccept : typProfileAccept c (typProfileCode D x) T (tupleCode x)
      (typProfilePairs (n := n)) 0 = true := by
    have go : ∀ (qs : List (Finset (Fin n) × Finset (Fin n))) (r : ℕ),
        (∀ q ∈ qs, q ∈ typProfilePairs (n := n)) →
        typProfileAccept c (typProfileCode D x) T (tupleCode x) qs r = true := by
      intro qs r hsub
      induction qs generalizing r with
      | nil => rfl
      | cons q qs ih =>
          rw [typProfileAccept, Bool.and_eq_true]
          refine ⟨?_, ih (r + 1) (fun z hz => hsub z (by simp [hz]))⟩
          rw [decide_eq_true_eq, typSubtupleFromCode_tupleCode,
            typSubtupleFromCode_tupleCode, typProfileBound_code D x (hsub q (by simp))]
          exact hout q
    exact go _ 0 (fun _ h => h)
  let full : Finset (Fin n) × Finset (Fin n) := (∅, Finset.univ)
  have hfull : full ∈ typProfilePairs (n := n) := mem_typProfilePairs (by simp)
  have hsource : tupleCode x ∈ conditionalOutputSnapshot c []
      (typProfileBound (typProfileCode D x)
        ((typProfilePairs (n := n)).findIdx (· == full))) T := by
    rw [typProfileBound_code D x hfull]
    simpa [full, subtupleCode_univ] using hout full
  refine ⟨T, ?_⟩
  unfold typProfileSnapshot
  dsimp only
  rw [List.mem_filter]
  refine ⟨?_, haccept⟩
  rw [List.mem_map]
  exact ⟨tupleCode x, hsource, typTupleFromCode_tupleCode x⟩

private lemma typTupleFromCode_eq_tupleCode (w : BitString) :
    typTupleFromCode (n := n) w =
      tupleCode (fun i : Fin n => (decodeListCode w).getD i.1 []) := by
  unfold typTupleFromCode tupleCode
  congr 1
  apply List.ext_get
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp

private lemma typProfileAccept_mem {c : Nat.Partrec.Code} {profile : BitString} {t r : ℕ}
    {w : BitString} {qs : List (Finset (Fin n) × Finset (Fin n))}
    (ha : typProfileAccept c profile t w qs r = true) {q} (hq : q ∈ qs) :
    typSubtupleFromCode q.2 w ∈
      conditionalOutputSnapshot c (typSubtupleFromCode q.1 w)
        (typProfileBound profile ((typProfilePairs (n := n)).findIdx (· == q))) t := by
  induction qs generalizing r with
  | nil => simp at hq
  | cons z zs ih =>
      rw [typProfileAccept, Bool.and_eq_true] at ha
      rcases List.mem_cons.mp hq with rfl | hq
      · exact of_decide_eq_true ha.1
      · exact ih ha.2 hq

private lemma typProfileAccept_dominated {D : Map} {c : Nat.Partrec.Code}
    (hc : IsCodeFor c D) (hD : isOptimalConditional D)
    (x y : Fin n → BitString) {t r : ℕ}
    (ha : typProfileAccept c (typProfileCode D x) t (tupleCode y)
      (typProfilePairs (n := n)) r = true) :
    HasDominatedConditionalProfile D y x := by
  intro I J hIJ
  let q : Finset (Fin n) × Finset (Fin n) := (I, J)
  have hq : q ∈ typProfilePairs (n := n) := mem_typProfilePairs hIJ
  have hm := typProfileAccept_mem ha hq
  rw [typSubtupleFromCode_tupleCode, typSubtupleFromCode_tupleCode,
    typProfileBound_code D x hq] at hm
  unfold conditionalOutputSnapshot at hm
  rw [List.mem_filterMap] at hm
  obtain ⟨p, hp, hrun⟩ := hm
  have hle := (condK_le_iff D (subtupleCode y J) (subtupleCode y I)
    (tupleCondK D x J I).toNat).2
      ⟨p, (mem_boundedPrograms_iff _ _).1 hp, conditionalRunOut_sound hc hrun⟩
  change tupleCondK D y J I ≤ tupleCondK D x J I
  exact hle.trans_eq (ENat.natCast_toNat (tupleCondK_ne_top D hD x J I))

private lemma typProfileSnapshot_sound {D : Map} {c : Nat.Partrec.Code}
    (hc : IsCodeFor c D) (hD : isOptimalConditional D)
    (x : Fin n → BitString) {t : ℕ} {w : BitString}
    (hw : w ∈ typProfileSnapshot (n := n) c (typProfileCode D x) t) :
    ∃ y : Fin n → BitString, w = tupleCode y ∧ HasDominatedConditionalProfile D y x := by
  unfold typProfileSnapshot at hw
  dsimp only at hw
  rw [List.mem_filter] at hw
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw.1
  let y : Fin n → BitString := fun i => (decodeListCode u).getD i.1 []
  have heq : typTupleFromCode (n := n) u = tupleCode y := typTupleFromCode_eq_tupleCode u
  refine ⟨y, heq, ?_⟩
  rw [heq] at hw
  exact typProfileAccept_dominated hc hD x y hw.2

private lemma typProfileStage_sound {D : Map} {c : Nat.Partrec.Code}
    (hc : IsCodeFor c D) (hD : isOptimalConditional D)
    (x : Fin n → BitString) {t : ℕ} {w : BitString}
    (hw : w ∈ typProfileStage (n := n) c (typProfileCode D x) t) :
    ∃ y : Fin n → BitString, w = tupleCode y ∧ HasDominatedConditionalProfile D y x := by
  induction t with
  | zero =>
      apply typProfileSnapshot_sound hc hD x
      simpa [typProfileStage, mem_eraseDups_bitString] using hw
  | succ t ih =>
      have hw' : w ∈ typProfileStage (n := n) c (typProfileCode D x) t ∨
          w ∈ typProfileSnapshot (n := n) c (typProfileCode D x) (t + 1) := by
        simpa [typProfileStage, mem_eraseDups_bitString] using hw
      exact hw'.elim ih (typProfileSnapshot_sound hc hD x)

private lemma typProfileSnapshot_mem_stage (c : Nat.Partrec.Code) (profile : BitString)
    (t : ℕ) {w : BitString} (hw : w ∈ typProfileSnapshot (n := n) c profile t) :
    w ∈ typProfileStage (n := n) c profile t := by
  cases t with
  | zero => simpa [typProfileStage, mem_eraseDups_bitString] using hw
  | succ t =>
      simp only [typProfileStage, mem_eraseDups_bitString, List.mem_append]
      exact Or.inr hw

private lemma typProfileStage_card_le_model {D : Map} {c : Nat.Partrec.Code}
    (hc : IsCodeFor c D) (hD : isOptimalConditional D)
    (x : Fin n → BitString) {m t : ℕ}
    (A : Finset (Fin n → Fin m)) (hA : IsConditionalProfileModel D x A) :
    (typProfileStage (n := n) c (typProfileCode D x) t).length ≤ A.card := by
  classical
  obtain ⟨decode, _, hcomplete, hmem⟩ := hA
  let L := typProfileStage (n := n) c (typProfileCode D x) t
  have hsound (w : {w // w ∈ L.toFinset}) :
      ∃ y : Fin n → BitString,
        w.1 = tupleCode y ∧ HasDominatedConditionalProfile D y x :=
    typProfileStage_sound hc hD x (List.mem_toFinset.mp w.2)
  let y : {w // w ∈ L.toFinset} → (Fin n → BitString) :=
    fun w => (hsound w).choose
  have hy (w : {w // w ∈ L.toFinset}) :
      w.1 = tupleCode (y w) ∧ HasDominatedConditionalProfile D (y w) x :=
    (hsound w).choose_spec
  have hrep (w : {w // w ∈ L.toFinset}) : ∀ i, ∃ a, decode a = y w i :=
    hcomplete (y w) (hy w).2
  choose a ha using hrep
  let f : {w // w ∈ L.toFinset} → (Fin n → Fin m) := fun w i => a w i
  have hfmem (w : {w // w ∈ L.toFinset}) : f w ∈ A := by
    rw [hmem]
    have heq : decode ∘ f w = y w := by
      funext i
      exact ha w i
    rw [heq]
    exact (hy w).2
  have hfinj : Function.Injective f := by
    intro u v huv
    have hyuv : y u = y v := by
      funext i
      rw [← ha u i, ← ha v i]
      exact congrArg decode (congrFun huv i)
    apply Subtype.ext
    exact (hy u).1.trans ((congrArg tupleCode hyuv).trans (hy v).1.symm)
  have hcard := Finset.card_le_card_of_injOn (s := L.toFinset.attach) (t := A) f
    (fun w _ => hfmem w) hfinj.injOn
  rw [Finset.card_attach, List.toFinset_card_of_nodup
    (typProfileStage_nodup c (typProfileCode D x) t)] at hcard
  simpa [L] using hcard

private lemma length_listCode_le (l : List BitString) :
    (listCode l).length ≤ 2 * (l.map List.length).sum + l.length := by
  induction l with
  | nil => simp [listCode]
  | cons w ws ih =>
      rw [length_listCode_cons]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private lemma typProfileCode_length_le (D : Map) (x : Fin n → BitString)
    (N a b : ℕ) (hbound : ∀ I J : Finset (Fin n),
      (tupleCondK D x J I).toNat ≤ a * N + b) :
    (typProfileCode D x).length ≤
      2 * (typProfilePairs (n := n)).length * (Nat.bits (a * N + b)).length +
        (typProfilePairs (n := n)).length := by
  let L := typProfilePairs (n := n)
  have hterm : ∀ q ∈ L,
      (Nat.bits (tupleCondK D x q.2 q.1).toNat).length ≤
        (Nat.bits (a * N + b)).length := by
    intro q _
    simpa [Nat.size_eq_bits_len] using Nat.size_le_size (hbound q.1 q.2)
  have hsum :
      ((L.map fun q => Nat.bits (tupleCondK D x q.2 q.1).toNat).map List.length).sum ≤
        L.length * (Nat.bits (a * N + b)).length := by
    rw [List.map_map]
    simpa [Function.comp_def] using List.sum_le_length_nsmul
      (L.map fun q => (Nat.bits (tupleCondK D x q.2 q.1).toNat).length)
      (Nat.bits (a * N + b)).length (fun _ hq => by
        obtain ⟨q, hqL, rfl⟩ := List.mem_map.mp hq
        exact hterm q hqL)
  unfold typProfileCode
  calc
    (listCode (L.map fun q => Nat.bits (tupleCondK D x q.2 q.1).toNat)).length
        ≤ 2 * ((L.map fun q => Nat.bits (tupleCondK D x q.2 q.1).toNat).map
            List.length).sum +
          (L.map fun q => Nat.bits (tupleCondK D x q.2 q.1).toNat).length :=
      length_listCode_le _
    _ ≤ 2 * (L.length * (Nat.bits (a * N + b)).length) + L.length := by
      simpa only [List.length_map] using
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsum) L.length
    _ = 2 * L.length * (Nat.bits (a * N + b)).length + L.length := by ring

/- The staged profile enumeration is a decoder: the position of `x` in the stage that contains
it, together with the complexity profile of `x`, describes `x`.  The position is below
`|A(x)|`, so `C(x) ≤ |bits |A(x)|| + 2 |profile| + 1 + c`. -/
private lemma exists_profile_description_length_le (D : Map) (hD : isOptimalConditional D) :
    ∃ cDec : ℕ, ∀ (x : Fin n → BitString) (m : ℕ) (A : Finset (Fin n → Fin m)),
      IsConditionalProfileModel D x A →
        plainK D (tupleCode x) ≤
          (((Nat.bits A.card).length + (2 * (typProfileCode D x).length + 1 + cDec) : ℕ) :
            ℕ∞) := by
  classical
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  have hc : IsCodeFor code D := hcode
  let enum : BitString → ℕ → List BitString := fun profile t =>
    typProfileStage (n := n) code profile t
  have henum : Computable (fun p : BitString × ℕ => enum p.1 p.2) :=
    (typProfileStage_primrec (n := n) code).to_comp
  let M : Map := fun pr =>
    StagedEnumeration.condFFixedLength enum (decodeFirst pr.1) (decodeSecond pr.1)
  have hM : isDecompressor M := by
    have hf := StagedEnumeration.condFFixedLength_partrec enum henum
    have hargs : Computable (fun pr : BitString × BitString =>
        (decodeSecond pr.1, decodeFirst pr.1)) :=
      decodeSecond_computable.comp Computable.fst |>.pair
        (decodeFirst_computable.comp Computable.fst)
    exact (hf.comp hargs).of_eq fun _ => rfl
  obtain ⟨cDec, hcDec⟩ := hD.2 M hM
  refine ⟨cDec, fun x m A hA => ?_⟩
  let profile := typProfileCode D x
  obtain ⟨t, hxtSnapshot⟩ := exists_mem_typProfileSnapshot hc hD x
  have hxt : tupleCode x ∈ enum profile t :=
    typProfileSnapshot_mem_stage code profile t hxtSnapshot
  let L := enum profile t
  let k := L.findIdx (· == tupleCode x)
  have hk : k < L.length := List.findIdx_lt_length_of_exists
    ⟨tupleCode x, hxt, by simp⟩
  have hget : L.getD k [] = tupleCode x := by
    rw [List.getD_eq_getElem _ _ hk]
    simpa using List.findIdx_getElem (w := hk) (p := (· == tupleCode x)) (xs := L)
  have hnodup : L.Nodup := typProfileStage_nodup code profile t
  have hkErase : bitsToNat (Nat.bits k) < (L.eraseDups).length := by
    rw [bitsToNat_bits, eraseDups_eq_self_of_nodup hnodup]
    exact hk
  have heval := StagedEnumeration.condFFixedLength_eval enum
    (fun y s => typProfileStage_prefix code y s) profile (Nat.bits k) t hkErase
  change (L.eraseDups).getD (bitsToNat (Nat.bits k)) [] ∈
    StagedEnumeration.condFFixedLength enum profile (Nat.bits k) at heval
  rw [eraseDups_eq_self_of_nodup hnodup, bitsToNat_bits, hget] at heval
  have hprod : tupleCode x ∈ M (pairCode profile (Nat.bits k), []) := by
    simpa [M, decodeFirst_pairCode, decodeSecond_pairCode] using heval
  have hprogram : plainK D (tupleCode x) ≤
      ((pairCode profile (Nat.bits k)).length : ℕ∞) + (cDec : ℕ∞) := by
    calc
      plainK D (tupleCode x) ≤ plainK M (tupleCode x) + (cDec : ℕ∞) := hcDec _ []
      _ ≤ ((pairCode profile (Nat.bits k)).length : ℕ∞) + (cDec : ℕ∞) := by
        gcongr
        exact (condK_le_iff M (tupleCode x) [] _).2 ⟨_, le_rfl, hprod⟩
  have hcard : L.length ≤ A.card := typProfileStage_card_le_model hc hD x A hA
  have hkcard : k ≤ A.card := (Nat.le_of_lt hk).trans hcard
  have hbits : (Nat.bits k).length ≤ (Nat.bits A.card).length :=
    by simpa [Nat.size_eq_bits_len] using Nat.size_le_size hkcard
  clear_value k
  have hlen : (pairCode profile (Nat.bits k)).length + cDec ≤
      (Nat.bits A.card).length + (2 * profile.length + 1 + cDec) := by
    rw [length_pairCode]
    omega
  exact hprogram.trans (by exact_mod_cast hlen)

/- Binary length is logarithmic: a positive `a` has at most `log₂ a + 1` binary digits. -/
private lemma length_bits_le_logb_add_one {a : ℕ} (ha : 0 < a) :
    ((Nat.bits a).length : ℝ) ≤ Real.logb 2 a + 1 := by
  have hpowNat : 2 ^ (Nat.size a - 1) ≤ a :=
    Nat.lt_size.mp (by have := Nat.size_pos.mpr ha; omega)
  have hpowReal : (2 : ℝ) ^ (Nat.size a - 1) ≤ a := by
    exact_mod_cast hpowNat
  have hlog := (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by positivity)
    (by exact_mod_cast ha)).mpr hpowReal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hlog
  have hone : 1 ≤ Nat.size a := Nat.size_pos.mpr ha
  push_cast [Nat.cast_sub hone] at hlog
  have hsize : (Nat.size a : ℝ) ≤ Real.logb 2 a + 1 := by linarith
  simpa [Nat.size_eq_bits_len] using hsize

/- The set `A(x)` is enumerable from its finite complexity vector.  Describing that vector
costs `O(log N)` bits, so indexing `x` in the enumeration gives
`C(x) ≤ log |A(x)| + O(log N)`. -/
private lemma exists_conditionalProfileModel_card_lower
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∀ (m : ℕ) (A : Finset (Fin n → Fin m)),
        IsConditionalProfileModel D x A →
        ((tupleCondK D x Finset.univ ∅).toNat : ℝ) - (logSlack c N : ℝ)
          ≤ Real.logb 2 A.card := by
  obtain ⟨cDec, hdesc⟩ := exists_profile_description_length_le (n := n) D hD
  obtain ⟨a, b, hab⟩ := exists_profile_component_linear_bound (n := n) D hD
  let pcount := (typProfilePairs (n := n)).length
  let e := 4 * pcount + cDec + 2
  obtain ⟨c, hcSlack⟩ := logSlack_linear_bound e a b
  refine ⟨c, fun N _ x hx m A hA => ?_⟩
  let profile := typProfileCode D x
  have hcomponent := hab N x hx
  have hprofile : profile.length ≤
      2 * pcount * (Nat.bits (a * N + b)).length + pcount := by
    exact typProfileCode_length_le D x N a b hcomponent
  have hcost : 2 * profile.length + 1 + cDec + 1 ≤ logSlack c N := by
    have hinner : 2 * profile.length + 1 + cDec + 1 ≤ logSlack e (a * N + b) := by
      dsimp [e, pcount, logSlack] at hprofile ⊢
      ring_nf at hprofile ⊢
      omega
    exact hinner.trans (hcSlack N)
  have hfull : tupleCondK D x Finset.univ ∅ = plainK D (tupleCode x) := by
    simp [tupleCondK, plainK, subtupleCode_univ]
  have hprogram' : tupleCondK D x Finset.univ ∅ ≤
      (((Nat.bits A.card).length + (2 * profile.length + 1 + cDec) : ℕ) : ℕ∞) := by
    rw [hfull]
    exact hdesc x m A hA
  have hnat := ENat.toNat_le_toNat hprogram' (ENat.natCast_ne_top _)
  simp only [ENat.toNat_natCast] at hnat
  have hcardPos : 0 < A.card := Finset.card_pos.mpr (conditionalProfileModel_nonempty hA)
  have hbitsReal := length_bits_le_logb_add_one hcardPos
  have hnatR : ((tupleCondK D x Finset.univ ∅).toNat : ℝ) ≤
      ((Nat.bits A.card).length : ℝ) +
        (2 * profile.length + 1 + cDec : ℝ) := by exact_mod_cast hnat
  have hcostR : (2 * profile.length + 1 + cDec + 1 : ℝ) ≤ logSlack c N := by
    exact_mod_cast hcost
  linarith

/- Taking logarithms turns the conditional-program counting bound into the upper section
estimate, with the extra one bit absorbed by `logSlack 1 N`. -/
private lemma logb_maxSection_le_of_profile_count {D : Map} {x : Fin n → BitString}
    {m N : ℕ} {A : Finset (Fin n → Fin m)}
    (hcount : ∀ I J : Finset (Fin n), Disjoint I J →
      maxSection A J I < 2 ^ ((tupleCondK D x J I).toNat + 1)) :
    ∀ I J : Finset (Fin n), Disjoint I J →
      Real.logb 2 (maxSection A J I) ≤
        ((tupleCondK D x J I).toNat : ℝ) + (logSlack 1 N : ℝ) := by
  intro I J hIJ
  let k := (tupleCondK D x J I).toNat
  have hcount' : maxSection A J I < 2 ^ (k + 1) := hcount I J hIJ
  by_cases hzero : maxSection A J I = 0
  · rw [hzero]
    simp only [Nat.cast_zero, Real.logb_zero]
    exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hpos : (0 : ℝ) < maxSection A J I := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    have hle : (maxSection A J I : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount'.le
    have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) hpos hle
    have hone : (1 : ℝ) ≤ logSlack 1 N := by
      exact_mod_cast (show 1 ≤ logSlack 1 N by simp [logSlack])
    rw [Nat.cast_pow, Real.logb_pow] at hlog
    norm_num at hlog
    dsimp [k] at hlog ⊢
    linarith

/-- **Typization candidates exist** (the first half of Theorem 211): every tuple of strings of
complexity at most `N` has a typization candidate with an `O(log N)` slack, namely the set of
tuples whose complexity profile is dominated by that of `x`. -/
lemma exists_isTypizationCandidate (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (N : ℕ), 1 < N → ∀ x : Fin n → BitString,
      (∀ i, plainK D (x i) ≤ (N : ℕ∞)) →
      ∃ (m : ℕ) (A : Finset (Fin n → Fin m)), IsTypizationCandidate D x N c A := by
  obtain ⟨cLower, hLower⟩ := exists_conditionalProfileModel_card_lower (n := n) D hD
  refine ⟨max cLower 1, fun N hN x hx => ?_⟩
  obtain ⟨m, A, hmodel⟩ := exists_conditionalProfileModel (n := n) D hD x
  have hnonempty : A.Nonempty := conditionalProfileModel_nonempty hmodel
  have hlower := hLower N hN x hx m A hmodel
  have hslackLower : (logSlack cLower N : ℝ) ≤ logSlack (max cLower 1) N := by
    exact_mod_cast logSlack_mono_left (le_max_left cLower 1) N
  have hcount : ∀ I J : Finset (Fin n), Disjoint I J →
      maxSection A J I < 2 ^ ((tupleCondK D x J I).toNat + 1) := by
    intro I J hIJ
    exact maxSection_conditionalProfileModel_lt_two_pow D hD x A hmodel I J hIJ
  have hupper := logb_maxSection_le_of_profile_count (N := N) hcount
  refine ⟨m, A, hnonempty, ?_, ?_⟩
  · linarith
  · intro I J hIJ
    have hslackUpper : (logSlack 1 N : ℝ) ≤ logSlack (max cLower 1) N := by
      exact_mod_cast logSlack_mono_left (le_max_right cLower 1) N
    exact (hupper I J hIJ).trans
      (add_le_add_right hslackUpper ((tupleCondK D x J I).toNat : ℝ))

end Kolmogorov
