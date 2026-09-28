import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedFamily
import KolmogorovMathlib.MonotoneComplexity.GacsDayRobustWitness

/-!
# Designated charges extracted from witness cylinders

The witness-forcing interface gives a globally incomparable finite family of
cylinders.  This module refines those cylinders to the final depth and selects
an exact finite quota for each family root.  The selected cells are therefore
globally unique and belong to the corresponding root's new gray area.
-/

namespace Kolmogorov

open scoped BigOperators

/-- All final-depth extensions of one witness cylinder. -/
def witnessExtensionsAt (deltaDepth : Nat) (c : BitString) : Finset BitString :=
  (stringsOfLength (deltaDepth - c.length)).image fun w => c ++ w

/-- The extensions of `c` to depth `deltaDepth` number `2 ^ (deltaDepth - c.length)`. -/
@[simp] lemma card_witnessExtensionsAt (deltaDepth : Nat) (c : BitString) :
    (witnessExtensionsAt deltaDepth c).card = 2 ^ (deltaDepth - c.length) := by
  classical
  rw [witnessExtensionsAt, Finset.card_image_of_injective _]
  · exact card_stringsOfLength _
  · intro w v h
    exact List.append_cancel_left h

/-- An extension of `c` has `c` as a prefix, and has length exactly `deltaDepth` once `c` is no
longer than that. -/
lemma mem_witnessExtensionsAt {deltaDepth : Nat} {c p : BitString}
    (hp : p ∈ witnessExtensionsAt deltaDepth c) :
    c <+: p ∧ (c.length ≤ deltaDepth → p.length = deltaDepth) := by
  classical
  rw [witnessExtensionsAt, Finset.mem_image] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  refine ⟨List.prefix_append _ _, fun hle => ?_⟩
  have hwlen : w.length = deltaDepth - c.length :=
    (mem_stringsOfLength _ _).mp hw
  simp [hwlen]
  omega

/-- The final-depth witness cells belonging to one family root. -/
def witnessRootCells {n m : Nat} (deltaDepth : Nat)
    (c : Fin n × Fin m → BitString) (i : Fin n) : Finset BitString :=
  (Finset.univ : Finset (Fin m)).biUnion fun j =>
    witnessExtensionsAt deltaDepth (c (i, j))

/-- Witness cells of different clients are disjoint when the witness strings are pairwise
incomparable. -/
lemma witnessRootCells_pairwiseDisjoint
    {n m deltaDepth : Nat} {c : Fin n × Fin m → BitString}
    (hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    {i i' : Fin n} (hii' : i ≠ i') :
    Disjoint (witnessRootCells deltaDepth c i)
      (witnessRootCells deltaDepth c i') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [witnessRootCells, Finset.mem_biUnion] at hp hp'
  obtain ⟨j, -, hpj⟩ := hp
  obtain ⟨j', -, hpj'⟩ := hp'
  have hpre := (mem_witnessExtensionsAt hpj).1
  have hpre' := (mem_witnessExtensionsAt hpj').1
  exact hc_disj (i, j) (i', j') (by
    intro h
    exact hii' (congrArg Prod.fst h))
      (List.prefix_or_prefix_of_prefix hpre hpre')

/-- For pairwise incomparable witness strings, the cells of a client number the sum of
`2 ^ (deltaDepth - length)` over its witnesses. -/
lemma card_witnessRootCells
    {n m deltaDepth : Nat} {c : Fin n × Fin m → BitString}
    (hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    (i : Fin n) :
    (witnessRootCells deltaDepth c i).card =
      ∑ j : Fin m, 2 ^ (deltaDepth - (c (i, j)).length) := by
  classical
  rw [witnessRootCells, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun j _ => card_witnessExtensionsAt _ _
  · intro j _ j' _ hjj'
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    have hpre := (mem_witnessExtensionsAt hp).1
    have hpre' := (mem_witnessExtensionsAt hp').1
    exact hc_disj (i, j) (i, j') (by
      intro h
      exact hjj' (congrArg Prod.snd h))
        (List.prefix_or_prefix_of_prefix hpre hpre')

/-- Witness cells that extend an allocated string and avoid the unavailable set lie in the new
gray area of that client. -/
lemma witnessRootCells_subset_newGray
    {n m epsDepth deltaDepth : Nat} {A : Allocation}
    {server : FamilyServerMove} {c : Fin n × Fin m → BitString}
    (hed : epsDepth ≤ deltaDepth)
    (hc_len : ∀ p, (c p).length ≤ deltaDepth)
    (hc_anc : ∀ p, ∃ y ∈ getFamilyAlloc server p.1.val [], y <+: c p)
    (hc_avoid : ∀ p, ∀ v ∈ A,
      ¬ ((c p) <+: v ∨ v <+: (c p)))
    (i : Fin n) :
    witnessRootCells deltaDepth c i ⊆
      newGrayCells epsDepth deltaDepth
        (getFamilyAlloc server i.val []).toFinset A.toFinset := by
  classical
  intro p hp
  rw [witnessRootCells, Finset.mem_biUnion] at hp
  obtain ⟨j, -, hpj⟩ := hp
  have hpref := (mem_witnessExtensionsAt hpj).1
  have hlen := (mem_witnessExtensionsAt hpj).2 (hc_len (i, j))
  refine mem_newGrayCells_iff.mpr ⟨hlen, ?_, ?_⟩
  · obtain ⟨y, hy, hyc⟩ := hc_anc (i, j)
    have hyp : y <+: p := hyc.trans hpref
    have htake : p.take epsDepth <+: p := List.take_prefix _ _
    have htakeLen : (p.take epsDepth).length = epsDepth := by
      simp [hlen]
      omega
    exact mem_neighborhoodCells_iff_prefixComparable.mpr
      ⟨htakeLen, y, List.mem_toFinset.mpr hy,
        List.prefix_or_prefix_of_prefix htake hyp⟩
  · intro hmem
    obtain ⟨-, v, hv, hcomp⟩ :=
      mem_neighborhoodCells_iff_prefixComparable.mp hmem
    refine hc_avoid (i, j) v (List.mem_toFinset.mp hv) ?_
    rcases hcomp with hcomp | hcomp
    · exact Or.inl (hpref.trans hcomp)
    · exact List.prefix_or_prefix_of_prefix hpref hcomp

/-- At amplification two, this many final cells have exactly the requested
charged mass for one root. -/
def twoGrayQuota (alphaDepth deltaDepth : Nat) : Nat :=
  2 * 2 ^ (deltaDepth - alphaDepth)

/-- The two-gray quota of cells at depth `deltaDepth` carries mass exactly
`2 * dyadicScale alphaDepth`. -/
lemma twoGrayQuota_mass {alphaDepth deltaDepth : Nat}
    (h : alphaDepth ≤ deltaDepth) :
    (twoGrayQuota alphaDepth deltaDepth : Rat) * dyadicScale deltaDepth =
      2 * dyadicScale alphaDepth := by
  rw [twoGrayQuota]
  push_cast
  unfold dyadicScale
  rw [mul_assoc, two_pow_sub_mul_half_pow h]

/-- A client whose witnesses carry mass at least `2 * dyadicScale alphaDepth` owns at least the
two-gray quota of cells. -/
lemma twoGrayQuota_le_card_witnessRootCells
    {n m alphaDepth deltaDepth : Nat}
    {c : Fin n × Fin m → BitString}
    (had : alphaDepth ≤ deltaDepth)
    (hc_len : ∀ p, (c p).length ≤ deltaDepth)
    (hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    (hmass : ∀ i : Fin n,
      2 * dyadicScale alphaDepth ≤
        ∑ j : Fin m, (1 / 2 : Rat) ^ (c (i, j)).length)
    (i : Fin n) :
    twoGrayQuota alphaDepth deltaDepth ≤
      (witnessRootCells deltaDepth c i).card := by
  have hlen : ∀ j : Fin m, (c (i, j)).length ≤ deltaDepth :=
    fun j => hc_len (i, j)
  have hsum :
      ∑ j : Fin m, (1 / 2 : Rat) ^ (c (i, j)).length =
        ((∑ j : Fin m, 2 ^ (deltaDepth - (c (i, j)).length) : Nat) : Rat) *
          dyadicScale deltaDepth := by
    unfold dyadicScale
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ =>
      (two_pow_sub_mul_half_pow (hlen j)).symm
  have hscale : 0 < dyadicScale deltaDepth := by
    unfold dyadicScale
    positivity
  have hq := twoGrayQuota_mass had
  have hrat :
      (twoGrayQuota alphaDepth deltaDepth : Rat) ≤
        ((∑ j : Fin m,
          2 ^ (deltaDepth - (c (i, j)).length) : Nat) : Rat) := by
    have hm := hmass i
    rw [← hq, hsum] at hm
    nlinarith
  have hnat : twoGrayQuota alphaDepth deltaDepth ≤
      ∑ j : Fin m, 2 ^ (deltaDepth - (c (i, j)).length) := by
    exact_mod_cast hrat
  simpa [card_witnessRootCells hc_disj i] using hnat

/-- Tag a finite selected set with its family-root index. -/
def taggedGrayCharge {n : Nat} (D : Fin n → Finset BitString) :
    Finset (Nat × BitString) :=
  (Finset.univ : Finset (Fin n)).biUnion fun i =>
    (D i).image fun p => (i.val, p)

/-- A tagged cell belongs to the tagged charge exactly when its string belongs to the family
member named by its tag. -/
lemma mem_taggedGrayCharge {n : Nat} {D : Fin n → Finset BitString}
    {z : Nat × BitString} :
    z ∈ taggedGrayCharge D ↔ ∃ i : Fin n, z.1 = i.val ∧ z.2 ∈ D i := by
  classical
  simp only [taggedGrayCharge, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨i, p, hp, rfl⟩
    exact ⟨i, rfl, hp⟩
  · rintro ⟨i, hi, hp⟩
    refine ⟨i, z.2, hp, ?_⟩
    exact Prod.ext hi.symm rfl

/-- The cells of the tagged charge tagged with `i` are exactly the elements of `D i`. -/
lemma taggedGrayCharge_mem_root {n : Nat} {D : Fin n → Finset BitString}
    {i : Fin n} {p : BitString} :
    (i.val, p) ∈ taggedGrayCharge D ↔ p ∈ D i := by
  classical
  rw [mem_taggedGrayCharge]
  constructor
  · rintro ⟨j, hij, hp⟩
    have hji : j = i := Fin.ext hij.symm
    simpa [hji] using hp
  · exact fun hp => ⟨i, rfl, hp⟩

/-- A tagged charge over `n` clients with `K` cells each has `n * K` cells. -/
lemma card_taggedGrayCharge {n K : Nat} {D : Fin n → Finset BitString}
    (hcard : ∀ i, (D i).card = K) :
    (taggedGrayCharge D).card = n * K := by
  classical
  rw [taggedGrayCharge, Finset.card_biUnion]
  · calc
      ∑ i : Fin n, ((D i).image fun p => (i.val, p)).card =
          ∑ i : Fin n, (D i).card := Finset.sum_congr rfl fun i _ =>
            Finset.card_image_of_injective _ fun p q h =>
              congrArg Prod.snd h
      _ = n * K := by simp [hcard]
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro z ⟨p, hp, rfl⟩ ⟨p', hp', hpair⟩
    exact hij (Fin.ext (congrArg Prod.fst hpair).symm)

/-- When the families are pairwise disjoint, a cell of the tagged charge is determined by its
string. -/
lemma taggedGrayCharge_cells_injective
    {n : Nat} {D : Fin n → Finset BitString}
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    {z z' : Nat × BitString}
    (hz : z ∈ taggedGrayCharge D) (hz' : z' ∈ taggedGrayCharge D)
    (heq : z.2 = z'.2) : z = z' := by
  classical
  obtain ⟨i, hi, hzi⟩ := mem_taggedGrayCharge.mp hz
  obtain ⟨j, hj, hzj⟩ := mem_taggedGrayCharge.mp hz'
  have hij : i = j := by
    by_contra hne
    have hd := hdisj i j hne
    have hzj' : z.2 ∈ D j := by simpa [heq] using hzj
    exact (Finset.disjoint_left.mp hd) hzi hzj'
  apply Prod.ext
  · simp [hi, hj, hij]
  · exact heq

/-- Every cell of a tagged charge has a tag below `n` and a string of the declared length. -/
lemma taggedGrayCharge_valid_universe
    {n deltaDepth : Nat} {D : Fin n → Finset BitString}
    (hlen : ∀ i p, p ∈ D i → p.length = deltaDepth)
    {z : Nat × BitString} (hz : z ∈ taggedGrayCharge D) :
    z.1 < n ∧ z.2.length = deltaDepth := by
  obtain ⟨i, hi, hp⟩ := mem_taggedGrayCharge.mp hz
  rw [hi]
  exact ⟨i.isLt, hlen i z.2 hp⟩

/-- The canonical form of a tagged charge with `K` cells per client has `n * K` cells. -/
lemma canonicalGrayCharge_length_of_tagged
    {n deltaDepth K : Nat} {D : Fin n → Finset BitString}
    (hlen : ∀ i p, p ∈ D i → p.length = deltaDepth)
    (hcard : ∀ i, (D i).card = K) :
    (canonicalGrayCharge n deltaDepth (taggedGrayCharge D)).length = n * K := by
  classical
  have hvalid : ∀ z ∈ taggedGrayCharge D,
      z.1 < n ∧ z.2.length = deltaDepth :=
    fun z hz => taggedGrayCharge_valid_universe hlen hz
  rw [← List.toFinset_card_of_nodup
    (canonicalGrayCharge_nodup n deltaDepth (taggedGrayCharge D))]
  have heq :
      (canonicalGrayCharge n deltaDepth (taggedGrayCharge D)).toFinset =
        taggedGrayCharge D := by
    ext z
    simp only [List.mem_toFinset, mem_canonicalGrayCharge hvalid]
  rw [heq, card_taggedGrayCharge hcard]

/-- The canonical form of a tagged charge keeps, at each root, as many cells as that client had. -/
lemma canonicalGrayCharge_root_length_of_tagged
    {n deltaDepth : Nat} {D : Fin n → Finset BitString}
    (hlen : ∀ i p, p ∈ D i → p.length = deltaDepth)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (i : Fin n) :
    (grayChargeAtRoot i.val
      (canonicalGrayCharge n deltaDepth (taggedGrayCharge D))).length =
        (D i).card := by
  classical
  let G := canonicalGrayCharge n deltaDepth (taggedGrayCharge D)
  have hvalid : ∀ z ∈ taggedGrayCharge D,
      z.1 < n ∧ z.2.length = deltaDepth :=
    fun z hz => taggedGrayCharge_valid_universe hlen hz
  have hcells : (G.map Prod.snd).Nodup :=
    canonicalGrayCharge_cells_nodup fun z hz z' hz' heq =>
      taggedGrayCharge_cells_injective hdisj hz hz' heq
  have hrootCells : ((grayChargeAtRoot i.val G).map Prod.snd).Nodup := by
    apply List.Nodup.map_on
      (l := grayChargeAtRoot i.val G)
      (fun z hz z' hz' heq => ?_)
      ((canonicalGrayCharge_nodup n deltaDepth (taggedGrayCharge D)).filter _)
    exact taggedGrayCharge_cells_injective hdisj
      ((mem_canonicalGrayCharge hvalid).mp (mem_grayChargeAtRoot.mp hz).1)
      ((mem_canonicalGrayCharge hvalid).mp (mem_grayChargeAtRoot.mp hz').1) heq
  rw [← List.length_map, ← List.toFinset_card_of_nodup hrootCells]
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_map, mem_grayChargeAtRoot]
  constructor
  · rintro ⟨z, ⟨hz, hzi⟩, hzp⟩
    have hzF := (mem_canonicalGrayCharge hvalid).mp hz
    obtain ⟨j, hj, hzD⟩ := mem_taggedGrayCharge.mp hzF
    have hji : j = i := Fin.ext (hj ▸ hzi)
    simpa [← hzp, hji] using hzD
  · intro hp
    refine ⟨(i.val, p), ⟨?_, rfl⟩, rfl⟩
    exact (mem_canonicalGrayCharge hvalid).mpr
      (taggedGrayCharge_mem_root.mpr hp)

/-- A constant per-root request sums to length times the constant. -/
lemma totalRootRequestOnList_const {c : FamilyClientMove} {alpha : Rat} :
    ∀ {I : List Nat}, (∀ i ∈ I, getFamilyReq c i [] = alpha) →
      totalRootRequestOnList I c = (I.length : Rat) * alpha := by
  intro I
  induction I with
  | nil => intro _; simp [totalRootRequestOnList]
  | cons i I ih =>
      intro hall
      have hi := hall i (List.mem_cons_self ..)
      have htail := ih fun j hj => hall j (List.mem_cons_of_mem i hj)
      unfold totalRootRequestOnList at htail ⊢
      rw [List.foldr_cons, htail, hi]
      simp only [List.length_cons]
      push_cast
      ring

/-- Under a constant per-root request function, the total root request equals `n * alpha`. -/
private lemma totalRootRequest_const {n : Nat} {client : FamilyClientMove} {alpha : Rat}
    (hroot : ∀ i, i < n → getFamilyReq client i [] = alpha) :
    totalRootRequest n client = (n : Rat) * alpha := by
  unfold totalRootRequest
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hroot i.val i.isLt]
  simp

/-- The cell family `c` is a witness family at depth `deltaDepth`: every cell is short enough,
extends one of the allocated cells of the server move, and is incomparable with every cell
of `A`. -/
private def WitnessCellFamily {n m : Nat} (deltaDepth : Nat) (A : Allocation)
    (server : FamilyServerMove) (c : Fin n × Fin m → BitString) : Prop :=
  (∀ p, (c p).length ≤ deltaDepth) ∧
    (∀ p, ∃ y ∈ getFamilyAlloc server p.1.val [], y <+: c p) ∧
    ∀ p, ∀ v ∈ A, ¬ ((c p) <+: v ∨ v <+: (c p))

/-- Cells in the tagged gray charge constructed from witness root subsets belong to new gray. -/
private lemma taggedGrayCharge_mem_newGray
    {n m epsDepth deltaDepth : Nat} {A : Allocation} {server : FamilyServerMove}
    {c : Fin n × Fin m → BitString} (hed : epsDepth ≤ deltaDepth)
    (hfam : WitnessCellFamily deltaDepth A server c)
    {D : Fin n → Finset BitString}
    (hDsub : ∀ i, D i ⊆ witnessRootCells deltaDepth c i)
    {z : Nat × BitString} (hz : z ∈ taggedGrayCharge D) :
    z.1 < n ∧ z.2 ∈ newGrayCellsList epsDepth deltaDepth (getFamilyAlloc server z.1 []) A := by
  obtain ⟨hc_len, hc_anc, hc_avoid⟩ := hfam
  obtain ⟨i, hi, hpD⟩ := mem_taggedGrayCharge.mp hz
  refine ⟨hi ▸ i.isLt, ?_⟩
  have hpW := hDsub i hpD
  have hpGray := witnessRootCells_subset_newGray hed hc_len hc_anc hc_avoid i hpW
  rw [← toFinset_newGrayCellsList hed, List.mem_toFinset] at hpGray
  simpa [hi] using hpGray

/-- The filtered charge mass over a sublist of roots with uniform mass `M` is `I.length * M`. -/
private lemma grayChargeMass_filter_range_sublist_const
    {n deltaDepth : Nat} {G : FamilyGrayCharge} {M : Rat} {I : List Nat}
    (hIsub : List.Sublist I (List.range n))
    (hrootMass : ∀ i : Fin n, grayChargeMass deltaDepth (grayChargeAtRoot i.val G) = M) :
    grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈ I)) = (I.length : Rat) * M := by
  have hInodup : I.Nodup := hIsub.nodup List.nodup_range
  have hIlt : ∀ i ∈ I, i < n := fun i hi => List.mem_range.mp (hIsub.mem hi)
  rw [grayChargeMass_filter_mem hInodup]
  have hmap : (I.map fun i => grayChargeMass deltaDepth (grayChargeAtRoot i G)) =
      I.map fun _ => M := by
    apply List.map_congr_left
    intro i hi
    exact hrootMass ⟨i, hIlt i hi⟩
  rw [hmap, List.map_const', List.sum_replicate, nsmul_eq_mul]

/-- Witness forcing at amplification two supplies an exact designated charge.
The charge uses only witness-cylinder extensions, hence different roots never
own the same final cell. -/
theorem exists_familyGrayChargeAtB_two_of_witnesses
    (eta : Rat) {alphaDepth epsDepth deltaDepth n m : Nat}
    {A : Allocation} {client : FamilyClientMove} {server : FamilyServerMove}
    (heta : 1 ≤ eta)
    (had : alphaDepth ≤ deltaDepth)
    (hed : epsDepth ≤ deltaDepth)
    (hroot : ∀ i, i < n →
      getFamilyReq client i [] = dyadicScale alphaDepth)
    (c : Fin n × Fin m → BitString)
    (hc_len : ∀ p, (c p).length ≤ deltaDepth)
    (hc_anc : ∀ p,
      ∃ y ∈ getFamilyAlloc server p.1.val [], y <+: c p)
    (hc_disj : ∀ p q, p ≠ q →
      ¬ ((c p) <+: (c q) ∨ (c q) <+: (c p)))
    (hc_avoid : ∀ p, ∀ v ∈ A,
      ¬ ((c p) <+: v ∨ v <+: (c p)))
    (hmass : ∀ i : Fin n,
      2 * dyadicScale alphaDepth ≤
        ∑ j : Fin m, (1 / 2 : Rat) ^ (c (i, j)).length) :
    ∃ G ∈ (familyGrayChargeUniverse n deltaDepth).sublists,
      familyGrayChargeAtB eta 2 (dyadicScale alphaDepth)
        ((3 / 4 : Rat) * dyadicScale alphaDepth)
        epsDepth deltaDepth n A client server G = true := by
  classical
  have hquota : ∀ i : Fin n,
      twoGrayQuota alphaDepth deltaDepth ≤
        (witnessRootCells deltaDepth c i).card :=
    fun i => twoGrayQuota_le_card_witnessRootCells had hc_len hc_disj hmass i
  choose D hDsub hDcard using fun i : Fin n =>
    Finset.exists_subset_card_eq (hquota i)
  have hDlen : ∀ i p, p ∈ D i → p.length = deltaDepth := by
    intro i p hp
    have hpW := hDsub i hp
    rw [witnessRootCells, Finset.mem_biUnion] at hpW
    obtain ⟨j, -, hpj⟩ := hpW
    exact (mem_witnessExtensionsAt hpj).2 (hc_len (i, j))
  have hDdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j) := by
    intro i j hij
    exact (witnessRootCells_pairwiseDisjoint hc_disj hij).mono
      (hDsub i) (hDsub j)
  let F : Finset (Nat × BitString) := taggedGrayCharge D
  let G : FamilyGrayCharge := canonicalGrayCharge n deltaDepth F
  have hFvalid : ∀ z ∈ F, z.1 < n ∧ z.2.length = deltaDepth := by
    intro z hz
    exact taggedGrayCharge_valid_universe hDlen hz
  have hGsub : G ∈ (familyGrayChargeUniverse n deltaDepth).sublists := by
    apply List.mem_sublists.mpr
    exact canonicalGrayCharge_sublist n deltaDepth F
  have hGcells : (G.map Prod.snd).Nodup := by
    exact canonicalGrayCharge_cells_nodup fun z hz z' hz' heq =>
      taggedGrayCharge_cells_injective hDdisj hz hz' heq
  have hrootLen : ∀ i : Fin n,
      (grayChargeAtRoot i.val G).length =
        twoGrayQuota alphaDepth deltaDepth := by
    intro i
    rw [show G = canonicalGrayCharge n deltaDepth (taggedGrayCharge D) from rfl,
      canonicalGrayCharge_root_length_of_tagged hDlen hDdisj i,
      hDcard i]
  have hGlen : G.length = n * twoGrayQuota alphaDepth deltaDepth := by
    rw [show G = canonicalGrayCharge n deltaDepth (taggedGrayCharge D) from rfl,
      canonicalGrayCharge_length_of_tagged hDlen hDcard]
  have hrootMass : ∀ i : Fin n,
      grayChargeMass deltaDepth (grayChargeAtRoot i.val G) =
        2 * dyadicScale alphaDepth := by
    intro i
    unfold grayChargeMass grayMassOfCount
    rw [hrootLen i]
    exact twoGrayQuota_mass had
  have htotalReq : totalRootRequest n client =
      (n : Rat) * dyadicScale alphaDepth := totalRootRequest_const hroot
  have htotalMass : grayChargeMass deltaDepth G =
      (n : Rat) * (2 * dyadicScale alphaDepth) := by
    unfold grayChargeMass grayMassOfCount
    rw [hGlen]
    push_cast
    change (n : Rat) * (twoGrayQuota alphaDepth deltaDepth : Rat) *
      dyadicScale deltaDepth = _
    calc
      _ = (n : Rat) * ((twoGrayQuota alphaDepth deltaDepth : Rat) *
          dyadicScale deltaDepth) := by ring
      _ = (n : Rat) * (2 * dyadicScale alphaDepth) := by
        rw [twoGrayQuota_mass had]
  refine ⟨G, hGsub, ?_⟩
  unfold familyGrayChargeAtB
  simp only [Bool.and_eq_true, grayChargeCellsUniqueB_eq_true_iff,
    List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hGcells, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro z hz
    have hzF : z ∈ F := (mem_canonicalGrayCharge hFvalid).mp hz
    exact taggedGrayCharge_mem_newGray hed ⟨hc_len, hc_anc, hc_avoid⟩ hDsub hzF
  · intro i hi
    have hin : i < n := List.mem_range.mp hi
    let fi : Fin n := ⟨i, hin⟩
    have hreq : getFamilyReq client i [] = dyadicScale alphaDepth := hroot i hin
    have hmassEq : grayChargeMass deltaDepth (grayChargeAtRoot i G) =
        2 * dyadicScale alphaDepth := hrootMass fi
    have halpha : 0 ≤ dyadicScale alphaDepth := by
      unfold dyadicScale
      positivity
    constructor
    · constructor
      · rw [hreq]; linarith
      · rw [hreq]
    · rw [hmassEq, hreq]; nlinarith
  · rw [htotalMass]
    have halpha : 0 ≤ dyadicScale alphaDepth := by unfold dyadicScale; positivity
    have hn : 0 ≤ (n : Rat) := by positivity
    nlinarith
  · rw [htotalMass, htotalReq]
    ring_nf
    exact le_rfl
  · intro I hImem
    have hIsub : List.Sublist I (List.range n) := List.mem_sublists.mp hImem
    have hIlt : ∀ i ∈ I, i < n := fun i hi => List.mem_range.mp (hIsub.mem hi)
    have hIlen : I.length ≤ n := by simpa using hIsub.length_le
    have hmassI : grayChargeMass deltaDepth (G.filter fun z => decide (z.1 ∈ I)) =
        (I.length : Rat) * (2 * dyadicScale alphaDepth) :=
      grayChargeMass_filter_range_sublist_const hIsub hrootMass
    have hreqI : totalRootRequestOnList I client =
        (I.length : Rat) * dyadicScale alphaDepth :=
      totalRootRequestOnList_const fun i hi => hroot i (hIlt i hi)
    rw [hmassI, hreqI, htotalReq]
    have halpha : 0 ≤ dyadicScale alphaDepth := by unfold dyadicScale; positivity
    have hlen : (I.length : Rat) ≤ (n : Rat) := by exact_mod_cast hIlen
    nlinarith

/-- Package amplification-two witness forcing as the charged family-game
interface.  The weak gray inequalities and the designated charge are proved at
the same witness-forcing time. -/
theorem chargedGrayFamilyGameSpec_two_of_witnessForcing
    (eta : Rat) (h b alphaDepth epsDepth deltaDepth n : Nat) [NeZero n]
    (A : Allocation) (sigma : ClientFamilyStrategy)
    (heta : 1 ≤ eta)
    (hForcing : FamilyWitnessForcing 2 h b alphaDepth deltaDepth n A sigma)
    (hweak : GrayFamilyGameSpec 2 (dyadicScale alphaDepth)
      ((3 / 4 : Rat) * dyadicScale alphaDepth)
      epsDepth deltaDepth h b n A sigma)
    (hroot : ∀ sm, familyServerPlayLegal n b A sm → ∀ t i, i < n →
      getFamilyReq (playClientFamily A n sigma sm t) i [] =
        dyadicScale alphaDepth)
    (had : alphaDepth ≤ deltaDepth)
    (hed : epsDepth ≤ deltaDepth) :
    ChargedGrayFamilyGameSpec eta 2 (dyadicScale alphaDepth)
      ((3 / 4 : Rat) * dyadicScale alphaDepth)
      epsDepth deltaDepth h b n A sigma := by
  refine ⟨hweak, ?_⟩
  intro sm hsm
  by_cases hwin : familyClientWinsUnservedPositive n h b
      (playClientFamily A n sigma sm) sm
  · exact Or.inl hwin
  · right
    have hserved : ∀ i < n, ∀ t0 (x : GacsDayNode), x.length ≤ h →
        (∀ dg ∈ x, dg < b) →
        0 < getReq
          (familyClientMoveAt (playClientFamily A n sigma sm t0) i) x →
        ∃ t, Serves (getAlloc (familyServerMoveAt (sm t) i) x)
          (getReq
            (familyClientMoveAt (playClientFamily A n sigma sm t0) i) x) := by
      intro i hi t0 x hlen hdig hpos
      by_contra hcon
      push_neg at hcon
      exact hwin ⟨i, hi, t0, x, hlen, hdig, hcon, hpos⟩
    obtain ⟨T, m, c, hc_len, hc_anc, hc_disj, hc_avoid,
        hmass_each, _⟩ := hForcing sm hsm hserved
    have hc_anc_all : ∀ p,
        ∃ y ∈ familyAllocated n T sm, y <+: c p := by
      intro p
      obtain ⟨y, hy, hyp⟩ := hc_anc p
      exact ⟨y, Finset.mem_biUnion.mpr
        ⟨p.1, Finset.mem_univ _, List.mem_toFinset.mpr hy⟩, hyp⟩
    have hgray := familyGrayMass_ge_of_incomparable_witnesses
      (epsDepth := epsDepth) (deltaDepth := deltaDepth)
      (n := n) (T := T) (A := A) (sm := sm)
      hed c hc_len hc_anc_all hc_disj hc_avoid
    have hsum :
        (n : Rat) * (2 * dyadicScale alphaDepth) ≤
          ∑ p : Fin n × Fin m, (1 / 2 : Rat) ^ (c p).length := by
      rw [Fintype.sum_prod_type]
      calc
        (n : Rat) * (2 * dyadicScale alphaDepth) =
            ∑ _i : Fin n, 2 * dyadicScale alphaDepth := by simp
        _ ≤ ∑ i : Fin n,
            ∑ j : Fin m, (1 / 2 : Rat) ^ (c (i, j)).length :=
          Finset.sum_le_sum fun i _ => hmass_each i
    have hrootEq :
        totalRootRequest n (playClientFamily A n sigma sm T) =
          (n : Rat) * dyadicScale alphaDepth := by
      unfold totalRootRequest
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        hroot sm hsm T i.val i.isLt]
      simp
    have hdy : 0 ≤ dyadicScale alphaDepth := by
      unfold dyadicScale
      positivity
    have hn : 0 ≤ (n : Rat) := by positivity
    have htarget :
        (n : Rat) * ((3 / 4 : Rat) * dyadicScale alphaDepth) ≤
          familyGrayMass epsDepth deltaDepth n T A sm := by
      calc
        _ ≤ (n : Rat) * (2 * dyadicScale alphaDepth) := by nlinarith
        _ ≤ _ := le_trans hsum hgray
    have hamp :
        2 * totalRootRequest n (playClientFamily A n sigma sm T) ≤
          familyGrayMass epsDepth deltaDepth n T A sm := by
      rw [hrootEq]
      calc
        2 * ((n : Rat) * dyadicScale alphaDepth) =
            (n : Rat) * (2 * dyadicScale alphaDepth) := by ring
        _ ≤ _ := le_trans hsum hgray
    have hprogress :
        (n : Rat) * ((3 / 4 : Rat) * dyadicScale alphaDepth) ≤
          2 * totalRootRequest n
            (playClientFamily A n sigma sm T) := by
      rw [hrootEq]
      nlinarith
    have hweakAt :
        familyGrayGoalAtB 2
          ((3 / 4 : Rat) * dyadicScale alphaDepth)
          epsDepth deltaDepth n A
          (playClientFamily A n sigma sm T)
          (familyAllocatedOnList (List.range n) (sm T)) = true := by
      have halloc : familyAllocatedOnList (List.range n) (sm T) =
          familyAllocatedList n T sm := by
        rfl
      rw [halloc]
      apply (familyGrayGoalAtB_eq_true_iff hed n T A
        (playClientFamily A n sigma sm) sm).2
      exact ⟨htarget, hamp, hprogress⟩
    obtain ⟨G, hGsub, hGvalid⟩ :=
      exists_familyGrayChargeAtB_two_of_witnesses eta heta had hed
        (fun i hi => hroot sm hsm T i hi)
        c hc_len hc_anc hc_disj hc_avoid hmass_each
    refine ⟨T, ?_⟩
    unfold familyChargedGrayGoalAtB
    simp only [Bool.and_eq_true, List.any_eq_true]
    exact ⟨hweakAt, G, hGsub, hGvalid⟩

end Kolmogorov
