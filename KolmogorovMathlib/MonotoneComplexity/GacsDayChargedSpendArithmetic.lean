import KolmogorovMathlib.MonotoneComplexity.GacsDayChargedController

/-!
# Arithmetic and finite capacity of the spend phase
-/

namespace Kolmogorov

/-- A spend pass opens exactly one pair of children per deficient client. -/
lemma grayChargedSpendCount_eq
    {q a e : Nat} (_hae : a <= e) :
    grayChargedSpendCount q a e = 1 := rfl

/-- The source children carry the whole root mass: their number times `dyadicScale e` is
`dyadicScale a`. -/
lemma grayChargedSource_mass
    {a e : Nat} (hae : a <= e) :
    (grayChargedSourceCount a e : Rat) * dyadicScale e =
      dyadicScale a := by
  simpa [grayChargedSourceCount] using two_pow_sub_mul_dyadicScale hae

/-- One spend sub-root at depth `a + 3` carries exactly an eighth of the root
scale. -/
lemma grayChargedSpendCount_mass
    {q a e : Nat} (_hae : a <= e) :
    (grayChargedSpendCount q a e : Rat) *
        dyadicScale (grayChargedSpendAlphaDepth a) = dyadicScale a / 8 := by
  unfold grayChargedSpendCount grayChargedSpendAlphaDepth dyadicScale
  push_cast
  rw [pow_add]
  ring

/-- The spare children have room for all eight spend passes. -/
lemma grayChargedSpend_capacity
    {q L a e : Nat} (_hae : a <= e) :
    8 * grayChargedSpendCount q a e <=
      (ladderBranching (grayTailBaseBranch q L) a e -
          grayChargedSourceCount a e) *
        ladderBranching (grayTailBaseBranch q L) a e := by
  have hb : 16 <= ladderBranching (grayTailBaseBranch q L) a e := by
    unfold ladderBranching grayTailBaseBranch
    have h16 : (16 : Nat) <= 256 * (q + 1) := by nlinarith
    have hpow : (1 : Nat) <= 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) :=
      Nat.one_le_two_pow
    calc (16 : Nat) <= 256 * (q + 1) := h16
      _ <= 256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)) := by
          nlinarith
      _ <= max 2 (256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1))) :=
          le_max_right _ _
      _ <= max (2 * 2 ^ (e - a))
          (max 2 (256 * (q + 1) * 2 ^ (256 * (q + 1) ^ 2 * L + 256 * (q + 1)))) :=
          le_max_right _ _
  have hsource : 2 * grayChargedSourceCount a e <=
      ladderBranching (grayTailBaseBranch q L) a e := by
    unfold ladderBranching grayChargedSourceCount
    exact le_max_left _ _
  set b := ladderBranching (grayTailBaseBranch q L) a e with hbdef
  have hroom : 1 <= b - grayChargedSourceCount a e := by
    have hs1 : 1 <= grayChargedSourceCount a e := Nat.one_le_two_pow
    omega
  calc 8 * grayChargedSpendCount q a e = 8 := by
        unfold grayChargedSpendCount; ring
    _ <= 1 * b := by omega
    _ <= (b - grayChargedSourceCount a e) * b :=
        Nat.mul_le_mul_right b hroom

/-- The spare pairs are pairwise distinct. -/
lemma grayChargedSparePairs_nodup (b source : Nat) :
    (grayChargedSparePairs b source).Nodup := by
  rw [grayChargedSparePairs, List.nodup_flatMap]
  constructor
  · intro c hc
    exact (List.nodup_finRange b).map fun d d' h => congrArg Prod.snd h
  · refine ((List.nodup_finRange b).drop).imp ?_
    intro c c' hne
    change (List.map (fun d => (c, d)) (List.finRange b)).Disjoint
      (List.map (fun d => (c', d)) (List.finRange b))
    rw [List.disjoint_iff_ne]
    intro x hx y hy heq
    obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hx
    obtain ⟨d', hd', hdy⟩ := List.mem_map.mp hy
    have hpairs : (c, d) = (c', d') := hdx.trans (heq.trans hdy.symm)
    exact hne (congrArg Prod.fst hpairs)

/-- There are `(b - source) * b` spare pairs. -/
@[simp] lemma grayChargedSparePairs_length (b source : Nat) :
    (grayChargedSparePairs b source).length = (b - source) * b := by
  simp [grayChargedSparePairs, List.length_flatMap]

/-- The spend pairs of a pass are pairwise distinct. -/
lemma grayChargedSpendPairs_nodup (b source count pass : Nat) :
    (grayChargedSpendPairs b source count pass).Nodup := by
  exact (grayChargedSparePairs_nodup b source).drop.take

/-- As long as the passes up to `pass` fit into the spare pairs, pass `pass` gets exactly `count`
pairs. -/
lemma grayChargedSpendPairs_length_of_le
    {b source count pass : Nat}
    (hfit : (pass + 1) * count <= (b - source) * b) :
    (grayChargedSpendPairs b source count pass).length = count := by
  simp only [grayChargedSpendPairs, List.length_take, List.length_drop,
    grayChargedSparePairs_length]
  rw [Nat.min_eq_left]
  have hadd : pass * count + count <= (b - source) * b := by
    simpa [Nat.add_mul] using hfit
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hadd)

/-- In the charged construction each of the eight passes gets exactly
`grayChargedSpendCount q a e` pairs. -/
lemma grayChargedSpendPairs_length
    {q L a e pass : Nat} (hae : a <= e) (hpass : pass < 8) :
    (grayChargedSpendPairs
      (ladderBranching (grayTailBaseBranch q L) a e)
      (grayChargedSourceCount a e)
      (grayChargedSpendCount q a e) pass).length =
        grayChargedSpendCount q a e := by
  apply grayChargedSpendPairs_length_of_le
  have hcap := grayChargedSpend_capacity (q := q) (L := L) hae
  have hmul : (pass + 1) * grayChargedSpendCount q a e <=
      8 * grayChargedSpendCount q a e :=
    Nat.mul_le_mul_right _ (by omega)
  exact le_trans hmul hcap

private lemma disjoint_slices_of_le {α : Type*}
    {l : List α} {i n j m : Nat} (hl : l.Nodup) (hij : i + n <= j) :
    ((l.drop i).take n).Disjoint ((l.drop j).take m) := by
  rw [List.disjoint_iff_ne]
  intro x hx y hy
  have hy0 : y ∈ l.drop j := List.mem_of_mem_take hy
  have hj : j = i + n + (j - (i + n)) := by omega
  have hy1 : y ∈ (l.drop (i + n)).drop (j - (i + n)) := by
    rw [List.drop_drop]
    rwa [← hj]
  have hy2 : y ∈ l.drop (i + n) := List.mem_of_mem_drop hy1
  have hy3 : y ∈ (l.drop i).drop n := by
    rw [List.drop_drop]
    exact hy2
  exact List.Pairwise.rel_of_mem_take_of_mem_drop hl.drop hx hy3

/-- Different passes use disjoint sets of spend pairs. -/
lemma grayChargedSpendPairs_disjoint
    {b source count pass pass' : Nat} (hpass : pass < pass') :
    (grayChargedSpendPairs b source count pass).Disjoint
      (grayChargedSpendPairs b source count pass') := by
  unfold grayChargedSpendPairs
  apply disjoint_slices_of_le (grayChargedSparePairs_nodup b source)
  simpa [Nat.succ_eq_add_one, Nat.add_mul] using
    Nat.mul_le_mul_right count (Nat.succ_le_of_lt hpass)

/-- An index left in `(List.finRange b).drop source` is at least `source`. -/
lemma finRange_drop_val_ge
    {b source : Nat} {c : Fin b}
    (hc : c ∈ (List.finRange b).drop source) : source <= c.val := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hc
  have htotal : source + i < (List.finRange b).length := by
    simp only [List.length_drop, List.length_finRange] at hi ⊢
    omega
  rw [List.getElem_drop] at hget
  rw [List.getElem_finRange htotal] at hget
  have hval := congrArg Fin.val hget
  simp at hval
  omega

/-- The first child of a spare pair is a spare child, of index at least `source`. -/
lemma grayChargedSparePairs_first_ge
    {b source : Nat} {p : Fin b × Fin b}
    (hp : p ∈ grayChargedSparePairs b source) : source <= p.1.val := by
  rw [grayChargedSparePairs, List.mem_flatMap] at hp
  obtain ⟨c, hc, hpc⟩ := hp
  rw [List.mem_map] at hpc
  obtain ⟨d, hd, hpair⟩ := hpc
  subst p
  exact finRange_drop_val_ge hc

/-- The first child of a spend pair is a spare child, of index at least `source`. -/
lemma grayChargedSpendPairs_first_ge
    {b source count pass : Nat} {p : Fin b × Fin b}
    (hp : p ∈ grayChargedSpendPairs b source count pass) : source <= p.1.val := by
  apply grayChargedSparePairs_first_ge
  exact List.mem_of_mem_drop (List.mem_of_mem_take hp)

/-- The deficient roots are listed without repetition. -/
lemma grayChargedDeficientRoots_nodup {n b : Nat}
    (source : Nat) (threshold eps alpha : Rat) (frozen : GrayTailFrozen n b) :
    (grayChargedDeficientRoots source threshold eps alpha frozen).Nodup := by
  exact (List.nodup_finRange n).filter _

/-- The slots a spend pass opens are pairwise distinct. -/
lemma grayChargedSpendSlots_nodup {n b : Nat}
    (source count pass : Nat) (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n b) :
    (grayChargedSpendSlots source count pass threshold eps alpha frozen).Nodup := by
  rw [grayChargedSpendSlots, List.nodup_flatMap]
  constructor
  · intro i hi
    exact (grayChargedSpendPairs_nodup b source count pass).map fun p p' h =>
      congrArg Prod.snd h
  · refine (grayChargedDeficientRoots_nodup source threshold eps alpha frozen).imp ?_
    intro i i' hne
    change (List.map (fun p => (i, p.1, p.2)) (grayChargedSpendPairs b source count pass)).Disjoint
      (List.map (fun p => (i', p.1, p.2)) (grayChargedSpendPairs b source count pass))
    rw [List.disjoint_iff_ne]
    intro x hx y hy heq
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    obtain ⟨p', hp', hpy⟩ := List.mem_map.mp hy
    have hslots : (i, p.1, p.2) = (i', p'.1, p'.2) :=
      hpx.trans (heq.trans hpy.symm)
    exact hne (congrArg Prod.fst hslots)

/-- A spend pass opens `grayChargedSpendCount q a e` slots per deficient client. -/
lemma grayChargedSpendSlots_length
    {q L n a e pass : Nat} (hae : a <= e) (hpass : pass < 8)
    (threshold eps alpha : Rat)
    (frozen : GrayTailFrozen n (ladderBranching (grayTailBaseBranch q L) a e)) :
    (grayChargedSpendSlots (grayChargedSourceCount a e)
      (grayChargedSpendCount q a e) pass threshold eps alpha frozen).length =
        (grayChargedDeficientRoots (grayChargedSourceCount a e)
          threshold eps alpha frozen).length * grayChargedSpendCount q a e := by
  unfold grayChargedSpendSlots
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [grayChargedSpendPairs_length (q := q) (L := L)
    (a := a) (e := e) hae hpass]
  simp

/-- Every slot of a spend pass sits at a spare child, of index at least `source`. -/
lemma grayChargedSpendSlots_son_ge {n b : Nat}
    {source count pass : Nat} {threshold eps alpha : Rat}
    {frozen : GrayTailFrozen n b} {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSpendSlots source count pass
      threshold eps alpha frozen) : source <= s.2.1.val := by
  rw [grayChargedSpendSlots, List.mem_flatMap] at hs
  obtain ⟨i, hi, hsi⟩ := hs
  rw [List.mem_map] at hsi
  obtain ⟨p, hp, hps⟩ := hsi
  have hge := grayChargedSpendPairs_first_ge hp
  have hson := congrArg (fun z => z.2.1.val) hps
  calc
    source <= p.1.val := hge
    _ = s.2.1.val := hson

/-- The two children named by a slot of a spend pass form one of the spend pairs of that pass. -/
lemma grayChargedSpendSlots_pair {n b : Nat}
    {source count pass : Nat} {threshold eps alpha : Rat}
    {frozen : GrayTailFrozen n b} {s : GrayTailSlot n b}
    (hs : s ∈ grayChargedSpendSlots source count pass
      threshold eps alpha frozen) :
    (s.2.1, s.2.2) ∈ grayChargedSpendPairs b source count pass := by
  rw [grayChargedSpendSlots, List.mem_flatMap] at hs
  obtain ⟨i, hi, hsi⟩ := hs
  rw [List.mem_map] at hsi
  obtain ⟨p, hp, hps⟩ := hsi
  have hpair := congrArg Prod.snd hps
  simpa using hpair ▸ hp

/-- Slots that live at source children are disjoint from the slots of any spend pass. -/
lemma grayChargedSource_disjoint_spend {n b : Nat}
    {source count pass : Nat} {slots : List (GrayTailSlot n b)}
    {threshold eps alpha : Rat} {frozen : GrayTailFrozen n b}
    (hsource : forall s, s ∈ slots -> s.2.1.val < source) :
    slots.Disjoint (grayChargedSpendSlots source count pass
      threshold eps alpha frozen) := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  have hslt := hsource s hs
  have htge := grayChargedSpendSlots_son_ge ht
  rw [heq] at hslt
  omega

/-- Different spend passes open disjoint slots. -/
lemma grayChargedSpendSlots_disjoint {n b : Nat}
    {source count pass pass' : Nat}
    {threshold eps alpha threshold' eps' alpha' : Rat}
    {frozen frozen' : GrayTailFrozen n b} (hpass : pass < pass') :
    (grayChargedSpendSlots source count pass threshold eps alpha frozen).Disjoint
      (grayChargedSpendSlots source count pass'
        threshold' eps' alpha' frozen') := by
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  have hsp := grayChargedSpendSlots_pair hs
  have htp := grayChargedSpendSlots_pair ht
  have hdisj := grayChargedSpendPairs_disjoint
    (b := b) (source := source) (count := count) hpass
  rw [List.disjoint_iff_ne] at hdisj
  exact hdisj (s.2.1, s.2.2) hsp (t.2.1, t.2.2) htp
    (congrArg Prod.snd heq)

/-- Frozen rounds that only use source children are disjoint from the slots of any spend pass. -/
lemma grayChargedFrozenSlots_source_disjoint_spend {n b : Nat}
    {source count pass : Nat} {frozen0 frozen : GrayTailFrozen n b}
    {threshold eps alpha : Rat}
    (hsource : forall p, p ∈ frozen0 ->
      forall s, s ∈ p.slots -> s.2.1.val < source) :
    (grayTailFrozenSlots frozen0).Disjoint
      (grayChargedSpendSlots source count pass threshold eps alpha frozen) := by
  apply grayChargedSource_disjoint_spend
  intro s hs
  rw [grayTailFrozenSlots, List.mem_flatMap] at hs
  obtain ⟨p, hp, hsp⟩ := hs
  exact hsource p hp s hsp

end Kolmogorov
