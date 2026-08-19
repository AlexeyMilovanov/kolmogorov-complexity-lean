import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Properties

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- The cardinality of the intersection of two lists, counted extensionally.
The deduplicated-list presentation is convenient for the computability proof. -/
def t1SparseIntersectionCard {α : Type} [DecidableEq α]
    (A C : List α) : Nat :=
  ((A.filter fun x => decide (x ∈ C)).dedup).length

theorem t1SparseIntersectionCard_eq {α : Type} [DecidableEq α]
    (A C : List α) :
    t1SparseIntersectionCard A C = (A.toFinset ∩ C.toFinset).card := by
  unfold t1SparseIntersectionCard
  rw [← List.card_toFinset, List.toFinset_filter]
  congr 1
  ext x
  simp

def t1SparseCandidateValid {α : Type} [DecidableEq α]
    (cand : List α) (Cs : List (List α)) (N t : Nat) : Bool :=
  cand.length == N &&
  Cs.all (fun C => decide (t1SparseIntersectionCard cand C ≤ t))

def t1SparseSubsetSelectorList {α : Type} [DecidableEq α]
    (U : List α) (Cs : List (List α)) (N t : Nat) : List α :=
  match U.sublists.find? (fun cand => t1SparseCandidateValid cand Cs N t) with
  | some cand => cand
  | none => []

private theorem t1ListDedupPrimrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (fun l : List α => l.dedup) := by
  have hmem := @decide_mem_primrec α _ _
  have hbool : Primrec (fun p : List α × (α × List α) =>
      decide (p.2.1 ∈ p.2.2)) :=
    hmem.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂
      (fun (_ : List α) (q : α × List α) =>
        if q.1 ∈ q.2 then q.2 else q.1 :: q.2) := by
    have h := Primrec.cond hbool (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
    exact h.of_eq fun p => by
      cases hq : decide (p.2.1 ∈ p.2.2) <;> simp_all
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a l ih =>
        change List.foldr
          (fun b s => if b ∈ s then s else b :: s) [] l = l.dedup at ih
        change List.foldr
          (fun b s => if b ∈ s then s else b :: s) [] (a :: l) =
            (a :: l).dedup
        rw [List.foldr_cons, ih, List.dedup_cons]
        by_cases ha : a ∈ l
        · rw [if_pos ha, if_pos (List.mem_dedup.mpr ha)]
        · rw [if_neg ha, if_neg (fun h => ha (List.mem_dedup.mp h))]

private theorem t1SparseIntersectionCard_primrec
    {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (fun A C : List α => t1SparseIntersectionCard A C) := by
  have hfilter : Primrec (fun p : List α × List α =>
      p.1.filter fun x => decide (x ∈ p.2)) :=
    list_filter_primrec Primrec.fst
      (decide_mem_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (Primrec.list_length.comp (t1ListDedupPrimrec.comp hfilter)).to₂

private theorem t1SparseCandidateValid_primrec
    {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (fun p : List α × List (List α) × Nat × Nat =>
      t1SparseCandidateValid p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := List α × List (List α) × Nat × Nat
  have hcand : Primrec (fun p : P => p.1) := Primrec.fst
  have hCs : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hN : Primrec (fun p : P => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : P => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hlenEq : Primrec (fun p : P => p.1.length == p.2.2.1) :=
    Primrec.beq.comp (Primrec.list_length.comp hcand) hN
  have hinter : Primrec (fun q : P × List α =>
      t1SparseIntersectionCard q.1.1 q.2) :=
    t1SparseIntersectionCard_primrec.comp
      (hcand.comp Primrec.fst) Primrec.snd
  have hle : Primrec₂ (fun (p : P) (C : List α) =>
      decide (t1SparseIntersectionCard p.1 C ≤ p.2.2.2)) :=
    (PrimrecPred.decide
      (Primrec.nat_le.comp hinter (ht.comp Primrec.fst))).to₂
  have hall : Primrec (fun p : P =>
      p.2.1.all fun C =>
        decide (t1SparseIntersectionCard p.1 C ≤ p.2.2.2)) :=
    list_all_primrec hCs hle
  exact Primrec.and.comp hlenEq hall

theorem t1SparseCandidateValid_computable {α : Type} [Primcodable α] [DecidableEq α] :
    Computable (fun p : List α × List (List α) × Nat × Nat =>
      t1SparseCandidateValid p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  t1SparseCandidateValid_primrec.to_comp

theorem t1SparseSubsetSelectorList_primrec {α : Type}
    [Primcodable α] [DecidableEq α] :
    Primrec (fun p : List α × List (List α) × Nat × Nat =>
      t1SparseSubsetSelectorList p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := List α × List (List α) × Nat × Nat
  have hU : Primrec (fun p : P => p.1) := Primrec.fst
  have hsublists : Primrec (fun p : P => p.1.sublists) :=
    primrec_sublists_gen hU
  have hpack : Primrec (fun q : P × List α =>
      (q.2, q.1.2.1, q.1.2.2.1, q.1.2.2.2)) :=
    Primrec.snd.pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  have hpred : Primrec₂ (fun (p : P) (cand : List α) =>
      t1SparseCandidateValid cand p.2.1 p.2.2.1 p.2.2.2) :=
    (t1SparseCandidateValid_primrec.comp hpack).to₂
  have hfind : Primrec (fun p : P =>
      (p.1.sublists.find? fun cand =>
        t1SparseCandidateValid cand p.2.1 p.2.2.1 p.2.2.2).getD []) :=
    Primrec.option_getD.comp
      (list_find?_primrec hsublists hpred) (Primrec.const [])
  exact hfind.of_eq fun p => by
    unfold t1SparseSubsetSelectorList
    cases p.1.sublists.find? (fun cand =>
      t1SparseCandidateValid cand p.2.1 p.2.2.1 p.2.2.2) <;> rfl

theorem t1SparseSubsetSelectorList_computable {α : Type}
    [Primcodable α] [DecidableEq α] :
    Computable (fun p : List α × List (List α) × Nat × Nat =>
      t1SparseSubsetSelectorList p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  t1SparseSubsetSelectorList_primrec.to_comp

/-- Composition form of `t1SparseSubsetSelectorList_computable`.  Keeping the
four input computations separate avoids forcing callers to expose the
selector's nested product encoding. -/
theorem t1SparseSubsetSelectorList_computable_comp
    {α β : Type} [Primcodable α] [DecidableEq α] [Primcodable β]
    {U : β → List α} {Cs : β → List (List α)} {N t : β → Nat}
    (hU : Computable U) (hCs : Computable Cs)
    (hN : Computable N) (ht : Computable t) :
    Computable (fun b =>
      t1SparseSubsetSelectorList (U b) (Cs b) (N b) (t b)) :=
  t1SparseSubsetSelectorList_computable.comp
    (hU.pair (hCs.pair (hN.pair ht)))

theorem t1SparseSubsetSelectorList_sublist
    {α : Type} [DecidableEq α]
    (U : List α) (Cs : List (List α)) (N t : Nat) :
    List.Sublist (t1SparseSubsetSelectorList U Cs N t) U := by
  unfold t1SparseSubsetSelectorList
  cases hfind : U.sublists.find? (fun cand =>
      t1SparseCandidateValid cand Cs N t) with
  | none =>
      exact List.nil_sublist U
  | some selected =>
      exact List.mem_sublists.mp
        (List.mem_of_find?_eq_some hfind)

theorem t1SparseSubsetSelectorList_nodup
    {α : Type} [DecidableEq α]
    (U : List α) (Cs : List (List α)) (N t : Nat)
    (hU : U.Nodup) :
    (t1SparseSubsetSelectorList U Cs N t).Nodup :=
  (t1SparseSubsetSelectorList_sublist U Cs N t).nodup hU

theorem t1SparseCandidateValid_eq_true {α : Type} [DecidableEq α]
    (cand : List α) (Cs : List (List α)) (N t : Nat) :
    t1SparseCandidateValid cand Cs N t = true ↔
      cand.length = N ∧
      ∀ C ∈ Cs, (cand.toFinset ∩ C.toFinset).card ≤ t := by
  simp only [t1SparseCandidateValid, Bool.and_eq_true_iff, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq]
  simp_rw [t1SparseIntersectionCard_eq]

theorem t1SparseSubsetSelector_spec {α : Type} [DecidableEq α]
    (U : List α) (Cs : List (List α)) (N t s : Nat)
    (hU_nodup : U.Nodup)
    (hN : N ≤ U.length)
    (hsmall : ∀ C ∈ Cs, C.toFinset.card ≤ s)
    (hcount : (Cs.map List.toFinset).toFinset.card * Nat.choose N (t + 1) * s ^ (t + 1) <
                (U.toFinset.card - t) ^ (t + 1)) :
    let A := t1SparseSubsetSelectorList U Cs N t
    A.Nodup ∧
    A.toFinset ⊆ U.toFinset ∧
    A.length = N ∧
    ∀ C ∈ Cs, (A.toFinset ∩ C.toFinset).card ≤ t := by
  let raw : Finset (Finset α) := (Cs.map List.toFinset).toFinset
  let clipped : Finset (Finset α) :=
    raw.image fun C => U.toFinset ∩ C
  have hclipped_small : ∀ C ∈ clipped, C ⊆ U.toFinset ∧ C.card ≤ s := by
    intro C hC
    change C ∈ raw.image (fun D => U.toFinset ∩ D) at hC
    rw [Finset.mem_image] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    refine ⟨Finset.inter_subset_left, ?_⟩
    refine (Finset.card_le_card Finset.inter_subset_right).trans ?_
    change D ∈ (Cs.map List.toFinset).toFinset at hD
    rw [List.mem_toFinset] at hD
    obtain ⟨L, hLCs, hLD⟩ := List.mem_map.mp hD
    rw [← hLD]
    exact hsmall L hLCs
  have hclipped_count :
      clipped.card * Nat.choose N (t + 1) * s ^ (t + 1) <
        (U.toFinset.card - t) ^ (t + 1) := by
    have hcard : clipped.card ≤ raw.card := by
      change (raw.image fun C => U.toFinset ∩ C).card ≤ raw.card
      exact Finset.card_image_le
    calc
      clipped.card * Nat.choose N (t + 1) * s ^ (t + 1)
          = clipped.card * (Nat.choose N (t + 1) * s ^ (t + 1)) := by ring
      _ ≤ raw.card * (Nat.choose N (t + 1) * s ^ (t + 1)) :=
        Nat.mul_le_mul_right _ hcard
      _ = raw.card * Nat.choose N (t + 1) * s ^ (t + 1) := by ring
      _ < (U.toFinset.card - t) ^ (t + 1) := hcount
  have hN' : N ≤ U.toFinset.card := by
    rw [List.toFinset_card_of_nodup hU_nodup]
    exact hN
  obtain ⟨A, hAU, hAcard, hAinter⟩ :=
    exists_sparse_intersection_subset U.toFinset clipped N s t
      hN' hclipped_small hclipped_count
  let cand := U.filter fun x => decide (x ∈ A)
  have hcand_sub : cand.Sublist U := List.filter_sublist
  have hcand_nodup : cand.Nodup := hcand_sub.nodup hU_nodup
  have hcand_finset : cand.toFinset = A := by
    ext x
    simp only [cand, List.toFinset_filter, Finset.mem_filter,
      List.mem_toFinset, decide_eq_true_eq]
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨List.mem_toFinset.mp (hAU hx), hx⟩
  have hcand_length : cand.length = N := by
    rw [← List.toFinset_card_of_nodup hcand_nodup, hcand_finset]
    exact hAcard
  have hcand_inter : ∀ C ∈ Cs,
      (cand.toFinset ∩ C.toFinset).card ≤ t := by
    intro C hC
    have hraw : C.toFinset ∈ raw := by
      change C.toFinset ∈ (Cs.map List.toFinset).toFinset
      rw [List.mem_toFinset]
      exact List.mem_map.mpr ⟨C, hC, rfl⟩
    have hclip : U.toFinset ∩ C.toFinset ∈ clipped := by
      change U.toFinset ∩ C.toFinset ∈
        raw.image (fun D => U.toFinset ∩ D)
      rw [Finset.mem_image]
      exact ⟨C.toFinset, hraw, rfl⟩
    have hbound := hAinter (U.toFinset ∩ C.toFinset) hclip
    rw [hcand_finset]
    have hinter_eq :
        A ∩ C.toFinset = A ∩ (U.toFinset ∩ C.toFinset) := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · exact fun hx => ⟨hx.1, ⟨hAU hx.1, hx.2⟩⟩
      · exact fun hx => ⟨hx.1, hx.2.2⟩
    rw [hinter_eq]
    exact hbound
  have hcand_valid : t1SparseCandidateValid cand Cs N t = true :=
    (t1SparseCandidateValid_eq_true cand Cs N t).2
      ⟨hcand_length, hcand_inter⟩
  have hfind_some :
      (U.sublists.find? fun candidate =>
        t1SparseCandidateValid candidate Cs N t).isSome = true :=
    List.find?_isSome.mpr
      ⟨cand, List.mem_sublists.mpr hcand_sub, hcand_valid⟩
  cases hfind : U.sublists.find? (fun candidate =>
      t1SparseCandidateValid candidate Cs N t) with
  | none =>
      simp [hfind] at hfind_some
  | some selected =>
      have hselected_sub : selected.Sublist U :=
        List.mem_sublists.mp (List.mem_of_find?_eq_some hfind)
      have hselected_bool :
          t1SparseCandidateValid selected Cs N t = true :=
        (List.find?_eq_some_iff_getElem.mp hfind).1
      have hselected_valid :=
        (t1SparseCandidateValid_eq_true selected Cs N t).1
          hselected_bool
      have hselected_finset : selected.toFinset ⊆ U.toFinset := by
        intro x hx
        rw [List.mem_toFinset] at hx ⊢
        exact hselected_sub.subset hx
      simpa [t1SparseSubsetSelectorList, hfind] using
        And.intro (hselected_sub.nodup hU_nodup)
          (And.intro hselected_finset hselected_valid)

private theorem t1_four_mul_sq_le_two_pow (n : Nat) (hn : 8 ≤ n) :
    4 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        4 * (n + 1) ^ 2 ≤ 2 * (4 * n ^ 2) := by
          nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ n * 2 := by ring

theorem t1_sparse_counting_inequality :
    ∀ cDesc, ∃ c0 cSparse, ∀ n k epsilon Ucard Fcard,
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      2 ^ (n - 1) ≤ Ucard →
      Fcard ≤ 2 ^ (n + (epsilon + logSlack cDesc n) + 1) →
      Fcard * Nat.choose (2 ^ (k - epsilon)) (cSparse * n + cSparse + 1) *
          (2 ^ (n - k - 4)) ^ (cSparse * n + cSparse + 1)
        < (Ucard - (cSparse * n + cSparse)) ^ (cSparse * n + cSparse + 1) := by
  intro cDesc
  let cSparse := cDesc + 2
  let c0 := max (2 * cSparse) 8
  refine ⟨c0, cSparse, ?_⟩
  intro n k epsilon Ucard Fcard h_c0 h_eps h_k hUcard hFcard
  let t := cSparse * n + cSparse
  let r := t + 1
  let a := k - epsilon
  let b := n - k - 4
  let fexp := n + (epsilon + logSlack cDesc n) + 1
  have hn8 : 8 ≤ n := by
    have : 8 ≤ c0 := le_max_right _ _
    omega
  have hc2n : 2 * cSparse ≤ n := by
    have : 2 * cSparse ≤ c0 := le_max_left _ _
    omega
  have hnpos : 0 < n := by omega
  have ht_le_sq : t ≤ n ^ 2 := by
    have hc_le_cmul : cSparse ≤ cSparse * n :=
      Nat.le_mul_of_pos_right cSparse hnpos
    have htwice : 2 * cSparse * n ≤ n * n := by
      exact (Nat.mul_le_mul_right n hc2n)
    dsimp [t]
    nlinarith
  have ht_le_pow : t ≤ 2 ^ (n - 2) := by
    have hfour : 4 * t ≤ 2 ^ n :=
      (Nat.mul_le_mul_left 4 ht_le_sq).trans
        (t1_four_mul_sq_le_two_pow n hn8)
    have hn_split : n = (n - 2) + 2 := by omega
    rw [hn_split, pow_add] at hfour
    norm_num at hfour
    omega
  have hbase : 2 ^ (n - 2) ≤ Ucard - t := by
    have hn1 : n - 1 = (n - 2) + 1 := by omega
    rw [hn1, pow_succ] at hUcard
    omega
  have hbits : (Nat.bits n).length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hlog : logSlack cDesc n ≤ cDesc * n + cDesc := by
    unfold logSlack
    exact Nat.add_le_add_right (Nat.mul_le_mul_left cDesc hbits) cDesc
  have hfexp_lt_r : fexp < r := by
    dsimp [fexp, r, t, cSparse]
    nlinarith
  have hfexp_lt_mul : fexp < (epsilon + 2) * r :=
    hfexp_lt_r.trans_le
      (Nat.le_mul_of_pos_left r (by omega))
  have hab : a + b = n - epsilon - 4 := by
    dsimp [a, b]
    omega
  have hn_decomp :
      n - 2 = (n - epsilon - 4) + (epsilon + 2) := by
    omega
  have hexp :
      fexp + a * r + b * r < (n - 2) * r := by
    calc
      fexp + a * r + b * r = fexp + (a + b) * r := by ring
      _ = fexp + (n - epsilon - 4) * r := by rw [hab]
      _ < (n - epsilon - 4) * r + (epsilon + 2) * r := by
        omega
      _ = (n - 2) * r := by rw [hn_decomp]; ring
  have hchoose :
      Nat.choose (2 ^ a) r ≤ 2 ^ (a * r) := by
    calc
      Nat.choose (2 ^ a) r ≤ (2 ^ a) ^ r := Nat.choose_le_pow _ _
      _ = 2 ^ (a * r) := (pow_mul 2 a r).symm
  have hbpow : (2 ^ b) ^ r = 2 ^ (b * r) :=
    (pow_mul 2 b r).symm
  have hlhs :
      Fcard * Nat.choose (2 ^ a) r * (2 ^ b) ^ r ≤
        2 ^ (fexp + a * r + b * r) := by
    rw [hbpow]
    calc
      Fcard * Nat.choose (2 ^ a) r * 2 ^ (b * r)
          ≤ 2 ^ fexp * 2 ^ (a * r) * 2 ^ (b * r) :=
            Nat.mul_le_mul (Nat.mul_le_mul hFcard hchoose) le_rfl
      _ = 2 ^ (fexp + a * r + b * r) := by
        rw [pow_add, pow_add]
        ring
  have hstrict :
      2 ^ (fexp + a * r + b * r) < 2 ^ ((n - 2) * r) :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  have hrhs :
      2 ^ ((n - 2) * r) ≤ (Ucard - t) ^ r := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hbase r
  change
    Fcard * Nat.choose (2 ^ a) r * (2 ^ b) ^ r <
      (Ucard - t) ^ r
  exact hlhs.trans_lt (hstrict.trans_le hrhs)

theorem t1_sparse_selector_available :
    ∀ cDesc, ∃ c0 cSparse, ∀ {α : Type} [DecidableEq α]
      (n k epsilon : Nat) (U : List α) (Cs : List (List α)),
      c0 ≤ epsilon →
      epsilon ≤ k →
      k + 4 ≤ n →
      U.Nodup →
      2 ^ (n - 1) ≤ U.length →
      (Cs.map List.toFinset).toFinset.card ≤
        2 ^ (n + (epsilon + logSlack cDesc n) + 1) →
      (∀ C ∈ Cs, C.toFinset.card ≤ 2 ^ (n - k - 4)) →
      let N := 2 ^ (k - epsilon)
      let t := cSparse * n + cSparse
      let A := t1SparseSubsetSelectorList U Cs N t
      A.Nodup ∧
      A.toFinset ⊆ U.toFinset ∧
      A.length = N ∧
      ∀ C ∈ Cs, (A.toFinset ∩ C.toFinset).card ≤ t := by
  intro cDesc
  obtain ⟨c0, cSparse, hcount⟩ :=
    t1_sparse_counting_inequality cDesc
  refine ⟨c0, cSparse, ?_⟩
  intro α inst n k epsilon U Cs h_c0 h_eps h_k hU_nodup
    hUcard hFcard hsmall
  apply t1SparseSubsetSelector_spec U Cs
    (2 ^ (k - epsilon)) (cSparse * n + cSparse)
    (2 ^ (n - k - 4)) hU_nodup
  · calc
      2 ^ (k - epsilon) ≤ 2 ^ (n - 1) := by
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ U.length := hUcard
  · exact hsmall
  · have h := hcount n k epsilon U.length
      (Cs.map List.toFinset).toFinset.card
      h_c0 h_eps h_k hUcard hFcard
    simpa [List.toFinset_card_of_nodup hU_nodup] using h

end Kolmogorov
