import KolmogorovMathlib.Complexity.GeneralScheme.LargeConditionsPlain.PlainJumpLimit

/-!
# Limsup Jump

Auxiliary constructions for the limsup-jump theorem
`exists_const_limsup_condK_eq_plainK_jump` of the general scheme with large conditions
(plain complexity). The module contains the enumerability of the sets `{C_U(x | m) < k}`, the
greedy ray test used to build a family of sets of fewer than `2 ^ k` elements, and the
conversion of a `0'`-enumerable family of such sets into a `0'`-computable decompressor `D`
with `C_D(x) ≤ k` on the `k`-th set.
-/

namespace Kolmogorov
namespace GeneralScheme

/-- Step 1 of the proof of `exists_const_limsup_condK_eq_plainK_jump`: the set of
triples `(k, m, x)` with `C_U(x | m) < k` is enumerable (the usual upper semicomputability of
`C`: search for a program of length `< k` and a halting run of `U`). -/
private theorem exists_const_limsup_condK_eq_plainK_jump_enumerableLess {U : Map}
    (hU : isDecompressor U) :
    IsRE (fun t : ℕ × ℕ × BitString => condK U t.2.2 (Nat.bits t.2.1) < (t.1 : ℕ∞)) := by
  have hg : Computable fun t : ℕ × ℕ × BitString => (t.2.2, Nat.bits t.2.1, t.1) :=
    Computable.pair (Computable.snd.comp Computable.snd)
      (Computable.pair (natBits_computable.comp (Computable.fst.comp Computable.snd))
        Computable.fst)
  exact (isRE_condK_lt hU).comp_computable hg

/-- The ray test of the greedy construction: every section of `G` (at level `k`) together with
the rays `{⟨m, x⟩ | m ≥ n}` for `(n, x) ∈ L` has fewer than `2 ^ k` elements. -/
private def exists_const_limsup_condK_eq_plainK_jump_rays_ok
    (G : Set (ℕ × ℕ × BitString)) (k : ℕ) (L : List (ℕ × BitString)) : Prop :=
  ∀ m : ℕ, ({x : BitString | (k, m, x) ∈ G} ∪ {x : BitString | ∃ n ≤ m, (n, x) ∈ L}).encard
    < 2 ^ k

open Classical in
/-- The greedy sequence of accepted rays at level `k`: go through the pairs `(n, x)` in the order
of `Encodable.decode`, and accept the pair when the test `..._ok` still holds. -/
private noncomputable def exists_const_limsup_condK_eq_plainK_jump_rays_seq
    (G : Set (ℕ × ℕ × BitString)) (k : ℕ) : ℕ → List (ℕ × BitString)
  | 0 => []
  | i + 1 =>
    match (Encodable.decode (α := ℕ × BitString) i) with
    | none => exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i
    | some p =>
      if exists_const_limsup_condK_eq_plainK_jump_rays_ok G k
          (p :: exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i)
      then p :: exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i
      else exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i

private theorem exists_const_limsup_condK_eq_plainK_jump_greedy_aux_ok
    (G : Set (ℕ × ℕ × BitString))
    (hsec : ∀ k m, {x : BitString | (k, m, x) ∈ G}.encard < 2 ^ k) (k i : ℕ) :
    exists_const_limsup_condK_eq_plainK_jump_rays_ok G k
      (exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i) := by
  induction i with
  | zero =>
    intro m
    simpa [exists_const_limsup_condK_eq_plainK_jump_rays_seq] using hsec k m
  | succ i ih =>
    unfold exists_const_limsup_condK_eq_plainK_jump_rays_seq
    rcases h : Encodable.decode (α := ℕ × BitString) i with _ | p
    · simpa using ih
    · simp only
      split_ifs with hp
      · exact hp
      · exact ih

private theorem exists_const_limsup_condK_eq_plainK_jump_greedy_aux_mono
    (G : Set (ℕ × ℕ × BitString)) (k : ℕ) {i j : ℕ} (hij : i ≤ j) {q : ℕ × BitString}
    (hq : q ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i) :
    q ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k j := by
  induction j, hij using Nat.le_induction with
  | base => exact hq
  | succ j _ ih =>
    unfold exists_const_limsup_condK_eq_plainK_jump_rays_seq
    rcases h : Encodable.decode (α := ℕ × BitString) j with _ | p
    · simpa using ih
    · simp only
      split_ifs with hp
      · exact List.mem_cons_of_mem _ ih
      · exact ih

private theorem exists_const_limsup_condK_eq_plainK_jump_greedy_aux_fin
    (G : Set (ℕ × ℕ × BitString)) (k : ℕ) (T : Finset BitString)
    (hT : ∀ x ∈ T, ∃ i n,
      (n, x) ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i) :
    ∃ i m, ∀ x ∈ T, ∃ n ≤ m,
      (n, x) ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert a T haT ih =>
    obtain ⟨i, m, h⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
    obtain ⟨i', n', hn'⟩ := hT a (Finset.mem_insert_self _ _)
    refine ⟨max i i', max m n', ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨n', le_max_right _ _,
        exists_const_limsup_condK_eq_plainK_jump_greedy_aux_mono G k
          (le_max_right _ _) hn'⟩
    · obtain ⟨n, hn, hmem⟩ := h x hx
      exact ⟨n, hn.trans (le_max_left _ _),
        exists_const_limsup_condK_eq_plainK_jump_greedy_aux_mono G k
          (le_max_left _ _) hmem⟩

/-- Step 1 of the proof of `exists_const_limsup_condK_eq_plainK_jump_rays`: the
combinatorics of the greedy construction. Put `W k = {x | ∃ i n, (n, x) ∈ seq k i}` (ordinates of
accepted rays). If all sections of `G` have fewer than `2 ^ k` elements then (invariant: every
accepted list passes the test, by induction on `i`; the empty list passes by `hsec`) `W k` has
fewer than `2 ^ k` elements (otherwise take `2 ^ k` of its elements, with accepted rays at starting
points `≤ m`, and the section `m` would be too big), and `x ∈ W k` whenever `(k, m, x) ∈ G` for all
large `m` (the pair `(n₀, x)` with `n₀` a threshold is tested at some stage; the ray lies in `G`,
so adding it leaves every section unchanged and the test passes). -/
private theorem exists_const_limsup_condK_eq_plainK_jump_greedy
    (G : Set (ℕ × ℕ × BitString))
    (hsec : ∀ k m, {x : BitString | (k, m, x) ∈ G}.encard < 2 ^ k) :
    (∀ k, {x : BitString | ∃ i n,
        (n, x) ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i}.encard < 2 ^ k) ∧
    ∀ k x, (∀ᶠ m in Filter.atTop, (k, m, x) ∈ G) →
      ∃ i n, (n, x) ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i := by
  have hok := exists_const_limsup_condK_eq_plainK_jump_greedy_aux_ok G hsec
  refine ⟨fun k => ?_, fun k x hx => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_encard_eq hcon
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe (k := 2 ^ k) (by
      rw [hTcard]; norm_cast)
    obtain ⟨i, m, hm⟩ := exists_const_limsup_condK_eq_plainK_jump_greedy_aux_fin
      G k hTfin.toFinset (fun x hx => hTsub (hTfin.mem_toFinset.1 hx))
    have hsub : T ⊆ {x : BitString | (k, m, x) ∈ G} ∪ {x : BitString | ∃ n ≤ m, (n, x) ∈
        exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i} := fun x hx =>
      Or.inr (hm x (hTfin.mem_toFinset.2 hx))
    have := (hok k i m).trans_le' (Set.encard_le_encard hsub)
    rw [hTcard] at this
    exact lt_irrefl _ this
  · obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hx
    refine ⟨Encodable.encode (n₀, x) + 1, n₀, ?_⟩
    unfold exists_const_limsup_condK_eq_plainK_jump_rays_seq
    simp only [Encodable.encodek]
    rw [ite_eq_left]
    · exact List.mem_cons_self
    · intro m
      refine lt_of_le_of_lt (Set.encard_le_encard ?_)
        (hok k (Encodable.encode (n₀, x)) m)
      rintro y (hy | ⟨n, hn, hy⟩)
      · exact Or.inl hy
      · rcases List.mem_cons.1 hy with h | h
        · have h1 : n = n₀ := (Prod.mk.inj h).1
          have h2 : y = x := (Prod.mk.inj h).2
          subst h1; subst h2
          exact Or.inl (hn₀ m (by omega))
        · exact Or.inr ⟨n, hn, h⟩

/-- The Boolean test used in step 2 of the ray test: `l` is a duplicate-free list of `2 ^ k`
strings, each of which is enumerated into `G` (stage `chk`) at `(k, m, ·)` or lies in a ray of `L`
starting at `≤ m`. -/
private def exists_const_limsup_condK_eq_plainK_jump_test_check
    (chk : ℕ × ℕ × BitString → ℕ → Bool)
    (a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) : Bool :=
  decide (a.2.2.1.length = 2 ^ a.1.1) &&
    a.2.2.1.all (fun x => decide ((a.2.2.1.filter (fun y => decide (y = x))).length ≤ 1)) &&
    a.2.2.1.all (fun x => chk (a.1.1, a.2.1, x) a.2.2.2 ||
      a.1.2.any (fun p => decide (p.1 ≤ a.2.1) && decide (p.2 = x)))

/-- Universal quantification over a computable list with a computable predicate. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_test_all
    {α β : Type*} [Primcodable α] [Primcodable β] [Inhabited β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).all (p a) := by
  have hnot : Computable₂ fun (a : α) (b : β) => !p a b := Primrec.not.to_comp.comp hp
  exact (Primrec.not.to_comp.comp (computable_list_any hf hnot)).of_eq fun a =>
    (List.all_eq_not_any_not).symm

/-- The test `..._check` is computable. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_test_check_computable
    {chk : ℕ × ℕ × BitString → ℕ → Bool} (hchk : Computable₂ chk) :
    Computable (exists_const_limsup_condK_eq_plainK_jump_test_check chk) := by
  unfold exists_const_limsup_condK_eq_plainK_jump_test_check
  have hl : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.1.1) := Computable.fst.comp Computable.fst
  have hL : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.1.2) := Computable.snd.comp Computable.fst
  have hm : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.2.1) := Computable.fst.comp Computable.snd
  have hs : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hpow : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      2 ^ a.1.1) :=
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id :
      Primrec (fun s : ℕ => 2 ^ s))).to_comp.comp hk
  have h1 : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      decide (a.2.2.1.length = 2 ^ a.1.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp
      (Primrec.list_length.to_comp.comp hl) hpow
  have h2 : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.2.2.1.all (fun x => decide ((a.2.2.1.filter (fun y => decide (y = x))).length ≤ 1))) := by
    have hl' : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
        BitString => q.1.2.2.1) := hl.comp Computable.fst
    have hp : Computable₂ (fun (q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
        BitString) (y : BitString) => decide (y = q.2)) :=
      (primrec_decideEq (β := BitString)).to_comp.comp
        (Computable.snd) (Computable.snd.comp Computable.fst)
    have hf : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
        BitString => (q.1.2.2.1.filter (fun y => decide (y = q.2)))) :=
      computable_list_filter hl' hp
    have hp2 : Computable₂ (fun (a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ))
        (x : BitString) => decide ((a.2.2.1.filter (fun y => decide (y = x))).length ≤ 1)) :=
      (PrimrecRel.decide Primrec.nat_le).to_comp.comp
        (Primrec.list_length.to_comp.comp hf) (Computable.const 1)
    exact exists_const_limsup_condK_eq_plainK_jump_test_all hl hp2
  have h3 : Computable (fun a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      a.2.2.1.all (fun x => chk (a.1.1, a.2.1, x) a.2.2.2 ||
        a.1.2.any (fun p => decide (p.1 ≤ a.2.1) && decide (p.2 = x)))) := by
    have hc : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
        BitString => chk (q.1.1.1, q.1.2.1, q.2) q.1.2.2.2) :=
      have hk' : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => q.1.1.1) := hk.comp Computable.fst
      have hm' : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => q.1.2.1) := hm.comp Computable.fst
      have hs' : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => q.1.2.2.2) := hs.comp Computable.fst
      have hx : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => q.2) := Computable.snd
      have hg : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => (q.1.1.1, q.1.2.1, q.2)) :=
        Computable.pair hk' (Computable.pair hm' hx)
      Computable₂.comp hchk hg hs'
    have hany : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
        BitString => q.1.1.2.any (fun p => decide (p.1 ≤ q.1.2.1) && decide (p.2 = q.2))) := by
      have hL' : Computable (fun q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString => q.1.1.2) := hL.comp Computable.fst
      have hle : Computable (fun w : (((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString) × (ℕ × BitString) => decide (w.2.1 ≤ w.1.1.2.1)) :=
        (PrimrecRel.decide Primrec.nat_le).to_comp.comp (Computable.fst.comp Computable.snd)
          (hm.comp (Computable.fst.comp Computable.fst))
      have heq : Computable (fun w : (((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString) × (ℕ × BitString) => decide (w.2.2 = w.1.2)) :=
        (primrec_decideEq (β := BitString)).to_comp.comp (Computable.snd.comp Computable.snd)
          (Computable.snd.comp Computable.fst)
      have hp : Computable₂ (fun (q : ((ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ)) ×
          BitString) (p : ℕ × BitString) => decide (p.1 ≤ q.1.2.1) && decide (p.2 = q.2)) :=
        Primrec.and.to_comp.comp hle heq
      exact computable_list_any hL' hp
    have hp3 : Computable₂ (fun (a : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ))
        (x : BitString) => chk (a.1.1, a.2.1, x) a.2.2.2 ||
          a.1.2.any (fun p => decide (p.1 ≤ a.2.1) && decide (p.2 = x))) :=
      Primrec.or.to_comp.comp hc hany
    exact exists_const_limsup_condK_eq_plainK_jump_test_all hl hp3
  exact Primrec.and.to_comp.comp (Primrec.and.to_comp.comp h1 h2) h3

/-- The specification of the test `..._check`. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_test_check_iff
    (chk : ℕ × ℕ × BitString → ℕ → Bool) (k : ℕ) (L : List (ℕ × BitString)) (m : ℕ)
    (l : List BitString) (s : ℕ) :
    exists_const_limsup_condK_eq_plainK_jump_test_check chk ((k, L), (m, l, s))
        = true ↔
      l.length = 2 ^ k ∧ l.Nodup ∧
        ∀ x ∈ l, chk (k, m, x) s = true ∨ ∃ n ≤ m, (n, x) ∈ L := by
  have hnd : (∀ x ∈ l, (l.filter (fun y => decide (y = x))).length ≤ 1) ↔ l.Nodup := by
    rw [List.nodup_iff_count_le_one]
    constructor
    · intro h a
      by_cases ha : a ∈ l
      · have := h a ha
        simpa only [List.count_eq_length_filter, beq_eq_decide] using this
      · simp [List.count_eq_zero_of_not_mem ha]
    · intro h x _
      have := h x
      simpa only [List.count_eq_length_filter, beq_eq_decide] using this
  unfold exists_const_limsup_condK_eq_plainK_jump_test_check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, Prod.exists]
  rw [hnd, and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun x _ => or_congr Iff.rfl ?_))
  constructor
  · rintro ⟨n, y, hy, h⟩
    exact ⟨n, h.1, h.2 ▸ hy⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, x, h, by simp [hn]⟩

/-- Step 2 of the proof of `exists_const_limsup_condK_eq_plainK_jump_rays`: the
ray test is decided by `0'`. For an enumerable `G`, the predicate `..._ok G k L` (on `(k, L)`) is
the complement of an enumerable predicate (a violation is witnessed by `m` and `2 ^ k` distinct
strings each either enumerated into `G` at `(k, m, ·)` or lying in a ray of `L` starting at
`≤ m`), hence it is decided by a `0'`-computable Boolean function
(`Kolmogorov.exists_computableInJump_semidecide`). -/
private theorem exists_const_limsup_condK_eq_plainK_jump_test
    (G : Set (ℕ × ℕ × BitString)) (hG : IsRE (fun t : ℕ × ℕ × BitString => t ∈ G)) :
    ∃ h : ℕ × List (ℕ × BitString) → Bool,
      ComputableIn {charOracle jumpSet} h ∧
      ∀ k L, h (k, L) = true ↔
        exists_const_limsup_condK_eq_plainK_jump_rays_ok G k L := by
  classical
  obtain ⟨chk, hchk, hmono, hspec⟩ := hG.exists_stageApprox
  -- the violation of the test is witnessed by `(m, l, s)`
  have hkey : ∀ (k : ℕ) (L : List (ℕ × BitString)),
      ¬ exists_const_limsup_condK_eq_plainK_jump_rays_ok G k L ↔
        ∃ b : ℕ × List BitString × ℕ,
          exists_const_limsup_condK_eq_plainK_jump_test_check chk
            ((k, L), b) = true := by
    intro k L
    unfold exists_const_limsup_condK_eq_plainK_jump_rays_ok
    push Not
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hm
      have htc' : t.encard = ((2 ^ k : ℕ) : ℕ∞) := by rw [htc]; norm_cast
      have htfin : t.Finite := Set.finite_of_encard_eq_coe htc'
      have hcard : htfin.toFinset.card = 2 ^ k := by
        have := htfin.encard_eq_coe_toFinset_card
        rw [htc'] at this
        exact_mod_cast this.symm
      -- a stage bounding the enumeration of all elements of `t`
      let sx : BitString → ℕ := fun x =>
        if h : (k, m, x) ∈ G then Classical.choose ((hspec _).1 h) else 0
      refine ⟨(m, htfin.toFinset.toList, htfin.toFinset.sup sx), ?_⟩
      rw [exists_const_limsup_condK_eq_plainK_jump_test_check_iff]
      refine ⟨by simpa using hcard, Finset.nodup_toList _, fun x hx => ?_⟩
      have hxt : x ∈ t := by simpa using hx
      rcases hts hxt with hxG | ⟨n, hn, hnx⟩
      · left
        have hxG' : (k, m, x) ∈ G := hxG
        have h1 : chk (k, m, x) (sx x) = true := by
          simp only [sx, dite_eq_left hxG']
          exact Classical.choose_spec ((hspec _).1 hxG')
        exact hmono _ _ _ (Finset.le_sup (f := sx) (by simpa using hx)) h1
      · exact Or.inr ⟨n, hn, hnx⟩
    · rintro ⟨⟨m, l, s⟩, hb⟩
      rw [exists_const_limsup_condK_eq_plainK_jump_test_check_iff] at hb
      obtain ⟨hlen, hnd, hl⟩ := hb
      refine ⟨m, ?_⟩
      have hsub : (↑l.toFinset : Set BitString) ⊆
          {x : BitString | (k, m, x) ∈ G} ∪ {x : BitString | ∃ n ≤ m, (n, x) ∈ L} := by
        intro x hx
        have hx' : x ∈ l := by simpa using hx
        rcases hl x hx' with h | h
        · exact Or.inl ((hspec _).2 ⟨s, h⟩)
        · exact Or.inr h
      have := Set.encard_le_encard hsub
      rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup hnd, hlen] at this
      exact_mod_cast this
  have hRE : IsRE (fun p : (ℕ × List (ℕ × BitString)) × (ℕ × List BitString × ℕ) =>
      exists_const_limsup_condK_eq_plainK_jump_test_check chk p = true) :=
    isRE_of_computable_bool _
      (exists_const_limsup_condK_eq_plainK_jump_test_check chk)
      (fun _ => Iff.rfl)
      (exists_const_limsup_condK_eq_plainK_jump_test_check_computable hchk)
  have hRE2 := IsRE.exists_encodable
    (R := fun (a : ℕ × List (ℕ × BitString)) (b : ℕ × List BitString × ℕ) =>
      exists_const_limsup_condK_eq_plainK_jump_test_check chk (a, b) = true) hRE
  obtain ⟨g, hg, -, hgspec⟩ := hRE2.exists_stageApprox
  obtain ⟨h', hh'J, hh'spec⟩ := exists_computableInJump_semidecide hg
  have hhalt : haltingChi = charOracle jumpSet := by
    funext n
    simp only [haltingChi, charOracle, jumpSet, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) h' := by
    simpa [ComputableInJump, hhalt] using hh'J
  refine ⟨fun a => !h' a, ?_, fun k L => ?_⟩
  · exact ComputableIn.comp (f := fun x : Bool => !x) (Primrec.not.to_comp.computableIn) hh'
  · have h1 : h' (k, L) = true ↔
        ¬ exists_const_limsup_condK_eq_plainK_jump_rays_ok G k L := by
      rw [hh'spec, ← hgspec, hkey]
    rw [Bool.not_eq_true', ← Bool.not_eq_true, h1, not_not]

/-- Step 3 of the proof of `exists_const_limsup_condK_eq_plainK_jump_rays`: the
greedy sequence is `0'`-computable. If the test `h` is `0'`-computable and decides `..._ok`, then
`(k, i) ↦ seq k i` is `0'`-computable (recursion on `i`, decoding the `i`-th pair by
`Encodable.decode`; `ComputableIn.nat_rec`). -/
private theorem exists_const_limsup_condK_eq_plainK_jump_seq
    (G : Set (ℕ × ℕ × BitString)) (h : ℕ × List (ℕ × BitString) → Bool)
    (hh : ComputableIn {charOracle jumpSet} h)
    (hspec : ∀ k L, h (k, L) = true ↔
      exists_const_limsup_condK_eq_plainK_jump_rays_ok G k L) :
    ComputableIn {charOracle jumpSet}
      (fun p : ℕ × ℕ => exists_const_limsup_condK_eq_plainK_jump_rays_seq G p.1 p.2) := by
  classical
  let O : Set (ℕ →. ℕ) := {charOracle jumpSet}
  have hstep : ComputableIn₂ O (fun (q : ℕ × ℕ) (r : ℕ × List (ℕ × BitString)) =>
      bif ((Encodable.decode (α := ℕ × BitString) r.1).isSome &&
          h (q.1, ((Encodable.decode (α := ℕ × BitString) r.1).getD default) :: r.2))
        then ((Encodable.decode (α := ℕ × BitString) r.1).getD default) :: r.2 else r.2) := by
    refine ComputableIn₂.mk ?_
    have hdec : Primrec (fun u : (ℕ × ℕ) × ℕ × List (ℕ × BitString) =>
        (Encodable.decode (α := ℕ × BitString) u.2.1).getD default) :=
      Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const default)
    have hcons : Primrec (fun u : (ℕ × ℕ) × ℕ × List (ℕ × BitString) =>
        ((Encodable.decode (α := ℕ × BitString) u.2.1).getD default) :: u.2.2) :=
      Primrec.list_cons.comp hdec (Primrec.snd.comp Primrec.snd)
    have hsome : Primrec (fun u : (ℕ × ℕ) × ℕ × List (ℕ × BitString) =>
        (Encodable.decode (α := ℕ × BitString) u.2.1).isSome) :=
      Primrec.option_isSome.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.snd))
    have hhc : ComputableIn O (fun u : (ℕ × ℕ) × ℕ × List (ℕ × BitString) =>
        h (u.1.1, ((Encodable.decode (α := ℕ × BitString) u.2.1).getD default) :: u.2.2)) :=
      hh.comp ((Primrec.fst.comp Primrec.fst).to_comp.computableIn.pair
        hcons.to_comp.computableIn)
    have hF : Primrec (fun w : Bool × Bool × List (ℕ × BitString) × List (ℕ × BitString) =>
        bif (w.1 && w.2.1) then w.2.2.1 else w.2.2.2) :=
      Primrec.cond (Primrec.and.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hc := hF.to_comp.computableIn.comp
      (hsome.to_comp.computableIn.pair (hhc.pair
        (hcons.to_comp.computableIn.pair
          (Primrec.snd.comp Primrec.snd).to_comp.computableIn)))
    exact hc
  have hrec := ComputableIn.nat_rec (O := O) (f := fun q : ℕ × ℕ => q.2)
    (g := fun _ => ([] : List (ℕ × BitString)))
    (h := fun (q : ℕ × ℕ) (r : ℕ × List (ℕ × BitString)) =>
      bif ((Encodable.decode (α := ℕ × BitString) r.1).isSome &&
          h (q.1, ((Encodable.decode (α := ℕ × BitString) r.1).getD default) :: r.2))
        then ((Encodable.decode (α := ℕ × BitString) r.1).getD default) :: r.2 else r.2)
    ComputableIn.snd (ComputableIn.const []) hstep
  refine hrec.of_eq fun q => ?_
  obtain ⟨k, i⟩ := q
  dsimp only
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [exists_const_limsup_condK_eq_plainK_jump_rays_seq]
    rw [← ih]
    dsimp only
    generalize Nat.rec (motive := fun _ => List (ℕ × BitString)) [] _ i = S
    cases hd : Encodable.decode (α := ℕ × BitString) i with
    | none => simp
    | some p =>
      by_cases hok : h (k, p :: S) = true
      · have := (hspec k (p :: S)).1 hok
        simp [hok, this]
      · have : ¬ exists_const_limsup_condK_eq_plainK_jump_rays_ok G k (p :: S) :=
          fun hc => hok ((hspec k (p :: S)).2 hc)
        simp [hok, this]

/-- Step 2 of the proof of `exists_const_limsup_condK_eq_plainK_jump`: the ray
construction. Let `G` be an enumerable set of triples `(k, m, x)` all of whose sections
`{x | (k, m, x) ∈ G}` have fewer than `2 ^ k` elements. Then there is a `0'`-enumerable family
`W k` of sets, each with fewer than `2 ^ k` elements, such that `x ∈ W k` whenever
`(k, m, x) ∈ G` for all large `m`. (Go through the pairs `⟨n, x⟩` and add the ray
`{⟨m, x⟩ | m ≥ n}` to the current set `S` if all sections of `G ∪ S ∪ ray` stay smaller than
`2 ^ k`; this is a co-enumerable test, decided by `0'`. `W k` is the set of ordinates of added
rays.) -/
private theorem exists_const_limsup_condK_eq_plainK_jump_rays
    (G : Set (ℕ × ℕ × BitString)) (hG : IsRE (fun t : ℕ × ℕ × BitString => t ∈ G))
    (hsec : ∀ k m, {x : BitString | (k, m, x) ∈ G}.encard < 2 ^ k) :
    ∃ W : ℕ → Set BitString,
      PointToSet.IsREIn jumpSet (fun t : ℕ × BitString => t.2 ∈ W t.1) ∧
      (∀ k, (W k).encard < 2 ^ k) ∧
      ∀ k x, (∀ᶠ m in Filter.atTop, (k, m, x) ∈ G) → x ∈ W k := by
  obtain ⟨h, hh, hspec⟩ := exists_const_limsup_condK_eq_plainK_jump_test G hG
  have hs := exists_const_limsup_condK_eq_plainK_jump_seq G h hh hspec
  obtain ⟨hcard, hmem⟩ := exists_const_limsup_condK_eq_plainK_jump_greedy G hsec
  refine ⟨fun k => {x : BitString | ∃ i n,
    (n, x) ∈ exists_const_limsup_condK_eq_plainK_jump_rays_seq G k i}, ?_, hcard, hmem⟩
  have hF : PointToSet.IsREIn jumpSet (fun q : (ℕ × BitString) × ℕ => q.1.2 ∈
      (exists_const_limsup_condK_eq_plainK_jump_rays_seq G q.1.1 q.2).map Prod.snd) := by
    refine PointToSet.isREIn_of_computableIn_decide jumpSet _ ?_
    have h0 : ComputableIn {charOracle jumpSet}
        (fun q : (ℕ × BitString) × ℕ =>
          exists_const_limsup_condK_eq_plainK_jump_rays_seq G q.1.1 q.2) :=
      hs.comp (ComputableIn.pair
        (Computable.fst.comp Computable.fst).computableIn Computable.snd.computableIn)
    have h1 : ComputableIn {charOracle jumpSet}
        (fun q : (ℕ × BitString) × ℕ =>
          ((exists_const_limsup_condK_eq_plainK_jump_rays_seq G q.1.1 q.2).map Prod.snd,
            q.1.2)) := by
      refine ComputableIn.pair ?_ ?_
      · exact ComputableIn.comp
          (f := fun l : List (ℕ × BitString) => l.map Prod.snd)
          (Computable.list_map Computable.id
            (Computable.snd.comp Computable.snd).to₂).computableIn h0
      · exact (Computable.snd.comp Computable.fst).computableIn
    have h2 : Computable (fun r : List BitString × BitString => decide (r.2 ∈ r.1)) := by
      have hp : Primrec (fun r : List BitString × BitString =>
          decide (@List.idxOf _ instBEqOfDecidableEq r.2 r.1 < r.1.length)) :=
        (PrimrecRel.decide Primrec.nat_lt).comp
          (Primrec.list_idxOf.comp Primrec.snd Primrec.fst)
          (Primrec.list_length.comp Primrec.fst)
      exact hp.to_comp.of_eq fun r => by simp [List.idxOf_lt_length_iff]
    have h3 : ComputableIn {charOracle jumpSet} (fun r : List BitString × BitString =>
        decide (r.2 ∈ r.1)) := h2.computableIn
    have h4 := ComputableIn.comp h3 h1
    exact h4
  obtain ⟨f, hf, hd⟩ := hF.exists
  refine ⟨f, hf, fun w => ?_⟩
  rw [← hd w]
  simp [List.mem_map]

/-- Little-endian binary value of a bit string. -/
private def exists_const_limsup_condK_eq_plainK_jump_decompressor_val (p : BitString) : ℕ :=
    p.foldr (fun b acc => (bif b then 1 else 0) + 2 * acc) 0

/-- Every `i < 2 ^ k` is the value of a bit string of length `k`. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_exists_val :
    ∀ (k i : ℕ), i < 2 ^ k → ∃ p : BitString, p.length = k ∧
        exists_const_limsup_condK_eq_plainK_jump_decompressor_val p = i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    exact ⟨[], rfl, by
      simp at hi
      simp [exists_const_limsup_condK_eq_plainK_jump_decompressor_val, hi]⟩
  | succ k ih =>
    intro i hi
    obtain ⟨q, hq, hqv⟩ := ih (i / 2) (by rw [pow_succ] at hi; omega)
    refine ⟨decide (i % 2 = 1) :: q, by simp [hq], ?_⟩
    simp only [exists_const_limsup_condK_eq_plainK_jump_decompressor_val, List.foldr_cons] at hqv ⊢
    rw [hqv]
    by_cases h : i % 2 = 1 <;> simp [h] <;> omega

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_primrec_val : Primrec
    exists_const_limsup_condK_eq_plainK_jump_decompressor_val := by
  unfold exists_const_limsup_condK_eq_plainK_jump_decompressor_val
  refine Primrec.list_foldr (f := fun p : BitString => p) (g := fun _ => 0)
    (h := fun _ r => (bif r.1 then 1 else 0) + 2 * r.2) Primrec.id (Primrec.const 0) ?_
  exact Primrec.nat_add.comp
    (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))

/-- Number of stages `< t` at which the enumeration `e` lists a pair with first component `k`. -/
private def exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt
    (e : ℕ → Option (ℕ × BitString)) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t +
               (bif decide ((e t).map Prod.fst = some k) then 1 else 0)

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_mono
    (e : ℕ → Option (ℕ × BitString)) (k : ℕ) {s t : ℕ} (h : s ≤ t) :
    exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k s ≤
        exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact ih.trans (Nat.le_add_right _ _)

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_succ_of
    (e : ℕ → Option (ℕ × BitString)) (k s : ℕ) {x : BitString}
    (h : e s = some (k, x)) : exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k
        (s + 1) = exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k s + 1 := by
  simp [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt, h]

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_le_encard
    (W : ℕ → Set BitString) (e : ℕ → Option (ℕ × BitString))
    (hinj : ∀ s t w, e s = some w → e t = some w → s = t)
    (hW : ∀ s k x, e s = some (k, x) → x ∈ W k) (k t : ℕ) :
    (exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t : ℕ∞) ≤ (W k).encard :=
        by
  have hcard : exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t =
      ((Finset.range t).filter
      (fun s => (e s).map Prod.fst = some k)).card := by
    induction t with
    | zero => simp [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt]
    | succ t ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : (e t).map Prod.fst = some k
      · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp), ← ih]
        simp [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt, h]
      · rw [ite_eq_right h, ← ih]
        simp [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt, h]
  rw [hcard]
  set T := (Finset.range t).filter (fun s => (e s).map Prod.fst = some k) with hT
  let g : ℕ → BitString := fun s => ((e s).map Prod.snd).getD []
  have hg : ∀ s ∈ T, e s = some (k, g s) := by
    intro s hs
    simp only [hT, Finset.mem_filter] at hs
    obtain ⟨_, hs⟩ := hs
    cases hes : e s with
    | none => simp [hes] at hs
    | some w =>
      obtain ⟨k', x⟩ := w
      simp only [hes, Option.map_some, Option.some.injEq] at hs
      subst hs
      simp [g, hes]
  have hinjOn : Set.InjOn g (T : Set ℕ) := by
    intro s hs s' hs' hss'
    exact hinj s s' (k, g s) (hg s hs) (by rw [hss']; exact hg s' hs')
  rw [← Set.encard_coe_eq_coe_finsetCard, ← hinjOn.encard_image]
  exact Set.encard_le_encard (by
    rintro _ ⟨s, hs, rfl⟩
    exact hW s k (g s) (hg s hs))

/-- Stage `t` of the search: outputs `x` if `e t = (|p|, x)` and `x` is the `val p`-th element
listed for `|p|`. -/
private def exists_const_limsup_condK_eq_plainK_jump_decompressor_hit
    (e : ℕ → Option (ℕ × BitString)) (a : BitString × BitString) (t : ℕ) :
    Option BitString :=
  (e t).bind fun kx =>
    bif (decide (kx.1 = a.1.length) && decide
        (exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e a.1.length t =
        exists_const_limsup_condK_eq_plainK_jump_decompressor_val a.1)) then
      some kx.2 else none

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_hit_eq_some
    (e : ℕ → Option (ℕ × BitString)) (a : BitString × BitString)
    (t : ℕ) (x : BitString) :
    exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e a t = some x ↔
      e t = some (a.1.length, x) ∧ exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e
          a.1.length t = exists_const_limsup_condK_eq_plainK_jump_decompressor_val a.1 := by
  unfold exists_const_limsup_condK_eq_plainK_jump_decompressor_hit
  cases het : e t with
  | none => simp
  | some w =>
    obtain ⟨k, y⟩ := w
    by_cases h : k = a.1.length ∧ exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e
        a.1.length t = exists_const_limsup_condK_eq_plainK_jump_decompressor_val a.1
    · obtain ⟨h1, h2⟩ := h
      subst h1
      simp [h2]
    · have : ¬ (k = a.1.length ∧ exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e
        a.1.length t = exists_const_limsup_condK_eq_plainK_jump_decompressor_val a.1) := h
      by_cases h1 : k = a.1.length
      · subst h1
        have h2 : ¬ exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e a.1.length t =
            exists_const_limsup_condK_eq_plainK_jump_decompressor_val a.1 :=
            fun h2 => this ⟨rfl, h2⟩
        simp [h2]
      · simp [h1]

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_computable_cnt
    (O : Set (ℕ →. ℕ)) (e : ℕ → Option (ℕ × BitString))
    (he : ComputableIn O e) :
    ComputableIn O (fun q : ℕ × ℕ => exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt
                                       e q.1 q.2) := by
  have hΦ : Primrec (fun t : ℕ × Option (ℕ × BitString) × ℕ =>
      t.2.2 + (bif decide (t.2.1.map Prod.fst = some t.1) then 1 else 0)) := by
    refine Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.cond ?_
      (Primrec.const 1) (Primrec.const 0))
    refine Primrec.eq.decide.comp ?_ (Primrec.option_some.comp
      (Primrec.fst : Primrec fun t : ℕ × Option (ℕ × BitString) × ℕ => t.1))
    exact Primrec.option_map
      (f := fun t : ℕ × Option (ℕ × BitString) × ℕ => t.2.1)
      (g := fun _ (x : ℕ × BitString) => x.1)
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hstep : ComputableIn₂ O (fun (q : ℕ × ℕ) (r : ℕ × ℕ) =>
      r.2 + (bif decide ((e r.1).map Prod.fst = some q.1) then 1 else 0)) := by
    refine ComputableIn₂.mk ?_
    have h1 : ComputableIn O (fun u : (ℕ × ℕ) × (ℕ × ℕ) =>
        (u.1.1, e u.2.1, u.2.2)) :=
      (ComputableIn.fst.comp ComputableIn.fst).pair
        ((he.comp (ComputableIn.fst.comp ComputableIn.snd)).pair
          (ComputableIn.snd.comp ComputableIn.snd))
    have hΦc : ComputableIn O (fun t : ℕ × Option (ℕ × BitString) × ℕ =>
        t.2.2 + (bif decide (t.2.1.map Prod.fst = some t.1) then 1 else 0)) :=
      hΦ.to_comp.computableIn
    have hc := hΦc.comp h1
    exact hc.of_eq fun u => rfl
  have hrec := ComputableIn.nat_rec (O := O) (f := fun q : ℕ × ℕ => q.2)
    (g := fun _ => 0)
    (h := fun (q : ℕ × ℕ) (r : ℕ × ℕ) =>
      r.2 + (bif decide ((e r.1).map Prod.fst = some q.1) then 1 else 0))
    ComputableIn.snd (ComputableIn.const 0) hstep
  refine hrec.of_eq fun q => ?_
  obtain ⟨k, t⟩ := q
  dsimp only
  induction t with
  | zero => rfl
  | succ t ih => rw [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt, ← ih]

private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor_computable_hit
    (O : Set (ℕ →. ℕ)) (e : ℕ → Option (ℕ × BitString))
    (he : ComputableIn O e) : ComputableIn₂ O
        (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e) := by
  have hcnt := exists_const_limsup_condK_eq_plainK_jump_decompressor_computable_cnt O e he
  have hΨ : Primrec (fun u : (BitString × BitString) × Option (ℕ × BitString) × ℕ =>
      u.2.1.bind fun kx =>
        bif (decide (kx.1 = u.1.1.length) && decide
            (u.2.2 = exists_const_limsup_condK_eq_plainK_jump_decompressor_val u.1.1)) then
          some kx.2 else none) := by
    refine Primrec.option_bind (Primrec.fst.comp Primrec.snd) ?_
    refine Primrec.cond ?_ (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const none)
    refine Primrec.and.comp ?_ ?_
    · exact Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    · exact Primrec.eq.decide.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (exists_const_limsup_condK_eq_plainK_jump_decompressor_primrec_val.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  refine ComputableIn₂.mk ?_
  have h1 : ComputableIn O (fun u : (BitString × BitString) × ℕ =>
      (u.1, e u.2, exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e u.1.1.length
          u.2)) :=
    ComputableIn.fst.pair ((he.comp ComputableIn.snd).pair
      (hcnt.comp ((Primrec.list_length.comp (Primrec.fst.comp
          Primrec.fst)).to_comp.computableIn.pair
        ComputableIn.snd)))
  have hc := hΨ.to_comp.computableIn.comp h1
  exact hc.of_eq fun u => rfl

/-- Step 3 of the proof of `exists_const_limsup_condK_eq_plainK_jump`: a `0'`-enumerable
family of sets `W k` with fewer than `2 ^ k` elements gives a `0'`-computable decompressor `D`
with `C_D(x) ≤ k` for every `x ∈ W k`. (The program is a string `p` of length `k`, read as the
number `i < 2 ^ k`; `D` outputs the `i`-th distinct element of the `0'`-enumeration of `W k`.) -/
private theorem exists_const_limsup_condK_eq_plainK_jump_decompressor (W : ℕ → Set BitString)
    (hW : PointToSet.IsREIn jumpSet (fun t : ℕ × BitString => t.2 ∈ W t.1))
    (hcard : ∀ k, (W k).encard < 2 ^ k) :
    ∃ D : Map, IsDecompressorIn haltingOracle D ∧ ∀ k x, x ∈ W k → condK D x [] ≤ (k : ℕ∞) := by
  obtain ⟨e, ⟨he, hrange⟩, hinj⟩ := PointToSet.relative_enumeration_injective jumpSet _ hW
  have hhit := exists_const_limsup_condK_eq_plainK_jump_decompressor_computable_hit
      {charOracle jumpSet} e he
  refine ⟨fun a => Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e
                     a), ?_, ?_⟩
  · have hp : PartrecIn {haltingOracle}
        (fun a : BitString × BitString =>
          Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e a)) :=
      PartrecIn.rfindOpt hhit
    unfold IsDecompressorIn
    rw [RecursiveIn.iff_nat]
    exact hp
  · intro k x hx
    obtain ⟨t, ht⟩ := (hrange (k, x)).1 hx
    have hWe : ∀ s k x, e s = some (k, x) → x ∈ W k := fun s k x h =>
      (hrange (k, x)).2 ⟨s, h⟩
    have hle := exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_le_encard W e hinj
        hWe k (t + 1)
    rw [exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_succ_of e k t ht] at hle
    have hlt : ((exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t + 1 : ℕ) :
        ℕ∞) < ((2 ^ k : ℕ) : ℕ∞) := by
      refine lt_of_le_of_lt (by exact_mod_cast hle) ?_
      have := hcard k
      simpa using this
    have hi : exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt e k t < 2 ^ k := by
      have := Nat.cast_lt.1 hlt
      omega
    obtain ⟨p, hplen, hpval⟩ :=
        exists_const_limsup_condK_eq_plainK_jump_decompressor_exists_val k _ hi
    have hmem : x ∈ Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e
        (p, [])) := by
      have hhit_t : exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e (p, []) t =
          some x := by
        rw [exists_const_limsup_condK_eq_plainK_jump_decompressor_hit_eq_some]
        exact ⟨by simpa [hplen] using ht, by simp [hplen, hpval]⟩
      have hdom : (Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e
          (p, []))).Dom :=
        Nat.rfindOpt_dom.2 ⟨t, x, hhit_t⟩
      have hget : (Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e
          (p, []))).get hdom ∈ Nat.rfindOpt
          (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e (p, [])) :=
        Part.get_mem hdom
      obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hget
      rw [Option.mem_def, exists_const_limsup_condK_eq_plainK_jump_decompressor_hit_eq_some]
          at hn
      obtain ⟨hn1, hn2⟩ := hn
      simp only [hplen, hpval] at hn1 hn2
      have hnt : n = t := by
        rcases lt_trichotomy n t with h | h | h
        · have h1 := exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_succ_of e k n
            hn1
          have h2 := exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_mono e k
              (show n + 1 ≤ t from h)
          omega
        · exact h
        · have h1 := exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_succ_of e k t
            ht
          have h2 := exists_const_limsup_condK_eq_plainK_jump_decompressor_cnt_mono e k
              (show t + 1 ≤ n from h)
          omega
      subst hnt
      rw [ht] at hn1
      have := (Option.some.inj hn1)
      have hx' : (Nat.rfindOpt (exists_const_limsup_condK_eq_plainK_jump_decompressor_hit e
          (p, []))).get hdom = x := by
        simpa using (congrArg Prod.snd this).symm
      rw [← hx']
      exact hget
    have hp : (programLength p : ℕ∞) = k := by simp [hplen]
    exact hp ▸ sInf_le ⟨p, hmem, rfl⟩

/-- For every `D`, fewer than `2 ^ k` strings `x` have `condK D x y < k`. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_encard_lt (D : Map) (k : ℕ)
    (y : BitString) : {x : BitString | condK D x y < k}.encard < 2 ^ k := by
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (not_lt.1 hcon)
  have htc' : t.encard = ((2 ^ k : ℕ) : ℕ∞) := by rw [htc]; norm_cast
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htc'
  have hcard : htfin.toFinset.card = 2 ^ k := by
    have := htfin.encard_eq_coe_toFinset_card
    rw [htc'] at this
    exact_mod_cast this.symm
  obtain ⟨x, hx, hle⟩ := exists_condK_ge_of_finset_card_pow D htfin.toFinset y k hcard.ge
  exact absurd (hts (htfin.mem_toFinset.1 hx)) (not_lt.2 hle)

/-- The `≤` half of Theorem 132, from Theorem 131 and the remark before the lemma. -/
private theorem exists_const_limsup_condK_eq_plainK_jump_le {U : Map}
    (hU : isOptimalConditional U) {V : Map} (hV : IsOptimalConditionalIn haltingOracle V) :
    ∃ c : ℕ, ∀ x,
      Filter.limsup (fun n => condK U x (Nat.bits n)) Filter.atTop ≤ plainK V x + c := by
  obtain ⟨U', hU'⟩ := exists_isOptimalSetCond
  obtain ⟨c₁, hc₁⟩ := exists_const_iInf_setCondK_atLeast_eq_plainK_jump hU' hV
  obtain ⟨c₂, hc₂⟩ := exists_const_iSup_condK_le_setCondK_atLeast hU' hU
  refine ⟨c₁ + c₂, fun x => ?_⟩
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  have h1 : (⨅ n, ⨆ i ≥ n, condK U x (Nat.bits i)) ≤ (⨅ n, setCondK U' x (atLeast n)) + c₂ := by
    rw [ENat.iInf_add]
    exact iInf_mono fun n => hc₂ x n
  refine h1.trans ?_
  calc (⨅ n, setCondK U' x (atLeast n)) + c₂
      ≤ (plainK V x + c₁) + c₂ := add_le_add (hc₁ x).1 le_rfl
    _ = plainK V x + ((c₁ + c₂ : ℕ) : ℕ∞) := by push_cast; ring

/-- **SUV Theorem 132 (Section 6.4.2, printed p. 205).**
`limsup_{n → ∞} C(x | n) = C^{0'}(x) + O(1)`.

Proof idea: `≤` follows from Theorem 131 and the previous remark. For `≥`, it is enough to put
the strings `x` with `C(x | n) < k` for all large `n` into a `0'`-enumerable set of fewer than
`2 ^ k` elements, uniformly in `k`. Go through the pairs `⟨n, x⟩` and try to add the horizontal
ray `{⟨m, x⟩ | m ≥ n}` to the enumerable set `{⟨m, x⟩ | C(x | m) < k}`, keeping every vertical
section smaller than `2 ^ k`. This is a co-enumerable test, decided by `0'`. The ordinates of
the added rays form the required set. -/
theorem exists_const_limsup_condK_eq_plainK_jump {U : Map} (hU : isOptimalConditional U)
    {V : Map} (hV : IsOptimalConditionalIn haltingOracle V) :
    ∃ c : ℕ, ∀ x,
      Filter.limsup (fun n => condK U x (Nat.bits n)) Filter.atTop ≤ plainK V x + c ∧
        plainK V x ≤ Filter.limsup (fun n => condK U x (Nat.bits n)) Filter.atTop + c := by
  obtain ⟨c₁, hc₁⟩ := exists_const_limsup_condK_eq_plainK_jump_le hU hV
  obtain ⟨W, hWre, hWcard, hWmem⟩ :=
    exists_const_limsup_condK_eq_plainK_jump_rays
      {t : ℕ × ℕ × BitString | condK U t.2.2 (Nat.bits t.2.1) < (t.1 : ℕ∞)}
      (exists_const_limsup_condK_eq_plainK_jump_enumerableLess hU.1)
      (fun k m => exists_const_limsup_condK_eq_plainK_jump_encard_lt U k (Nat.bits m))
  obtain ⟨D, hD, hDW⟩ :=
    exists_const_limsup_condK_eq_plainK_jump_decompressor W hWre hWcard
  obtain ⟨c₂, hc₂⟩ := hV.2 D hD
  refine ⟨c₁ + (c₂ + 1), fun x => ⟨?_, ?_⟩⟩
  · exact (hc₁ x).trans (add_le_add le_rfl (by exact_mod_cast Nat.le_add_right _ _))
  · by_cases htop : Filter.limsup (fun n => condK U x (Nat.bits n)) Filter.atTop = ⊤
    · rw [htop]; simp
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
      have hlt : Filter.limsup (fun n => condK U x (Nat.bits n)) Filter.atTop
          < ((m + 1 : ℕ) : ℕ∞) := by
        rw [← hm]; exact_mod_cast Nat.lt_succ_self m
      have hev := Filter.eventually_lt_of_limsup_lt hlt
      have hx : x ∈ W (m + 1) := hWmem (m + 1) x (hev.mono fun n hn => hn)
      have h2 : plainK V x ≤ ((m + 1 : ℕ) : ℕ∞) + c₂ :=
        (hc₂ x []).trans (add_le_add (hDW _ x hx) le_rfl)
      refine h2.trans ?_
      rw [← hm]
      have : ((m + 1 : ℕ) : ℕ∞) + c₂ = (m : ℕ∞) + ((c₂ + 1 : ℕ) : ℕ∞) := by
        push_cast; ring
      rw [this]
      exact add_le_add le_rfl (by exact_mod_cast Nat.le_add_left _ _)

end GeneralScheme

end Kolmogorov
