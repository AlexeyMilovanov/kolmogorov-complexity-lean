import KolmogorovMathlib.Complexity.GeneralScheme.Decision
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.NatLogCode
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Decision complexity: existence and comparison with `C`, `KM` (SUV Section 6.1)

SUV Problem 192 and Theorem 127 (a)–(f) (printed pp. 194–195): existence of an optimal decision
decompressor, monotonicity, the characterization of computable sequences, and the comparison
of `KR` with plain complexity `C`, monotone complexity `KM`, and `C(x | l(x))`.
-/

namespace Kolmogorov

namespace GeneralScheme

/-- The row `i` of the universal family of decision decompressors: the prefix closure (in the
output) of the `i`-th sanitized universal stream relation read on the prefix-free code
`natCode (encode p)` of the input `p`. -/
private def exists_optimal_decisionDecompressor_U (i : ℕ) (p y : BitString) : Prop :=
  y = [] ∨ ∃ y', y <+: y' ∧ sanitizedUniversalStreamRel i (natCode (Encodable.encode p)) y'

private lemma exists_optimal_decisionDecompressor_decide_prefix :
    Primrec (fun q : BitString × BitString => decide (q.1 <+: q.2)) := by
  have H : Primrec (fun q : BitString × BitString =>
      decide (q.1 = q.2.take q.1.length)) :=
    (PrimrecPred.decide Primrec.eq).comp
      (Primrec.pair Primrec.fst
        (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd))
  exact H.of_eq fun q =>
    decide_eq_decide.mpr (List.prefix_iff_eq_take (l₁ := q.1) (l₂ := q.2)).symm

private lemma exists_optimal_decisionDecompressor_U_isRE :
    IsRE (fun q : ℕ × (BitString × BitString) =>
      exists_optimal_decisionDecompressor_U q.1 q.2.1 q.2.2) := by
  have h1 : IsRE (fun a : (ℕ × BitString × BitString) × BitString =>
      sanitizedUniversalStreamRel a.1.1 (natCode (Encodable.encode a.1.2.1)) a.2) :=
    sanitizedUniversalStreamRel_isRE_uniform.comp_computable
      (g := fun a : (ℕ × BitString × BitString) × BitString =>
        (a.1.1, (natCode (Encodable.encode a.1.2.1), a.2)))
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair
          (primrec_natCode.to_comp.comp
            (Computable.encode.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))))
          Computable.snd))
  have hdp : Primrec (fun a : (ℕ × BitString × BitString) × BitString =>
      decide (a.1.2.2 <+: a.2)) :=
    exists_optimal_decisionDecompressor_decide_prefix.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have h2 := h1.and_computable hdp.to_comp
  have h3 : IsRE (fun a : (ℕ × BitString × BitString) × BitString =>
      a.1.2.2 <+: a.2 ∧
        sanitizedUniversalStreamRel a.1.1 (natCode (Encodable.encode a.1.2.1)) a.2) :=
    h2.of_iff fun a => by rw [decide_eq_true_iff]
  have h4 : IsRE (fun q : ℕ × BitString × BitString =>
      ∃ y', q.2.2 <+: y' ∧
        sanitizedUniversalStreamRel q.1 (natCode (Encodable.encode q.2.1)) y') :=
    IsRE.exists_encodable
      (R := fun (q : ℕ × BitString × BitString) (y' : BitString) =>
        q.2.2 <+: y' ∧ sanitizedUniversalStreamRel q.1 (natCode (Encodable.encode q.2.1)) y') h3
  have h0 : IsRE (fun q : ℕ × BitString × BitString => q.2.2 = []) := by
    refine isRE_of_computable_bool _ (fun q => decide (q.2.2 = [])) (fun q => ?_) ?_
    · simp
    · exact ((PrimrecPred.decide (Primrec.eq (α := BitString))).comp
        (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const []))).to_comp
  exact (IsRE.or h0 h4).of_iff fun q => Iff.rfl

private lemma exists_optimal_decisionDecompressor_U_prefix_closed (i : ℕ) (p : BitString)
    {x x' : BitString} (hx : exists_optimal_decisionDecompressor_U i p x) (hx' : x' <+: x) :
    exists_optimal_decisionDecompressor_U i p x' := by
  rcases hx with rfl | ⟨y, hy, hxy⟩
  · exact Or.inl (List.prefix_nil.mp hx')
  · exact Or.inr ⟨y, hx'.trans hy, hxy⟩

private lemma exists_optimal_decisionDecompressor_U_regular (i : ℕ) (p : BitString)
    {x x' : BitString} (hx : exists_optimal_decisionDecompressor_U i p x)
    (hx' : exists_optimal_decisionDecompressor_U i p x') : x <+: x' ∨ x' <+: x := by
  rcases hx with rfl | ⟨y, hy, hxy⟩
  · exact Or.inl List.nil_prefix
  rcases hx' with rfl | ⟨y', hy', hxy'⟩
  · exact Or.inr List.nil_prefix
  have hc := sanitizedUniversalStreamRel_isConsistent i _ _ _ _ hxy hxy' (Or.inl List.prefix_rfl)
  rcases hc with h | h
  · exact List.prefix_or_prefix_of_prefix (hy.trans h) hy'
  · exact List.prefix_or_prefix_of_prefix hy (hy'.trans h)

private lemma exists_optimal_decisionDecompressor_natCode_prefix {m n : ℕ}
    (h : natCode m <+: natCode n) : m = n := by
  obtain ⟨t, ht⟩ := h
  exact (natCode_append_inj (a := t) (b := []) (by simpa using ht)).1

private lemma exists_optimal_decisionDecompressor_encode_inj {p p' : BitString}
    (h : natCode (Encodable.encode p) = natCode (Encodable.encode p')) : p = p' :=
  Encodable.encode_injective
    (exists_optimal_decisionDecompressor_natCode_prefix (h ▸ List.prefix_refl _))

private lemma exists_optimal_decisionDecompressor_U_complete (M : DecisionDecompressor) :
    ∃ i, ∀ p x, M.rel p x ↔ exists_optimal_decisionDecompressor_U i p x := by
  let R : BitString → BitString → Prop := fun x y =>
    ∃ p, x = natCode (Encodable.encode p) ∧ M.rel p y
  have hcons : IsConsistentStreamRelation R := by
    rintro x₁ x₂ y₁ y₂ ⟨p₁, rfl, h₁⟩ ⟨p₂, rfl, h₂⟩ hpre
    have : p₁ = p₂ := by
      refine exists_optimal_decisionDecompressor_encode_inj ?_
      rcases hpre with h | h
      · exact congrArg natCode (exists_optimal_decisionDecompressor_natCode_prefix h)
      · exact congrArg natCode (exists_optimal_decisionDecompressor_natCode_prefix h).symm
    subst this
    exact M.regular h₁ h₂ rfl
  have hre : IsRE (fun q : BitString × BitString => R q.1 q.2) := by
    have h1 : IsRE (fun a : (BitString × BitString) × BitString => M.rel a.2 a.1.2) :=
      M.re.comp_computable (g := fun a : (BitString × BitString) × BitString => (a.2, a.1.2))
        (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
    have hdp : Primrec (fun a : (BitString × BitString) × BitString =>
        decide (a.1.1 = natCode (Encodable.encode a.2))) :=
      (PrimrecPred.decide (Primrec.eq (α := BitString))).comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (primrec_natCode.comp (Primrec.encode.comp Primrec.snd)))
    have h2 := h1.and_computable hdp.to_comp
    have h3 : IsRE (fun a : (BitString × BitString) × BitString =>
        a.1.1 = natCode (Encodable.encode a.2) ∧ M.rel a.2 a.1.2) :=
      h2.of_iff fun a => by rw [decide_eq_true_iff, and_comm]
    exact IsRE.exists_encodable
      (R := fun (q : BitString × BitString) (p : BitString) =>
        q.1 = natCode (Encodable.encode p) ∧ M.rel p q.2) h3
  obtain ⟨i, hi⟩ := sanitizedUniversalStreamRel_complete hcons hre
  refine ⟨i, fun p x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Or.inr ⟨x, List.prefix_refl x, (hi _ _).mpr ⟨p, rfl, h⟩⟩
  · rcases h with rfl | ⟨y, hy, hs⟩
    · exact M.nil_mem p
    · obtain ⟨p', hp', hM⟩ := (hi _ _).mp hs
      obtain rfl := exists_optimal_decisionDecompressor_encode_inj hp'
      exact M.prefix_closed hM hy

/-- **SUV Problem 192 (Section 6.1, printed p. 194).** There is an optimal decision decompressor:
some `R` with `KR_R ≤ KR_M + O(1)` for every decision decompressor `M`.

Proof idea (as for Theorem 84, `exists_optimalMonotoneDecompressor`): enumerate the enumerable
relations, trim each one to a decision decompressor (keep a pair only while it stays compatible
with the pairs enumerated before for the same input, and close under prefixes), and let
`R(ẑ p) = M_z(p)` for a self-delimiting code `ẑ` of the index `z`. -/
theorem exists_optimal_decisionDecompressor : ∃ R : DecisionDecompressor, R.IsOptimal := by
  let R : DecisionDecompressor :=
    { rel := taggedStreamLowerGraph exists_optimal_decisionDecompressor_U
      re := taggedStreamLowerGraph_isRE exists_optimal_decisionDecompressor_U_isRE
      nil_mem := fun p => Or.inl rfl
      prefix_closed := by
        rintro p x x' (rfl | ⟨i, q, rfl, h⟩) hx'
        · exact Or.inl (List.prefix_nil.mp hx')
        · exact Or.inr ⟨i, q, rfl,
            exists_optimal_decisionDecompressor_U_prefix_closed i q h hx'⟩
      regular := by
        intro p₁ x₁ p₂ x₂ h₁ h₂ hp
        change p₁ = p₂ at hp
        subst hp
        change x₁ <+: x₂ ∨ x₂ <+: x₁
        rcases h₁ with rfl | ⟨i, q, hq, h⟩
        · exact Or.inl List.nil_prefix
        rcases h₂ with rfl | ⟨j, r, hr, h'⟩
        · exact Or.inr List.nil_prefix
        obtain ⟨rfl, rfl⟩ := natCode_append_inj (hq.symm.trans hr)
        exact exists_optimal_decisionDecompressor_U_regular i q h h' }
  refine ⟨R, fun M => ?_⟩
  obtain ⟨i, hi⟩ := exists_optimal_decisionDecompressor_U_complete M
  refine ⟨(natCode i).length, fun x => ?_⟩
  unfold KROf modeComplexity
  by_cases hne : {l : ℕ∞ | ∃ p, M.rel p x ∧ l = p.length} = ∅
  · rw [hne, sInf_empty, top_add]
    exact le_top
  · obtain ⟨p, hp, hpl⟩ := csInf_mem (Set.nonempty_iff_ne_empty.mpr hne)
    rw [hpl]
    refine (modeComplexity_le_length (R := R.rel) (p := natCode i ++ p) (x := x)
      (Or.inr ⟨i, p, rfl, (hi p x).mp hp⟩)).trans ?_
    rw [List.length_append]
    push_cast
    rw [add_comm]

/-- **SUV Section 6.1 (printed p. 194), unnumbered.** `KR(x) ≤ l(x) + O(1)` for an optimal
decision decompressor. The book uses it tacitly (it is also a consequence of Theorem 127 (c)).
In particular `KR` is finite.

Proof idea: the machine that prints its input, `rel p x ↔ x <+: p`, is a decision decompressor
with complexity `l(x)`. -/
theorem exists_const_KROf_le_length {R : DecisionDecompressor} (hR : R.IsOptimal) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ x.length + c := by
  let M : DecisionDecompressor :=
    { rel := fun p x => x <+: p
      re := by
        have H : Computable (fun q : BitString × BitString => q.1.take q.2.length) :=
          (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst).to_comp
        have H2 : Computable (fun q : BitString × BitString =>
            decide (q.1.take q.2.length = q.2)) :=
          (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp
            (Computable.pair H Computable.snd)
        refine isRE_of_computable_bool _ _ (fun q => ?_) H2
        rw [decide_eq_true_iff]
        rw [eq_comm]
        exact List.prefix_iff_eq_take.symm
      nil_mem := fun p => List.nil_prefix
      prefix_closed := fun _ _ _ h h' => h'.trans h
      regular := fun p₁ x₁ p₂ x₂ h₁ h₂ hp => by
        change p₁ = p₂ at hp
        subst hp
        rcases le_total x₁.length x₂.length with h | h
        · exact Or.inl (List.prefix_of_prefix_length_le h₁ h₂ h)
        · exact Or.inr (List.prefix_of_prefix_length_le h₂ h₁ h) }
  obtain ⟨c, hc⟩ := hR M
  refine ⟨c, fun x => ?_⟩
  refine (hc x).trans ?_
  gcongr
  exact modeComplexity_le_length (p := x) (List.prefix_refl x)

/-- **SUV Section 6.1 (printed p. 194), unnumbered.** The decision complexity with respect to an
optimal decompressor is finite.

Proof: `exists_const_KROf_le_length`. -/
theorem KROf_ne_top {R : DecisionDecompressor} (hR : R.IsOptimal) (x : BitString) :
    KROf R x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_const_KROf_le_length hR
  exact ne_top_of_le_natCast_add (hc x)

/-- **SUV Theorem 127 (a) (Section 6.1, printed p. 194).** If `x` is a prefix of `y` then
`KR(x) ≤ KR(y)`. This holds exactly, for every decision decompressor, because a description of
`y` is a description of every prefix of `y` (`KROf_mono_of_prefix`). -/
theorem theorem127a_KROf_mono (M : DecisionDecompressor) {x y : BitString} (h : x <+: y) :
    KROf M x ≤ KROf M y :=
  KROf_mono_of_prefix M h

/-- **SUV Theorem 127 (b), first half (Section 6.1, printed p. 194).** The complexities of the
prefixes of a sequence form a non-decreasing sequence. This is a corollary of (a). -/
theorem KROf_cantorPrefix_monotone (M : DecisionDecompressor) (w : CantorSeq) :
    Monotone fun n => KROf M (cantorPrefix w n) :=
  fun _ _ h => KROf_mono_of_prefix M (cantorPrefix_mono w h)

/-- A sequence all of whose prefixes are accepted by an enumerable predicate that accepts only
prefixes of `w` is computable. -/
private lemma computable_iff_KROf_prefixes_bounded_aux_computable (chk : BitString → ℕ → Bool)
    (hchk : Computable₂ chk) (w : CantorSeq) (h1 : ∀ x s, chk x s = true → IsCantorPrefix x w)
    (h2 : ∀ n, ∃ s, chk (cantorPrefix w n) s = true) : Computable w := by
  let cand : ℕ → BitString := fun t => (Encodable.decode (α := BitString) (Nat.unpair t).2).getD []
  have hcand : Computable cand :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const [])
  let pred : ℕ → ℕ → Bool := fun i t =>
    chk (cand t) (Nat.unpair t).1 && decide (i < (cand t).length)
  have hpred : Computable₂ pred := by
    have hA : Computable₂ (fun (_ : ℕ) (t : ℕ) => chk (cand t) (Nat.unpair t).1) :=
      hchk.comp (hcand.comp Computable.snd)
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    have hB : Computable₂ (fun (i : ℕ) (t : ℕ) => decide (i < (cand t).length)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp Computable.fst
        (Primrec.list_length.to_comp.comp (hcand.comp Computable.snd))
    exact Primrec.and.to_comp.comp hA hB
  have hout : Computable₂ (fun n t : ℕ => (cand t).getD n false) :=
    (Primrec.list_getD false).to_comp.comp (hcand.comp Computable.snd) Computable.fst
  let P : ℕ → ℕ →. Bool := fun n t => Part.some (pred n t)
  have hpart : Partrec (fun n : ℕ =>
      (Nat.rfind (P n)).map fun t => (cand t).getD n false) :=
    Partrec.map (Partrec.rfind (Computable₂.partrec₂ hpred)) hout
  refine hpart.of_eq fun n => ?_
  change _ = Part.some (w n)
  rw [Part.eq_some_iff]
  have hdom : (Nat.rfind (P n)).Dom := by
    rw [Nat.rfind_dom]
    obtain ⟨s, hs⟩ := h2 (n + 1)
    refine ⟨Nat.pair s (Encodable.encode (cantorPrefix w (n + 1))), ?_, fun {m} _ => trivial⟩
    refine Part.mem_some_iff.mpr ?_
    simp [pred, cand, hs]
  have hmem := Part.get_mem hdom
  have hspec := Nat.rfind_spec hmem
  have ht : pred n ((Nat.rfind (P n)).get hdom) = true := by
    exact (Part.mem_some_iff.mp hspec).symm
  simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at ht
  refine Part.mem_map_iff _ |>.mpr ⟨_, hmem, ?_⟩
  have := h1 _ _ ht.1 n ht.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht.2]
  simp [this]

/-- The decision decompressor that ignores its input and prints the computable sequence `w`. -/
private def computable_iff_KROf_prefixes_bounded_const (w : CantorSeq) (hw : Computable w) :
    DecisionDecompressor where
  rel _ x := IsCantorPrefix x w
  re := by
    have H : Computable (fun p : BitString × BitString => cantorPrefix w p.2.length) :=
      (computable_cantorPrefix w hw).comp
        (Primrec.to_comp (Primrec.list_length.comp Primrec.snd))
    have H2 : Computable (fun p : BitString × BitString =>
        decide (cantorPrefix w p.2.length = p.2)) :=
      (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp
        (Computable.pair H Computable.snd)
    refine isRE_of_computable_bool _ _ (fun p => ?_) H2
    rw [decide_eq_true_iff]
    exact (isCantorPrefix_iff_cantorPrefix_eq p.2 w).symm
  nil_mem _ := fun i hi => by simp at hi
  prefix_closed := fun _ x x' hx hx' i hi => by
    rw [hx i (lt_of_lt_of_le hi hx'.length_le)]
    exact (hx'.getElem hi).symm
  regular := fun p₁ x₁ p₂ x₂ h₁ h₂ _ => by
    replace h₁ : IsCantorPrefix x₁ w := h₁
    replace h₂ : IsCantorPrefix x₂ w := h₂
    rw [isCantorPrefix_iff_cantorPrefix_eq] at h₁ h₂
    rw [← h₁, ← h₂]
    rcases le_total x₁.length x₂.length with h | h
    · exact Or.inl (cantorPrefix_mono w h)
    · exact Or.inr (cantorPrefix_mono w h)

/-- **SUV Theorem 127 (b), second half (Section 6.1, printed p. 194).** The decision complexities
of the prefixes of `w` are bounded if and only if `w` is computable. Equivalently `KRSeq R w` is
finite exactly for computable `w`.

Proof idea: if `w` is computable, the machine that ignores its input and prints `w` describes
every prefix by the empty string. Conversely, if all prefixes have complexity `≤ c`, some
description of length `≤ c` describes infinitely many prefixes, hence all of them (regularity),
so `w` is the output of a machine on a fixed input and is computable. Compare
`computable_iff_KMOf_prefixes_bounded` (Theorem 85). -/
theorem computable_iff_KROf_prefixes_bounded {R : DecisionDecompressor} (hR : R.IsOptimal)
    (w : CantorSeq) :
    Computable w ↔ ∃ c : ℕ, ∀ n, KROf R (cantorPrefix w n) ≤ c := by
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hR (computable_iff_KROf_prefixes_bounded_const w hw)
    refine ⟨c, fun n => ?_⟩
    have h0 : KROf (computable_iff_KROf_prefixes_bounded_const w hw) (cantorPrefix w n) ≤ 0 :=
      (modeComplexity_le_length (p := []) (fun i hi => by
        rw [cantorPrefix_getElem])).trans (by simp)
    calc KROf R (cantorPrefix w n) ≤ _ + c := hc _
      _ ≤ 0 + c := add_le_add_left h0 _
      _ = c := zero_add _
  · rintro ⟨c, hc⟩
    -- every prefix has a description of length ≤ c
    have hex : ∀ n, ∃ p : BitString, p.length ≤ c ∧ R.rel p (cantorPrefix w n) := by
      intro n
      have hne : {l : ℕ∞ | ∃ p, R.rel p (cantorPrefix w n) ∧ l = p.length}.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        have : KROf R (cantorPrefix w n) = ⊤ := by
          unfold KROf modeComplexity
          rw [hempty, sInf_empty]
        have := hc n
        rw [‹KROf R (cantorPrefix w n) = ⊤›] at this
        exact absurd this (by simp)
      obtain ⟨p, hp, hpl⟩ := csInf_mem hne
      refine ⟨p, ?_, hp⟩
      have := hc n
      have h2 : ((p.length : ℕ) : ℕ∞) ≤ c := by
        rw [← hpl]; exact this
      exact_mod_cast h2
    choose p hpl hp using hex
    -- pigeonhole: a single description serves infinitely many prefixes
    have : Finite {q : BitString // q.length ≤ c} := (List.finite_length_le Bool c).to_subtype
    obtain ⟨⟨q, hqc⟩, hinf⟩ := Finite.exists_infinite_fiber
      (fun n : ℕ => (⟨p n, hpl n⟩ : {q : BitString // q.length ≤ c}))
    have hsetinf : {n : ℕ | p n = q}.Infinite := by
      have := Set.infinite_coe_iff.mp hinf
      refine this.mono ?_
      intro n hn
      simpa using hn
    have hall : ∀ m, R.rel q (cantorPrefix w m) := by
      intro m
      obtain ⟨n, hn, hmn⟩ := hsetinf.exists_gt m
      have h1 : p n = q := hn
      have h2 := hp n
      rw [h1] at h2
      exact R.prefix_closed h2 (cantorPrefix_mono w hmn.le)
    obtain ⟨chk, hchk, -, hchk_iff⟩ := IsRE.exists_stageApprox
      (IsRE.comp_computable R.re (g := fun x : BitString => (q, x))
        ((Computable.const q).pair Computable.id))
    refine computable_iff_KROf_prefixes_bounded_aux_computable (fun x s => chk x s) hchk w
      (fun x s hs => ?_) (fun n => (hchk_iff _).mp (hall n))
    have hx : R.rel q x := (hchk_iff x).mpr ⟨s, hs⟩
    rw [isCantorPrefix_iff_cantorPrefix_eq]
    rcases R.regular (hall x.length) hx rfl with h | h
    · exact h.eq_of_length (by simp)
    · exact (h.eq_of_length (by simp)).symm

/-- **SUV Theorem 127 (b), parenthetical remark (Section 6.1, printed p. 194).** The decision
complexity of a sequence (the limit of the complexities of its prefixes) is finite for
computable sequences and infinite for non-computable ones.

Proof idea: `computable_iff_KROf_prefixes_bounded`. A supremum of naturals in `ℕ∞` is finite
iff the naturals are bounded. -/
theorem KRSeq_ne_top_iff {R : DecisionDecompressor} (hR : R.IsOptimal) (w : CantorSeq) :
    KRSeq R w ≠ ⊤ ↔ Computable w := by
  rw [computable_iff_KROf_prefixes_bounded hR w]
  constructor
  · intro h
    refine ⟨(KRSeq R w).toNat, fun n => ?_⟩
    rw [ENat.natCast_toNat h]
    exact le_iSup (fun n => KROf R (cantorPrefix w n)) n
  · rintro ⟨c, hc⟩
    exact ne_top_of_le_natCast (iSup_le hc)

/-- The decision decompressor of a partial computable plain decompressor `U`: the output on `p`
is the (possibly not yet printed) value `U(p, [])`. -/
private noncomputable def exists_const_KROf_le_plainK_dec (U : Map) (hU : isDecompressor U) :
    DecisionDecompressor where
  rel p x := x = [] ∨ ∃ y, y ∈ U (p, []) ∧ x <+: y
  re := by
    have hpref : Computable (fun r : (BitString × BitString) × BitString =>
        decide (r.1.2 <+: r.2)) := by
      have h : Primrec (fun r : (BitString × BitString) × BitString =>
          decide (r.1.2 = r.2.take r.1.2.length)) :=
        (PrimrecPred.decide Primrec.eq).comp
          (Primrec.pair (Primrec.snd.comp Primrec.fst)
            (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
              Primrec.snd))
      exact (h.to_comp).of_eq fun r =>
        decide_eq_decide.mpr (List.prefix_iff_eq_take (l₁ := r.1.2) (l₂ := r.2)).symm
    have hgraph : IsRE (fun r : (BitString × BitString) × BitString =>
        r.2 ∈ U ((r.1.1, []))) :=
      IsRE.comp_computable (Partrec.graphIsRe U hU)
        (g := fun r : (BitString × BitString) × BitString => ((r.1.1, ([] : BitString)), r.2))
        (((Computable.fst.comp Computable.fst).pair
          ((Computable.const ([] : BitString)).comp Computable.fst)).pair Computable.snd)
    have h2 : IsRE (fun q : BitString × BitString => ∃ y, y ∈ U (q.1, []) ∧ q.2 <+: y) := by
      refine IsRE.exists_encodable (R := fun (q : BitString × BitString) (y : BitString) => y ∈ U
          (q.1, []) ∧ q.2 <+: y) ?_
      refine IsRE.of_iff (IsRE.and_computable hgraph hpref) ?_
      intro r
      simp [and_comm]
    have h1 : IsRE (fun q : BitString × BitString => q.2 = []) := by
      refine isRE_of_computable_bool _ (fun q => decide (q.2 = [])) (fun q => ?_) ?_
      · simp
      · exact (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp
          (Computable.pair Computable.snd (Computable.const []))
    exact IsRE.or h1 h2
  nil_mem p := Or.inl rfl
  prefix_closed := by
    rintro p x x' (hx | ⟨y, hy, hxy⟩) hx'
    · left
      subst hx
      exact List.prefix_nil.mp hx'
    · right
      exact ⟨y, hy, hx'.trans hxy⟩
  regular := by
    intro p₁ x₁ p₂ x₂ h₁ h₂ hp
    change p₁ = p₂ at hp
    subst hp
    change x₁ <+: x₂ ∨ x₂ <+: x₁
    rcases h₁ with rfl | ⟨y₁, hy₁, hx₁⟩
    · exact Or.inl (List.nil_prefix)
    rcases h₂ with rfl | ⟨y₂, hy₂, hx₂⟩
    · exact Or.inr (List.nil_prefix)
    have : y₁ = y₂ := Part.mem_unique hy₁ hy₂
    subst this
    exact List.prefix_or_prefix_of_prefix hx₁ hx₂

/-- **SUV Theorem 127 (c) (Section 6.1, printed p. 194).** `KR(x) ≤ C(x) + O(1)`.

Proof idea: a partial computable function is a decision decompressor that prints nothing
before the computation halts and then prints the result. -/
theorem exists_const_KROf_le_plainK {R : DecisionDecompressor} (hR : R.IsOptimal) {U : Map}
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ plainK U x + c := by
  obtain ⟨c, hc⟩ := hR (exists_const_KROf_le_plainK_dec U hU.1)
  refine ⟨c, fun x => (hc x).trans (add_le_add_left ?_ _)⟩
  unfold plainK condK
  refine le_sInf ?_
  rintro n ⟨p, hp, rfl⟩
  exact modeComplexity_le_length (R := (exists_const_KROf_le_plainK_dec U hU.1).rel)
    (Or.inr ⟨x, hp, List.prefix_refl x⟩)

/-- **SUV Theorem 127 (d) (Section 6.1, printed p. 194).** `KR(x) ≤ KM(x) + O(1)`.

Proof idea: a computable continuous map `Σ → Σ` restricted to finite inputs is a decision
decompressor. The input is typed in at the start and the output is printed as the monotone
machine produces it. Use the lower graph `streamLowerGraph D`. -/
theorem exists_const_KROf_le_KMOf {R : DecisionDecompressor} (hR : R.IsOptimal)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ KMOf D x + c := by
  have hgraph : IsStreamLowerGraph (streamLowerGraph D) :=
    continuousStreamMap_lowerGraph_isStreamLowerGraph hD.1.1.1
  let M : DecisionDecompressor :=
    { rel := streamLowerGraph D
      re := hD.1.2
      nil_mem := fun p => hgraph.1 p
      prefix_closed := fun p x x' hx hx' => hgraph.2.1 p x x' hx hx'
      regular := fun p₁ x₁ p₂ x₂ h₁ h₂ hp => by
        have hp' : p₁ = p₂ := hp
        subst hp'
        exact hgraph.2.2.2 p₁ x₁ x₂ h₁ h₂ }
  obtain ⟨c, hc⟩ := hR M
  exact ⟨c, fun x => (hc x).trans (add_le_add_left (le_of_eq rfl) _)⟩

/-- The relation of the proof of `exists_const_KMOf_le_KROf_add_log`: the description of `x` is
the self-delimiting code of the length of a `KR`-description `p` followed by `p`. -/
private def exists_const_KMOf_le_KROf_add_log_rel (R : DecisionDecompressor)
    (q x : BitString) : Prop :=
  ∃ p : BitString, q = natLogCode p.length ++ p ∧ R.rel p x

/-- The length of `natLogCode n` is at most `2 log₂ n + 3`. -/
private lemma exists_const_KMOf_le_KROf_add_log_length_natLogCode (n : ℕ) :
    (natLogCode n).length ≤ 2 * Nat.log 2 n + 3 := by
  have h : (Nat.bits n).length ≤ Nat.log 2 n + 1 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)
  simp only [natLogCode, List.length_append, length_natCode]
  omega

/-- The relation is consistent. -/
private lemma exists_const_KMOf_le_KROf_add_log_consistent (R : DecisionDecompressor) :
    IsConsistentStreamRelation (exists_const_KMOf_le_KROf_add_log_rel R) := by
  have key : ∀ (p₁ p₂ t : BitString),
      natLogCode p₁.length ++ p₁ ++ t = natLogCode p₂.length ++ p₂ → p₁ = p₂ := by
    intro p₁ p₂ t h
    rw [List.append_assoc] at h
    obtain ⟨hl, h2⟩ := natLogCode_append_inj h
    have h3 := congrArg List.length h2
    simp only [List.length_append] at h3
    have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
    subst ht
    simpa using h2
  rintro x₁ x₂ y₁ y₂ ⟨p₁, rfl, h₁⟩ ⟨p₂, rfl, h₂⟩ hx
  rcases hx with ⟨t, ht⟩ | ⟨t, ht⟩
  · have := key p₁ p₂ t ht
    subst this
    exact R.regular h₁ h₂ rfl
  · have := key p₂ p₁ t ht
    subst this
    exact R.regular h₁ h₂ rfl

/-- The relation is enumerable. -/
private lemma exists_const_KMOf_le_KROf_add_log_re (R : DecisionDecompressor) :
    IsRE fun q : BitString × BitString => exists_const_KMOf_le_KROf_add_log_rel R q.1 q.2 := by
  have h1 : IsRE fun a : (BitString × BitString) × BitString =>
      (decide (a.1.1 = natLogCode a.2.length ++ a.2) = true) ∧ R.rel a.2 a.1.2 := by
    refine IsRE.and_computable (R := fun a : (BitString × BitString) × BitString =>
      R.rel a.2 a.1.2) ?_ ?_
    · exact IsRE.comp_computable R.re (g := fun a : (BitString × BitString) × BitString =>
        (a.2, a.1.2)) (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
    · have hq : Primrec fun a : (BitString × BitString) × BitString => a.1.1 :=
        Primrec.fst.comp Primrec.fst
      have hr : Primrec fun a : (BitString × BitString) × BitString =>
          natLogCode a.2.length ++ a.2 :=
        Primrec.list_append.comp
          (primrec_natLogCode.comp (Primrec.list_length.comp Primrec.snd)) Primrec.snd
      have hp : Primrec fun a : (BitString × BitString) × BitString =>
          decide (a.1.1 = natLogCode a.2.length ++ a.2) :=
        (Primrec.eq.comp hq hr).decide
      exact hp.to_comp
  refine IsRE.of_iff (IsRE.exists_encodable
    (R := fun (q : BitString × BitString) (p : BitString) =>
      (decide (q.1 = natLogCode p.length ++ p) = true) ∧ R.rel p q.2) h1) ?_
  intro q
  simp [exists_const_KMOf_le_KROf_add_log_rel, eq_comm]

/-- **SUV Theorem 127 (e) (Section 6.1, printed p. 194).** `KM(x) ≤ KR(x) + O(log KR(x))`.

Proof idea: the monotone decompressor `R̂(x̂ u) = R(x)` reads a self-delimiting code `x̂` of the
input (length `l(x) + O(log l(x))`) and ignores the rest `u`. The `toNat` is harmless because
`KROf R x` is finite (`KROf_ne_top`). -/
theorem exists_const_KMOf_le_KROf_add_log {R : DecisionDecompressor} (hR : R.IsOptimal)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x,
      KMOf D x ≤ KROf R x + ((c * Nat.log 2 (KROf R x).toNat + c : ℕ) : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := exists_const_KMOf_le_consistentRelationKMOf hD
    (exists_const_KMOf_le_KROf_add_log_consistent R) (exists_const_KMOf_le_KROf_add_log_re R)
  refine ⟨c₀ + 3, fun x => ?_⟩
  have hfin := KROf_ne_top hR x
  set n := (KROf R x).toNat with hn
  have hKR : KROf R x = (n : ℕ∞) := (ENat.natCast_toNat hfin).symm
  have hne : {l : ℕ∞ | ∃ p, R.rel p x ∧ l = p.length}.Nonempty := by
    by_contra h
    apply hfin
    unfold KROf modeComplexity
    rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact sInf_empty
  obtain ⟨p, hp, hpl⟩ := csInf_mem hne
  have hpn : p.length = n := by
    have : (p.length : ℕ∞) = (n : ℕ∞) := by
      rw [← hKR]
      exact hpl.symm
    exact_mod_cast this
  have hS : consistentRelationKMOf (exists_const_KMOf_le_KROf_add_log_rel R) x ≤
      ((natLogCode p.length ++ p).length : ℕ∞) :=
    sInf_le ⟨natLogCode p.length ++ p, ⟨p, rfl, hp⟩, rfl⟩
  have hlen : (natLogCode p.length ++ p).length ≤ n + (2 * Nat.log 2 n + 3) := by
    have := exists_const_KMOf_le_KROf_add_log_length_natLogCode p.length
    rw [hpn] at this
    simp only [List.length_append, hpn]
    omega
  calc KMOf D x
      ≤ consistentRelationKMOf (exists_const_KMOf_le_KROf_add_log_rel R) x + (c₀ : ℕ∞) := hc₀ x
    _ ≤ ((natLogCode p.length ++ p).length : ℕ∞) + (c₀ : ℕ∞) := by gcongr
    _ ≤ ((n + (2 * Nat.log 2 n + 3) + c₀ : ℕ) : ℕ∞) := by exact_mod_cast Nat.add_le_add_right hlen _
    _ ≤ KROf R x + (((c₀ + 3) * Nat.log 2 n + (c₀ + 3) : ℕ) : ℕ∞) := by
      rw [hKR, ← Nat.cast_add]
      exact_mod_cast (by nlinarith : n + (2 * Nat.log 2 n + 3) + c₀ ≤
        n + ((c₀ + 3) * Nat.log 2 n + (c₀ + 3)))

/-- The conditional decompressor `S(p, y)`: the first `decodeBits y` bits of `R(p)`. -/
private lemma exists_const_condK_length_le_KROf_aux (R : DecisionDecompressor) :
    ∃ S : Map, Partrec S ∧ ∀ p x, R.rel p x → x ∈ S (p, Nat.bits x.length) := by
  obtain ⟨chk, hchk, -, hchk_iff⟩ := IsRE.exists_stageApprox R.re
  let cand : ℕ → BitString := fun t => (Encodable.decode (α := BitString) (Nat.unpair t).2).getD []
  have hcand : Computable cand :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const [])
  let pred : BitString × BitString → ℕ → Bool := fun q t =>
    chk (q.1, cand t) (Nat.unpair t).1 && decide ((cand t).length = decodeBits q.2)
  have hpred : Computable₂ pred := by
    have hA : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
        chk (q.1, cand t) (Nat.unpair t).1) :=
      hchk.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (hcand.comp Computable.snd))
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    have hB : Computable₂ (fun (q : BitString × BitString) (t : ℕ) =>
        decide ((cand t).length = decodeBits q.2)) :=
      (Primrec.to_comp (PrimrecPred.decide Primrec.eq)).comp
        (Computable.pair (Primrec.list_length.to_comp.comp (hcand.comp Computable.snd))
          (decodeBits_computable.comp (Computable.snd.comp Computable.fst)))
    exact Primrec.and.to_comp.comp hA hB
  let P : BitString × BitString → ℕ →. Bool := fun q t => Part.some (pred q t)
  refine ⟨fun q => (Nat.rfind (P q)).map cand, ?_, ?_⟩
  · exact Partrec.map (Partrec.rfind (Computable₂.partrec₂ hpred))
      (hcand.comp Computable.snd).to₂
  · intro p x hx
    have hdom : (Nat.rfind (P (p, Nat.bits x.length))).Dom := by
      rw [Nat.rfind_dom]
      obtain ⟨s, hs⟩ := (hchk_iff (p, x)).mp hx
      refine ⟨Nat.pair s (Encodable.encode x), ?_, fun {m} _ => trivial⟩
      refine Part.mem_some_iff.mpr ?_
      simp [pred, cand, hs, decodeBits_natBits]
    have hmem := Part.get_mem hdom
    have hspec := Nat.rfind_spec hmem
    have ht : pred (p, Nat.bits x.length) ((Nat.rfind (P (p, Nat.bits x.length))).get hdom)
        = true := (Part.mem_some_iff.mp hspec).symm
    simp only [pred, Bool.and_eq_true, decide_eq_true_eq, decodeBits_natBits] at ht
    obtain ⟨h1, h2⟩ := ht
    have hz : R.rel p (cand ((Nat.rfind (P (p, Nat.bits x.length))).get hdom)) :=
      (hchk_iff _).mpr ⟨_, h1⟩
    have heq : cand ((Nat.rfind (P (p, Nat.bits x.length))).get hdom) = x := by
      rcases R.regular hz hx rfl with h | h
      · exact h.eq_of_length h2
      · exact (h.eq_of_length h2.symm).symm
    exact Part.mem_map_iff _ |>.mpr ⟨_, hmem, heq⟩

/-- **SUV Theorem 127 (f) (Section 6.1, printed p. 194).** `C(x | l(x)) ≤ KR(x) + O(1)`. The
condition `l(x)` is the string `Nat.bits x.length`, as in
`computable_iff_condK_prefix_bounded`.

Proof idea: the conditional decompressor `S(y, n)` returns the first `n` bits of `R(y)`, and is
undefined if `R(y)` is shorter. -/
theorem exists_const_condK_length_le_KROf {R : DecisionDecompressor} (_hR : R.IsOptimal)
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, condK U x (Nat.bits x.length) ≤ KROf R x + c := by
  obtain ⟨S, hSpart, hS⟩ := exists_const_condK_length_le_KROf_aux R
  obtain ⟨c, hc⟩ := hU.2 S hSpart
  refine ⟨c, fun x => ?_⟩
  refine (hc x _).trans (add_le_add ?_ le_rfl)
  refine le_sInf ?_
  rintro l ⟨p, hp, rfl⟩
  exact sInf_le ⟨p, hS p x hp, rfl⟩

end GeneralScheme

end Kolmogorov
