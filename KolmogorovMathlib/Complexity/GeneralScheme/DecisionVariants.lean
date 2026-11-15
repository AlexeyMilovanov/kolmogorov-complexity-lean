import KolmogorovMathlib.Complexity.GeneralScheme.DecisionBasic
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds

/-!
# Decision complexity: equivalent definitions (SUV Problems 194–196)

SUV Problem 194 (printed p. 196) defines `KR` through bitwise decompressors `S(y, i) = x_i`.
Problems 195–196 (printed p. 197) express `KR` and a bound on `KM` through the complexity of
programs that print `x` or an extension of `x`.
-/

namespace Kolmogorov

namespace GeneralScheme

private lemma exists_isOptimalBitwise_prefix_of_agree {z z' : BitString}
    (h : ∀ i (hi : i < z.length) (hi' : i < z'.length), z[i] = z'[i]) :
    z <+: z' ∨ z' <+: z := by
  rcases le_total z.length z'.length with hl | hl
  · left
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact h i (by simpa [hl] using hi) (lt_of_lt_of_le (by simpa [hl] using hi) hl)
  · right
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact (h i (lt_of_lt_of_le (by simpa [hl] using hi) hl) (by simpa [hl] using hi)).symm

private lemma exists_isOptimalBitwise_isRE {S : BitString × ℕ →. Bool} (hS : Partrec S) :
    IsRE (fun w : BitString × BitString => ∀ i (hi : i < w.2.length), w.2[i] ∈ S (w.1, i)) := by
  classical
  let h : (BitString × BitString) × (ℕ × Unit) →. Unit := fun q =>
    (S (q.1.1, q.2.1)).bind fun b =>
      (↑(if b = q.1.2.getD q.2.1 false then some () else none) : Part Unit)
  have hh : Partrec₂ (fun (a : BitString × BitString) (u : ℕ × Unit) =>
      h (a, u)) := by
    refine Partrec.bind (hS.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd))) ?_
    have : Partrec (fun q : (((BitString × BitString) × (ℕ × Unit)) × Bool) =>
        (↑(if q.2 = q.1.1.2.getD q.1.2.1 false then some () else none) : Part Unit)) := by
      refine Computable.ofOption ((Computable.cond
        ((Primrec.to_comp Primrec.beq).comp
          (Computable.pair Computable.snd
            (Computable.of_eq ((Primrec.list_getD false).to_comp.comp
              (Computable.snd.comp (Computable.fst.comp Computable.fst))
              (Computable.fst.comp (Computable.snd.comp Computable.fst))) fun _ => rfl)))
        (Computable.const (some ()))
        (Computable.const none)).of_eq (fun q => by simp [beq_iff_eq]))
    exact this.to₂
  have hF : Partrec (fun a : BitString × BitString =>
      (a.2.length).rec (Part.some ()) (fun y IH => IH.bind fun i => h (a, (y, i)))) :=
    Partrec.nat_rec (Primrec.list_length.comp Primrec.snd).to_comp
      (Partrec.const' (Part.some ())) hh
  refine ⟨_, hF, fun a => ?_⟩
  have hd : ∀ (k : ℕ) (u : Unit), (h (a, (k, u))).Dom ↔ a.2.getD k false ∈ S (a.1, k) := by
    intro k u
    simp only [h, Part.bind_dom]
    constructor
    · rintro ⟨hdom, hc⟩
      refine ⟨hdom, ?_⟩
      simpa [List.getD_eq_getElem?_getD] using hc
    · rintro ⟨hdom, heq⟩
      refine ⟨hdom, ?_⟩
      simp [heq]
  have key : ∀ n : ℕ, ((n.rec (Part.some ()) (fun y IH => IH.bind fun i => h (a, (y, i))) :
      Part Unit)).Dom ↔ ∀ i < n, a.2.getD i false ∈ S (a.1, i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (Part.bind _ _).Dom ↔ _
      rw [Part.bind_dom]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ih.1 h1 i hi
        · exact (hd _ _).1 h2
      · intro H
        exact ⟨ih.2 fun i hi => H i (by omega), (hd _ _).2 (H n (by omega))⟩
  refine (key a.2.length).trans ?_
  constructor
  · intro H i hi
    have := H i hi
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro H i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact H i hi

/-- The decision decompressor of a bitwise decompressor `S`: `M(y)` starts with `x` iff
`S(y, i) = xᵢ` for all `i < l(x)`. -/
private def exists_isOptimalBitwise_machine {S : BitString × ℕ →. Bool} (hS : Partrec S) :
    DecisionDecompressor where
  rel y x := ∀ i (hi : i < x.length), x[i] ∈ S (y, i)
  re := exists_isOptimalBitwise_isRE hS
  nil_mem := fun p i hi => by simp at hi
  prefix_closed := fun p x x' hx hx' i hi => by
    have h1 := hx i (lt_of_lt_of_le hi hx'.length_le)
    rwa [← hx'.getElem hi] at h1
  regular := fun p₁ x₁ p₂ x₂ h₁ h₂ hp => by
    change p₁ = p₂ at hp
    subst hp
    refine exists_isOptimalBitwise_prefix_of_agree fun i hi hi' => ?_
    exact Part.mem_unique (h₁ i hi) (h₂ i hi')

private lemma exists_isOptimalBitwise_machine_le {S : BitString × ℕ →. Bool}
    (hS : Partrec S) (x : BitString) :
    KROf (exists_isOptimalBitwise_machine hS) x ≤ bitwiseKR S x := by
  unfold KROf modeComplexity bitwiseKR
  exact le_of_eq rfl

/-- The bitwise decompressor `S'(y, i)`: search for an output `x'` of `R` on `y` with `i < l(x')`
and return `x'ᵢ`. -/
private lemma exists_isOptimalBitwise_bitwise (R : DecisionDecompressor) :
    ∃ S' : BitString × ℕ →. Bool, Partrec S' ∧ ∀ x, bitwiseKR S' x ≤ KROf R x := by
  obtain ⟨chk, hchk, -, hchk_iff⟩ := IsRE.exists_stageApprox R.re
  let cand : ℕ → BitString := fun t =>
    (Encodable.decode (α := BitString) (Nat.unpair t).2).getD []
  have hcand : Computable cand :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const [])
  let pred : BitString × ℕ → ℕ → Bool := fun a t =>
    chk (a.1, cand t) (Nat.unpair t).1 && decide (a.2 < (cand t).length)
  have hpred : Computable₂ pred := by
    have hA : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) =>
        chk (a.1, cand t) (Nat.unpair t).1) :=
      hchk.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (hcand.comp Computable.snd))
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    have hB : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) => decide (a.2 < (cand t).length)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp (Computable.snd.comp Computable.fst)
        (Primrec.list_length.to_comp.comp (hcand.comp Computable.snd))
    exact Primrec.and.to_comp.comp hA hB
  have hout : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) => (cand t).getD a.2 false) :=
    (Primrec.list_getD false).to_comp.comp (hcand.comp Computable.snd)
      (Computable.snd.comp Computable.fst)
  let P : BitString × ℕ → ℕ →. Bool := fun a t => Part.some (pred a t)
  let S' : BitString × ℕ →. Bool := fun a => (Nat.rfind (P a)).map fun t => (cand t).getD a.2 false
  have hS' : Partrec S' := Partrec.map (Partrec.rfind (Computable₂.partrec₂ hpred)) hout
  refine ⟨S', hS', fun x => ?_⟩
  unfold KROf modeComplexity bitwiseKR
  refine sInf_le_sInf fun l ⟨p, hp, hl⟩ => ⟨p, fun i hi => ?_, hl⟩
  have hdom : (Nat.rfind (P (p, i))).Dom := by
    rw [Nat.rfind_dom]
    obtain ⟨s, hs⟩ := (hchk_iff (p, x)).mp hp
    refine ⟨Nat.pair s (Encodable.encode x), ?_, fun {m} _ => trivial⟩
    refine Part.mem_some_iff.mpr ?_
    simp [pred, cand, hs, hi]
  have hmem := Part.get_mem hdom
  have hspec := Nat.rfind_spec hmem
  have ht : pred (p, i) ((Nat.rfind (P (p, i))).get hdom) = true :=
    (Part.mem_some_iff.mp hspec).symm
  simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hx0 : R.rel p (cand ((Nat.rfind (P (p, i))).get hdom)) := (hchk_iff _).mpr ⟨_, ht.1⟩
  refine Part.mem_map_iff _ |>.mpr ⟨_, hmem, ?_⟩
  have hc := R.regular hp hx0 rfl
  have hle : i < (cand ((Nat.rfind (P (p, i))).get hdom)).length := ht.2
  have : x[i] = (cand ((Nat.rfind (P (p, i))).get hdom))[i] := by
    rcases hc with h | h
    · exact h.getElem hi
    · exact (h.getElem hle).symm
  rw [List.getD_eq_getElem _ _ hle, this]

/-- **SUV Problem 194 (Section 6.1, printed p. 196), part 1.** There is an optimal bitwise
decompressor: a partial computable `S(y, i)` with bit values such that `bitwiseKR S` is minimal
up to an additive constant.

Proof idea: the usual universal construction `S(ẑ y, i) = S_z(y, i)`. -/
theorem exists_isOptimalBitwise : ∃ S : BitString × ℕ →. Bool, IsOptimalBitwise S := by
  obtain ⟨R, hR⟩ := exists_optimal_decisionDecompressor
  obtain ⟨S, hSc, hSle⟩ := exists_isOptimalBitwise_bitwise R
  refine ⟨S, hSc, fun S' hS' => ?_⟩
  obtain ⟨c, hc⟩ := hR (exists_isOptimalBitwise_machine hS')
  refine ⟨c, fun x => ?_⟩
  calc bitwiseKR S x ≤ KROf R x := hSle x
    _ ≤ KROf (exists_isOptimalBitwise_machine hS') x + c := hc x
    _ ≤ bitwiseKR S' x + c := add_le_add_left (exists_isOptimalBitwise_machine_le hS' x) _

private lemma exists_const_bitwiseKR_equiv_prefix_of_agree {z z' : BitString}
    (h : ∀ i (hi : i < z.length) (hi' : i < z'.length), z[i] = z'[i]) :
    z <+: z' ∨ z' <+: z := by
  rcases le_total z.length z'.length with hl | hl
  · left
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact h i (by simpa [hl] using hi) (lt_of_lt_of_le (by simpa [hl] using hi) hl)
  · right
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact (h i (lt_of_lt_of_le (by simpa [hl] using hi) hl) (by simpa [hl] using hi)).symm

private lemma exists_const_bitwiseKR_equiv_isRE {S : BitString × ℕ →. Bool} (hS : Partrec S) :
    IsRE (fun w : BitString × BitString => ∀ i (hi : i < w.2.length), w.2[i] ∈ S (w.1, i)) := by
  classical
  let h : (BitString × BitString) × (ℕ × Unit) →. Unit := fun q =>
    (S (q.1.1, q.2.1)).bind fun b =>
      (↑(if b = q.1.2.getD q.2.1 false then some () else none) : Part Unit)
  have hh : Partrec₂ (fun (a : BitString × BitString) (u : ℕ × Unit) =>
      h (a, u)) := by
    refine Partrec.bind (hS.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd))) ?_
    have : Partrec (fun q : (((BitString × BitString) × (ℕ × Unit)) × Bool) =>
        (↑(if q.2 = q.1.1.2.getD q.1.2.1 false then some () else none) : Part Unit)) := by
      refine Computable.ofOption ((Computable.cond
        ((Primrec.to_comp Primrec.beq).comp
          (Computable.pair Computable.snd
            (Computable.of_eq ((Primrec.list_getD false).to_comp.comp
              (Computable.snd.comp (Computable.fst.comp Computable.fst))
              (Computable.fst.comp (Computable.snd.comp Computable.fst))) fun _ => rfl)))
        (Computable.const (some ()))
        (Computable.const none)).of_eq (fun q => by simp [beq_iff_eq]))
    exact this.to₂
  have hF : Partrec (fun a : BitString × BitString =>
      (a.2.length).rec (Part.some ()) (fun y IH => IH.bind fun i => h (a, (y, i)))) :=
    Partrec.nat_rec (Primrec.list_length.comp Primrec.snd).to_comp
      (Partrec.const' (Part.some ())) hh
  refine ⟨_, hF, fun a => ?_⟩
  have hd : ∀ (k : ℕ) (u : Unit), (h (a, (k, u))).Dom ↔ a.2.getD k false ∈ S (a.1, k) := by
    intro k u
    simp only [h, Part.bind_dom]
    constructor
    · rintro ⟨hdom, hc⟩
      refine ⟨hdom, ?_⟩
      simpa [List.getD_eq_getElem?_getD] using hc
    · rintro ⟨hdom, heq⟩
      refine ⟨hdom, ?_⟩
      simp [heq]
  have key : ∀ n : ℕ, ((n.rec (Part.some ()) (fun y IH => IH.bind fun i => h (a, (y, i))) :
      Part Unit)).Dom ↔ ∀ i < n, a.2.getD i false ∈ S (a.1, i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (Part.bind _ _).Dom ↔ _
      rw [Part.bind_dom]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ih.1 h1 i hi
        · exact (hd _ _).1 h2
      · intro H
        exact ⟨ih.2 fun i hi => H i (by omega), (hd _ _).2 (H n (by omega))⟩
  refine (key a.2.length).trans ?_
  constructor
  · intro H i hi
    have := H i hi
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro H i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact H i hi

/-- The decision decompressor of a bitwise decompressor `S`: `M(y)` starts with `x` iff
`S(y, i) = xᵢ` for all `i < l(x)`. -/
private def exists_const_bitwiseKR_equiv_machine {S : BitString × ℕ →. Bool} (hS : Partrec S) :
    DecisionDecompressor where
  rel y x := ∀ i (hi : i < x.length), x[i] ∈ S (y, i)
  re := exists_const_bitwiseKR_equiv_isRE hS
  nil_mem := fun p i hi => by simp at hi
  prefix_closed := fun p x x' hx hx' i hi => by
    have h1 := hx i (lt_of_lt_of_le hi hx'.length_le)
    rwa [← hx'.getElem hi] at h1
  regular := fun p₁ x₁ p₂ x₂ h₁ h₂ hp => by
    change p₁ = p₂ at hp
    subst hp
    refine exists_const_bitwiseKR_equiv_prefix_of_agree fun i hi hi' => ?_
    exact Part.mem_unique (h₁ i hi) (h₂ i hi')

private lemma exists_const_bitwiseKR_equiv_machine_le {S : BitString × ℕ →. Bool}
    (hS : Partrec S) (x : BitString) :
    KROf (exists_const_bitwiseKR_equiv_machine hS) x ≤ bitwiseKR S x := by
  unfold KROf modeComplexity bitwiseKR
  exact le_of_eq rfl

/-- The bitwise decompressor `S'(y, i)`: search for an output `x'` of `R` on `y` with `i < l(x')`
and return `x'ᵢ`. -/
private lemma exists_const_bitwiseKR_equiv_bitwise (R : DecisionDecompressor) :
    ∃ S' : BitString × ℕ →. Bool, Partrec S' ∧ ∀ x, bitwiseKR S' x ≤ KROf R x := by
  obtain ⟨chk, hchk, -, hchk_iff⟩ := IsRE.exists_stageApprox R.re
  let cand : ℕ → BitString := fun t =>
    (Encodable.decode (α := BitString) (Nat.unpair t).2).getD []
  have hcand : Computable cand :=
    Computable.option_getD
      (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const [])
  let pred : BitString × ℕ → ℕ → Bool := fun a t =>
    chk (a.1, cand t) (Nat.unpair t).1 && decide (a.2 < (cand t).length)
  have hpred : Computable₂ pred := by
    have hA : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) =>
        chk (a.1, cand t) (Nat.unpair t).1) :=
      hchk.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (hcand.comp Computable.snd))
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp)
    have hB : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) => decide (a.2 < (cand t).length)) :=
      (PrimrecRel.decide Primrec.nat_lt).to_comp.comp (Computable.snd.comp Computable.fst)
        (Primrec.list_length.to_comp.comp (hcand.comp Computable.snd))
    exact Primrec.and.to_comp.comp hA hB
  have hout : Computable₂ (fun (a : BitString × ℕ) (t : ℕ) => (cand t).getD a.2 false) :=
    (Primrec.list_getD false).to_comp.comp (hcand.comp Computable.snd)
      (Computable.snd.comp Computable.fst)
  let P : BitString × ℕ → ℕ →. Bool := fun a t => Part.some (pred a t)
  let S' : BitString × ℕ →. Bool := fun a => (Nat.rfind (P a)).map fun t => (cand t).getD a.2 false
  have hS' : Partrec S' := Partrec.map (Partrec.rfind (Computable₂.partrec₂ hpred)) hout
  refine ⟨S', hS', fun x => ?_⟩
  unfold KROf modeComplexity bitwiseKR
  refine sInf_le_sInf fun l ⟨p, hp, hl⟩ => ⟨p, fun i hi => ?_, hl⟩
  have hdom : (Nat.rfind (P (p, i))).Dom := by
    rw [Nat.rfind_dom]
    obtain ⟨s, hs⟩ := (hchk_iff (p, x)).mp hp
    refine ⟨Nat.pair s (Encodable.encode x), ?_, fun {m} _ => trivial⟩
    refine Part.mem_some_iff.mpr ?_
    simp [pred, cand, hs, hi]
  have hmem := Part.get_mem hdom
  have hspec := Nat.rfind_spec hmem
  have ht : pred (p, i) ((Nat.rfind (P (p, i))).get hdom) = true :=
    (Part.mem_some_iff.mp hspec).symm
  simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hx0 : R.rel p (cand ((Nat.rfind (P (p, i))).get hdom)) := (hchk_iff _).mpr ⟨_, ht.1⟩
  refine Part.mem_map_iff _ |>.mpr ⟨_, hmem, ?_⟩
  have hc := R.regular hp hx0 rfl
  have hle : i < (cand ((Nat.rfind (P (p, i))).get hdom)).length := ht.2
  have : x[i] = (cand ((Nat.rfind (P (p, i))).get hdom))[i] := by
    rcases hc with h | h
    · exact h.getElem hi
    · exact (h.getElem hle).symm
  rw [List.getD_eq_getElem _ _ hle, this]

/-- **SUV Problem 194 (Section 6.1, printed p. 196), part 2.** The optimal bitwise complexity is
decision complexity: `bitwiseKR S = KR + O(1)`.

Proof idea: a decision machine `M` gives the bitwise decompressor `S(y, i) = (M(y))ᵢ`.
Conversely, a bitwise `S` gives the machine that on input `y` computes `S(y, 0), S(y, 1), …` in
order and prints them as they are found. -/
theorem exists_const_bitwiseKR_equiv {S : BitString × ℕ →. Bool} (hS : IsOptimalBitwise S)
    {R : DecisionDecompressor} (hR : R.IsOptimal) :
    ∃ c : ℕ, ∀ x, bitwiseKR S x ≤ KROf R x + c ∧ KROf R x ≤ bitwiseKR S x + c := by
  obtain ⟨S', hS'c, hS'le⟩ := exists_const_bitwiseKR_equiv_bitwise R
  obtain ⟨c₁, hc₁⟩ := hS.2 S' hS'c
  obtain ⟨c₂, hc₂⟩ := hR (exists_const_bitwiseKR_equiv_machine hS.1)
  refine ⟨max c₁ c₂, fun x => ⟨?_, ?_⟩⟩
  · calc bitwiseKR S x ≤ bitwiseKR S' x + c₁ := hc₁ x
      _ ≤ KROf R x + c₁ := add_le_add_left (hS'le x) _
      _ ≤ KROf R x + (max c₁ c₂ : ℕ) := by
        gcongr
        exact le_max_left _ _
  · calc KROf R x ≤ KROf (exists_const_bitwiseKR_equiv_machine hS.1) x + c₂ := hc₂ x
      _ ≤ bitwiseKR S x + c₂ :=
        add_le_add_left (exists_const_bitwiseKR_equiv_machine_le hS.1 x) _
      _ ≤ bitwiseKR S x + (max c₁ c₂ : ℕ) := by
        gcongr
        exact le_max_right _ _

/-- The bitwise decompressor `S(p, i)`: decode `U(p, [])` as a program `e` and return bit `i` of
its output (a bit is `true` when the value of `e` is `1`). -/
private noncomputable def exists_const_programKR_equiv_S (U : Map) : BitString × ℕ →. Bool :=
  fun a => (U (a.1, [])).bind fun y =>
    (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (decodeBits y)) a.2).map
      fun n => decide (n = 1)

private lemma exists_const_programKR_equiv_S_partrec {U : Map} (hU : isDecompressor U) :
    Partrec (exists_const_programKR_equiv_S U) := by
  unfold exists_const_programKR_equiv_S
  refine Partrec.bind (hU.comp (Computable.pair Computable.fst (Computable.const []))) ?_
  refine Partrec.map ?_ ?_
  · have h1 : Computable (fun q : (BitString × ℕ) × BitString =>
        Denumerable.ofNat Nat.Partrec.Code (decodeBits q.2)) :=
      (Primrec.ofNat Nat.Partrec.Code).to_comp.comp
        (decodeBits_computable.comp Computable.snd)
    exact Nat.Partrec.Code.eval_part.comp h1 (Computable.snd.comp Computable.fst)
  · exact (Primrec.to_comp ((PrimrecRel.decide Primrec.eq).comp Primrec.snd
      (Primrec.const 1))).to₂

private lemma exists_const_programKR_equiv_step_le {R : DecisionDecompressor} (hR : R.IsOptimal)
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ programKR U x + c := by
  have hS := exists_const_programKR_equiv_S_partrec hU.1
  obtain ⟨c, hc⟩ := hR (exists_const_bitwiseKR_equiv_machine hS)
  refine ⟨c, fun x => ?_⟩
  calc KROf R x ≤ KROf (exists_const_bitwiseKR_equiv_machine hS) x + c := hc x
    _ ≤ bitwiseKR (exists_const_programKR_equiv_S U) x + c :=
        add_le_add_left (exists_const_bitwiseKR_equiv_machine_le hS x) _
    _ ≤ programKR U x + c := by
        gcongr
        refine le_iInf₂ fun e he => ?_
        unfold plainK condK
        refine le_sInf ?_
        rintro n ⟨p, hp, rfl⟩
        refine sInf_le ⟨p, fun i hi => ?_, rfl⟩
        have h1 := he i hi
        unfold exists_const_programKR_equiv_S
        rw [Part.mem_bind_iff]
        refine ⟨Nat.bits e, hp, ?_⟩
        rw [decodeBits_natBits]
        refine Part.mem_map_iff _ |>.mpr ⟨_, h1, ?_⟩
        cases hb : x[i] <;> simp

private lemma exists_const_programKR_equiv_step_ge {R : DecisionDecompressor}
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, programKR U x ≤ KROf R x + c := by
  obtain ⟨S', hS', hle⟩ := exists_const_bitwiseKR_equiv_bitwise R
  let F : ℕ →. ℕ := fun n =>
    (S' ((Encodable.decode (α := BitString) (Nat.unpair n).1).getD [], (Nat.unpair n).2)).map
      Bool.toNat
  have hF : Partrec F := by
    refine Partrec.map (hS'.comp (Computable.pair
      (Computable.option_getD
        (Computable.decode.comp (Primrec.fst.comp Primrec.unpair).to_comp)
        (Computable.const []))
      (Primrec.snd.comp Primrec.unpair).to_comp)) ?_
    exact (Primrec.to_comp (Primrec.dom_finite Bool.toNat)).comp Computable.snd |>.to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hF)
  let f : BitString → ℕ := fun y =>
    Encodable.encode (Nat.Partrec.Code.curry c (Encodable.encode y))
  have hf : Computable f :=
    (Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c)
      Primrec.encode)).to_comp
  let V : Map := fun a => Part.some (Nat.bits (f a.1))
  have hV : isDecompressor V :=
    Computable.partrec (natBits_computable.comp (hf.comp Computable.fst))
  obtain ⟨c0, hc0⟩ := hU.2 V hV
  refine ⟨c0, fun x => ?_⟩
  by_cases htop : KROf R x = ⊤
  · rw [htop]; simp
  have hb : bitwiseKR S' x ≠ ⊤ := ne_top_of_le_ne_top htop (hle x)
  have hne : ({l : ℕ∞ | ∃ y, (∀ i (hi : i < x.length), x[i] ∈ S' (y, i)) ∧ l = y.length}).Nonempty
      := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hb
    unfold bitwiseKR
    rw [h]; exact sInf_empty
  obtain ⟨y, hy, hl⟩ := csInf_mem hne
  have hprints : PrintsPrefix (f y) x := by
    intro i hi
    change _ ∈ Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code
      (Encodable.encode (Nat.Partrec.Code.curry c (Encodable.encode y)))) i
    rw [Denumerable.ofNat_encode, Nat.Partrec.Code.eval_curry, hc]
    change _ ∈ (S' _).map Bool.toNat
    simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]
    exact Part.mem_map _ (hy i hi)
  calc programKR U x ≤ plainK U (Nat.bits (f y)) := iInf₂_le (f y) hprints
    _ ≤ condK V (Nat.bits (f y)) [] + c0 := hc0 _ _
    _ ≤ (y.length : ℕ∞) + c0 := by
        gcongr
        exact sInf_le ⟨y, Part.mem_some _, rfl⟩
    _ ≤ KROf R x + c0 := by
        gcongr
        refine le_trans (le_of_eq hl.symm) ?_
        exact (hle x)

/-- **SUV Problem 195 (Section 6.1, printed p. 197).** Up to `O(1)`, the decision complexity of
`x` is the least plain complexity `C(p)` of a program `p` that ignores its input and prints `x`
or an extension of `x`. Programs are `Nat.Partrec.Code`s printing bit `i` as their value at
`i` (`PrintsPrefix`).

Proof idea: `≤` — the decision machine that decompresses `p` with an optimal plain decompressor
and runs it is a decision decompressor. `≥` — the code of the machine `R` applied to a fixed
description `q` is computable from `q`, so its complexity is at most `l(q) + O(1)`. -/
theorem exists_const_programKR_equiv {R : DecisionDecompressor} (hR : R.IsOptimal) {U : Map}
    (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, KROf R x ≤ programKR U x + c ∧ programKR U x ≤ KROf R x + c := by
  obtain ⟨c₁, h₁⟩ := exists_const_programKR_equiv_step_le hR hU
  obtain ⟨c₂, h₂⟩ := exists_const_programKR_equiv_step_ge (R := R) hU
  refine ⟨max c₁ c₂, fun x => ⟨?_, ?_⟩⟩
  · exact (h₁ x).trans (add_le_add le_rfl (by exact_mod_cast le_max_left c₁ c₂))
  · exact (h₂ x).trans (add_le_add le_rfl (by exact_mod_cast le_max_right c₁ c₂))

/-- The lower graph of the monotone machine "decode a program `e` from a prefix `q` of the input
with the prefix machine `U`, then print the bits of `e`". -/
private def exists_const_KMOf_le_programKP_graph (U : Map) (p z : BitString) : Prop :=
  z = [] ∨ ∃ (q : BitString) (e : ℕ), q <+: p ∧ produces U q [] (Nat.bits e) ∧ PrintsPrefix e z

private lemma exists_const_KMOf_le_programKP_prefix_of_agree {z z' : BitString}
    (h : ∀ i (hi : i < z.length) (hi' : i < z'.length), z[i] = z'[i]) :
    z <+: z' ∨ z' <+: z := by
  rcases le_total z.length z'.length with hl | hl
  · left
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact h i (by simpa [hl] using hi) (lt_of_lt_of_le (by simpa [hl] using hi) hl)
  · right
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
    simp only [List.getElem_take]
    exact (h i (lt_of_lt_of_le (by simpa [hl] using hi) hl) (by simpa [hl] using hi)).symm

private lemma exists_const_KMOf_le_programKP_graph_isStreamLowerGraph {U : Map}
    (hU : IsPrefixMachine U) :
    IsStreamLowerGraph (exists_const_KMOf_le_programKP_graph U) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_⟩
  · rintro p z z' (rfl | ⟨q, e, hq, hprod, hz⟩) hz'
    · exact Or.inl (List.prefix_nil.1 hz')
    · exact Or.inr ⟨q, e, hq, hprod, fun i hi => by
        have h1 := hz i (lt_of_lt_of_le hi hz'.length_le)
        rwa [← hz'.getElem hi] at h1⟩
  · rintro p p' z (rfl | ⟨q, e, hq, hprod, hz⟩) hpp'
    · exact Or.inl rfl
    · exact Or.inr ⟨q, e, hq.trans hpp', hprod, hz⟩
  · rintro p z z' (rfl | ⟨q, e, hq, hprod, hz⟩) hz'
    · exact Or.inl List.nil_prefix
    · rcases hz' with rfl | ⟨q', e', hq', hprod', hz'⟩
      · exact Or.inr List.nil_prefix
      · have hqq' : q = q' := by
          rcases isPrefix_or_isPrefix_of_isPrefix hq hq' with h | h
          · exact hU.eq_of_prefix hprod hprod' h
          · exact (hU.eq_of_prefix hprod' hprod h).symm
        subst hqq'
        have hbits : Nat.bits e = Nat.bits e' := Part.mem_unique hprod hprod'
        have hee : e = e' := natBits_injective hbits
        subst hee
        refine exists_const_KMOf_le_programKP_prefix_of_agree fun i hi hi' => ?_
        have h1 := hz i hi
        have h2 := hz' i hi'
        have := Part.mem_unique h1 h2
        cases hb : z[i] <;> cases hb' : z'[i] <;> simp_all

/-- Stage-`s` check that the program `e` prints `z`. -/
private def exists_const_KMOf_le_programKP_chk (w : ℕ × BitString) (s : ℕ) : Bool :=
  decide ((List.range w.2.length).map
      (fun i => Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code w.1) i) =
    w.2.map (fun b => some b.toNat))

private lemma exists_const_KMOf_le_programKP_chk_primrec :
    Primrec₂ exists_const_KMOf_le_programKP_chk := by
  unfold exists_const_KMOf_le_programKP_chk
  have hcode : Primrec (fun a : (ℕ × BitString) × ℕ => Denumerable.ofNat Nat.Partrec.Code a.1.1) :=
    (Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.fst)
  have hev : Primrec₂ (fun (a : (ℕ × BitString) × ℕ) (i : ℕ) =>
      Nat.Partrec.Code.evaln a.2 (Denumerable.ofNat Nat.Partrec.Code a.1.1) i) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (hcode.comp Primrec.fst)) Primrec.snd)
  have hL : Primrec (fun a : (ℕ × BitString) × ℕ =>
      (List.range a.1.2.length).map
        (fun i => Nat.Partrec.Code.evaln a.2 (Denumerable.ofNat Nat.Partrec.Code a.1.1) i)) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp
      (Primrec.snd.comp Primrec.fst))) hev
  have hR : Primrec (fun a : (ℕ × BitString) × ℕ =>
      a.1.2.map (fun b => some b.toNat)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp ((Primrec.dom_finite Bool.toNat).comp Primrec.snd)).to₂
  exact (PrimrecRel.decide Primrec.eq).comp hL hR

private lemma exists_const_KMOf_le_programKP_exists_stage (n : ℕ) (P : ℕ → ℕ → Prop)
    (hmono : ∀ i k k', k ≤ k' → P i k → P i k') (h : ∀ i < n, ∃ k, P i k) :
    ∃ k, ∀ i < n, P i k := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨k', hk'⟩ := h n (by omega)
    refine ⟨max k k', fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hmono _ _ _ (le_max_left _ _) (hk i hi)
    · exact hmono _ _ _ (le_max_right _ _) hk'

private lemma exists_const_KMOf_le_programKP_chk_iff (e : ℕ) (z : BitString) :
    PrintsPrefix e z ↔ ∃ s, exists_const_KMOf_le_programKP_chk (e, z) s = true := by
  unfold PrintsPrefix exists_const_KMOf_le_programKP_chk
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_const_KMOf_le_programKP_exists_stage z.length
      (fun i k => Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code e) i =
        some (z.getD i false).toNat)
      (fun i k k' hk hP => Option.mem_def.mp
        (Nat.Partrec.Code.evaln_mono hk (Option.mem_def.mpr hP)))
      (fun i hi => by
        obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp (h i hi)
        exact ⟨k, by rw [List.getD_eq_getElem _ _ hi]; exact Option.mem_def.mp hk⟩)
    refine ⟨s, List.ext_getElem (by simp) fun i h1 h2 => ?_⟩
    have hi : i < z.length := by simpa using h1
    have := hs i hi
    rw [List.getD_eq_getElem _ _ hi] at this
    simpa using this
  · rintro ⟨s, hs⟩ i hi
    have := congrArg (fun l => l[i]?) hs
    simp only [List.getElem?_map, List.getElem?_range hi, hi, List.getElem?_eq_getElem,
      Option.map_some] at this
    exact Nat.Partrec.Code.evaln_sound (k := s) (Option.mem_def.mpr (Option.some.inj this))

private lemma exists_const_KMOf_le_programKP_graph_isRE {U : Map} (hU : isDecompressor U) :
    IsRE (fun w : BitString × BitString => exists_const_KMOf_le_programKP_graph U w.1 w.2) := by
  -- the witness is `b = (q, e)`
  have hgr : IsRE (fun v : (BitString × BitString) × (BitString × ℕ) =>
      produces U v.2.1 [] (Nat.bits v.2.2)) := by
    refine (Partrec.graphIsRe U hU).comp_computable
      (g := fun v : (BitString × BitString) × (BitString × ℕ) =>
        ((v.2.1, ([] : BitString)), Nat.bits v.2.2)) ?_
    exact Computable.pair
      (Computable.pair (Computable.fst.comp Computable.snd) (Computable.const []))
      (natBits_computable.comp (Computable.snd.comp Computable.snd))
  have hpr : IsRE (fun v : (BitString × BitString) × (BitString × ℕ) =>
      PrintsPrefix v.2.2 v.1.2) := by
    have hc : Computable (fun x : ((BitString × BitString) × (BitString × ℕ)) × ℕ =>
        exists_const_KMOf_le_programKP_chk (x.1.2.2, x.1.1.2) x.2) :=
      (exists_const_KMOf_le_programKP_chk_primrec.comp
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to_comp
    have hre := IsRE.exists_encodable
      (R := fun (v : (BitString × BitString) × (BitString × ℕ)) (s : ℕ) =>
        exists_const_KMOf_le_programKP_chk (v.2.2, v.1.2) s = true)
      (isRE_of_computable_bool _ _ (fun _ => Iff.rfl) hc)
    exact IsRE.of_iff hre (fun v => (exists_const_KMOf_le_programKP_chk_iff v.2.2 v.1.2).symm)
  have hpre : Computable (fun v : (BitString × BitString) × (BitString × ℕ) =>
      decide (v.2.1 = v.1.1.take v.2.1.length)) :=
    Primrec.to_comp ((PrimrecRel.decide Primrec.eq).comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst)))
  have hall := IsRE.and_computable (hgr.and hpr) hpre
  have hex := IsRE.exists_encodable
    (R := fun (a : BitString × BitString) (b : BitString × ℕ) =>
      decide (b.1 = a.1.take b.1.length) = true ∧
        (produces U b.1 [] (Nat.bits b.2) ∧ PrintsPrefix b.2 a.2)) hall
  refine IsRE.of_iff (IsRE.or isRE_nil hex) (fun w => ?_)
  unfold exists_const_KMOf_le_programKP_graph
  simp only [decide_eq_true_eq, ← List.prefix_iff_eq_take, Prod.exists]

/-- **SUV Problem 196 (Section 6.1, printed p. 197), part 1.** Replacing `C` by `K` in
Problem 195 gives an upper bound for monotone complexity: `KM(x) ≤ min K(p) + O(1)` over
programs `p` printing `x` or an extension.

Proof idea: a monotone machine reads a self-delimiting description of `p` (prefix-free
decompressor) and then runs `p`. -/
theorem exists_const_KMOf_le_programKP {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, KMOf D x ≤ programKP U x + c := by
  have hlow := exists_const_KMOf_le_programKP_graph_isStreamLowerGraph hU.isPrefixMachine
  set D' := streamMapOfLowerGraph _ hlow with hD'
  have hD'c : IsComputableStreamMap D' :=
    ⟨streamMapOfLowerGraph_isContinuousStreamMap _,
      IsRE.of_iff (exists_const_KMOf_le_programKP_graph_isRE hU.isDecompressor)
        (fun w => (streamMapOfLowerGraph_finite_spec hlow w.1 w.2).symm)⟩
  have hle : ∀ x, KMOf D' x ≤ programKP U x := by
    intro x
    refine le_iInf₂ fun e he => ?_
    by_cases htop : KPPlain U (Nat.bits e) = ⊤
    · rw [htop]; exact le_top
    obtain ⟨q, hq, hlen⟩ := exists_program_of_KP_ne_top (M := U) (x := Nat.bits e) (y := []) htop
    have hprod : monotoneProduces D' q x :=
      (streamMapOfLowerGraph_finite_spec hlow q x).mpr (Or.inr ⟨q, e, List.prefix_rfl, hq, he⟩)
    exact (KMOf_le_length_of_monotoneProduces hprod).trans (le_of_eq hlen)
  obtain ⟨c, hc⟩ := hD.2 D' hD'c
  exact ⟨c, fun x => (hc x).trans (add_le_add_left (hle x) _)⟩

/-- Two prefixes of the same length printed by one program coincide. -/
private lemma not_exists_const_programKP_le_KMOf_aux_unique {e : ℕ} {x x' : BitString}
    (h : PrintsPrefix e x) (h' : PrintsPrefix e x') (hl : x.length = x'.length) : x = x' := by
  refine List.ext_getElem hl fun i hi hi' => ?_
  have h1 := Part.mem_unique (h i hi) (h' i hi')
  generalize x[i] = a at h1
  generalize x'[i] = b at h1
  cases a <;> cases b <;> simp_all

/-- The pure counting argument: a Kraft-bounded weight cannot give weight `M 2⁻ᵏ` to `2ᵏ`
elements for every `k`, even if the sets overlap (first-appearance counting). -/
private lemma not_exists_const_programKP_le_KMOf_aux_core (w : ℕ → ℝ)
    (hw : ∀ T : Finset ℕ, ∑ e ∈ T, w e ≤ 1) (M : ℝ) (hM : 0 < M) (E : ℕ → Finset ℕ)
    (hE : ∀ k, 2 ^ k ≤ (E k).card) (hwE : ∀ k, ∀ e ∈ E k, M * (1 / 2) ^ k ≤ w e) : False := by
  classical
  let F : ℕ → Finset ℕ := fun N => (Finset.range (N + 1)).biUnion E
  have hFsucc : ∀ N, F (N + 1) = F N ∪ E (N + 1) := by
    intro N
    simp only [F]
    rw [Finset.range_add_one (n := N + 1), Finset.biUnion_insert, Finset.union_comm]
  have hFsub : ∀ N, F N ⊆ F (N + 1) := fun N => by rw [hFsucc]; exact Finset.subset_union_left
  have hEF : ∀ k, E k ⊆ F k := fun k =>
    Finset.subset_biUnion_of_mem E (Finset.mem_range.2 (Nat.lt_succ_self k))
  have hcard : ∀ k, (2 : ℝ) ^ k ≤ ((F k).card : ℝ) := fun k => by
    exact_mod_cast (hE k).trans (Finset.card_le_card (hEF k))
  have key : ∀ N, M * (((F N).card : ℝ) * (1 / 2) ^ N +
      ∑ k ∈ Finset.range N, ((F k).card : ℝ) * (1 / 2) ^ (k + 1)) ≤ ∑ e ∈ F N, w e := by
    intro N
    induction N with
    | zero =>
      have hF0 : F 0 = E 0 := by simp [F]
      rw [hF0]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, mul_one]
      calc M * ((E 0).card : ℝ) = ∑ _e ∈ E 0, M := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun e he => by simpa using hwE 0 e he
    | succ N ih =>
      have hsd := Finset.sum_sdiff (f := w) (hFsub N)
      have hcs := Finset.card_sdiff_add_card_eq_card (hFsub N)
      have hbound : ((F (N + 1) \ F N).card : ℝ) * (M * (1 / 2) ^ (N + 1)) ≤
          ∑ e ∈ F (N + 1) \ F N, w e := by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun e he => hwE (N + 1) e ?_
        rw [Finset.mem_sdiff, hFsucc, Finset.mem_union] at he
        tauto
      have hc' : ((F (N + 1)).card : ℝ) = ((F (N + 1) \ F N).card : ℝ) + (F N).card := by
        exact_mod_cast hcs.symm
      have hq : (1 / 2 : ℝ) ^ N = 2 * (1 / 2) ^ (N + 1) := by rw [pow_succ]; ring
      rw [Finset.sum_range_succ]
      rw [hq] at ih
      rw [hc']
      nlinarith [ih, hbound, hsd]
  have hN := fun N => (key N).trans (hw (F N))
  obtain ⟨N, hN'⟩ := exists_nat_gt (2 / M)
  have h1 : (1 : ℝ) ≤ ((F N).card : ℝ) * (1 / 2) ^ N := by
    calc (1 : ℝ) = 2 ^ N * (1 / 2) ^ N := by rw [← mul_pow]; norm_num
      _ ≤ _ := by gcongr; exact hcard N
  have h2 : (N : ℝ) / 2 ≤ ∑ k ∈ Finset.range N, ((F k).card : ℝ) * (1 / 2) ^ (k + 1) := by
    calc (N : ℝ) / 2 = ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum fun k _ => by
        calc (1 / 2 : ℝ) = 2 ^ k * (1 / 2) ^ (k + 1) := by
              rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
          _ ≤ _ := by gcongr; exact hcard k
  have h3 := hN N
  have h4 : M * (1 + N / 2) ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hM.le) h3
    linarith
  rw [div_lt_iff₀ hM] at hN'
  nlinarith

/-- **SUV Problem 196 (Section 6.1, printed p. 197), part 2.** The bound of part 1 is not
`O(1)`-tight.

Proof idea (book's hint): all `n`-bit strings have `KM ≤ n + O(1)`. Their programs (printing
them or extensions) are pairwise different, and there are not enough strings with prefix
complexity `n + O(1)`, since `∑ 2 ^ (-K) ≤ 1`. One length alone gives no contradiction (Kraft
allows `2 ^ (n + c)` such programs), so combine all lengths. Let `aₙ` count the chosen programs
that first appear at length `n`. Then `∑_{n ≤ N} aₙ ≥ 2 ^ N` for every `N`, and
`K(e) ≤ n + O(1)` for these programs, so `∑ₙ aₙ 2 ^ (-n)` would be finite. These two facts
contradict each other. -/
theorem not_exists_const_programKP_le_KMOf {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) {U : Map} (hU : IsOptimalPrefixConditional U) :
    ¬ ∃ c : ℕ, ∀ x, programKP U x ≤ KMOf D x + c := by
  rintro ⟨c, hc⟩
  obtain ⟨c', hc'⟩ := exists_const_KMOf_le_length hD
  have hex : ∀ x : BitString, ∃ e, PrintsPrefix e x ∧
      KPPlain U (Nat.bits e) ≤ ((x.length + (c + c') : ℕ) : ℕ∞) := by
    intro x
    have h1 : programKP U x < ((x.length + (c + c') + 1 : ℕ) : ℕ∞) := by
      calc programKP U x ≤ KMOf D x + c := hc x
        _ ≤ (x.length : ℕ∞) + c' + c := add_le_add (hc' x) le_rfl
        _ = ((x.length + (c + c') : ℕ) : ℕ∞) := by push_cast; ring
        _ < _ := by exact_mod_cast Nat.lt_succ_self _
    simp only [programKP, iInf_lt_iff] at h1
    obtain ⟨e, he, hlt⟩ := h1
    exact ⟨e, he, ENat.lt_natCast_add_one_iff.1 (by exact_mod_cast hlt)⟩
  choose p hp1 hp2 using hex
  let E : ℕ → Finset ℕ := fun k => Finset.univ.image (fun v : Fin k → Bool => p (List.ofFn v))
  have hinj : ∀ k, Function.Injective (fun v : Fin k → Bool => p (List.ofFn v)) := by
    intro k v v' h
    have h' : PrintsPrefix (p (List.ofFn v)) (List.ofFn v') := by
      simp only at h
      rw [h]; exact hp1 _
    exact List.ofFn_injective
      (not_exists_const_programKP_le_KMOf_aux_unique (hp1 _) h' (by simp))
  have hbits : Function.Injective Nat.bits := fun a b h => by
    rw [← bitsToNat_bits a, h, bitsToNat_bits]
  refine not_exists_const_programKP_le_KMOf_aux_core
    (fun e => (complexityWeight (KPPlain U (Nat.bits e))).toReal) ?_ ((1 / 2) ^ (c + c'))
    (by positivity) E ?_ ?_
  · intro T
    have hsum : ∑ e ∈ T, complexityWeight (KPPlain U (Nat.bits e)) ≤ 1 := by
      calc ∑ e ∈ T, complexityWeight (KPPlain U (Nat.bits e))
          = ∑ x ∈ T.image Nat.bits, complexityWeight (KPPlain U x) :=
            (Finset.sum_image (f := fun x => complexityWeight (KPPlain U x))
              (fun a _ b _ h => hbits h)).symm
        _ ≤ ∑' x, complexityWeight (KPPlain U x) := ENNReal.sum_le_tsum _
        _ ≤ 1 := KPPlain_kraft_sum_le_one U hU.isPrefixDecompressor
    have := ENNReal.toReal_mono ENNReal.one_ne_top hsum
    rwa [ENNReal.toReal_sum fun e _ => complexityWeight_ne_top _, ENNReal.toReal_one] at this
  · intro k
    simp only [E]
    rw [Finset.card_image_of_injective _ (hinj k)]
    simp
  · intro k e he
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 he
    have hle := hp2 (List.ofFn v)
    rw [List.length_ofFn] at hle
    have := ENNReal.toReal_mono (complexityWeight_ne_top _) (complexityWeight_le_of_le hle)
    rw [complexityWeight_coe] at this
    refine le_trans (le_of_eq ?_) this
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp [pow_add, mul_comm]

end GeneralScheme

end Kolmogorov
