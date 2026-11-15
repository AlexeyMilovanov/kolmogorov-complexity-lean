import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs.MonotoneDecompressors

/-!
# Maximal Semimeasure

For an oracle `A`, there is a maximal `A`-lower-semicomputable continuous semimeasure on binary
strings: one that multiplicatively dominates every other such semimeasure.  The construction
lists all `A`-enumerable sets of pairs `(x, q)` with the universal oracle machine, trims each row
to a continuous tree semimeasure, and sums the rows with dyadic weights `2 ^ (-i - 1)`.

The main declaration is `exists_isMaximalContinuousSemimeasureIn`, the relativized form of
Theorem 78 of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and algorithmic
randomness" (Section 6.4.1).
-/

open scoped ENNReal
namespace Kolmogorov
namespace GeneralScheme
open Nat.Partrec (Code)

/-- Step 1 of the proof of `exists_isMaximalContinuousSemimeasureIn_enumeration`:
there is a uniformly `A`-enumerable family `W i` of sets of pairs `(x, q)` (the universal oracle
machine `PointToSet.oracleEval A`, applied to the code of the pair) containing every
`A`-enumerable set of pairs: the set of triples `(i, x, q)` with `W i x q` is `A`-enumerable, and
every `A`-enumerable relation `R` equals some row `W i`. -/
private theorem exists_isMaximalContinuousSemimeasureIn_universal
    (A : Set ℕ) :
    ∃ W : ℕ → BitString → ℚ → Prop,
      PointToSet.IsREIn A (fun p : ℕ × (BitString × ℚ) => W p.1 p.2.1 p.2.2) ∧
      ∀ R : BitString → ℚ → Prop,
        PointToSet.IsREIn A (fun p : BitString × ℚ => R p.1 p.2) →
          ∃ i, ∀ x q, W i x q ↔ R x q := by
  let enc : BitString × ℚ → ℕ := fun y => @Encodable.encode _ Primcodable.toEncodable y
  refine ⟨fun i x q => (PointToSet.oracleEval A i (enc (x, q))).Dom, ?_, ?_⟩
  · refine ⟨fun p : ℕ × (BitString × ℚ) =>
      PointToSet.oracleEval A p.1 (enc p.2), ?_, fun _ => Iff.rfl⟩
    have hargs : Computable (fun p : ℕ × (BitString × ℚ) =>
        (p.1, enc p.2)) :=
      Computable.fst.pair (Computable.encode.comp Computable.snd)
    exact PartrecIn.comp (g := fun p : ℕ × (BitString × ℚ) => (p.1, enc p.2))
      (PointToSet.oracleStage_evaluator A) hargs.computableIn
  · intro R ⟨f, hf, hfdom⟩
    have hd : Computable (fun n => @Encodable.decode (BitString × ℚ) Primcodable.toEncodable n) :=
      Computable.decode
    have hopt := (Computable.ofOption hd).partrecIn (O := {charOracle A})
    have hmap : PartrecIn₂ {charOracle A}
        (fun (_ : ℕ) (a : BitString × ℚ) => f a) :=
      hf.comp ComputableIn.snd
    have hg := PartrecIn.bind hopt hmap
    obtain ⟨e, he⟩ := PointToSet.oracleStage_universal A _ hg
    refine ⟨e, fun x y => ?_⟩
    refine Iff.trans ?_ (hfdom (x, y)).symm
    change (PointToSet.oracleEval A e (enc (x, y))).Dom ↔ _
    change (Nat.rfindOpt fun t => PointToSet.oracleStage A t e _).Dom ↔ _
    rw [Nat.rfindOpt_dom]
    constructor
    · rintro ⟨t, v, hv⟩
      have := (he (enc (x, y)) v).mpr ⟨t, Option.mem_def.mp hv⟩
      simp only [Part.ofOption, enc, Encodable.encodek, Part.bind_some] at this
      exact Part.dom_iff_mem.mpr ⟨v, this⟩
    · intro h
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
      obtain ⟨t, ht⟩ := (he (enc (x, y)) v).mp (by
        simp only [Part.ofOption, enc, Encodable.encodek, Part.bind_some]; exact hv)
      exact ⟨t, v, Option.mem_def.mpr ht⟩

/-- Step 2 of the proof of `exists_isMaximalContinuousSemimeasureIn_enumeration`:
stage approximations of a uniformly `A`-enumerable family `W i` of sets of pairs `(x, q)`. There is
an `A`-computable rational function `c i s x` (the largest `q ≥ 0` with `(x, q)` enumerated into
`W i` within `s` steps, `0` if there is none) which is nonnegative, nondecreasing in the stage
`s`, takes only the value `0` or values `q` with `W i x q`, and eventually reaches every `q ≥ 0`
with `W i x q` (`q ≤ c i s x` for some `s`). -/
private theorem exists_isMaximalContinuousSemimeasureIn_stages
    (A : Set ℕ) (W : ℕ → BitString → ℚ → Prop)
    (hW : PointToSet.IsREIn A (fun p : ℕ × (BitString × ℚ) => W p.1 p.2.1 p.2.2)) :
    ∃ c : ℕ → ℕ → BitString → ℚ,
      ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => c p.1 p.2.1 p.2.2) ∧
      (∀ i s x, 0 ≤ c i s x) ∧ (∀ i s x, c i s x ≤ c i (s + 1) x) ∧
      (∀ i s x, c i s x = 0 ∨ W i x (c i s x)) ∧
      ∀ i x q, W i x q → 0 ≤ q → ∃ s, q ≤ c i s x := by
  obtain ⟨e, he, hrange⟩ := (PointToSet.relative_enumeration A _).mp hW
  let cand : Option (ℕ × (BitString × ℚ)) × ℕ × BitString → ℚ := fun p =>
    match p.1 with
    | none => 0
    | some (j, (y, q)) => if j = p.2.1 then if y = p.2.2 then if q < 0 then 0 else q else 0 else 0
  have hcand : Computable cand := by
    have hj : Computable (fun x : (Option (ℕ × (BitString × ℚ)) × ℕ × BitString) ×
        (ℕ × (BitString × ℚ)) => decide (x.2.1 = x.1.2.1)) :=
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to_comp
    have hy : Computable (fun x : (Option (ℕ × (BitString × ℚ)) × ℕ × BitString) ×
        (ℕ × (BitString × ℚ)) => decide (x.2.2.1 = x.1.2.2)) :=
      (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to_comp
    have hq : Computable (fun x : (Option (ℕ × (BitString × ℚ)) × ℕ × BitString) ×
        (ℕ × (BitString × ℚ)) => x.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    have hl : Computable (fun x : (Option (ℕ × (BitString × ℚ)) × ℕ × BitString) ×
        (ℕ × (BitString × ℚ)) => decide (x.2.2.2 < 0)) :=
      computable₂_ratLt.comp hq (Computable.const (0 : ℚ))
    have hg : Computable₂ (fun (p : Option (ℕ × (BitString × ℚ)) × ℕ × BitString)
        (w : ℕ × (BitString × ℚ)) =>
        if w.1 = p.2.1 then if w.2.1 = p.2.2 then if w.2.2 < 0 then 0 else w.2.2 else 0
        else (0 : ℚ)) := by
      refine (Computable.cond hj (Computable.cond hy (Computable.cond hl
        (Computable.const (0 : ℚ)) hq) (Computable.const (0 : ℚ)))
        (Computable.const (0 : ℚ))).of_eq ?_
      intro x
      simp
    refine (Computable.option_casesOn Computable.fst (Computable.const (0 : ℚ)) hg).of_eq ?_
    intro p
    rcases p with ⟨o, i, x⟩
    cases o <;> simp [cand]
  let c : ℕ → ℕ → BitString → ℚ := fun i s x =>
    @Nat.rec (fun _ => ℚ) 0 (fun n ih => max ih (cand (e n, i, x))) s
  have hcs : ∀ i s x, c i (s + 1) x = max (c i s x) (cand (e s, i, x)) := fun _ _ _ => rfl
  have hc0 : ∀ i x, c i 0 x = 0 := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · refine ComputableIn.nat_rec (f := fun p : ℕ × ℕ × BitString => p.2.1)
      (g := fun _ => (0 : ℚ))
      (h := fun (p : ℕ × ℕ × BitString) (nih : ℕ × ℚ) =>
        max nih.2 (cand (e nih.1, p.1, p.2.2))) ?_ ?_ ?_
    · exact ComputableIn.fst.comp ComputableIn.snd
    · exact (Computable.const (0 : ℚ)).computableIn
    · refine ComputableIn₂.mk ?_
      have h1 : ComputableIn {charOracle A}
          (fun x : (ℕ × ℕ × BitString) × (ℕ × ℚ) => x.2.2) :=
        ComputableIn.snd.comp ComputableIn.snd
      have h2 : ComputableIn {charOracle A}
          (fun x : (ℕ × ℕ × BitString) × (ℕ × ℚ) =>
            ((e x.2.1, x.1.1, x.1.2.2) : Option (ℕ × (BitString × ℚ)) × ℕ × BitString)) :=
        ComputableIn.pair (he.comp (ComputableIn.fst.comp ComputableIn.snd))
          (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst)
            (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst)))
      have h3 : ComputableIn {charOracle A}
          (fun x : (ℕ × ℕ × BitString) × (ℕ × ℚ) => cand (e x.2.1, x.1.1, x.1.2.2)) :=
        hcand.computableIn.comp h2
      exact ComputableIn₂.comp (f := fun a b : ℚ => max a b)
        computable₂_ratMax.computableIn₂ h1 h3
  · intro i s x
    induction s with
    | zero => rw [hc0]
    | succ s ih => rw [hcs]; exact le_max_of_le_left ih
  · intro i s x
    rw [hcs]; exact le_max_left _ _
  · have hcandW : ∀ s i x, cand (e s, i, x) = 0 ∨ W i x (cand (e s, i, x)) := by
      intro s i x
      cases h : e s with
      | none => left; simp [cand]
      | some w =>
        obtain ⟨j, y, q⟩ := w
        by_cases h1 : j = i
        · by_cases h2 : y = x
          · by_cases h3 : q < 0
            · left; simp [cand, h1, h2, h3]
            · right
              have : cand (some (j, y, q), i, x) = q := by simp [cand, h1, h2, h3]
              rw [this]
              subst h1; subst h2
              exact (hrange (j, (y, q))).mpr ⟨s, h⟩
          · left; simp [cand, h1, h2]
        · left; simp [cand, h1]
    intro i s x
    induction s with
    | zero => left; rw [hc0]
    | succ s ih =>
      rw [hcs]
      rcases max_choice (c i s x) (cand (e s, i, x)) with h | h
      · rw [h]; exact ih
      · rw [h]; exact hcandW s i x
  · intro i x q hq hq0
    obtain ⟨n, hn⟩ := (hrange (i, (x, q))).mp hq
    refine ⟨n + 1, ?_⟩
    rw [hcs]
    have : cand (e n, i, x) = q := by simp [cand, hn, not_lt.mpr hq0]
    rw [← this]
    exact le_max_right _ _

/-- Auxiliary for the upward closure: the stage-`s` closure value of `x` with `m` levels of
recursion left, `cl 0 x = c i s x`, `cl (m+1) x = max (c i s x) (cl m (x0) + cl m (x1))`. -/
private noncomputable def
    exists_isMaximalContinuousSemimeasureIn_closure_cl
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) : ℕ → BitString → ℚ
  | 0, x => c i s x
  | m + 1, x => max (c i s x)
      (exists_isMaximalContinuousSemimeasureIn_closure_cl
          c i s m (x ++ [false]) +
        exists_isMaximalContinuousSemimeasureIn_closure_cl
          c i s m (x ++ [true]))

/-- Auxiliary for the upward closure: the stage-`s` upward closure,
`u_s x = cl (s - |x|) x` on strings of length `≤ s` and `0` beyond. -/
private noncomputable def
    exists_isMaximalContinuousSemimeasureIn_closure_clo
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) (x : BitString) : ℚ :=
  if x.length ≤ s then
    exists_isMaximalContinuousSemimeasureIn_closure_cl
      c i s (s - x.length) x
  else 0

private lemma exists_isMaximalContinuousSemimeasureIn_closure_cl_ge
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) :
    ∀ m x, c i s x ≤
      exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i s m x := by
  intro m x
  cases m with
  | zero => exact le_rfl
  | succ m => exact le_max_left _ _

private lemma exists_isMaximalContinuousSemimeasureIn_closure_cl_nonneg
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i s : ℕ) (m : ℕ) (x : BitString) :
    0 ≤ exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i s m x :=
  (hc0 i s x).trans
    (exists_isMaximalContinuousSemimeasureIn_closure_cl_ge
      c i s m x)

private lemma exists_isMaximalContinuousSemimeasureIn_closure_clo_nonneg
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i s : ℕ) (x : BitString) :
    0 ≤ exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s x := by
  unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
  split_ifs
  · exact exists_isMaximalContinuousSemimeasureIn_closure_cl_nonneg
      c hc0 i s _ x
  · exact le_rfl

private lemma exists_isMaximalContinuousSemimeasureIn_closure_cl_mono
    (c : ℕ → ℕ → BitString → ℚ) (hcm : ∀ i s x, c i s x ≤ c i (s + 1) x) (i s : ℕ) :
    ∀ m x,
      exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i s m x ≤
      exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i (s + 1) (m + 1) x := by
  intro m
  induction m with
  | zero =>
    intro x
    exact (hcm i s x).trans (le_max_left _ _)
  | succ m ih =>
    intro x
    change max (c i s x) (_ + _) ≤ max (c i (s + 1) x) (_ + _)
    exact max_le_max (hcm i s x) (add_le_add (ih _) (ih _))

private lemma exists_isMaximalContinuousSemimeasureIn_closure_clo_mono
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x)
    (hcm : ∀ i s x, c i s x ≤ c i (s + 1) x) (i s : ℕ) (x : BitString) :
    exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s x ≤
      exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i (s + 1) x := by
  unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
  by_cases h : x.length ≤ s
  · have h' : x.length ≤ s + 1 := by omega
    rw [ite_eq_left h, ite_eq_left h']
    have : s + 1 - x.length = (s - x.length) + 1 := by omega
    rw [this]
    exact exists_isMaximalContinuousSemimeasureIn_closure_cl_mono
      c hcm i s _ x
  · rw [ite_eq_right h]
    split_ifs
    · exact exists_isMaximalContinuousSemimeasureIn_closure_cl_nonneg
        c hc0 i _ _ x
    · exact le_rfl

private lemma exists_isMaximalContinuousSemimeasureIn_closure_clo_super
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i s : ℕ) (x : BitString) :
    exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s (x ++ [false]) +
      exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s (x ++ [true]) ≤
    exists_isMaximalContinuousSemimeasureIn_closure_clo
      c i s x := by
  by_cases h : x.length < s
  · have h1 : (x ++ [false]).length ≤ s := by simp; omega
    have h2 : (x ++ [true]).length ≤ s := by simp; omega
    have h3 : x.length ≤ s := h.le
    unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3]
    obtain ⟨m, hm⟩ : ∃ m, s - x.length = m + 1 := ⟨s - x.length - 1, by omega⟩
    have e1 : s - (x ++ [false]).length = m := by simp; omega
    have e2 : s - (x ++ [true]).length = m := by simp; omega
    rw [e1, e2, hm]
    exact le_max_right _ _
  · have h1 : ¬ (x ++ [false]).length ≤ s := by simp; omega
    have h2 : ¬ (x ++ [true]).length ≤ s := by simp; omega
    have := exists_isMaximalContinuousSemimeasureIn_closure_clo_nonneg
      c hc0 i s x
    unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
      at this ⊢
    rw [ite_eq_right h1, ite_eq_right h2]
    simpa using this

private lemma exists_isMaximalContinuousSemimeasureIn_closure_clo_low
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) (x : BitString) (h : x.length ≤ s) :
    c i s x ≤
      exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s x := by
  unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
  rw [ite_eq_left h]
  exact exists_isMaximalContinuousSemimeasureIn_closure_cl_ge
    c i s _ x

private lemma exists_isMaximalContinuousSemimeasureIn_closure_clo_le
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i : ℕ) (a : BitString → ℝ)
    (ha : ∀ x, a (x ++ [false]) + a (x ++ [true]) ≤ a x)
    (hca : ∀ s x, (c i s x : ℝ) ≤ a x) (s : ℕ) (x : BitString) :
    (exists_isMaximalContinuousSemimeasureIn_closure_clo
        c i s x : ℝ) ≤ a x := by
  have key : ∀ m x,
      ((exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i s m x : ℚ) : ℝ) ≤ a x := by
    intro m
    induction m with
    | zero => intro x; exact hca s x
    | succ m ih =>
      intro x
      change ((max (c i s x) (_ + _) : ℚ) : ℝ) ≤ a x
      rw [Rat.cast_max, max_le_iff]
      refine ⟨hca s x, ?_⟩
      push_cast
      exact (add_le_add (ih _) (ih _)).trans (ha x)
  unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
  split_ifs
  · exact key _ x
  · have : (0:ℝ) ≤ c i s x := by exact_mod_cast hc0 i s x
    simpa using this.trans (hca s x)

/-- Auxiliary: one step of the bit-extraction automaton (peel the lowest bit of the number). -/
private def exists_isMaximalContinuousSemimeasureIn_closure_bstep
    (st : ℕ × BitString) : ℕ × BitString :=
  (st.1 / 2, decide (st.1 % 2 = 1) :: st.2)

/-- Auxiliary: the bit string of length `j` of the binary expansion of `n` (most significant
bit first). -/
private def exists_isMaximalContinuousSemimeasureIn_closure_bstr
    (j n : ℕ) : BitString :=
  ((exists_isMaximalContinuousSemimeasureIn_closure_bstep)^[j]
    (n, [])).2

private lemma exists_isMaximalContinuousSemimeasureIn_closure_biter_acc
    (j : ℕ) : ∀ (m : ℕ) (acc : BitString),
    ((exists_isMaximalContinuousSemimeasureIn_closure_bstep)^[j]
        (m, acc)).2 =
      ((exists_isMaximalContinuousSemimeasureIn_closure_bstep)^[j]
        (m, [])).2 ++ acc := by
  induction j with
  | zero => intro m acc; simp
  | succ j ih =>
    intro m acc
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simp only [exists_isMaximalContinuousSemimeasureIn_closure_bstep]
    rw [ih (m / 2) (decide (m % 2 = 1) :: acc), ih (m / 2) [decide (m % 2 = 1)]]
    simp

private lemma exists_isMaximalContinuousSemimeasureIn_closure_bstr_succ
    (j m : ℕ) :
    exists_isMaximalContinuousSemimeasureIn_closure_bstr (j + 1)
        m
      = exists_isMaximalContinuousSemimeasureIn_closure_bstr
          j (m / 2) ++ [decide (m % 2 = 1)] := by
  unfold exists_isMaximalContinuousSemimeasureIn_closure_bstr
  rw [Function.iterate_succ_apply]
  simp only [exists_isMaximalContinuousSemimeasureIn_closure_bstep]
  rw [exists_isMaximalContinuousSemimeasureIn_closure_biter_acc j
    (m / 2) [decide (m % 2 = 1)]]

private lemma exists_isMaximalContinuousSemimeasureIn_closure_bstr_zero
    (m : ℕ) :
    exists_isMaximalContinuousSemimeasureIn_closure_bstr 0 m
      = [] := by
  simp [exists_isMaximalContinuousSemimeasureIn_closure_bstr]

private lemma exists_isMaximalContinuousSemimeasureIn_closure_bstr_even
    (j k : ℕ) :
    exists_isMaximalContinuousSemimeasureIn_closure_bstr
        (j + 1) (2 * k)
      = exists_isMaximalContinuousSemimeasureIn_closure_bstr
          j k ++ [false] := by
  rw [exists_isMaximalContinuousSemimeasureIn_closure_bstr_succ]
  have h1 : 2 * k / 2 = k := by omega
  have h2 : (2 * k) % 2 = 0 := by omega
  simp [h1, h2]

private lemma exists_isMaximalContinuousSemimeasureIn_closure_bstr_odd
    (j k : ℕ) :
    exists_isMaximalContinuousSemimeasureIn_closure_bstr
        (j + 1) (2 * k + 1)
      = exists_isMaximalContinuousSemimeasureIn_closure_bstr
          j k ++ [true] := by
  rw [exists_isMaximalContinuousSemimeasureIn_closure_bstr_succ]
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : (2 * k + 1) % 2 = 1 := by omega
  simp [h1, h2]

private lemma exists_isMaximalContinuousSemimeasureIn_closure_bstr_computable :
    Computable₂
      exists_isMaximalContinuousSemimeasureIn_closure_bstr := by
  have hstep : Primrec
      exists_isMaximalContinuousSemimeasureIn_closure_bstep := by
    unfold exists_isMaximalContinuousSemimeasureIn_closure_bstep
    refine Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 2)) ?_
    refine Primrec.list_cons.comp ?_ Primrec.snd
    exact (PrimrecPred.decide (PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 1)))
  have hit : Primrec (fun p : ℕ × ℕ =>
      ((exists_isMaximalContinuousSemimeasureIn_closure_bstep)^[p.1]
        (p.2, ([] : BitString)))) :=
    Primrec.nat_iterate (f := fun p : ℕ × ℕ => p.1)
      (g := fun p : ℕ × ℕ => (p.2, ([] : BitString)))
      (h := fun _ st =>
        exists_isMaximalContinuousSemimeasureIn_closure_bstep st)
      Primrec.fst (Primrec.pair Primrec.snd (Primrec.const [])) (hstep.comp Primrec.snd)
  exact (Primrec.snd.comp hit).to_comp

/-- Auxiliary: oracle-computable map over an initial segment of `ℕ`. -/
private lemma exists_isMaximalContinuousSemimeasureIn_closure_lmap
    {O : Set (ℕ →. ℕ)} {α σ : Type*} [Primcodable α] [Primcodable σ]
    {N : α → ℕ} {g : α → ℕ → σ} (hN : ComputableIn O N) (hg : ComputableIn₂ O g) :
    ComputableIn O (fun a => (List.range (N a)).map (g a)) := by
  have h := ComputableIn.nat_rec (O := O) (f := N) (g := fun _ => ([] : List σ))
    (h := fun a (ns : ℕ × List σ) => ns.2 ++ [g a ns.1]) hN
    (Computable.const ([] : List σ)).computableIn ?_
  · refine h.of_eq (fun a => ?_)
    change @Nat.rec (fun _ => List σ) [] (fun y ih => ih ++ [g a y]) (N a) = _
    generalize N a = n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ← ih]
  · refine ComputableIn₂.mk ?_
    have h1 : ComputableIn O (fun r : α × (ℕ × List σ) => r.2.2) :=
      ComputableIn.snd.comp ComputableIn.snd
    have h2 : ComputableIn O (fun r : α × (ℕ × List σ) => [g r.1 r.2.1]) := by
      have h3 : ComputableIn O (fun r : α × (ℕ × List σ) => g r.1 r.2.1) :=
        hg.comp (ComputableIn.fst) (ComputableIn.fst.comp ComputableIn.snd)
      exact ComputableIn₂.comp (f := fun (a : σ) (b : List σ) => a :: b)
        (Computable₂.computableIn₂ Computable.list_cons) h3
        (Computable.const ([] : List σ)).computableIn
    exact ComputableIn₂.comp (f := fun (a b : List σ) => a ++ b)
      (Computable₂.computableIn₂ (Primrec.list_append.to_comp)) h1 h2

/-- Auxiliary: from the list `V` of closure values on the extensions of `x` of length `j + 1`
(in binary order, `0` beyond the list), the list of closure values on the extensions of length
`j`. -/
private def exists_isMaximalContinuousSemimeasureIn_closure_lstep
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) (x : BitString) (j : ℕ) (V : List ℚ) : List ℚ :=
  (List.range (2 ^ j)).map (fun k =>
    max (c i s (x ++
      exists_isMaximalContinuousSemimeasureIn_closure_bstr j k))
      (V.getD (2 * k) 0 + V.getD (2 * k + 1) 0))

/-- Auxiliary: the list of closure values after `n` steps, from the (all zero) level
`s - |x| + 1` upwards. -/
private noncomputable def
    exists_isMaximalContinuousSemimeasureIn_closure_lstate
    (c : ℕ → ℕ → BitString → ℚ) (i s : ℕ) (x : BitString) (n : ℕ) : List ℚ :=
  @Nat.rec (fun _ => List ℚ) []
    (fun m V =>
      exists_isMaximalContinuousSemimeasureIn_closure_lstep
        c i s x (s - x.length - m) V) n

private lemma exists_isMaximalContinuousSemimeasureIn_closure_lstate_spec
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i s : ℕ) (x : BitString)
    (hx : x.length ≤ s) (n : ℕ) :
    n ≤ s - x.length + 1 → ∀ k, k < 2 ^ (s - x.length + 1 - n) →
      (exists_isMaximalContinuousSemimeasureIn_closure_lstate
          c i s x n).getD k 0 =
        (match n with
        | 0 => 0
        | n' + 1 =>
          exists_isMaximalContinuousSemimeasureIn_closure_cl
            c i s n' (x ++
              exists_isMaximalContinuousSemimeasureIn_closure_bstr
                (s - x.length + 1 - (n' + 1)) k)) := by
  induction n with
  | zero =>
    intro _ k _
    simp [exists_isMaximalContinuousSemimeasureIn_closure_lstate]
  | succ n ih =>
    intro hn k hk
    have hlt : k < 2 ^ (s - x.length - n) := by
      have : s - x.length + 1 - (n + 1) = s - x.length - n := by omega
      rwa [this] at hk
    have hstate :
        exists_isMaximalContinuousSemimeasureIn_closure_lstate
        c i s x (n + 1) =
        exists_isMaximalContinuousSemimeasureIn_closure_lstep
          c i s x (s - x.length - n)
          (exists_isMaximalContinuousSemimeasureIn_closure_lstate
            c i s x n) := rfl
    rw [hstate]
    unfold exists_isMaximalContinuousSemimeasureIn_closure_lstep
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    simp only [Option.map_some, Option.getD_some]
    have hd : s - x.length + 1 - n = (s - x.length - n) + 1 := by omega
    have h2 : 2 ^ (s - x.length + 1 - n) = 2 * 2 ^ (s - x.length - n) := by
      rw [hd, pow_succ]; ring
    have hk0 : 2 * k < 2 ^ (s - x.length + 1 - n) := by omega
    have hk1 : 2 * k + 1 < 2 ^ (s - x.length + 1 - n) := by omega
    have e0 := ih (by omega) (2 * k) hk0
    have e1 := ih (by omega) (2 * k + 1) hk1
    have hbd : (s - x.length - n) + 1 = s - x.length + 1 - n := hd.symm
    rcases n with _ | n'
    · simp only at e0 e1 ⊢
      rw [e0, e1]
      simp only [add_zero]
      have := hc0 i s (x ++
        exists_isMaximalContinuousSemimeasureIn_closure_bstr
          (s - x.length - 0) k)
      rw [max_eq_left this]
      have e : s - x.length + 1 - (0 + 1) = s - x.length - 0 := by omega
      rw [e]
      rfl
    · simp only at e0 e1 ⊢
      rw [e0, e1]
      have e : s - x.length + 1 - (n' + 1 + 1) = s - x.length - (n' + 1) := by omega
      rw [e]
      have ee : s - x.length + 1 - (n' + 1) = (s - x.length - (n' + 1)) + 1 := by omega
      rw [ee,
        exists_isMaximalContinuousSemimeasureIn_closure_bstr_even,
        exists_isMaximalContinuousSemimeasureIn_closure_bstr_odd]
      simp only [exists_isMaximalContinuousSemimeasureIn_closure_cl,
        List.append_assoc]

private lemma exists_isMaximalContinuousSemimeasureIn_closure_lstate_final
    (c : ℕ → ℕ → BitString → ℚ) (hc0 : ∀ i s x, 0 ≤ c i s x) (i s : ℕ) (x : BitString)
    (hx : x.length ≤ s) :
    (exists_isMaximalContinuousSemimeasureIn_closure_lstate
        c i s x (s - x.length + 1)).getD 0 0 =
      exists_isMaximalContinuousSemimeasureIn_closure_cl
        c i s (s - x.length) x := by
  have h := exists_isMaximalContinuousSemimeasureIn_closure_lstate_spec
    c hc0 i s x hx (s - x.length + 1) le_rfl 0 (by simp)
  rw [h]
  simp only [Nat.sub_self,
    exists_isMaximalContinuousSemimeasureIn_closure_bstr_zero,
    List.append_nil]

/-- Step 1 of the proof of
`exists_isMaximalContinuousSemimeasureIn_closure`:
`A`-computability of the stage-`s` upward closure
`u i s x = if |x| ≤ s then cl (s - |x|) x else 0`, where
`cl 0 x = c i s x` and `cl (m+1) x = max (c i s x) (cl m (x0) + cl m (x1))` (an `A`-computable
`Nat.rec` on `s - |x|`, whose state is the list of closure values on the `2^j` extensions of `x`
of a fixed length `j`, computed bottom-up from the deepest level `s - |x|` to the root). -/
private theorem exists_isMaximalContinuousSemimeasureIn_computable
    (A : Set ℕ) (c : ℕ → ℕ → BitString → ℚ)
    (hc : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => c p.1 p.2.1 p.2.2))
    (hc0 : ∀ i s x, 0 ≤ c i s x) :
    ComputableIn {charOracle A}
      (fun p : ℕ × ℕ × BitString =>
        exists_isMaximalContinuousSemimeasureIn_closure_clo
          c p.1 p.2.1 p.2.2) := by
  have hpow : Primrec (fun m : ℕ => 2 ^ m) := by
    have h := Primrec.nat_iterate (f := fun m : ℕ => m) (g := fun _ : ℕ => (1 : ℕ))
      (h := fun (_ : ℕ) (x : ℕ) => 2 * x) Primrec.id (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    refine h.of_eq (fun m => ?_)
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring
  have hdq : Primrec (fun q : (ℕ × ℕ × BitString) × (ℕ × List ℚ) =>
      q.1.2.1 - q.1.2.2.length - q.2.1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.fst.comp Primrec.snd)
  have hN : ComputableIn {charOracle A}
      (fun q : (ℕ × ℕ × BitString) × (ℕ × List ℚ) => 2 ^ (q.1.2.1 - q.1.2.2.length - q.2.1)) :=
    (hpow.comp hdq).to_comp.computableIn
  have hargs : Computable (fun r : ((ℕ × ℕ × BitString) × (ℕ × List ℚ)) × ℕ =>
      (r.1.1.1, r.1.1.2.1, r.1.1.2.2 ++
        exists_isMaximalContinuousSemimeasureIn_closure_bstr
          (r.1.1.2.1 - r.1.1.2.2.length - r.1.2.1) r.2)) := by
    refine Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp
        Computable.fst))) ?_)
    refine (Primrec.list_append.to_comp).comp
      (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))) ?_
    exact exists_isMaximalContinuousSemimeasureIn_closure_bstr_computable.comp
      (hdq.to_comp.comp Computable.fst) Computable.snd
  have hA : ComputableIn {charOracle A}
      (fun r : ((ℕ × ℕ × BitString) × (ℕ × List ℚ)) × ℕ =>
        c r.1.1.1 r.1.1.2.1 (r.1.1.2.2 ++
          exists_isMaximalContinuousSemimeasureIn_closure_bstr
            (r.1.1.2.1 - r.1.1.2.2.length - r.1.2.1) r.2)) := by
    have h := ComputableIn.comp (O := {charOracle A})
      (f := fun p : ℕ × ℕ × BitString => c p.1 p.2.1 p.2.2) hc hargs.computableIn
    exact h
  have hget : ∀ f : ((ℕ × ℕ × BitString) × (ℕ × List ℚ)) × ℕ → ℕ, Computable f →
      Computable (fun r : ((ℕ × ℕ × BitString) × (ℕ × List ℚ)) × ℕ => r.1.2.2.getD (f r) 0) := by
    intro f hf
    exact (Primrec.list_getD (0 : ℚ)).to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) hf
  have hB : Computable (fun r : ((ℕ × ℕ × BitString) × (ℕ × List ℚ)) × ℕ =>
      r.1.2.2.getD (2 * r.2) 0 + r.1.2.2.getD (2 * r.2 + 1) 0) := by
    refine computable₂_ratAdd.comp
      (hget _ (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to_comp)
      (hget _ (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 1)).to_comp)
  have hg : ComputableIn₂ {charOracle A}
      (fun (q : (ℕ × ℕ × BitString) × (ℕ × List ℚ)) (k : ℕ) =>
        max (c q.1.1 q.1.2.1 (q.1.2.2 ++
          exists_isMaximalContinuousSemimeasureIn_closure_bstr
            (q.1.2.1 - q.1.2.2.length - q.2.1) k))
          (q.2.2.getD (2 * k) 0 + q.2.2.getD (2 * k + 1) 0)) :=
    ComputableIn₂.comp (f := fun a b : ℚ => max a b)
      computable₂_ratMax.computableIn₂ hA hB.computableIn
  have hstep : ComputableIn₂ {charOracle A}
      (fun (p : ℕ × ℕ × BitString) (nV : ℕ × List ℚ) =>
        exists_isMaximalContinuousSemimeasureIn_closure_lstep
          c p.1 p.2.1 p.2.2 (p.2.1 - p.2.2.length - nV.1) nV.2) := by
    have h := exists_isMaximalContinuousSemimeasureIn_closure_lmap
      (O := {charOracle A}) (N := fun q : (ℕ × ℕ × BitString) × (ℕ × List ℚ) =>
        2 ^ (q.1.2.1 - q.1.2.2.length - q.2.1)) hN hg
    refine ComputableIn₂.mk (h.of_eq (fun q => ?_))
    rfl
  have hrec : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ × BitString =>
        exists_isMaximalContinuousSemimeasureIn_closure_lstate
          c p.1 p.2.1 p.2.2 (p.2.1 - p.2.2.length + 1)) :=
    ComputableIn.nat_rec (f := fun p : ℕ × ℕ × BitString => p.2.1 - p.2.2.length + 1)
      (g := fun _ => ([] : List ℚ))
      (h := fun (p : ℕ × ℕ × BitString) (nV : ℕ × List ℚ) =>
        exists_isMaximalContinuousSemimeasureIn_closure_lstep
          c p.1 p.2.1 p.2.2 (p.2.1 - p.2.2.length - nV.1) nV.2)
      (Primrec.nat_add.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const
            1)).to_comp.computableIn
      (Computable.const ([] : List ℚ)).computableIn hstep
  have hval : ComputableIn {charOracle A}
      (fun p : ℕ × ℕ × BitString =>
        (exists_isMaximalContinuousSemimeasureIn_closure_lstate
          c p.1 p.2.1 p.2.2 (p.2.1 - p.2.2.length + 1)).getD 0 0) :=
    ComputableIn₂.comp (f := fun (l : List ℚ) (n : ℕ) => l.getD n 0)
      (Primrec.list_getD (0 : ℚ)).to_comp.computableIn₂ hrec
      (Computable.const (0 : ℕ)).computableIn
  have hguard : Computable (fun p : ℕ × ℕ × BitString => decide (p.2.2.length ≤ p.2.1)) :=
    (PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd))).to_comp
  have hG : Computable (fun q : Bool × ℚ => cond q.1 q.2 0) :=
    Computable.cond Computable.fst Computable.snd (Computable.const (0 : ℚ))
  have hF := hG.computableIn.comp (hguard.computableIn.pair hval)
  refine hF.of_eq (fun p => ?_)
  obtain ⟨i, s, x⟩ := p
  unfold exists_isMaximalContinuousSemimeasureIn_closure_clo
  by_cases h : x.length ≤ s
  · simp only [h, decide_true, Bool.cond_true, ite_true]
    exact exists_isMaximalContinuousSemimeasureIn_closure_lstate_final
      c hc0 i s x h
  · simp [h]

/-- Step 1 of the proof of
`exists_isMaximalContinuousSemimeasureIn_trim`: the upward closure.
From `A`-computable nonnegative rational stage approximations `c i s x`, nondecreasing in `s`,
build `A`-computable `u i s x ≥ 0`, nondecreasing in `s`, with `u i s (x0) + u i s (x1) ≤ u i s x`,
`c i s x ≤ u i s x` on strings of length `≤ s`, and `u i s ≤ a` for every real function `a`
with `a x0 + a x1 ≤ a x` and `c i s x ≤ a x` (stage `s`:
`u_s x = max (c i s x) (u_s (x0) + u_s (x1))` on strings of length `≤ s` and `0` beyond, by
recursion on `s - |x|`; the last property is an induction on `s - |x|`). -/
private theorem exists_isMaximalContinuousSemimeasureIn_closure
    (A : Set ℕ) (c : ℕ → ℕ → BitString → ℚ)
    (hc : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => c p.1 p.2.1 p.2.2))
    (hc0 : ∀ i s x, 0 ≤ c i s x) (hcm : ∀ i s x, c i s x ≤ c i (s + 1) x) :
    ∃ u : ℕ → ℕ → BitString → ℚ,
      ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => u p.1 p.2.1 p.2.2) ∧
      (∀ i s x, 0 ≤ u i s x) ∧ (∀ i s x, u i s x ≤ u i (s + 1) x) ∧
      (∀ i s x, u i s (x ++ [false]) + u i s (x ++ [true]) ≤ u i s x) ∧
      (∀ i s x, x.length ≤ s → c i s x ≤ u i s x) ∧
      ∀ i (a : BitString → ℝ), (∀ x, a (x ++ [false]) + a (x ++ [true]) ≤ a x) →
        (∀ s x, (c i s x : ℝ) ≤ a x) → ∀ s x, (u i s x : ℝ) ≤ a x := by
  refine ⟨exists_isMaximalContinuousSemimeasureIn_closure_clo c,
    exists_isMaximalContinuousSemimeasureIn_computable
      A c hc hc0,
    exists_isMaximalContinuousSemimeasureIn_closure_clo_nonneg
      c hc0,
    exists_isMaximalContinuousSemimeasureIn_closure_clo_mono
      c hc0 hcm,
    exists_isMaximalContinuousSemimeasureIn_closure_clo_super
      c hc0,
    fun i s x h =>
      exists_isMaximalContinuousSemimeasureIn_closure_clo_low
        c i s x h, ?_⟩
  intro i a ha hca s x
  exact exists_isMaximalContinuousSemimeasureIn_closure_clo_le
    c hc0 i a ha hca s x

/-- Auxiliary for step 2: the value at the last stage `s' ≤ s` with `u i s' [] ≤ 1`
(`0` if there is none). -/
private noncomputable def
    exists_isMaximalContinuousSemimeasureIn_trim_freezeRec
    (u : ℕ → ℕ → BitString → ℚ) (i : ℕ) (x : BitString) : ℕ → ℚ
  | 0 => if 1 < u i 0 [] then 0 else u i 0 x
  | n + 1 =>
    if 1 < u i (n + 1) [] then
      exists_isMaximalContinuousSemimeasureIn_trim_freezeRec u i x n
    else u i (n + 1) x

private lemma exists_isMaximalContinuousSemimeasureIn_trim_le_root
    (u : ℕ → ℕ → BitString → ℚ) (hu0 : ∀ i s x, 0 ≤ u i s x)
    (hus : ∀ i s x, u i s (x ++ [false]) + u i s (x ++ [true]) ≤ u i s x) (i s : ℕ) :
    ∀ x, u i s x ≤ u i s [] := by
  intro x
  induction x using List.reverseRecOn with
  | nil => exact le_rfl
  | append_singleton y b ih =>
    refine le_trans ?_ ih
    have h := hus i s y
    cases b
    · have := hu0 i s (y ++ [true]); linarith
    · have := hu0 i s (y ++ [false]); linarith

private lemma exists_isMaximalContinuousSemimeasureIn_trim_freezeRec_spec
    (u : ℕ → ℕ → BitString → ℚ) (i s : ℕ) :
    (∀ x, exists_isMaximalContinuousSemimeasureIn_trim_freezeRec u i x s
        = 0) ∨
      ∃ s' ≤ s, u i s' [] ≤ 1 ∧ ∀ x,
        exists_isMaximalContinuousSemimeasureIn_trim_freezeRec u i x s
          = u i s' x := by
  induction s with
  | zero =>
    by_cases h : 1 < u i 0 []
    · left; intro x
      simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, h]
    · right
      exact ⟨0, le_rfl, not_lt.mp h, fun x => by
        simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, h]⟩
  | succ n ih =>
    by_cases h : 1 < u i (n + 1) []
    · rcases ih with h1 | ⟨s', hs', h1, h2⟩
      · left; intro x
        simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, h,
          h1]
      · right
        exact ⟨s', by omega, h1, fun x => by
          simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, h,
            h2]⟩
    · right
      exact ⟨n + 1, le_rfl, not_lt.mp h, fun x => by
        simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, h]⟩

private lemma exists_isMaximalContinuousSemimeasureIn_trim_cond
    {O : Set (ℕ →. ℕ)} {α σ : Type*} [Primcodable α] [Primcodable σ] {c : α → Bool}
    {f g : α → σ} (hc : ComputableIn O c) (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O (fun a => cond (c a) (f a) (g a)) := by
  have h := PartrecIn.cond hc hf.partrecIn hg.partrecIn
  refine PartrecIn.of_eq h (fun a => ?_)
  change _ = Part.some (cond (c a) (f a) (g a))
  cases c a <;> rfl

/-- Step 2 of the proof of
`exists_isMaximalContinuousSemimeasureIn_trim`: freezing. From
`A`-computable nonnegative `u i s x`, nondecreasing in `s`, with
`u i s (x0) + u i s (x1) ≤ u i s x`, build `A`-computable `v i s x ∈ [0, 1]`, nondecreasing in `s`,
with `v i s [] = 1` and `v i s (x0) + v i s (x1) ≤ v i s x`: take the last stage `s' ≤ s` with
`u i s' [] ≤ 1` (these stages form an initial segment) and put `v i s x = u i s' x`, except
`v i s [] = 1`; if there is no such stage, `v i s x = 0` off the root (recursion on `s`). If
`u i s [] ≤ 1` then `s' = s`, so `v i s x = u i s x` off the root. -/
private theorem exists_isMaximalContinuousSemimeasureIn_freeze
    (A : Set ℕ) (u : ℕ → ℕ → BitString → ℚ)
    (hu : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => u p.1 p.2.1 p.2.2))
    (hu0 : ∀ i s x, 0 ≤ u i s x) (hum : ∀ i s x, u i s x ≤ u i (s + 1) x)
    (hus : ∀ i s x, u i s (x ++ [false]) + u i s (x ++ [true]) ≤ u i s x) :
    ∃ v : ℕ → ℕ → BitString → ℚ,
      ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => v p.1 p.2.1 p.2.2) ∧
      (∀ i s, v i s [] = 1) ∧ (∀ i s x, 0 ≤ v i s x ∧ v i s x ≤ 1) ∧
      (∀ i s x, v i s x ≤ v i (s + 1) x) ∧
      (∀ i s x, v i s (x ++ [false]) + v i s (x ++ [true]) ≤ v i s x) ∧
      ∀ i s x, u i s [] ≤ 1 → x ≠ [] → v i s x = u i s x := by
  have hroot :=
    exists_isMaximalContinuousSemimeasureIn_trim_le_root u hu0 hus
  have hspec :=
    exists_isMaximalContinuousSemimeasureIn_trim_freezeRec_spec u
  have hnn : ∀ i s x,
      0 ≤ exists_isMaximalContinuousSemimeasureIn_trim_freezeRec
        u i x s := by
    intro i s x
    rcases hspec i s with h | ⟨s', _, _, h⟩
    · rw [h x]
    · rw [h x]; exact hu0 _ _ _
  refine ⟨fun i s x => if x = [] then 1 else
    exists_isMaximalContinuousSemimeasureIn_trim_freezeRec u i x s,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrec : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString =>
        exists_isMaximalContinuousSemimeasureIn_trim_freezeRec
          u p.1 p.2.2 p.2.1) := by
      have hlt : ComputableIn {charOracle A} (fun r : ℚ × ℚ => decide (r.1 < r.2)) :=
        computable₂_ratLt.computableIn
      have hu3 : ∀ {γ : Type} [Primcodable γ] {fi fs : γ → ℕ} {fx : γ → BitString},
          ComputableIn {charOracle A} fi → ComputableIn {charOracle A} fs →
          ComputableIn {charOracle A} fx →
          ComputableIn {charOracle A} (fun g => u (fi g) (fs g) (fx g)) :=
        fun {γ} _ {fi fs fx} hi hs hx =>
          ComputableIn.comp (f := fun p : ℕ × ℕ × BitString => u p.1 p.2.1 p.2.2)
            (g := fun g : γ => (fi g, fs g, fx g)) hu (hi.pair (hs.pair hx))
      have hgt : ∀ {γ : Type} [Primcodable γ] {fq : γ → ℚ},
          ComputableIn {charOracle A} fq →
          ComputableIn {charOracle A} (fun g => decide (1 < fq g)) :=
        fun {γ} _ {fq} hq =>
          (ComputableIn.comp (f := fun r : ℚ × ℚ => decide (r.1 < r.2))
            (g := fun g : γ => ((1 : ℚ), fq g)) hlt
            ((ComputableIn.const (1 : ℚ)).pair hq)).of_eq fun g => by simp
      have hp1 : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => p.1) :=
        ComputableIn.fst
      have hpx : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => p.2.2) :=
        ComputableIn.snd.comp ComputableIn.snd
      have hps : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => p.2.1) :=
        ComputableIn.fst.comp ComputableIn.snd
      have hg : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString =>
          cond (decide (1 < u p.1 0 [])) (0 : ℚ) (u p.1 0 p.2.2)) :=
        exists_isMaximalContinuousSemimeasureIn_trim_cond
          (hgt (hu3 hp1 (ComputableIn.const 0) (ComputableIn.const [])))
          (ComputableIn.const 0) (hu3 hp1 (ComputableIn.const 0) hpx)
      have hh : ComputableIn₂ {charOracle A}
          (fun (p : ℕ × ℕ × BitString) (q : ℕ × ℚ) =>
            cond (decide (1 < u p.1 (q.1 + 1) [])) q.2 (u p.1 (q.1 + 1) p.2.2)) := by
        have hq1 : ComputableIn {charOracle A}
            (fun r : (ℕ × ℕ × BitString) × (ℕ × ℚ) => r.2.1 + 1) :=
          Primrec.succ.computableIn.comp (ComputableIn.fst.comp ComputableIn.snd)
        have hr1 : ComputableIn {charOracle A}
            (fun r : (ℕ × ℕ × BitString) × (ℕ × ℚ) => r.1.1) :=
          ComputableIn.fst.comp ComputableIn.fst
        have hrx : ComputableIn {charOracle A}
            (fun r : (ℕ × ℕ × BitString) × (ℕ × ℚ) => r.1.2.2) :=
          hpx.comp ComputableIn.fst
        exact exists_isMaximalContinuousSemimeasureIn_trim_cond
          (hgt (hu3 hr1 hq1 (ComputableIn.const [])))
          (ComputableIn.snd.comp ComputableIn.snd) (hu3 hr1 hq1 hrx)
      have hnr := ComputableIn.nat_rec hps hg hh
      refine hnr.of_eq fun p => ?_
      obtain ⟨i, s, x⟩ := p
      change @Nat.rec (fun _ => ℚ) _ _ s = _
      induction s with
      | zero =>
        simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec]
      | succ n ih =>
        simp only [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec]
        rw [← ih]
        simp
    have hroot1 : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => decide (p.2.2 = [])) :=
      (primrec_decideEq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])).computableIn
    refine (exists_isMaximalContinuousSemimeasureIn_trim_cond hroot1
      (ComputableIn.const (1 : ℚ)) hrec).of_eq fun p => ?_
    by_cases h : p.2.2 = [] <;> simp [h]
  · intro i s; simp
  · intro i s x
    by_cases hx : x = []
    · subst hx; simp
    · simp only [hx, ite_false]
      refine ⟨hnn i s x, ?_⟩
      rcases hspec i s with h | ⟨s', _, h1, h⟩
      · rw [h x]; exact zero_le_one
      · rw [h x]; exact (hroot i s' x).trans h1
  · intro i s x
    by_cases hx : x = []
    · subst hx; simp
    · simp only [hx, ite_false]
      by_cases hc : 1 < u i (s + 1) []
      · simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, hc]
      · have : exists_isMaximalContinuousSemimeasureIn_trim_freezeRec
            u i x (s + 1) = u i (s + 1) x := by
          simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec, hc]
        rw [this]
        rcases hspec i s with h | ⟨s', hs', h1, h⟩
        · rw [h x]; exact hu0 _ _ _
        · rw [h x]
          exact monotone_nat_of_le_succ (fun t => hum i t x) (by omega : s' ≤ s + 1)
  · intro i s x
    have hf : x ++ [false] ≠ [] := by simp
    have ht : x ++ [true] ≠ [] := by simp
    simp only [hf, ht, ite_false]
    by_cases hx : x = []
    · subst hx
      simp only [ite_true]
      rcases hspec i s with h | ⟨s', hs', h1, h⟩
      · simp only [h]; simp
      · simp only [h]; exact (hus i s' []).trans h1
    · simp only [hx, ite_false]
      rcases hspec i s with h | ⟨s', hs', h1, h⟩
      · simp only [h]; simp
      · simp only [h]; exact hus i s' x
  · intro i s x h hx
    simp only [hx, ite_false]
    cases s with
    | zero =>
      simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec,
        not_lt.mpr h]
    | succ n =>
      simp [exists_isMaximalContinuousSemimeasureIn_trim_freezeRec,
        not_lt.mpr h]

/-- Step 3 of the proof of `exists_isMaximalContinuousSemimeasureIn_enumeration`:
trimming. From `A`-computable nonnegative rational stage approximations `c i s x`, nondecreasing in
`s`, build `A`-computable stage values `v i s x ∈ [0, 1]`, nondecreasing in `s`, with
`v i s [] = 1` and `v i s (x0) + v i s (x1) ≤ v i s x` for all `x` (stage `s`: the upward closure
`u_s x = max (c i s x) (u_s (x0) + u_s (x1))` on strings of length `≤ s` and `0` beyond; take the
last stage `s' ≤ s` with `u_{s'} [] ≤ 1` (stages with `u_{s'} [] ≤ 1` form an initial segment) and
put `v i s x = u_{s'} x`, except `v i s [] = 1`; if there is no such stage, `v i s x = 0` off the
root). Moreover, if `a` is a real tree semimeasure (`a [] = 1`, `a x0 + a x1 ≤ a x`) with
`c i s x ≤ a x` and every `r < a x` below some `c i s x`, then `v i s x ≤ a x` and every
`r < a x` is below some `v i s x` (the upward closure of `c ≤ a` stays below `a`, so nothing is
ever frozen, and `u_s ≥ c_s` on strings of length `≤ s`). -/
private theorem exists_isMaximalContinuousSemimeasureIn_trim
    (A : Set ℕ) (c : ℕ → ℕ → BitString → ℚ)
    (hc : ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => c p.1 p.2.1 p.2.2))
    (hc0 : ∀ i s x, 0 ≤ c i s x) (hcm : ∀ i s x, c i s x ≤ c i (s + 1) x) :
    ∃ v : ℕ → ℕ → BitString → ℚ,
      ComputableIn {charOracle A} (fun p : ℕ × ℕ × BitString => v p.1 p.2.1 p.2.2) ∧
      (∀ i s, v i s [] = 1) ∧ (∀ i s x, 0 ≤ v i s x ∧ v i s x ≤ 1) ∧
      (∀ i s x, v i s x ≤ v i (s + 1) x) ∧
      (∀ i s x, v i s (x ++ [false]) + v i s (x ++ [true]) ≤ v i s x) ∧
      ∀ i (a : BitString → ℝ), a [] = 1 → (∀ x, a (x ++ [false]) + a (x ++ [true]) ≤ a x) →
        (∀ s x, (c i s x : ℝ) ≤ a x) → (∀ x (r : ℝ), r < a x → ∃ s, r < c i s x) →
        (∀ s x, (v i s x : ℝ) ≤ a x) ∧ (∀ x (r : ℝ), r < a x → ∃ s, r < v i s x) := by
  obtain ⟨u, huc, hu0, hum, hus, hulow, huup⟩ :=
    exists_isMaximalContinuousSemimeasureIn_closure
      A c hc hc0 hcm
  obtain ⟨v, hvc, hv1, hvb, hvm, hvs, hveq⟩ :=
    exists_isMaximalContinuousSemimeasureIn_freeze
      A u huc hu0 hum hus
  refine ⟨v, hvc, hv1, hvb, hvm, hvs, ?_⟩
  intro i a ha1 has hca hcr
  have hroot : ∀ s, u i s [] ≤ 1 := by
    intro s
    have h := huup i a has hca s []
    rw [ha1] at h
    exact_mod_cast h
  have hveq' : ∀ s x, x ≠ [] → v i s x = u i s x := fun s x hx => hveq i s x (hroot s) hx
  refine ⟨fun s x => ?_, fun x r hr => ?_⟩
  · by_cases hx : x = []
    · subst hx
      rw [hv1, ha1]
      simp
    · rw [hveq' s x hx]
      exact huup i a has hca s x
  · by_cases hx : x = []
    · subst hx
      refine ⟨0, ?_⟩
      rw [hv1]
      rw [ha1] at hr
      exact_mod_cast hr
    · obtain ⟨s₀, hs₀⟩ := hcr x r hr
      refine ⟨max s₀ x.length, ?_⟩
      rw [hveq' _ x hx]
      have h1 : c i s₀ x ≤ c i (max s₀ x.length) x := by
        have : Monotone (fun s => c i s x) := monotone_nat_of_le_succ (fun s => hcm i s x)
        exact this (le_max_left _ _)
      have h2 := hulow i (max s₀ x.length) x (le_max_right _ _)
      calc r < c i s₀ x := hs₀
        _ ≤ u i (max s₀ x.length) x := by
          have : (c i s₀ x : ℚ) ≤ u i (max s₀ x.length) x := h1.trans h2
          exact_mod_cast this

/-- Step 1 of the proof of `exists_isMaximalContinuousSemimeasureIn`: there is a
uniformly `A`-lower-semicomputable sequence `b` of continuous tree semimeasures (the trimmed
enumeration) that contains every `A`-lower-semicomputable continuous semimeasure. Here "uniformly
`A`-lower-semicomputable" means that the real function `(i, x) ↦ (b i x).toReal` is
`A`-lower-semicomputable. Construction: enumerate the `A`-enumerable sets of pairs `(x, q)` with
`q : ℚ` (universal oracle machine `PointToSet.oracleEval`), and trim the `i`-th one stage by
stage to a coherent family (the upward closure `u_s x = max (c_s x) (u_s (x0) + u_s (x1))` of the
stage-`s` finite approximation `c_s`, frozen as soon as the root value would exceed `1`, with the
root set to `1`), so that the result is always a continuous semimeasure and equals the original
semimeasure when the enumerated cut is already that of a semimeasure. -/
private theorem exists_isMaximalContinuousSemimeasureIn_enumeration (A : Set ℕ) :
    ∃ b : ℕ → BitString → ℝ≥0∞, (∀ i, IsContinuousTreeSemimeasure (b i)) ∧
      PointToSet.IsLowerSemicomputableIn A (fun p : ℕ × BitString => (b p.1 p.2).toReal) ∧
      ∀ a, IsLSCContinuousSemimeasureIn A a → ∃ i, b i = a := by
  obtain ⟨W, hWre, hWuni⟩ :=
    exists_isMaximalContinuousSemimeasureIn_universal A
  obtain ⟨c, hcc, hc0, hcm, hcW, hcW'⟩ :=
    exists_isMaximalContinuousSemimeasureIn_stages A W hWre
  obtain ⟨v, hvc, hv1, hvb, hvm, hvs, hvspec⟩ :=
    exists_isMaximalContinuousSemimeasureIn_trim A c hcc hc0 hcm
  have hvm' : ∀ i x, Monotone (fun s => ENNReal.ofReal ((v i s x : ℚ) : ℝ)) := fun i x s t h =>
    ENNReal.ofReal_le_ofReal (by exact_mod_cast monotone_nat_of_le_succ (fun s => hvm i s x) h)
  have hcont : ∀ i, IsContinuousTreeSemimeasure
      (fun x => ⨆ s, ENNReal.ofReal ((v i s x : ℚ) : ℝ)) := by
    intro i
    refine ⟨?_, fun x => ?_⟩
    · simp [hv1]
    · change (⨆ s, ENNReal.ofReal ((v i s (x ++ [false]) : ℚ) : ℝ)) +
        (⨆ s, ENNReal.ofReal ((v i s (x ++ [true]) : ℚ) : ℝ)) ≤
          ⨆ s, ENNReal.ofReal ((v i s x : ℚ) : ℝ)
      rw [ENNReal.iSup_add_iSup_of_monotone (hvm' i _) (hvm' i _)]
      refine iSup_mono fun s => ?_
      rw [← ENNReal.ofReal_add (by exact_mod_cast (hvb i s _).1)
        (by exact_mod_cast (hvb i s _).1)]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hvs i s x)
  have hfin : ∀ i x, (⨆ s, ENNReal.ofReal ((v i s x : ℚ) : ℝ)) ≠ ⊤ :=
    fun i x => (hcont i).ne_top x
  have hcut : ∀ i x (q : ℚ), (q : ℝ) < (⨆ s, ENNReal.ofReal ((v i s x : ℚ) : ℝ)).toReal ↔
      ∃ s, q < v i s x := by
    intro i x q
    by_cases hq : q < 0
    · refine iff_of_true ?_ ⟨0, lt_of_lt_of_le hq (hvb i 0 x).1⟩
      exact lt_of_lt_of_le (by exact_mod_cast hq) ENNReal.toReal_nonneg
    · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast not_lt.mp hq
      rw [← ENNReal.ofReal_lt_iff_lt_toReal hq' (hfin i x), lt_iSup_iff]
      refine exists_congr fun s => ?_
      rw [ENNReal.ofReal_lt_ofReal_iff']
      constructor
      · rintro ⟨h, _⟩
        exact_mod_cast h
      · intro h
        have h' : (q : ℝ) < v i s x := by exact_mod_cast h
        exact ⟨h', lt_of_le_of_lt hq' h'⟩
  refine ⟨fun i x => ⨆ s, ENNReal.ofReal ((v i s x : ℚ) : ℝ), hcont, ?_, ?_⟩
  · have hre : PointToSet.IsREIn A (fun w : (ℕ × BitString) × ℚ => ∃ s : ℕ, w.2 < v w.1.1 s w.1.2)
      := by
      refine PointToSet.IsREIn.exists (F := fun p : ((ℕ × BitString) × ℚ) × ℕ =>
        p.1.2 < v p.1.1.1 p.2 p.1.1.2) ?_
      refine PointToSet.isREIn_of_computableIn_decide A _ ?_
      have hargs : ComputableIn {charOracle A} (fun p : ((ℕ × BitString) × ℚ) × ℕ =>
          v p.1.1.1 p.2 p.1.1.2) :=
        ComputableIn.comp (g := fun p : ((ℕ × BitString) × ℚ) × ℕ => (p.1.1.1, p.2, p.1.1.2)) hvc
          (ComputableIn.pair (ComputableIn.fst.comp (ComputableIn.fst.comp ComputableIn.fst))
            (ComputableIn.pair ComputableIn.snd
              (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))))
      have hq : ComputableIn {charOracle A} (fun p : ((ℕ × BitString) × ℚ) × ℕ => p.1.2) :=
        ComputableIn.snd.comp ComputableIn.fst
      have hlt : ComputableIn {charOracle A} (fun r : ℚ × ℚ => decide (r.1 < r.2)) :=
        computable₂_ratLt.computableIn
      exact ComputableIn.comp (g := fun p : ((ℕ × BitString) × ℚ) × ℕ =>
        (p.1.2, v p.1.1.1 p.2 p.1.1.2)) hlt (ComputableIn.pair hq hargs)
    unfold PointToSet.IsLowerSemicomputableIn
    have hfun : (fun w : (ℕ × BitString) × ℚ =>
        ((w.2 : ℚ) : ℝ) < (⨆ s, ENNReal.ofReal ((v w.1.1 s w.1.2 : ℚ) : ℝ)).toReal) =
        fun w => ∃ s : ℕ, w.2 < v w.1.1 s w.1.2 :=
      funext fun w => propext (hcut _ _ _)
    rw [hfun]
    exact hre
  · intro a ha
    obtain ⟨hac, hL⟩ := ha
    obtain ⟨i, hi⟩ := hWuni (fun x q => (q : ℝ) < (a x).toReal) hL
    have hroot : (a []).toReal = 1 := by rw [hac.1]; simp
    have hsemi : ∀ x, (a (x ++ [false])).toReal + (a (x ++ [true])).toReal ≤ (a x).toReal := by
      intro x
      rw [← ENNReal.toReal_add (hac.ne_top _) (hac.ne_top _)]
      exact ENNReal.toReal_mono (hac.ne_top _) (hac.2 x)
    have hcle : ∀ s x, (c i s x : ℝ) ≤ (a x).toReal := by
      intro s x
      rcases hcW i s x with h | h
      · rw [h]; simp
      · exact ((hi _ _).mp h).le
    have hreach : ∀ x (r : ℝ), r < (a x).toReal → ∃ s, r < c i s x := by
      intro x r hr
      by_cases h0 : r < 0
      · exact ⟨0, lt_of_lt_of_le h0 (by exact_mod_cast hc0 i 0 x)⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
        have hq0 : 0 ≤ q := by
          have : (0 : ℝ) ≤ q := le_trans (not_lt.mp h0) hq1.le
          exact_mod_cast this
        obtain ⟨s, hs⟩ := hcW' i x q ((hi _ _).mpr hq2) hq0
        exact ⟨s, lt_of_lt_of_le hq1 (by exact_mod_cast hs)⟩
    obtain ⟨hle, hge⟩ := hvspec i (fun x => (a x).toReal) hroot hsemi hcle hreach
    refine ⟨i, funext fun x => le_antisymm (iSup_le fun s => ?_) ?_⟩
    · rw [← ENNReal.ofReal_toReal (hac.ne_top x)]
      exact ENNReal.ofReal_le_ofReal (hle s x)
    · refine le_of_forall_lt fun y hy => ?_
      have hy' : y ≠ ⊤ := ne_top_of_lt hy
      rw [← ENNReal.ofReal_toReal (hac.ne_top x),
        ENNReal.lt_ofReal_iff_toReal_lt hy'] at hy
      obtain ⟨s, hs⟩ := hge x _ hy
      refine lt_iSup_iff.mpr ⟨s, ?_⟩
      rw [ENNReal.lt_ofReal_iff_toReal_lt hy']
      exact hs

/-- Bounded conjunction of relatively enumerable predicates is relatively enumerable. -/
private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_bforall
    {α : Type*} [Primcodable α] (A : Set ℕ) (F : α × ℕ → Prop)
    (hF : PointToSet.IsREIn A F) (n : α → ℕ) (hn : ComputableIn {charOracle A} n) :
    PointToSet.IsREIn A (fun a => ∀ i < n a, F (a, i)) := by
  obtain ⟨f, hf, hdom⟩ := hF
  have hh : PartrecIn₂ {charOracle A} (fun (a : α) (p : ℕ × ℕ) => f (a, p.1)) :=
    hf.comp (ComputableIn.pair ComputableIn.fst (ComputableIn.fst.comp ComputableIn.snd))
  have hg : PartrecIn {charOracle A} (fun _ : α => (Part.some (0 : ℕ))) :=
    (ComputableIn.const (0 : ℕ)).partrecIn
  have := PointToSet.relative_closure_nat_rec A n (fun _ => Part.some 0)
    (fun a p => f (a, p.1)) hn hg hh
  refine ⟨_, this, fun a => ?_⟩
  have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => Part ℕ) (Part.some (0:ℕ))
        (fun i ih => ih.bind fun b => f (a, (i, b).1)) m).Dom
      ↔ ∀ i < m, F (a, i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Part.bind_dom]
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h1 i h
        · subst h; exact (hdom _).mpr h2
      · intro h
        exact ⟨fun i hi => h i (by omega), (hdom _).mp (h m (by omega))⟩
  exact (key (n a)).symm

/-- The `i`-th term `2 ^ (-i - 1) * L[i]` of a weighted rational sum. -/
private def exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU
    (L : List ℚ) (i : ℕ) : ℚ := (1 / 2 : ℚ) ^ (i + 1) * L.getD i 0

private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_getD :
    Computable₂ (fun (L : List ℚ) (i : ℕ) => L.getD i 0) :=
  (Primrec.list_getD (0 : ℚ)).to_comp

private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable₂_mixU :
    Computable₂ exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU := by
  have h1 : Computable (fun p : List ℚ × ℕ => (1 / 2 : ℚ) ^ (p.2 + 1)) :=
    (computable_half_pow.comp (Computable.succ.comp Computable.snd))
  have h2 : Computable (fun p : List ℚ × ℕ => p.1.getD p.2 0) :=
    exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_getD
  have h3 : Computable (fun p : List ℚ × ℕ => (1 / 2 : ℚ) ^ (p.2 + 1) * p.1.getD p.2 0) :=
    Computable₂.comp computable₂_ratMul h1 h2
  exact h3

private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_mixS :
    Computable (fun L : List ℚ => ratRangeSumP
      exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU L L.length) := by
  have hl : Computable (fun L : List ℚ => L.length) := Computable.list_length
  have hp : Computable (fun L : List ℚ => (L, L.length)) := Computable.pair Computable.id hl
  have h := (computable_ratRangeSumP
    exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable₂_mixU).comp hp
  exact h

private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_mixTest :
    Computable (fun a : (BitString × ℚ) × List ℚ =>
      decide (a.1.2 < ratRangeSumP
        exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU a.2 a.2.length)) := by
  have h : Computable (fun a : (BitString × ℚ) × List ℚ =>
      ratLtPair (a.1.2, ratRangeSumP
        exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU a.2 a.2.length)) :=
    computable_ratLtPair.comp (Computable.pair (Computable.snd.comp Computable.fst)
      (exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_mixS.comp
        Computable.snd))
  exact h

/-- Real analysis behind the mixture: the strict lower cut of `∑ 2 ^ (-i - 1) cᵢ` for
`cᵢ ∈ [0, 1]` is given by finite rational approximations from below. -/
private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixIff
    (c : ℕ → ℝ) (c0 : ∀ i, 0 ≤ c i) (c1 : ∀ i, c i ≤ 1) (q : ℚ) :
    (q : ℝ) < ∑' i, (1 / 2 : ℝ) ^ (i + 1) * c i ↔
      ∃ L : List ℚ, (∀ i < L.length, ((L.getD i 0 : ℚ) : ℝ) < c i) ∧
        (q : ℝ) < ∑ i ∈ Finset.range L.length, (1 / 2 : ℝ) ^ (i + 1) * ((L.getD i 0 : ℚ) : ℝ) := by
  have hnn : ∀ i, 0 ≤ (1 / 2 : ℝ) ^ (i + 1) * c i := fun i => by
    have := c0 i; positivity
  have hsum : Summable (fun i => (1 / 2 : ℝ) ^ (i + 1) * c i) := by
    refine Summable.of_nonneg_of_le (f := fun i : ℕ => (1 / 2 : ℝ) * (1 / 2) ^ i) hnn (fun i => ?_)
      ((summable_geometric_two.mul_left (1 / 2)))
    calc (1 / 2 : ℝ) ^ (i + 1) * c i ≤ (1 / 2 : ℝ) ^ (i + 1) * 1 :=
          mul_le_mul_of_nonneg_left (c1 i) (by positivity)
      _ = (1 / 2) * (1 / 2) ^ i := by ring
  constructor
  · intro h
    have ht := hsum.hasSum.tendsto_sum_nat
    obtain ⟨N, hN⟩ := (ht.eventually (lt_mem_nhds h)).exists
    set δ := ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * c i - q with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    set ε : ℝ := δ / (N + 1) with hε
    have hεpos : 0 < ε := by positivity
    have hex : ∀ i, ∃ r : ℚ, c i - ε < r ∧ (r : ℝ) < c i := fun i =>
      exists_rat_btwn (by linarith)
    choose r hr1 hr2 using hex
    refine ⟨(List.range N).map r, ?_, ?_⟩
    · intro i hi
      simp only [List.length_map, List.length_range] at hi
      simpa [List.getD_eq_getElem?_getD, hi] using hr2 i
    · simp only [List.length_map, List.length_range]
      have hg : ∀ i ∈ Finset.range N, ((((List.range N).map r).getD i 0 : ℚ) : ℝ) = r i := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simp [List.getD_eq_getElem?_getD, hi']
      rw [Finset.sum_congr rfl (fun i hi => by rw [hg i hi])]
      have hle : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * (c i - r i) ≤ N * ε := by
        calc ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * (c i - r i)
            ≤ ∑ i ∈ Finset.range N, ε := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              have h1 : (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
              have h2 : 0 ≤ c i - r i := by linarith [hr2 i]
              have h3 : c i - r i ≤ ε := by linarith [hr1 i]
              calc (1 / 2 : ℝ) ^ (i + 1) * (c i - r i) ≤ 1 * (c i - r i) :=
                    mul_le_mul_of_nonneg_right h1 h2
                _ ≤ ε := by linarith
          _ = N * ε := by simp
      have hNε : (N : ℝ) * ε < δ := by
        rw [hε, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      have : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * (c i - r i)
          = ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * c i
            - ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (i + 1) * (r i : ℝ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      linarith
  · rintro ⟨L, hL, hq⟩
    refine lt_of_lt_of_le hq ?_
    refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (hsum.sum_le_tsum _ (fun i _ => hnn i))
    exact mul_le_mul_of_nonneg_left (hL i (Finset.mem_range.mp hi)).le (by positivity)

/-- Enumerability of the finite-approximation cut of a dyadic mixture of an `A`-enumerable
family of rational lower cuts. -/
private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc_rePart
    (A : Set ℕ) (c : ℕ → BitString → ℝ)
    (hL : PointToSet.IsREIn A
      (fun w : (ℕ × BitString) × ℚ => (w.2 : ℝ) < c w.1.1 w.1.2)) :
    PointToSet.IsREIn A (fun w : BitString × ℚ => ∃ L : List ℚ,
      (∀ i < L.length, ((L.getD i 0 : ℚ) : ℝ) < c i w.1) ∧
        (w.2 : ℝ) < ∑ i ∈ Finset.range L.length,
          (1 / 2 : ℝ) ^ (i + 1) * ((L.getD i 0 : ℚ) : ℝ)) := by
  have hR3 : PointToSet.IsREIn A (fun a : (BitString × ℚ) × List ℚ =>
      a.1.2 < ratRangeSumP
        exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU a.2 a.2.length) :=
    PointToSet.isREIn_of_computableIn_decide A _
      exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_mixTest.computableIn
  have hm : Computable (fun p : ((BitString × ℚ) × List ℚ) × ℕ =>
      ((p.2, p.1.1.1), p.1.2.getD p.2 0)) :=
    Computable.pair (Computable.pair Computable.snd
      (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      (exists_isMaximalContinuousSemimeasureIn_mixture_lsc_computable_getD.comp
        (Computable.snd.comp Computable.fst) Computable.snd)
  have hR1 := hL.comp hm.computableIn
  have hR2 := exists_isMaximalContinuousSemimeasureIn_mixture_lsc_bforall A _ hR1
    (fun a : (BitString × ℚ) × List ℚ => a.2.length)
    (Computable.list_length.comp Computable.snd).computableIn
  have hR := (hR2.and hR3).exists (β := List ℚ)
  obtain ⟨f, hf, hd⟩ := hR
  refine ⟨f, hf, fun w => ?_⟩
  rw [← hd w]
  refine exists_congr (fun L => ?_)
  have hcast : ((ratRangeSumP
      exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU L L.length : ℚ) : ℝ) =
      ∑ i ∈ Finset.range L.length, (1 / 2 : ℝ) ^ (i + 1) * ((L.getD i 0 : ℚ) : ℝ) := by
    rw [ratRangeSumP_eq]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixU]
  rw [← hcast]
  simp only [Rat.cast_lt]

/-- Step 2 of the proof of `exists_isMaximalContinuousSemimeasureIn`: the dyadic
mixture `∑ᵢ 2 ^ (-i - 1) bᵢ` of a uniformly `A`-lower-semicomputable sequence of tree
semimeasures is `A`-lower-semicomputable. (`q < ∑ᵢ 2 ^ (-i - 1) bᵢ x` iff for some `N` there are
rationals `rᵢ < bᵢ x`, `i < N`, with `q < ∑_{i<N} 2 ^ (-i - 1) rᵢ`; the values `bᵢ x` are
nonnegative reals, so the partial sums increase to the mixture.) -/
private theorem exists_isMaximalContinuousSemimeasureIn_mixture_lsc (A : Set ℕ)
    (b : ℕ → BitString → ℝ≥0∞) (hb : ∀ i, IsContinuousTreeSemimeasure (b i))
    (hL : PointToSet.IsLowerSemicomputableIn A (fun p : ℕ × BitString => (b p.1 p.2).toReal)) :
    PointToSet.IsLowerSemicomputableIn A (fun x => (continuousTreeMixture b x).toReal) := by
  set c : ℕ → BitString → ℝ := fun i x => (b i x).toReal with hc
  have hL' : PointToSet.IsREIn A
      (fun w : (ℕ × BitString) × ℚ => (w.2 : ℝ) < c w.1.1 w.1.2) := hL
  obtain ⟨f, hf, hd⟩ :=
    exists_isMaximalContinuousSemimeasureIn_mixture_lsc_rePart A c hL'
  refine ⟨f, hf, fun w => ?_⟩
  rw [← hd w]
  obtain ⟨x, q⟩ := w
  have hfin : ∀ i, b i x ≠ ⊤ := fun i => by
    have h1 : b i x ≤ b i [] := (hb i).antitone_of_prefix (List.nil_prefix)
    rw [(hb i).1] at h1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hm : (continuousTreeMixture b x).toReal = ∑' i, (1 / 2 : ℝ) ^ (i + 1) * c i x := by
    unfold continuousTreeMixture
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top (dyadicWeight_ne_top i) (hfin i))]
    refine tsum_congr (fun i => ?_)
    rw [ENNReal.toReal_mul, dyadicWeight, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp [hc]
  have c0 : ∀ i, 0 ≤ c i x := fun i => ENNReal.toReal_nonneg
  have c1 : ∀ i, c i x ≤ 1 := fun i => by
    have h1 : b i x ≤ b i [] := (hb i).antitone_of_prefix (List.nil_prefix)
    rw [(hb i).1] at h1
    simpa [hc] using ENNReal.toReal_mono ENNReal.one_ne_top h1
  change (q : ℝ) < (continuousTreeMixture b x).toReal ↔ _
  rw [hm]
  exact exists_isMaximalContinuousSemimeasureIn_mixture_lsc_mixIff (fun i => c i x) c0 c1 q

/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Relativized Theorem 78: a maximal
`A`-lower-semicomputable continuous semimeasure exists.

Proof idea: the proof of `exists_maximal_lowerSemicomputableContinuousSemimeasure`
relativizes. Enumerate the `A`-lower-semicomputable continuous semimeasures (trimmed so that the
semimeasure inequalities hold at every stage) and take `∑ᵢ 2 ^ (-i - 1) aᵢ`, with the root value
set to `1`. -/
theorem exists_isMaximalContinuousSemimeasureIn (A : Set ℕ) :
    ∃ a, IsMaximalContinuousSemimeasureIn A a := by
  obtain ⟨b, hbc, hbL, hcomp⟩ := exists_isMaximalContinuousSemimeasureIn_enumeration A
  refine ⟨continuousTreeMixture b, ⟨continuousTreeMixture_isContinuousTreeSemimeasure b hbc,
    exists_isMaximalContinuousSemimeasureIn_mixture_lsc A b hbc hbL⟩, ?_⟩
  intro a' ha'
  obtain ⟨i, hi⟩ := hcomp a' ha'
  refine ⟨(dyadicWeight i)⁻¹, ENNReal.inv_ne_top.mpr (dyadicWeight_pos i).ne', fun x => ?_⟩
  have h1 := continuousTreeMixture_dominates_component b i x
  rw [hi] at h1
  calc
    a' x = (dyadicWeight i)⁻¹ * (dyadicWeight i * a' x) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (dyadicWeight_pos i).ne' (dyadicWeight_ne_top i),
        one_mul]
    _ ≤ (dyadicWeight i)⁻¹ * continuousTreeMixture b x := by gcongr

end GeneralScheme

end Kolmogorov
