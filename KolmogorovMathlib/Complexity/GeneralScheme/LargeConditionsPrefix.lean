import KolmogorovMathlib.Complexity.GeneralScheme.SetConditions
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import KolmogorovMathlib.AlgorithmicProbability.ConditionalUniversalSemimeasure
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision

/-!
# Large numbers as conditions: prefix complexity (SUV Section 6.4.2)

SUV Theorem 133 (printed p. 206), Theorem 134 and Problem 208 (printed p. 208), together with the
unnumbered facts about the prefix versions `K(x ‖ A)` (prefix-stable decompressors) and
`K'(x ‖ A)` (prefix-free decompressors) on printed pp. 207–208. `K^{0'}` is `KP V x []` for an
optimal prefix-free `0'`-decompressor `V` (`PointToSet.IsOptimalOraclePrefix jumpSet V`).
-/

open scoped ENNReal

namespace Kolmogorov

namespace GeneralScheme

/-- **SUV Section 6.4.2 (printed pp. 206–207), lemma in the proof of Theorem 133.** The
`liminf` of a family of semimeasures is a semimeasure: if `∑ₓ m(x | n) ≤ 1` for every `n`, then
`∑ₓ liminf_n m(x | n) ≤ 1`.

Proof: Fatou's lemma for the counting measure (`MeasureTheory.lintegral_liminf_le`). -/
theorem tsum_liminf_le_one (m : ℕ → BitString → ℝ≥0∞) (hm : ∀ n, ∑' x, m n x ≤ 1) :
    ∑' x, Filter.liminf (fun n => m n x) Filter.atTop ≤ 1 := by
  let _ : MeasurableSpace BitString := ⊤
  have h := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count)
    (u := Filter.atTop) (f := m) (fun _ => measurable_from_top)
  rw [MeasureTheory.lintegral_count' measurable_from_top] at h
  simp only [MeasureTheory.lintegral_count' measurable_from_top] at h
  exact h.trans (Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hm).frequently)

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_eval`: the
`m`-step approximation `A_m` of `0'`, as a list of its first `u` characteristic bits. -/
private def exists_const_limsup_KP_eq_KP_jump_eval_approxPre
    (m u : ℕ) : List ℕ :=
  (List.range u).map fun k =>
    bif (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome then 1 else 0

private lemma exists_const_limsup_KP_eq_KP_jump_eval_approxPre_primrec :
    Primrec₂
      exists_const_limsup_KP_eq_KP_jump_eval_approxPre := by
  have hg : Primrec₂ (fun (a : ℕ × ℕ) (k : ℕ) =>
      bif (Nat.Partrec.Code.evaln a.1 (Denumerable.ofNat Nat.Partrec.Code k) k).isSome
        then 1 else 0) := by
    have hev : Primrec (fun b : (ℕ × ℕ) × ℕ =>
        Nat.Partrec.Code.evaln b.1.1 (Denumerable.ofNat Nat.Partrec.Code b.2) b.2) :=
      Nat.Partrec.Code.primrec_evaln.comp (((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.snd)).pair Primrec.snd)
    exact (Primrec.cond (Primrec.option_isSome.comp hev) (Primrec.const 1)
      (Primrec.const 0)).to₂
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hg).to₂

open Classical in
private lemma exists_const_limsup_KP_eq_KP_jump_eval_approxPre_eq
    (u : ℕ) : ∃ M, ∀ m ≥ M, ∀ u' ≤ u,
      exists_const_limsup_KP_eq_KP_jump_eval_approxPre m u' =
        (List.range u').map (fun k => if k ∈ jumpSet then 1 else 0) := by
  classical
  have hconv : ∀ u, ∃ M, ∀ m ≥ M, ∀ k < u,
      (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome = true ↔
        k ∈ jumpSet := by
    intro u
    induction u with
    | zero => exact ⟨0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ u ih =>
      obtain ⟨M, hM⟩ := ih
      by_cases hu : u ∈ jumpSet
      · have hu' : ((Denumerable.ofNat Nat.Partrec.Code u).eval u).Dom := hu
        obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hu'
        obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
        refine ⟨max M s, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m (le_of_max_le_left hm) k hk
        · refine ⟨fun _ => hu, fun _ => ?_⟩
          exact Option.isSome_iff_exists.mpr
            ⟨v, Nat.Partrec.Code.evaln_mono (le_of_max_le_right hm) hs⟩
      · refine ⟨M, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m hm k hk
        · refine ⟨fun h => ?_, fun h => absurd h hu⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩
  obtain ⟨M, hM⟩ := hconv u
  refine ⟨M, fun m hm u' hu' => List.map_congr_left fun k hk => ?_⟩
  have hiff := hM m hm k (lt_of_lt_of_le (List.mem_range.mp hk) hu')
  by_cases hj : k ∈ jumpSet
  · simp [hj, hiff.mpr hj]
  · have hf : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome =
        false := by
      cases h : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome
      · rfl
      · exact absurd (hiff.mp h) hj
    simp [hj, hf]

/-- Auxiliary: the run of the code `c` for at most `s.unpair.2` steps, on the oracle prefix
`pre s.unpair.1` and the input `(p, [])`, decoded as a bit string. -/
private def exists_const_limsup_KP_eq_KP_jump_eval_gStage
    (c : Nat.Partrec.Code) (pre : ℕ → List ℕ) (s : ℕ) (p : BitString) : Option BitString :=
  (Nat.Partrec.Code.evaln s.unpair.2 c
    (Encodable.encode (pre s.unpair.1, Encodable.encode (p, ([] : BitString))))).bind
      fun v => Encodable.decode (α := BitString) v

/-- Auxiliary: the first successful run among the stages `s ≤ t`. -/
private def exists_const_limsup_KP_eq_KP_jump_eval_evStage
    (c : Nat.Partrec.Code) (pre : ℕ → List ℕ) (t : ℕ) (p : BitString) : Option BitString :=
  ((List.range (t + 1)).filterMap fun s =>
    exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p).head?

private lemma exists_const_limsup_KP_eq_KP_jump_eval_evStage_mono
    (c : Nat.Partrec.Code) (pre : ℕ → List ℕ) {t t' : ℕ} (p : BitString) (a : BitString)
    (htt : t ≤ t')
    (h : exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre t p
      = some a) :
    exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre t' p
      = some a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  unfold
    exists_const_limsup_KP_eq_KP_jump_eval_evStage at h ⊢
  rw [show t + k + 1 = (t + 1) + k by omega, List.range_add, List.filterMap_append,
    List.head?_append, h]
  rfl

private lemma exists_const_limsup_KP_eq_KP_jump_eval_evStage_some
    (c : Nat.Partrec.Code) (pre : ℕ → List ℕ) {t : ℕ} (p : BitString) (a : BitString)
    (h : exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre t p
      = some a) :
    ∃ s ≤ t,
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p
        = some a := by
  unfold
    exists_const_limsup_KP_eq_KP_jump_eval_evStage at h
  have := List.mem_of_mem_head? h
  obtain ⟨s, hs, hs'⟩ := List.mem_filterMap.mp this
  exact ⟨s, Nat.lt_succ_iff.mp (List.mem_range.mp hs), hs'⟩

private lemma exists_const_limsup_KP_eq_KP_jump_eval_evStage_exists
    (c : Nat.Partrec.Code) (pre : ℕ → List ℕ) {t : ℕ} (p : BitString) (s : ℕ) (hs : s ≤ t)
    (a : BitString)
    (h : exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p
      = some a) :
    ∃ y, exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre t p
      = some y := by
  unfold
    exists_const_limsup_KP_eq_KP_jump_eval_evStage
  have hmem : a ∈ (List.range (t + 1)).filterMap fun s =>
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p :=
    List.mem_filterMap.mpr ⟨s, List.mem_range.mpr (Nat.lt_succ_of_le hs), h⟩
  cases hl : (List.range (t + 1)).filterMap fun s =>
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p with
  | nil => rw [hl] at hmem; simp at hmem
  | cons y ys => exact ⟨y, rfl⟩

private lemma exists_const_limsup_KP_eq_KP_jump_eval_evStage_congr
    (c : Nat.Partrec.Code) (pre pre' : ℕ → List ℕ) (t : ℕ) (p : BitString)
    (h : ∀ s ≤ t,
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre s p =
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c pre' s p) :
    exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre t p =
      exists_const_limsup_KP_eq_KP_jump_eval_evStage c pre' t p := by
  unfold
    exists_const_limsup_KP_eq_KP_jump_eval_evStage
  rw [List.filterMap_congr fun s hs => h s (Nat.lt_succ_iff.mp (List.mem_range.mp hs))]

private lemma exists_const_limsup_KP_eq_KP_jump_eval_evStage_computable
    (c : Nat.Partrec.Code) :
    Computable (fun r : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_eval_evStage c
        (exists_const_limsup_KP_eq_KP_jump_eval_approxPre r.1)
        r.2.1 r.2.2) := by
  have hpre :=
      exists_const_limsup_KP_eq_KP_jump_eval_approxPre_primrec
  have hu : Primrec (fun b : (ℕ × ℕ × BitString) × ℕ => b.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hin : Primrec (fun b : (ℕ × ℕ × BitString) × ℕ => Encodable.encode
      (exists_const_limsup_KP_eq_KP_jump_eval_approxPre
        b.1.1 b.2.unpair.1, Encodable.encode (b.1.2.2, ([] : BitString)))) :=
    Primrec.encode.comp ((hpre.comp (Primrec.fst.comp Primrec.fst) hu).pair
      (Primrec.encode.comp ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.const ([] : BitString)))))
  have hev : Primrec (fun b : (ℕ × ℕ × BitString) × ℕ => Nat.Partrec.Code.evaln b.2.unpair.2 c
      (Encodable.encode
      (exists_const_limsup_KP_eq_KP_jump_eval_approxPre
        b.1.1 b.2.unpair.1, Encodable.encode (b.1.2.2, ([] : BitString))))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).pair (Primrec.const c)).pair hin)
  have hg : Primrec₂ (fun (r : ℕ × ℕ × BitString) (s : ℕ) =>
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c
        (exists_const_limsup_KP_eq_KP_jump_eval_approxPre r.1)
        s r.2.2) :=
    (Primrec.option_bind hev (Primrec.decode.comp Primrec.snd).to₂).to₂
  exact (Primrec.list_head?.comp (Primrec.listFilterMap
    (f := fun r : ℕ × ℕ × BitString => List.range (r.2.1 + 1))
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) hg)).to_comp

/-- Step 1 of the proof of `exists_const_limsup_KP_eq_KP_jump_approx_semimeasure`:
step-bounded evaluation of a `0'`-computable decompressor with the `n`-step approximation of `0'`
as the oracle.

For `V` a `0'`-decompressor (`IsDecompressorIn (charOracle jumpSet) V`) there are
* `ev n t p`: the result of running `V` on `(p, [])` for `t` steps (each oracle query counts as one
  step), where the oracle is replaced by `χ_{A_n}`, `A_n = {e | φ_e(e) halts within n steps}`; it
  is computable in `(n, t, p)` and monotone in `t` (once halted, the result stays the same);
* `evT t p`: the same with the true oracle `0'`; it is monotone in `t` and exhausts `V`:
  `x ∈ V (p, [])` iff `evT t p = some x` for some `t`;
* stabilization: for every `T` there is `N` such that for all `n ≥ N`, `t ≤ T` and `|p| ≤ T`, the
  approximate and the true runs coincide (`ev n t p = evT t p`): within `t` steps a run on `p`
  queries finitely many numbers, and `A_n` agrees with `0'` on any finite set for large `n`
  (and only finitely many `p` have `|p| ≤ T`).

Proof idea: by induction on the `RecursiveIn {charOracle jumpSet}` derivation of
`mapToNatFun V` define the step-bounded evaluation relative to an arbitrary oracle `χ_A`, show it
is computable in `(A restricted to a finite table, t, p)` and monotone in the step bound, and
compare the runs for `A = A_n` and `A = 0'`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_eval {V : Map}
    (hV : IsDecompressorIn (charOracle jumpSet) V) :
    ∃ (ev : ℕ → ℕ → BitString → Option BitString) (evT : ℕ → BitString → Option BitString),
      Computable (fun r : ℕ × ℕ × BitString => ev r.1 r.2.1 r.2.2) ∧
      (∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a) ∧
      (∀ t t' p a, t ≤ t' → evT t p = some a → evT t' p = some a) ∧
      (∀ p x, x ∈ V (p, []) ↔ ∃ t, evT t p = some x) ∧
      ∀ T, ∃ N, ∀ n ≥ N, ∀ t ≤ T, ∀ p : BitString, p.length ≤ T → ev n t p = evT t p := by
  classical
  obtain ⟨Φ, hΦ, -, hex⟩ := PointToSet.exists_exact_string_operator
    (fun k => if k ∈ jumpSet then 1 else 0) (mapToNatFun V) hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hΦ
  have hceval : ∀ w : List ℕ × ℕ, c.eval (Encodable.encode w) = Φ w := by
    intro w
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.map_id' (fun _ => rfl) _
  let preT : ℕ → List ℕ := fun u => (List.range u).map fun k => if k ∈ jumpSet then 1 else 0
  have hsound : ∀ s p x,
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c preT s p
        = some x → x ∈ V (p, []) := by
    intro s p x h
    unfold exists_const_limsup_KP_eq_KP_jump_eval_gStage at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hdec⟩ := h
    have hvΦ := Nat.Partrec.Code.evaln_sound hv
    rw [hceval] at hvΦ
    have hvf := (hex _ v).mpr ⟨s.unpair.1, hvΦ⟩
    simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some,
      Part.mem_map_iff] at hvf
    obtain ⟨z, hz, rfl⟩ := hvf
    rw [Encodable.encodek, Option.some_inj] at hdec
    rw [← hdec]
    exact hz
  have hcompl : ∀ p x, x ∈ V (p, []) → ∃ s,
      exists_const_limsup_KP_eq_KP_jump_eval_gStage c preT s p
        = some x := by
    intro p x hpx
    have hmemf : Encodable.encode x ∈ mapToNatFun V (Encodable.encode (p, ([] : BitString))) := by
      simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some]
      exact Part.mem_map _ hpx
    obtain ⟨u, hu⟩ := (hex _ _).mp hmemf
    rw [← hceval] at hu
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hu
    refine ⟨Nat.pair u k, ?_⟩
    simp only [
      exists_const_limsup_KP_eq_KP_jump_eval_gStage,
      Nat.unpair_pair]
    rw [show preT u = (List.range u).map fun k => if k ∈ jumpSet then 1 else 0 from rfl, hk]
    simp
  refine ⟨fun n =>
      exists_const_limsup_KP_eq_KP_jump_eval_evStage c
        (exists_const_limsup_KP_eq_KP_jump_eval_approxPre n),
    exists_const_limsup_KP_eq_KP_jump_eval_evStage c preT,
    exists_const_limsup_KP_eq_KP_jump_eval_evStage_computable c,
    ?_, ?_, ?_, ?_⟩
  · intro n t t' p a htt h
    exact exists_const_limsup_KP_eq_KP_jump_eval_evStage_mono
      c _ p a htt h
  · intro t t' p a htt h
    exact exists_const_limsup_KP_eq_KP_jump_eval_evStage_mono
      c _ p a htt h
  · intro p x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := hcompl p x hx
      obtain ⟨y, hy⟩ :=
        exists_const_limsup_KP_eq_KP_jump_eval_evStage_exists
          c preT p s le_rfl x hs
      refine ⟨s, ?_⟩
      obtain ⟨s', -, hs'⟩ :=
        exists_const_limsup_KP_eq_KP_jump_eval_evStage_some
          c preT p y hy
      have hyV := hsound s' p y hs'
      have : y = x := Part.mem_unique hyV hx
      rw [← this]; exact hy
    · rintro ⟨t, ht⟩
      obtain ⟨s, -, hs⟩ :=
        exists_const_limsup_KP_eq_KP_jump_eval_evStage_some
          c preT p x ht
      exact hsound s p x hs
  · intro T
    obtain ⟨N, hN⟩ :=
      exists_const_limsup_KP_eq_KP_jump_eval_approxPre_eq T
    refine ⟨N, fun n hn t ht p _ => ?_⟩
    refine
      exists_const_limsup_KP_eq_KP_jump_eval_evStage_congr
        c _ _ t p fun s hs => ?_
    unfold exists_const_limsup_KP_eq_KP_jump_eval_gStage
    have hu : s.unpair.1 ≤ T := (Nat.unpair_left_le s).trans (hs.trans ht)
    rw [hN n hn _ hu]

/-- Stage-`s` halting predicate for the `n`-th approximation: `p` has length at most `s` and
`ev n s p` is defined. -/
private def exists_const_limsup_KP_eq_KP_jump_trim_H
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (p : BitString) : Prop :=
  p.length ≤ s ∧ (ev n s p).isSome

/-- The first stage at which `p` halts in the `n`-th approximation (`0` if it never does). -/
private noncomputable def exists_const_limsup_KP_eq_KP_jump_trim_key
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (p : BitString) : ℕ :=
  sInf {s | exists_const_limsup_KP_eq_KP_jump_trim_H ev n s p}

/-- `q` precedes `p`: `q` halts, and `(key q, encode q) < (key p, encode p)` lexicographically. -/
private def exists_const_limsup_KP_eq_KP_jump_trim_prec
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (q p : BitString) : Prop :=
  (∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) ∧
    (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q <
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n p ∨
      (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q =
          exists_const_limsup_KP_eq_KP_jump_trim_key ev n p ∧
        Encodable.encode q < Encodable.encode p))

/-- `p` is accepted: it halts and no other prefix-comparable halting `q` precedes it. -/
private def exists_const_limsup_KP_eq_KP_jump_trim_acc
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (p : BitString) : Prop :=
  (∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s p) ∧
    ∀ q : BitString, q ≠ p → (q <+: p ∨ p <+: q) →
      ¬ exists_const_limsup_KP_eq_KP_jump_trim_prec ev n q p

/-- The output of `p` in the `n`-th approximation (the value at its first halting stage). -/
private noncomputable def exists_const_limsup_KP_eq_KP_jump_trim_out
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (p : BitString) : Option BitString :=
  ev n (exists_const_limsup_KP_eq_KP_jump_trim_key ev n p) p

open Classical in
/-- Total weight `∑ 2^{-|q|}` of the accepted `q` with output `x` in the `n`-th approximation. -/
private noncomputable def exists_const_limsup_KP_eq_KP_jump_trim_mass
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (x : BitString) : ℝ≥0∞ :=
  ∑' q : BitString,
    if exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q ∧
        exists_const_limsup_KP_eq_KP_jump_trim_out ev n q = some x
      then ((2 : ℝ≥0∞)⁻¹) ^ q.length else 0

open Classical in
/-- The same weight restricted to the accepted `q` with first halting stage `≤ s`. -/
private noncomputable def
    exists_const_limsup_KP_eq_KP_jump_trim_massAt
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (x : BitString) : ℝ≥0∞ :=
  ∑' q : BitString,
    if exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ s ∧
        exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q ∧
        exists_const_limsup_KP_eq_KP_jump_trim_out ev n q = some x
      then ((2 : ℝ≥0∞)⁻¹) ^ q.length else 0

open Classical in
/-- The candidate semimeasure: `m x (Nat.bits n) = mass n x`, and `0` off the range of `Nat.bits`.
-/
private noncomputable def exists_const_limsup_KP_eq_KP_jump_trim_m
    (ev : ℕ → ℕ → BitString → Option BitString) (x z : BitString) : ℝ≥0∞ :=
  if h : ∃ n, Nat.bits n = z then
    exists_const_limsup_KP_eq_KP_jump_trim_mass ev
      (Classical.choose h) x
  else 0

/-- Step 1 of the proof of
`exists_const_limsup_KP_eq_KP_jump_trim`:
the accepted programs of the `n`-th approximation are pairwise prefix-incomparable (of two
comparable halting programs the later one in the order `(key, encode)` is rejected). -/
private theorem exists_const_limsup_KP_eq_KP_jump_prefixfree
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (p q : BitString)
    (hp : exists_const_limsup_KP_eq_KP_jump_trim_acc ev n p)
    (hq : exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q)
    (hpq : p <+: q) : p = q := by
  by_contra hne
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have h1 := hq2 p hne (Or.inl hpq)
  have h2 := hp2 q (Ne.symm hne) (Or.inr hpq)
  simp only [exists_const_limsup_KP_eq_KP_jump_trim_prec,
    not_and, not_or] at h1 h2
  have a1 := h1 hp1
  have a2 := h2 hq1
  have hk : exists_const_limsup_KP_eq_KP_jump_trim_key ev n p =
      exists_const_limsup_KP_eq_KP_jump_trim_key ev n q := by
    omega
  have he : Encodable.encode p = Encodable.encode q := by
    have b1 := a1.2 hk
    have b2 := a2.2 hk.symm
    omega
  exact hne (Encodable.encode_injective he)

/-- Step 2 of the proof of
`exists_const_limsup_KP_eq_KP_jump_trim`:
the weights of the accepted programs of the `n`-th approximation, summed over all outputs, are at
most `1` (Kraft's inequality for the prefix-free set of accepted programs; uses step 1). -/
private theorem exists_const_limsup_KP_eq_KP_jump_kraft
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) :
    ∑' x : BitString,
      exists_const_limsup_KP_eq_KP_jump_trim_mass ev n x ≤ 1 := by
  classical
  unfold exists_const_limsup_KP_eq_KP_jump_trim_mass
  rw [ENNReal.tsum_comm]
  calc ∑' q : BitString, ∑' x : BitString,
        (if exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q ∧
          exists_const_limsup_KP_eq_KP_jump_trim_out ev n q = some x
          then ((2 : ℝ≥0∞)⁻¹) ^ q.length else 0)
      ≤ ∑' q : BitString,
        (if exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q
          then ((2 : ℝ≥0∞)⁻¹) ^ q.length else 0) := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        by_cases hacc :
          exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q
        · by_cases hy : ∃ y,
            exists_const_limsup_KP_eq_KP_jump_trim_out ev n q =
              some y
          · obtain ⟨y, hy⟩ := hy
            rw [tsum_eq_single y]
            · simp [hacc, hy]
            · intro x hx
              have : ¬ (some y = some x) := fun h => hx (Option.some.inj h).symm
              simp [hy, this]
          · simp only [not_exists] at hy
            simp [hy]
        · simp [hacc]
    _ ≤ 1 := by
        rw [ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun F => ?_
        rw [← Finset.sum_filter]
        have := finset_kraft_progWeight_le_one
          (F.filter fun q =>
            exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q)
          (fun p hp q hq hpq =>
            exists_const_limsup_KP_eq_KP_jump_prefixfree
              ev n p q (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2 hpq)
        simpa [progWeight, programLength] using this

/-- Step 3 of the proof of
`exists_const_limsup_KP_eq_KP_jump_trim`:
the stage-`s` masses are monotone in `s` and their supremum is the full mass. -/
private theorem exists_const_limsup_KP_eq_KP_jump_sup
    (ev : ℕ → ℕ → BitString → Option BitString) (n : ℕ) (x : BitString) :
    (∀ s, exists_const_limsup_KP_eq_KP_jump_trim_massAt ev n s x ≤
        exists_const_limsup_KP_eq_KP_jump_trim_massAt ev n (s + 1) x)
            ∧
    ⨆ s, exists_const_limsup_KP_eq_KP_jump_trim_massAt ev n s x =
      exists_const_limsup_KP_eq_KP_jump_trim_mass ev n x := by
  classical
  unfold exists_const_limsup_KP_eq_KP_jump_trim_massAt
    exists_const_limsup_KP_eq_KP_jump_trim_mass
  refine ⟨fun s => ENNReal.tsum_le_tsum fun q => ?_, le_antisymm (iSup_le fun s =>
    ENNReal.tsum_le_tsum fun q => ?_) ?_⟩
  · split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1.trans (Nat.le_succ s), h1.2⟩ h2
    · exact bot_le
    · exact le_rfl
  · split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.2 h2
    · exact bot_le
    · exact le_rfl
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    refine le_trans ?_ (le_iSup _ (F.sup fun q =>
      exists_const_limsup_KP_eq_KP_jump_trim_key ev n q))
    refine le_trans (Finset.sum_le_sum fun q hq => ?_) (ENNReal.sum_le_tsum F)
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨Finset.le_sup (f := fun q =>
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) hq,
        h1⟩ h2
    · exact bot_le
    · exact le_rfl

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
all bit strings of length at most `s`. -/
private def exists_const_limsup_KP_eq_KP_jump_approx_strs
    :
    ℕ → List BitString
  | 0 => [[]]
  | s + 1 => [] ::
      (exists_const_limsup_KP_eq_KP_jump_approx_strs
          s).flatMap
        (fun q => [false :: q, true :: q])

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
stage-`s` halting test (`|p| ≤ s` and `ev n s p` defined). -/
private def exists_const_limsup_KP_eq_KP_jump_approx_Hb
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (p : BitString) : Bool :=
  decide (p.length ≤ s) && (ev n s p).isSome

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
the first halting stage of `q`, computed by counting the stages `k ≤ s` at which `q` has not
yet halted (exact when `q` halts by stage `s`). -/
private def exists_const_limsup_KP_eq_KP_jump_approx_keyB
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (q : BitString) : ℕ :=
  (List.range (s + 1)).foldl (fun acc k => acc + bif
    exists_const_limsup_KP_eq_KP_jump_approx_Hb
      ev n k q then 0 else 1) 0

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
`q'` halts by stage `k` and precedes `q` (whose first halting stage is `k`) in the order
`(key, encode)`. -/
private def exists_const_limsup_KP_eq_KP_jump_approx_precB
    (ev : ℕ → ℕ → BitString → Option BitString) (n k : ℕ) (q' q : BitString) : Bool :=
  exists_const_limsup_KP_eq_KP_jump_approx_Hb ev n k q' &&
    (decide (exists_const_limsup_KP_eq_KP_jump_approx_keyB
        ev n k q' < k) ||
      (decide (exists_const_limsup_KP_eq_KP_jump_approx_keyB
          ev n k q' = k) && decide (Encodable.encode q' < Encodable.encode q)))

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
acceptance of `q` (assumed to halt by stage `s`), checked against all strings of length `≤ s`. -/
private def exists_const_limsup_KP_eq_KP_jump_approx_accB
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (q : BitString) : Bool :=
  (exists_const_limsup_KP_eq_KP_jump_approx_strs s).foldl
    (fun acc q' =>
      acc && (decide (q' = q) ||
        !(decide (q.take q'.length = q') || decide (q'.take q.length = q)) ||
        !exists_const_limsup_KP_eq_KP_jump_approx_precB
          ev n
          (exists_const_limsup_KP_eq_KP_jump_approx_keyB
            ev n s q) q' q)) true

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_approx`:
the dyadic numerator `∑ 2^(s-|q|)` over accepted `q` with output `x` and first halting stage
`≤ s`. -/
private def exists_const_limsup_KP_eq_KP_jump_approx_core
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (x : BitString) : ℕ :=
  (exists_const_limsup_KP_eq_KP_jump_approx_strs s).foldl
    (fun acc q => acc + bif
      (exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev n s q &&
        exists_const_limsup_KP_eq_KP_jump_approx_accB
          ev n s q &&
        decide (ev n
          (exists_const_limsup_KP_eq_KP_jump_approx_keyB
            ev n s q) q = some x)) then 2 ^ (s - q.length) else 0) 0

/-- Step 1 of the proof of
`exists_const_limsup_KP_eq_KP_jump_approx`:
`..._step4_approx_strs s` lists exactly the bit strings of length `≤ s`, without repetition,
and is computable in `s`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_strs :
    Computable
        exists_const_limsup_KP_eq_KP_jump_approx_strs ∧
      (∀ s q, q ∈
          exists_const_limsup_KP_eq_KP_jump_approx_strs s
              ↔
        q.length ≤ s) ∧
      (∀ s,
        (exists_const_limsup_KP_eq_KP_jump_approx_strs
          s).Nodup) := by
  refine ⟨?_, ?_, ?_⟩
  · have hstep : Primrec₂ (fun (_ : ℕ) (l : List BitString) =>
        ([] : BitString) :: l.flatMap (fun q => [false :: q, true :: q])) := by
      have hg : Primrec₂ (fun (p : ℕ × List BitString) (q : BitString) =>
          [false :: q, true :: q]) := by
        refine Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
          (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
            (Primrec.const [])) |>.to₂
      exact (Primrec.list_cons.comp (Primrec.const []) (Primrec.list_flatMap Primrec.snd hg)).to₂
    have h := (Primrec.nat_rec₁ ([[]] : List BitString) hstep).to_comp
    refine h.of_eq fun s => ?_
    induction s with
    | zero => rfl
    | succ s ih =>
      change _ :: _ = _ :: _
      rw [← ih]
  · intro s
    induction s with
    | zero =>
      intro q
      simp [exists_const_limsup_KP_eq_KP_jump_approx_strs]
    | succ s ih =>
      intro q
      simp only [exists_const_limsup_KP_eq_KP_jump_approx_strs,
        List.mem_cons, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      cases q with
      | nil => simp
      | cons b q =>
        constructor
        · rintro (h | ⟨q', hq', h⟩)
          · exact absurd h (by simp)
          · rcases h with h | h
            · rw [List.cons.injEq] at h
              obtain ⟨-, h2⟩ := h
              have := (ih q').1 hq'
              simpa [← h2] using this
            · rw [List.cons.injEq] at h
              obtain ⟨-, h2⟩ := h
              have := (ih q').1 hq'
              simpa [← h2] using this
        · intro h
          right
          refine ⟨q, (ih q).2 (by simpa using h), ?_⟩
          cases b <;> simp
  · intro s
    induction s with
    | zero => simp [exists_const_limsup_KP_eq_KP_jump_approx_strs]
    | succ s ih =>
      simp only [exists_const_limsup_KP_eq_KP_jump_approx_strs]
      refine List.nodup_cons.2 ⟨?_, ?_⟩
      · simp
      · refine List.nodup_flatMap.2 ⟨fun q _ => by simp, ?_⟩
        refine List.Pairwise.imp (fun {a b} hab => ?_) ih
        change List.Disjoint [false :: a, true :: a] [false :: b, true :: b]
        rw [List.disjoint_left]
        intro c hc hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hc'
        rcases hc with rfl | rfl <;> rcases hc' with h | h <;>
          simp_all [List.cons.injEq]

/-- Step 2 of the proof of
`exists_const_limsup_KP_eq_KP_jump_approx`:
a computable partial inverse of `Nat.bits`: computable `f : BitString → ℕ` and
`ok : BitString → Bool` with `ok (Nat.bits n) = true`, `f (Nat.bits n) = n`, and `ok z = false`
for `z` outside the range of `Nat.bits`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_inv :
    ∃ (f : BitString → ℕ) (ok : BitString → Bool), Computable f ∧ Computable ok ∧
      (∀ n, ok (Nat.bits n) = true ∧ f (Nat.bits n) = n) ∧
      (∀ z, (¬ ∃ n, Nat.bits n = z) → ok z = false) := by
  have hnum : Computable (fun v : BitString => bitsToNat v) := bitsToNat_primrec.to_comp
  have heqb : Computable₂ (fun x y : BitString => decide (x = y)) :=
    (PrimrecRel.decide (Primrec.eq (α := BitString))).to_comp
  have htest : Computable (fun v : BitString => decide (Nat.bits (bitsToNat v) = v)) :=
    Computable₂.comp heqb (natBits_computable.comp hnum) Computable.id
  refine ⟨fun v => bitsToNat v, fun v => decide (Nat.bits (bitsToNat v) = v), hnum, htest,
    fun n => ⟨?_, bitsToNat_bits n⟩, fun z hz => ?_⟩
  · simp [bitsToNat_bits]
  · simp only [decide_eq_false_iff_not]
    intro h
    exact hz ⟨_, h⟩

/-- Step 3 of the proof of
`exists_const_limsup_KP_eq_KP_jump_approx`:
`(n, s, x) ↦ ..._step4_approx_core ev n s x` is computable when `ev` is (a composition of
bounded folds over the computable list `..._strs s`, with `ev`, `Encodable.encode`, `List.take`,
`decide` on equality and `<`). -/
private theorem exists_const_limsup_KP_eq_KP_jump_core_computable
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hev : Computable (fun r : ℕ × ℕ × BitString => ev r.1 r.2.1 r.2.2)) :
    Computable (fun r : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_core
        ev r.1 r.2.1 r.2.2) := by
  classical
  have hand : Computable₂ (fun a b : Bool => a && b) := (Primrec.dom_bool₂ _).to_comp
  have hor : Computable₂ (fun a b : Bool => a || b) := (Primrec.dom_bool₂ _).to_comp
  have hnot : Computable (fun a : Bool => !a) := (Primrec.dom_bool _).to_comp
  have heqN : Computable₂ (fun a b : ℕ => decide (a = b)) := Primrec.eq.decide.to_comp
  have hltN : Computable₂ (fun a b : ℕ => decide (a < b)) := Primrec.nat_lt.decide.to_comp
  have hleN : Computable₂ (fun a b : ℕ => decide (a ≤ b)) := Primrec.nat_le.decide.to_comp
  have heqB : Computable₂ (fun a b : BitString => decide (a = b)) :=
    Primrec.eq.decide.to_comp
  have heqO : Computable₂ (fun a b : Option BitString => decide (a = b)) :=
    Primrec.eq.decide.to_comp
  have hadd : Computable₂ (fun a b : ℕ => a + b) := Primrec.nat_add.to_comp
  have hsub : Computable₂ (fun a b : ℕ => a - b) := Primrec.nat_sub.to_comp
  have hlen : Computable (fun q : BitString => q.length) := Computable.list_length
  have htake : Computable₂ (fun (n : ℕ) (q : BitString) => q.take n) :=
    Primrec.list_take.to_comp
  have hpow : Computable (fun m : ℕ => 2 ^ m) := primrec_two_pow_aux.to_comp
  have henc : Computable (fun q : BitString => Encodable.encode q) := Computable.encode
  have hstrs :=
    (exists_const_limsup_KP_eq_KP_jump_strs).1
  have hHb : Computable (fun r : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_Hb
        ev r.1 r.2.1 r.2.2) :=
    (hand.comp (hleN.comp (hlen.comp (Computable.snd.comp Computable.snd))
      (Computable.fst.comp Computable.snd))
      (Primrec.option_isSome.to_comp.comp hev)).of_eq (fun r => rfl)
  have hkey : Computable (fun r : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_keyB
        ev r.1 r.2.1 r.2.2) := by
    refine (computable_list_foldl
      (f := fun a : ℕ × ℕ × BitString => List.range (a.2.1 + 1))
      (g := fun _ => (0 : ℕ))
      (h := fun (a : ℕ × ℕ × BitString) (u : ℕ × ℕ) =>
        u.1 + bif
          exists_const_limsup_KP_eq_KP_jump_approx_Hb
            ev a.1 u.2 a.2.2 then 0 else 1)
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.fst.comp Primrec.snd))).to_comp (Computable.const 0) ?_).of_eq (fun r => rfl)
    change Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × ℕ) =>
      v.2.1 + bif
        exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev v.1.1 v.2.2 v.1.2.2 then 0 else 1)
    have hn : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × ℕ) => v.1.1) :=
      Computable.fst.comp Computable.fst
    have hk : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × ℕ) => v.2.2) :=
      Computable.snd.comp Computable.snd
    have hq : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × ℕ) => v.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hac : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × ℕ) => v.2.1) :=
      Computable.fst.comp Computable.snd
    have h1 := hHb.comp (hn.pair (hk.pair hq))
    exact hadd.comp hac (Computable.cond h1 (Computable.const 0) (Computable.const 1))
  have hprec : Computable (fun r : ℕ × ℕ × BitString × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_precB
        ev r.1 r.2.1 r.2.2.1 r.2.2.2) := by
    have hn : Computable (fun r : ℕ × ℕ × BitString × BitString => r.1) := Computable.fst
    have hk : Computable (fun r : ℕ × ℕ × BitString × BitString => r.2.1) :=
      Computable.fst.comp Computable.snd
    have hq' : Computable (fun r : ℕ × ℕ × BitString × BitString => r.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.snd)
    have hq : Computable (fun r : ℕ × ℕ × BitString × BitString => r.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    have h1 := hHb.comp (hn.pair (hk.pair hq'))
    have h2 := hkey.comp (hn.pair (hk.pair hq'))
    exact (hand.comp h1 (hor.comp (hltN.comp h2 hk)
      (hand.comp (heqN.comp h2 hk) (hltN.comp (henc.comp hq') (henc.comp hq))))).of_eq
        (fun r => rfl)
  have hacc : Computable (fun r : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_accB
        ev r.1 r.2.1 r.2.2) := by
    refine (computable_list_foldl
      (f := fun a : ℕ × ℕ × BitString =>
        exists_const_limsup_KP_eq_KP_jump_approx_strs
          a.2.1)
      (g := fun _ => true)
      (h := fun (a : ℕ × ℕ × BitString) (u : Bool × BitString) =>
        u.1 && (decide (u.2 = a.2.2) ||
          !(decide (a.2.2.take u.2.length = u.2) || decide (u.2.take a.2.2.length = a.2.2)) ||
          !exists_const_limsup_KP_eq_KP_jump_approx_precB
            ev a.1
            (exists_const_limsup_KP_eq_KP_jump_approx_keyB
              ev a.1 a.2.1 a.2.2) u.2 a.2.2))
      (hstrs.comp (Computable.fst.comp Computable.snd)) (Computable.const true) ?_).of_eq
        (fun r => rfl)
    change Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) =>
      v.2.1 && (decide (v.2.2 = v.1.2.2) ||
        !(decide (v.1.2.2.take v.2.2.length = v.2.2) ||
          decide (v.2.2.take v.1.2.2.length = v.1.2.2)) ||
        !exists_const_limsup_KP_eq_KP_jump_approx_precB
          ev v.1.1
          (exists_const_limsup_KP_eq_KP_jump_approx_keyB
            ev v.1.1 v.1.2.1 v.1.2.2) v.2.2 v.1.2.2))
    have hn : Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) => v.1.1) :=
      Computable.fst.comp Computable.fst
    have hs : Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) => v.1.2.1) :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hq : Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) => v.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hq' : Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) => v.2.2) :=
      Computable.snd.comp Computable.snd
    have hac : Computable (fun v : (ℕ × ℕ × BitString) × (Bool × BitString) => v.2.1) :=
      Computable.fst.comp Computable.snd
    have hk := hkey.comp (hn.pair (hs.pair hq))
    have hp := hprec.comp (hn.pair (hk.pair (hq'.pair hq)))
    refine hand.comp hac (hor.comp (hor.comp (heqB.comp hq' hq) (hnot.comp
      (hor.comp (heqB.comp (htake.comp (hlen.comp hq') hq) hq')
        (heqB.comp (htake.comp (hlen.comp hq) hq') hq)))) (hnot.comp hp))
  refine (computable_list_foldl
    (f := fun a : ℕ × ℕ × BitString =>
      exists_const_limsup_KP_eq_KP_jump_approx_strs
        a.2.1)
    (g := fun _ => (0 : ℕ))
    (h := fun (a : ℕ × ℕ × BitString) (u : ℕ × BitString) =>
      u.1 + bif
        (exists_const_limsup_KP_eq_KP_jump_approx_Hb
            ev a.1 a.2.1 u.2 &&
          exists_const_limsup_KP_eq_KP_jump_approx_accB
            ev a.1 a.2.1 u.2 &&
          decide (ev a.1
            (exists_const_limsup_KP_eq_KP_jump_approx_keyB
              ev a.1 a.2.1 u.2) u.2 = some a.2.2)) then 2 ^ (a.2.1 - u.2.length) else 0)
    (hstrs.comp (Computable.fst.comp Computable.snd)) (Computable.const 0) ?_).of_eq
      (fun r => rfl)
  change Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) =>
    v.2.1 + bif
      (exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev v.1.1 v.1.2.1 v.2.2 &&
        exists_const_limsup_KP_eq_KP_jump_approx_accB
          ev v.1.1 v.1.2.1 v.2.2 &&
        decide (ev v.1.1
          (exists_const_limsup_KP_eq_KP_jump_approx_keyB
            ev v.1.1 v.1.2.1 v.2.2) v.2.2 = some v.1.2.2)) then
          2 ^ (v.1.2.1 - v.2.2.length) else 0)
  have hn : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) => v.1.1) :=
    Computable.fst.comp Computable.fst
  have hs : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) => v.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hx : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) => v.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hq : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) => v.2.2) :=
    Computable.snd.comp Computable.snd
  have hac : Computable (fun v : (ℕ × ℕ × BitString) × (ℕ × BitString) => v.2.1) :=
    Computable.fst.comp Computable.snd
  have h1 := hHb.comp (hn.pair (hs.pair hq))
  have h2 := hacc.comp (hn.pair (hs.pair hq))
  have h3 := hkey.comp (hn.pair (hs.pair hq))
  have h4 := hev.comp (hn.pair (h3.pair hq))
  refine hadd.comp hac (Computable.cond (hand.comp (hand.comp h1 h2)
    (heqO.comp h4 ((Computable.option_some.comp hx)))) ?_ (Computable.const 0))
  exact hpow.comp (hsub.comp hs (hlen.comp hq))

/-- Step 1 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
a left fold with `&&` is `true` iff the start value and all tested values are `true`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_foldl_and
    {α : Type} (l : List α) (f : α → Bool) (b : Bool) :
    l.foldl (fun acc x => acc && f x) b = true ↔ b = true ∧ ∀ x ∈ l, f x = true := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

/-- Step 2 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
a left fold with `+` is the start value plus the sum. -/
private theorem exists_const_limsup_KP_eq_KP_jump_foldl_add
    {α : Type} (l : List α) (g : α → ℕ) (a : ℕ) :
    l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    omega

/-- Step 3 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
halting is upward closed in the stage. -/
private theorem exists_const_limsup_KP_eq_KP_jump_H_mono
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n s s' : ℕ) (q : BitString) (hss : s ≤ s')
    (h : exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) :
    exists_const_limsup_KP_eq_KP_jump_trim_H ev n s' q := by
  obtain ⟨hl, hs⟩ := h
  refine ⟨hl.trans hss, ?_⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hs
  rw [Option.isSome_iff_exists]
  exact ⟨a, hmono n s s' q a hss ha⟩

/-- Step 4 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
for a halting `q`, `H k q` iff `key q ≤ k`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_key_spec
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n : ℕ) (q : BitString)
    (hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) :
    exists_const_limsup_KP_eq_KP_jump_trim_H ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q ∧
      ∀ k, exists_const_limsup_KP_eq_KP_jump_trim_H ev n k q ↔
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ k := by
  have h1 : exists_const_limsup_KP_eq_KP_jump_trim_H ev n
      (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q := by
    unfold exists_const_limsup_KP_eq_KP_jump_trim_key
    exact Nat.sInf_mem
      (s := {s | exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q})
          hh
  refine ⟨h1, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · unfold exists_const_limsup_KP_eq_KP_jump_trim_key
    exact Nat.sInf_le
      (s := {s | exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q})
          hk
  · exact
      exists_const_limsup_KP_eq_KP_jump_H_mono
        ev hmono n _ _ q hk h1

/-- Step 5 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
recursion for `keyB`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_keyB_succ
    (ev : ℕ → ℕ → BitString → Option BitString) (n s : ℕ) (q : BitString) :
    exists_const_limsup_KP_eq_KP_jump_approx_keyB ev n (s
        + 1) q =
      exists_const_limsup_KP_eq_KP_jump_approx_keyB ev n s
          q +
        bif exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev n (s + 1) q then 0 else 1 := by
  unfold exists_const_limsup_KP_eq_KP_jump_approx_keyB
  rw [List.range_succ (n := s + 1), List.foldl_append]
  rfl

/-- Step 6 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
`keyB n s q = min (key q) (s+1)` for halting `q`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_keyB
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n : ℕ) (q : BitString)
    (hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q)
    (s : ℕ) :
    exists_const_limsup_KP_eq_KP_jump_approx_keyB ev n s q
        =
      min (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) (s + 1)
          := by
  obtain ⟨-, hspec⟩ :=
    exists_const_limsup_KP_eq_KP_jump_key_spec
      ev hmono n q hh
  have hHb : ∀ k,
      exists_const_limsup_KP_eq_KP_jump_approx_Hb ev n k q
          = true ↔
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ k := fun
            k => by
    rw [← hspec k]
    simp [exists_const_limsup_KP_eq_KP_jump_approx_Hb,
      exists_const_limsup_KP_eq_KP_jump_trim_H]
  induction s with
  | zero =>
    have : exists_const_limsup_KP_eq_KP_jump_approx_keyB
        ev n 0 q =
        0 + bif exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev n 0 q then 0 else 1 := by
      unfold exists_const_limsup_KP_eq_KP_jump_approx_keyB
      rfl
    rw [this]
    by_cases h : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤
        0
    · simp [(hHb 0).2 h]; omega
    · have : ¬ exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev n 0 q = true := fun h' => h ((hHb 0).1 h')
      simp [this]; omega
  | succ s ih =>
    rw [exists_const_limsup_KP_eq_KP_jump_keyB_succ,
      ih]
    by_cases h : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤
        s + 1
    · simp [(hHb (s + 1)).2 h]; omega
    · have : ¬ exists_const_limsup_KP_eq_KP_jump_approx_Hb
          ev n (s + 1) q = true := fun h' => h ((hHb (s + 1)).1 h')
      simp [this]; omega

/-- Step 7 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
`keyB n s q = key q` once `q` halts by stage `s`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_keyB_eq
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n s : ℕ) (q : BitString)
    (hs : exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) :
    exists_const_limsup_KP_eq_KP_jump_approx_keyB ev n s q
        =
      exists_const_limsup_KP_eq_KP_jump_trim_key ev n q := by
  have hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q :=
    ⟨s, hs⟩
  have := ((exists_const_limsup_KP_eq_KP_jump_key_spec
    ev hmono n q hh).2 s).1 hs
  rw [exists_const_limsup_KP_eq_KP_jump_keyB
    ev hmono n q hh]
  omega

/-- Step 8 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
`precB` at `k = key q` is `prec`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_precB_iff
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n : ℕ) (q' q : BitString) :
    exists_const_limsup_KP_eq_KP_jump_approx_precB ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q' q =
            true ↔
      exists_const_limsup_KP_eq_KP_jump_trim_prec ev n q' q := by
  unfold exists_const_limsup_KP_eq_KP_jump_approx_precB
    exists_const_limsup_KP_eq_KP_jump_trim_prec
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : exists_const_limsup_KP_eq_KP_jump_trim_H ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q' := by
      simpa [exists_const_limsup_KP_eq_KP_jump_approx_Hb,
        exists_const_limsup_KP_eq_KP_jump_trim_H] using h1
    have hh' : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s
        q' :=
      ⟨_, h1'⟩
    have hk :=
      exists_const_limsup_KP_eq_KP_jump_keyB_eq
        ev hmono n _ q' h1'
    refine ⟨hh', ?_⟩
    rw [hk] at h2
    simpa using h2
  · rintro ⟨hh', h2⟩
    have hle : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q' ≤
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n q := by omega
    have h1' : exists_const_limsup_KP_eq_KP_jump_trim_H ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q' :=
      ((exists_const_limsup_KP_eq_KP_jump_key_spec
        ev hmono n q' hh').2 _).2 hle
    have hk :=
      exists_const_limsup_KP_eq_KP_jump_keyB_eq
        ev hmono n _ q' h1'
    have h1 : exists_const_limsup_KP_eq_KP_jump_approx_Hb
        ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q' = true
            := by
      simpa [exists_const_limsup_KP_eq_KP_jump_approx_Hb,
        exists_const_limsup_KP_eq_KP_jump_trim_H] using h1'
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨h1, ?_⟩
    rw [hk]
    simpa using h2

/-- Step 9 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
for `q` halting by stage `s`, `accB n s q` is `acc`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_accB_iff
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n s : ℕ) (q : BitString)
    (hs : exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) :
    exists_const_limsup_KP_eq_KP_jump_approx_accB ev n s q
        = true ↔
      exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q := by
  have hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q :=
    ⟨s, hs⟩
  obtain ⟨hKH, hspec⟩ :=
    exists_const_limsup_KP_eq_KP_jump_key_spec
      ev hmono n q hh
  have hKs : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ s :=
    (hspec s).1 hs
  have hkB :=
    exists_const_limsup_KP_eq_KP_jump_keyB_eq
      ev hmono n s q hs
  obtain ⟨-, hmem, -⟩ :=
    exists_const_limsup_KP_eq_KP_jump_strs
  unfold exists_const_limsup_KP_eq_KP_jump_approx_accB
  rw [exists_const_limsup_KP_eq_KP_jump_foldl_and]
  simp only [true_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, hkB]
  unfold exists_const_limsup_KP_eq_KP_jump_trim_acc
  constructor
  · intro h
    refine ⟨hh, fun q' hne hcmp hprec => ?_⟩
    have hmem' : q' ∈
        exists_const_limsup_KP_eq_KP_jump_approx_strs s :=
            by
      obtain ⟨⟨s', hs'⟩, hlt⟩ := hprec
      have h1 :=
        exists_const_limsup_KP_eq_KP_jump_key_spec
          ev hmono n q' ⟨s', hs'⟩
      have h2 := h1.1.1
      have hlt' : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q'
          ≤
          exists_const_limsup_KP_eq_KP_jump_trim_key ev n q := by
        omega
      exact (hmem s q').2 (by omega)
    have := h q' hmem'
    rcases this with (h1 | h1) | h1
    · exact hne h1
    · exfalso
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h1
      rcases hcmp with hc | hc
      · exact h1.1 (List.prefix_iff_eq_take.1 hc).symm
      · exact h1.2 (List.prefix_iff_eq_take.1 hc).symm
    · have := (exists_const_limsup_KP_eq_KP_jump_precB_iff
        ev hmono n q' q).2 hprec
      simp [this] at h1
  · rintro ⟨-, h⟩ q' hq'
    by_cases hne : q' = q
    · exact Or.inl (Or.inl hne)
    by_cases hc : q.take q'.length = q' ∨ q'.take q.length = q
    · right
      have : ¬ exists_const_limsup_KP_eq_KP_jump_trim_prec ev n q' q
          := by
        refine h q' hne ?_
        rcases hc with hc | hc
        · left; exact List.prefix_iff_eq_take.2 hc.symm
        · right; exact List.prefix_iff_eq_take.2 hc.symm
      rw [← exists_const_limsup_KP_eq_KP_jump_precB_iff
        ev hmono n q' q] at this
      simpa using this
    · refine Or.inl (Or.inr ?_)
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact not_or.1 hc

/-- Step 10 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
the test inside `core` holds iff `key q ≤ s`, `q` is accepted and `out q = some x`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_cond_iff
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (n s : ℕ) (q x : BitString) :
    (exists_const_limsup_KP_eq_KP_jump_approx_Hb ev n s q
        &&
        exists_const_limsup_KP_eq_KP_jump_approx_accB ev n
            s q &&
        decide (ev n
          (exists_const_limsup_KP_eq_KP_jump_approx_keyB
            ev n s q) q = some x)) = true ↔
      (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ s ∧
        exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q ∧
        exists_const_limsup_KP_eq_KP_jump_trim_out ev n q = some x)
            := by
  have hbH : exists_const_limsup_KP_eq_KP_jump_approx_Hb
      ev n s q = true ↔
      exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q := by
    simp [exists_const_limsup_KP_eq_KP_jump_approx_Hb,
      exists_const_limsup_KP_eq_KP_jump_trim_H]
  simp only [Bool.and_eq_true, decide_eq_true_eq, hbH]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q
        :=
      ⟨s, h1⟩
    refine ⟨((exists_const_limsup_KP_eq_KP_jump_key_spec
      ev hmono n q hh).2 s).1 h1,
      (exists_const_limsup_KP_eq_KP_jump_accB_iff
        ev hmono n s q h1).1 h2, ?_⟩
    rw [exists_const_limsup_KP_eq_KP_jump_keyB_eq
      ev hmono n s q h1] at h3
    exact h3
  · rintro ⟨h1, h2, h3⟩
    have hh : ∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q
        :=
      h2.1
    have hH := ((exists_const_limsup_KP_eq_KP_jump_key_spec
      ev hmono n q hh).2 s).2 h1
    refine ⟨⟨hH,
      (exists_const_limsup_KP_eq_KP_jump_accB_iff
        ev hmono n s q hH).2 h2⟩, ?_⟩
    rw [exists_const_limsup_KP_eq_KP_jump_keyB_eq
      ev hmono n s q hH]
    exact h3

/-- Step 11 of the proof of
`exists_const_limsup_KP_eq_KP_jump_core_eq`:
`2^(s-l) / 2^s = (2⁻¹)^l` for `l ≤ s`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_pow
    (s l : ℕ) (h : l ≤ s) :
    ((2 ^ (s - l) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ s)⁻¹ = ((2 : ℝ≥0∞)⁻¹) ^ l := by
  have h2 : (2 : ℝ≥0∞) ^ s = 2 ^ (s - l) * 2 ^ l := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have h0 : (2 : ℝ≥0∞) ^ (s - l) ≠ 0 := by simp
  have ht : (2 : ℝ≥0∞) ^ (s - l) ≠ ⊤ := by simp
  rw [Nat.cast_pow, Nat.cast_ofNat, h2, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul, ENNReal.inv_pow]

/-- Step 4 of the proof of
`exists_const_limsup_KP_eq_KP_jump_approx`:
for `t`-monotone `ev`, the numerator `..._step4_approx_core ev n s x` over `2^s` is the stage-`s`
mass `massAt n s x` (the tsum over accepted `q` with `key q ≤ s` is the finite sum over the strings
of length `≤ s`; `key q` is read off from `..._keyB` and acceptance of `q` only involves strings
of length `≤ key q ≤ s`). -/
private theorem exists_const_limsup_KP_eq_KP_jump_core_eq
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (s n : ℕ) (x : BitString) :
    dyadicValue
        (exists_const_limsup_KP_eq_KP_jump_approx_core
          ev n s x) s =
      exists_const_limsup_KP_eq_KP_jump_trim_massAt ev n s x := by
  classical
  obtain ⟨-, hmem, hnd⟩ :=
    exists_const_limsup_KP_eq_KP_jump_strs
  have hsum : ∀ (F : BitString → ℝ≥0∞),
      (∀ q ∉ (exists_const_limsup_KP_eq_KP_jump_approx_strs s).toFinset,
        F q = 0) →
      ∑' q, F q =
        ((exists_const_limsup_KP_eq_KP_jump_approx_strs
            s).map
          F).sum := by
    intro F hF
    rw [tsum_eq_sum hF, List.sum_toFinset F (hnd s)]
  unfold dyadicValue
    exists_const_limsup_KP_eq_KP_jump_trim_massAt
  refine Eq.trans ?_ (hsum _ ?_).symm
  · unfold exists_const_limsup_KP_eq_KP_jump_approx_core
    rw [exists_const_limsup_KP_eq_KP_jump_foldl_add,
      zero_add, Nat.cast_list_sum, div_eq_mul_inv, ← List.sum_map_mul_right, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    have hlen := (hmem s q).1 hq
    have hiff :=
      exists_const_limsup_KP_eq_KP_jump_cond_iff
        ev hmono n s q x
    simp only [Function.comp_apply, Bool.cond_eq_ite]
    by_cases hc :
        exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤ s ∧
        exists_const_limsup_KP_eq_KP_jump_trim_acc ev n q ∧
        exists_const_limsup_KP_eq_KP_jump_trim_out ev n q = some x
    · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc)]
      exact
        exists_const_limsup_KP_eq_KP_jump_pow
          s q.length hlen
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h))]
      simp
  · intro q hq
    have hlen : ¬ q.length ≤ s := fun h => hq (List.mem_toFinset.2 ((hmem s q).2 h))
    rw [ite_eq_right]
    rintro ⟨hk, hacc, -⟩
    obtain ⟨⟨s', hs'⟩, -⟩ := hacc
    exact hlen
      (((exists_const_limsup_KP_eq_KP_jump_key_spec
        ev hmono n q ⟨s', hs'⟩).1.1).trans hk)

/-- Step 4 of the proof of
`exists_const_limsup_KP_eq_KP_jump_trim`:
the stage-`s` masses have a computable dyadic numerator: there is a computable
`approx : ℕ → BitString → BitString → ℕ` with `approx s x (Nat.bits n) / 2^s = massAt n s x` and
`approx s x z = 0` for `z` outside the range of `Nat.bits`.

Proof idea: for `p` of length `≤ s` (finitely many), `key p ≤ s` and acceptance of `p` only involve
`ev n s' q` for `s' ≤ s` and prefix-comparable `q` of length `≤ s` (a competitor preceding `p` has
`|q| ≤ key q ≤ key p ≤ s`), hence are decidable from `ev` by bounded search. Put
`approx s x (Nat.bits n) = ∑ 2^{s-|q|}` over such accepted `q` with output `x`, and `0` for other
conditions (`Nat.bits` is injective, with computable partial inverse). -/
private theorem exists_const_limsup_KP_eq_KP_jump_approx
    (ev : ℕ → ℕ → BitString → Option BitString)
    (hev : Computable (fun r : ℕ × ℕ × BitString => ev r.1 r.2.1 r.2.2))
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a) :
    ∃ approx : ℕ → BitString → BitString → ℕ,
      Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2) ∧
      (∀ s x n, dyadicValue (approx s x (Nat.bits n)) s =
        exists_const_limsup_KP_eq_KP_jump_trim_massAt ev n s x) ∧
      (∀ s x z, (¬ ∃ n, Nat.bits n = z) → approx s x z = 0) := by
  obtain ⟨f, ok, hf, hok, hfok, hnok⟩ :=
    exists_const_limsup_KP_eq_KP_jump_inv
  have hcore :=
    exists_const_limsup_KP_eq_KP_jump_core_computable
      ev hev
  refine ⟨fun s x z => bif ok z then
    exists_const_limsup_KP_eq_KP_jump_approx_core
      ev (f z) s x else 0, ?_, ?_, ?_⟩
  · have h2 : Computable (fun p : ℕ × BitString × BitString => (f p.2.2, p.1, p.2.1)) :=
      (hf.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.fst.pair (Computable.fst.comp Computable.snd))
    have h3 := hcore.comp h2
    have h4 : Computable (fun p : ℕ × BitString × BitString => ok p.2.2) :=
      hok.comp (Computable.snd.comp Computable.snd)
    exact Computable.cond h4 h3 (Computable.const 0)
  · intro s x n
    simp only [(hfok n).1, (hfok n).2, Bool.cond_true]
    exact
      exists_const_limsup_KP_eq_KP_jump_core_eq
        ev hmono s n x
  · intro s x z hz
    simp [hnok z hz]

/-- Step 5 of the proof of
`exists_const_limsup_KP_eq_KP_jump_trim`:
if `evT t p = some x` and `n` is large (stabilization for `T = max t |p|`), then `p` is accepted in
the `n`-th approximation with output `x`, so `2^{-|p|} ≤ mass n x`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_lower
    (ev : ℕ → ℕ → BitString → Option BitString) (evT : ℕ → BitString → Option BitString)
    (hmonoT : ∀ t t' p a, t ≤ t' → evT t p = some a → evT t' p = some a)
    (hpf : ∀ t p q a b, evT t p = some a → evT t q = some b → p <+: q → p = q)
    (hstab : ∀ T, ∃ N, ∀ n ≥ N, ∀ t ≤ T, ∀ p : BitString, p.length ≤ T → ev n t p = evT t p)
    (t : ℕ) (p x : BitString) (h : evT t p = some x) :
    ∀ᶠ n in Filter.atTop, ((2 : ℝ≥0∞)⁻¹) ^ p.length ≤
      exists_const_limsup_KP_eq_KP_jump_trim_mass ev n x := by
  classical
  obtain ⟨N, hN⟩ := hstab (max t p.length)
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hTt : t ≤ max t p.length := le_max_left _ _
  have hTp : p.length ≤ max t p.length := le_max_right _ _
  have hpT : evT (max t p.length) p = some x := hmonoT t _ p x hTt h
  have hq_halt : ∀ q : BitString,
      (∃ s, exists_const_limsup_KP_eq_KP_jump_trim_H ev n s q) →
      exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤
        max t p.length →
      ∃ b, evT (max t p.length) q = some b ∧
        exists_const_limsup_KP_eq_KP_jump_trim_out ev n q =
          some b := by
    intro q hq hkT
    have hHk : exists_const_limsup_KP_eq_KP_jump_trim_H ev n
        (exists_const_limsup_KP_eq_KP_jump_trim_key ev n q) q :=
      Nat.sInf_mem hq
    obtain ⟨hlen, hsome⟩ := hHk
    have heq := hN n hn _ hkT q (hlen.trans hkT)
    rw [heq] at hsome
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨b, hmonoT _ _ q b hkT hb, ?_⟩
    unfold exists_const_limsup_KP_eq_KP_jump_trim_out
    rw [heq]
    exact hb
  have hpH : ∃ s,
      exists_const_limsup_KP_eq_KP_jump_trim_H ev n s p := by
    refine ⟨max t p.length, hTp, ?_⟩
    rw [hN n hn _ le_rfl p hTp, hpT]
    rfl
  have hpk : exists_const_limsup_KP_eq_KP_jump_trim_key ev n p ≤
      max t p.length := by
    apply Nat.sInf_le
    refine ⟨hTp, ?_⟩
    rw [hN n hn _ le_rfl p hTp, hpT]
    rfl
  obtain ⟨b, hb, hbout⟩ := hq_halt p hpH hpk
  have hbx : b = x := by
    rw [hpT] at hb
    exact (Option.some.inj hb).symm
  subst hbx
  have hacc : exists_const_limsup_KP_eq_KP_jump_trim_acc ev n p := by
    refine ⟨hpH, fun q hqne hcomp hprec => ?_⟩
    obtain ⟨hqH, hlt⟩ := hprec
    have hkq : exists_const_limsup_KP_eq_KP_jump_trim_key ev n q ≤
        max t p.length := by omega
    obtain ⟨c, hc, -⟩ := hq_halt q hqH hkq
    rcases hcomp with h' | h'
    · exact hqne (hpf _ q p c b hc hb h')
    · exact hqne (hpf _ p q b c hb hc h').symm
  unfold exists_const_limsup_KP_eq_KP_jump_trim_mass
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum p)
  rw [ite_eq_left ⟨hacc, hbout⟩]

/-- Step 2 of the proof of `exists_const_limsup_KP_eq_KP_jump_approx_semimeasure`:
trimming a family of step-bounded computations to prefix-free sets and summing the weights.

Let `ev n t p` be a computable, `t`-monotone family of step-bounded runs (stage parameter `n`) and
`evT t p` a `t`-monotone family of runs that is prefix-free (two halting programs at the same
time that are prefix-comparable are equal), with `ev n t p = evT t p` for `n` large (depending on
a bound `T ≥ t, |p|`). Then there is a lower-semicomputable conditional semimeasure `m` with
`m x (Nat.bits n) ≥ 2^{-|p|}` for large `n` whenever `evT t p = some x`.

Proof idea: fix `n`. Say `p` halts at stage `s` if `|p| ≤ s` and `ev n s p ≠ none` (monotone in
`s`); let `key p` be the least such `s`. Accept `p` if it halts and no other halting `q`
comparable with `p` (one is a prefix of the other) has `(key q, q) < (key p, p)` (lexicographic
order on the stage, then on an encoding). Accepted programs are pairwise prefix-incomparable (of
two comparable halting programs the later one is rejected), so by Kraft the weights `∑ 2^{-|q|}`
over accepted `q` sum, over all outputs, to at most `1`. Put
`m x (Nat.bits n) = ∑_{accepted q with output x} 2^{-|q|}` and `m x z = 0` for `z` not of the
form `Nat.bits n` (`Nat.bits` is injective: `bits_injective`). The stage-`s` approximation sums over
programs of length `≤ s` accepted by looking at stages `≤ s` only (acceptance of `p` depends only
on programs with key `≤ key p`); the numerators `∑ 2^{s-|q|}` are monotone in `s` and computable
since `ev` is. If `evT t p = some x`, take `T = max t |p|` and `N` from the stabilization: for
`n ≥ N`, `p` has the same key and output under `ev n` as under `evT`, and every `q` with key
`≤ key p` halts under `evT` too (at the same time), so it is prefix-incomparable with `p`
unless `q = p` by prefix-freeness: `p` is accepted. -/
private theorem exists_const_limsup_KP_eq_KP_jump_trim
    (ev : ℕ → ℕ → BitString → Option BitString) (evT : ℕ → BitString → Option BitString)
    (hev : Computable (fun r : ℕ × ℕ × BitString => ev r.1 r.2.1 r.2.2))
    (hmono : ∀ n t t' p a, t ≤ t' → ev n t p = some a → ev n t' p = some a)
    (hmonoT : ∀ t t' p a, t ≤ t' → evT t p = some a → evT t' p = some a)
    (hpf : ∀ t p q a b, evT t p = some a → evT t q = some b → p <+: q → p = q)
    (hstab : ∀ T, ∃ N, ∀ n ≥ N, ∀ t ≤ T, ∀ p : BitString, p.length ≤ T → ev n t p = evT t p) :
    ∃ m : BitString → BitString → ℝ≥0∞, IsConditionalSemimeasure m ∧ IsLSC m ∧
      ∀ t p x, evT t p = some x →
        ∀ᶠ n in Filter.atTop, ((2 : ℝ≥0∞)⁻¹) ^ p.length ≤ m x (Nat.bits n) := by
  classical
  have hbits : ∀ n x,
      exists_const_limsup_KP_eq_KP_jump_trim_m ev x (Nat.bits n) =
        exists_const_limsup_KP_eq_KP_jump_trim_mass ev n x := by
    intro n x
    have h : ∃ k, Nat.bits k = Nat.bits n := ⟨n, rfl⟩
    unfold exists_const_limsup_KP_eq_KP_jump_trim_m
    rw [dite_eq_left h]
    have := natBits_injective (Classical.choose_spec h)
    rw [this]
  have hnb : ∀ x z, ¬ (∃ n, Nat.bits n = z) →
      exists_const_limsup_KP_eq_KP_jump_trim_m ev x z = 0 := by
    intro x z h
    unfold exists_const_limsup_KP_eq_KP_jump_trim_m
    rw [dite_eq_right h]
  refine ⟨exists_const_limsup_KP_eq_KP_jump_trim_m ev, ?_, ?_, ?_⟩
  · intro z
    by_cases h : ∃ n, Nat.bits n = z
    · obtain ⟨n, rfl⟩ := h
      simp only [hbits]
      exact exists_const_limsup_KP_eq_KP_jump_kraft ev n
    · simp [hnb _ _ h]
  · obtain ⟨approx, hc, hv, hz⟩ :=
      exists_const_limsup_KP_eq_KP_jump_approx ev hev
          hmono
    refine ⟨approx, ?_, ?_, hc⟩
    · intro s out ctx
      by_cases h : ∃ n, Nat.bits n = ctx
      · obtain ⟨n, rfl⟩ := h
        rw [hv, hv]
        exact (exists_const_limsup_KP_eq_KP_jump_sup
          ev n out).1 s
      · rw [hz _ _ _ h, hz _ _ _ h]
        simp [dyadicValue]
    · intro out ctx
      by_cases h : ∃ n, Nat.bits n = ctx
      · obtain ⟨n, rfl⟩ := h
        simp only [hv, hbits]
        exact (exists_const_limsup_KP_eq_KP_jump_sup
          ev n out).2
      · rw [hnb _ _ h]
        simp [hz _ _ _ h, dyadicValue]
  · intro t p x h
    filter_upwards [
      exists_const_limsup_KP_eq_KP_jump_lower
        ev evT hmonoT hpf hstab t p x h] with n hn
    rw [hbits]
    exact hn

/-- Step 1 of the proof of `exists_const_limsup_KP_eq_KP_jump` (the `≥` half,
construction): there is a lower-semicomputable conditional semimeasure `m(x | z)` such that, for
every `x`, `2^{-K^{0'}(x)} ≤ m(x | n)` for all large `n`.

Proof idea: run the optimal `0'`-decompressor `V` with the `n`-step approximation of `0'` as the
oracle (the oracle answer for `e` is `1` iff `φ_e(e)` halts within `n` steps), on the empty
condition, and trim the resulting machine to a prefix-free one (accept a halting program unless
an earlier-halting accepted program is prefix-comparable to it). Let `m(x | n)` be the total weight
`∑ 2^{-|p|}` of accepted programs `p` with output `x` (and `m(x | z) = 0` for `z` not of the form
`Nat.bits n`). It is lower semicomputable, each `m(· | z)` has mass `≤ 1` (accepted programs are
prefix-free), and for fixed `x` a shortest `0'`-program `p` for `x` halts after finitely many
steps using finitely many oracle answers, so for large `n` the approximation answers them
correctly, `p` halts at the same stage, and no earlier-halting program conflicts with it (those
halt with correct answers too, and `V` is prefix-free with the true oracle). -/
private theorem exists_const_limsup_KP_eq_KP_jump_approx_semimeasure {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) :
    ∃ m : BitString → BitString → ℝ≥0∞, IsConditionalSemimeasure m ∧ IsLSC m ∧
      ∀ x, ∀ᶠ n in Filter.atTop, complexityWeight (KP V x []) ≤ m x (Nat.bits n) := by
  obtain ⟨ev, evT, hev, hmono, hmonoT, hiff, hstab⟩ :=
    exists_const_limsup_KP_eq_KP_jump_eval hV.1
  have hpf : ∀ t p q a b, evT t p = some a → evT t q = some b → p <+: q → p = q := by
    intro t p q a b ha hb hpre
    exact hV.2.1.eq_of_prefix (p := p) (q := q) (y := []) (a := a) (b := b)
      ((hiff p a).2 ⟨t, ha⟩) ((hiff q b).2 ⟨t, hb⟩) hpre
  obtain ⟨m, hm1, hm2, hm3⟩ :=
    exists_const_limsup_KP_eq_KP_jump_trim ev evT hev hmono
      hmonoT hpf hstab
  refine ⟨m, hm1, hm2, fun x => ?_⟩
  by_cases hx : KP V x [] = ⊤
  · rw [hx, complexityWeight_top]
    exact Filter.Eventually.of_forall fun n => bot_le
  · obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top hx
    obtain ⟨t, ht⟩ := (hiff p x).1 hp
    filter_upwards [hm3 t p x ht] with n hn
    rw [← hlen, complexityWeight_coe]
    exact hn

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_accepted_triples`:
the family `m*_L` obtained from `m` by raising, for each triple `⟨N, x, q⟩ ∈ L`, the value
`m(x | Nat.bits n)` to at least `q` for every `n ≥ N`. -/
private noncomputable def
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar
    (m : BitString → BitString → ℝ≥0∞) :
    List (ℕ × BitString × ℚ) → BitString → BitString → ℝ≥0∞
  | [], z, y => m z y
  | τ :: L, z, y =>
    open Classical in
    if τ.2.1 = z ∧ ∃ n, τ.1 ≤ n ∧ y = Nat.bits n then
      max (ENNReal.ofReal (τ.2.2 : ℝ))
        (exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z
            y)
    else
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z y

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_accepted_triples`:
the family `m*_L` is still a conditional semimeasure along the conditions `Nat.bits n`. -/
private def exists_const_limsup_KP_eq_KP_jump_accepted_triples_good
    (m : BitString → BitString → ℝ≥0∞) (L : List (ℕ × BitString × ℚ)) : Prop :=
  ∀ n, ∑' z,
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z
      (Nat.bits n) ≤ 1

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_accepted_triples`:
a computable surjective enumeration of all triples. -/
private def exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
    (k : ℕ) : ℕ × BitString × ℚ :=
  (@Encodable.decode (ℕ × BitString × ℚ) Primcodable.toEncodable k).getD (0, [], 0)

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_accepted_triples`:
the code of a triple (through its `Primcodable` structure). -/
private def exists_const_limsup_KP_eq_KP_jump_accepted_triples_code
    (τ : ℕ × BitString × ℚ) : ℕ :=
  @Encodable.encode (ℕ × BitString × ℚ) Primcodable.toEncodable τ

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum_code
    (τ : ℕ × BitString × ℚ) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ)
      = τ := by
  unfold exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_code
  rw [@Encodable.encodek (ℕ × BitString × ℚ) Primcodable.toEncodable τ]
  rfl

/-- Auxiliary for `exists_const_limsup_KP_eq_KP_jump_accepted_triples`:
the greedy sequence of accepted lists, relative to a test `d`. -/
private def exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq
    (d : List (ℕ × BitString × ℚ) → Bool) : ℕ → List (ℕ × BitString × ℚ)
  | 0 => []
  | k + 1 =>
    cond (d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k
        ::
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k))
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k ::
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k)
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k)

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_base
    (m : BitString → BitString → ℝ≥0∞) :
    ∀ (L : List (ℕ × BitString × ℚ)) z y,
      m z y ≤
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L
          z y := by
  intro L z y
  induction L with
  | nil => exact le_rfl
  | cons τ L ih =>
    simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar]
    split_ifs
    · exact ih.trans (le_max_right _ _)
    · exact ih

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_mem
    (m : BitString → BitString → ℝ≥0∞) :
    ∀ (L : List (ℕ × BitString × ℚ)) (N : ℕ) (x : BitString) (q : ℚ) (n : ℕ),
      (N, x, q) ∈ L → N ≤ n →
      ENNReal.ofReal (q : ℝ) ≤
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L x
          (Nat.bits n) := by
  intro L N x q n hmem hN
  induction L with
  | nil => simp at hmem
  | cons τ L ih =>
    simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar]
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      rw [ite_eq_left ⟨rfl, n, hN, rfl⟩]
      exact le_max_left _ _
    · have := ih h
      split_ifs
      · exact this.trans (le_max_right _ _)
      · exact this

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_cons_of_le
    (m : BitString → BitString → ℝ≥0∞)
    (L : List (ℕ × BitString × ℚ)) (N : ℕ) (x : BitString) (q : ℚ)
    (h : ∀ n, N ≤ n → ENNReal.ofReal (q : ℝ) ≤ m x (Nat.bits n)) (z y : BitString) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m
        ((N, x, q) :: L) z y =
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L
        z y := by
  simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar]
  split_ifs with hc
  · obtain ⟨rfl, n, hn, rfl⟩ := hc
    exact max_eq_right ((h n hn).trans
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_base
        m L _ _))
  · rfl

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_succ_subset
    (d : List (ℕ × BitString × ℚ) → Bool) (k : ℕ)
    {τ : ℕ × BitString × ℚ}
    (h : τ ∈
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k) :
    τ ∈ exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d
      (k + 1) := by
  simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq]
  cases d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k ::
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k)
  · simpa using h
  · simp [h]

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_mono
    (d : List (ℕ × BitString × ℚ) → Bool) {k K : ℕ} (hk : k ≤ K)
    {τ : ℕ × BitString × ℚ}
    (h : τ ∈
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k) :
    τ ∈ exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d
      K := by
  induction K, hk using Nat.le_induction with
  | base => exact h
  | succ K _ ih =>
    exact
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_succ_subset
        d K ih

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_good
    (m : BitString → BitString → ℝ≥0∞) (hm : IsConditionalSemimeasure m)
    (d : List (ℕ × BitString × ℚ) → Bool)
    (hd : ∀ L, d L = true ↔
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_good m L) :
    ∀ k, exists_const_limsup_KP_eq_KP_jump_accepted_triples_good m
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k) :=
          by
  intro k
  induction k with
  | zero =>
    exact fun n => by
      simpa [exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq,
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar]
        using hm (Nat.bits n)
  | succ k ih =>
    simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq]
    cases hc : d
        (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k ::
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k)
    · simpa using ih
    · simpa using (hd _).1 hc

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_mem_of_test
    (d : List (ℕ × BitString × ℚ) → Bool) (k : ℕ)
    (h : d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k
        ::
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d k) =
      true) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum k ∈
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d
        (k + 1) := by
  simp [exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq, h]

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_cond_computable
    {O : Set (ℕ →. ℕ)} {α σ : Type} [Primcodable α] [Primcodable σ]
    {c : α → Bool} {f g : α → σ} (hc : ComputableIn O c) (hf : ComputableIn O f)
    (hg : ComputableIn O g) : ComputableIn O fun a => cond (c a) (f a) (g a) := by
  have := PartrecIn.cond hc hf hg
  refine this.of_eq fun a => ?_
  cases h : c a <;> simp [h]

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_cons_computable
    (S : ℕ → List (ℕ × BitString × ℚ)) (hS : ComputableIn {charOracle jumpSet} S) :
    ComputableIn {charOracle jumpSet}
      (fun τ : ℕ × BitString × ℚ => τ ::
        S (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ))
            := by
  have hc : Computable
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_code :=
    Computable.encode
  have hs : ComputableIn {charOracle jumpSet}
      (fun τ : ℕ × BitString × ℚ =>
        S (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ))
            :=
    ComputableIn.comp hS hc.computableIn
  have hcons0 : ComputableIn {charOracle jumpSet}
      (fun p : (ℕ × BitString × ℚ) × List (ℕ × BitString × ℚ) => p.1 :: p.2) :=
    Computable.computableIn (Primrec.list_cons.to_comp)
  have hp : ComputableIn {charOracle jumpSet}
      (fun τ : ℕ × BitString × ℚ => (τ,
        S (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ)))
            :=
    ComputableIn.pair (f := fun τ : ℕ × BitString × ℚ => τ)
      (g := fun τ : ℕ × BitString × ℚ =>
        S (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ))
      ComputableIn.id hs
  exact ComputableIn.comp
    (f := fun p : (ℕ × BitString × ℚ) × List (ℕ × BitString × ℚ) => p.1 :: p.2)
    (g := fun τ : ℕ × BitString × ℚ => (τ,
        S (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ)))
    hcons0 hp

private lemma exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_computable
    (d : List (ℕ × BitString × ℚ) → Bool)
    (hd : ComputableIn {charOracle jumpSet} d) :
    ComputableIn {charOracle jumpSet}
      (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d) := by
  have henum : Computable
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum := by
    unfold exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
    exact Computable.option_getD Computable.decode (Computable.const _)
  have hcons : Computable
      (fun x : ℕ × (ℕ × List (ℕ × BitString × ℚ)) =>
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
          x.2.1 :: x.2.2) :=
    Primrec.list_cons.to_comp.comp (henum.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  have hcons' : ComputableIn {charOracle jumpSet}
      (fun x : ℕ × (ℕ × List (ℕ × BitString × ℚ)) =>
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
          x.2.1 :: x.2.2) := hcons.computableIn
  have hstep : ComputableIn {charOracle jumpSet}
      (fun x : ℕ × (ℕ × List (ℕ × BitString × ℚ)) =>
        cond (d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
          x.2.1 :: x.2.2))
          (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
            x.2.1 :: x.2.2) x.2.2) :=
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_cond_computable
      (ComputableIn.comp hd hcons') hcons' (Computable.snd.comp Computable.snd).computableIn
  have hrec := ComputableIn.nat_rec (O := {charOracle jumpSet}) (f := fun k : ℕ => k)
    (g := fun _ : ℕ => ([] : List (ℕ × BitString × ℚ)))
    (h := fun (_ : ℕ) (p : ℕ × List (ℕ × BitString × ℚ)) =>
      cond (d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
          p.1 :: p.2))
        (exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
          p.1 :: p.2) p.2)
    ComputableIn.id (ComputableIn.const _) hstep
  refine hrec.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq]
    rw [← ih]

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_test_decidable`:
the rational raise of `z` at the condition `Nat.bits n` by the list `L`. -/
private def exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
    (L : List (ℕ × BitString × ℚ)) (z : BitString) (n : ℕ) : ℚ :=
  L.foldr (fun τ acc => if τ.2.1 = z ∧ τ.1 ≤ n then max τ.2.2 acc else acc) 0

private lemma exists_const_limsup_KP_eq_KP_jump_test_decidable_rL_computable :
    Computable (fun q : List (ℕ × BitString × ℚ) × BitString × ℕ =>
      exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
        q.1 q.2.1 q.2.2) := by
  let P := (List (ℕ × BitString × ℚ) × BitString × ℕ) × ((ℕ × BitString × ℚ) × ℚ)
  have hq : Computable (fun x : P => x.1) := Computable.fst
  have hτ : Computable (fun x : P => x.2.1) := Computable.fst.comp Computable.snd
  have hacc : Computable (fun x : P => x.2.2) := Computable.snd.comp Computable.snd
  have hz : Computable (fun x : P => x.1.2.1) := Computable.fst.comp (Computable.snd.comp hq)
  have hn : Computable (fun x : P => x.1.2.2) := Computable.snd.comp (Computable.snd.comp hq)
  have hN : Computable (fun x : P => x.2.1.1) := Computable.fst.comp hτ
  have hz' : Computable (fun x : P => x.2.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp hτ)
  have hqq : Computable (fun x : P => x.2.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp hτ)
  have heq : Computable (fun x : P => decide (x.2.1.2.1 = x.1.2.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hz' hz
  have hle : Computable (fun x : P => decide (x.2.1.1 ≤ x.1.2.2)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hN hn
  have hmx : Computable (fun x : P => max x.2.1.2.2 x.2.2) :=
    computable₂_ratMax.comp hqq hacc
  have hh : Computable (fun x : P =>
      cond (decide (x.2.1.2.1 = x.1.2.1))
        (cond (decide (x.2.1.1 ≤ x.1.2.2)) (max x.2.1.2.2 x.2.2) x.2.2) x.2.2) :=
    Computable.cond heq (Computable.cond hle hmx hacc) hacc
  have := Computable.list_foldr
    (l := fun q : List (ℕ × BitString × ℚ) × BitString × ℕ => q.1)
    (g := fun _ => (0 : ℚ))
    (h := fun (q : List (ℕ × BitString × ℚ) × BitString × ℕ) (p : (ℕ × BitString × ℚ) × ℚ) =>
      cond (decide (p.1.2.1 = q.2.1))
        (cond (decide (p.1.1 ≤ q.2.2)) (max p.1.2.2 p.2) p.2) p.2)
    Computable.fst (Computable.const 0) hh.to₂
  refine this.of_eq fun q => ?_
  obtain ⟨L, z, n⟩ := q
  simp only [exists_const_limsup_KP_eq_KP_jump_test_decidable_rL]
  induction L with
  | nil => rfl
  | cons τ L ih =>
    simp only [List.foldr_cons, ih]
    by_cases h1 : τ.2.1 = z <;> by_cases h2 : τ.1 ≤ n <;> simp [h1, h2]

private lemma exists_const_limsup_KP_eq_KP_jump_test_decidable_half_pow :
    Computable (fun a : ℕ => (1 / 2 : ℚ) ^ a) := by
  refine computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun a : ℕ => 2 ^ a)
    (Computable.const 1)
    ((nat_pow_primrec₂.comp (Primrec.const 2) Primrec.id).to_comp)
    (fun a => by positivity) (fun a => ?_)
  push_cast
  rw [div_pow, one_pow]

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_test_decidable`:
the rational value `max (a_s(z, Nat.bits n) / 2^s) (raise of z)`. -/
private def exists_const_limsup_KP_eq_KP_jump_test_decidable_w
    (a : ℕ → BitString → BitString → ℕ) (L : List (ℕ × BitString × ℚ))
    (n s : ℕ) (z : BitString) : ℚ :=
  max ((a s z (Nat.bits n) : ℚ) * (1 / 2 : ℚ) ^ s)
    (exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
      L z n)

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_test_decidable`:
`..._w` at the string with code `i` (and `0` if `i` codes no string). -/
private def exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
    (a : ℕ → BitString → BitString → ℕ) (L : List (ℕ × BitString × ℚ))
    (n s i : ℕ) : ℚ :=
  ((Encodable.decode (α := BitString) i).map
    (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
      a L n s)).getD 0

/-- Auxiliary for
`exists_const_limsup_KP_eq_KP_jump_test_decidable`:
the partial sum of `..._wo` over the codes `< K`. -/
private def exists_const_limsup_KP_eq_KP_jump_test_decidable_S
    (a : ℕ → BitString → BitString → ℕ) (L : List (ℕ × BitString × ℚ))
    (n s : ℕ) : ℕ → ℚ
  | 0 => 0
  | K + 1 =>
    exists_const_limsup_KP_eq_KP_jump_test_decidable_S
      a L n s K +
    exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
      a L n s K

private lemma exists_const_limsup_KP_eq_KP_jump_test_decidable_w_computable
    (a : ℕ → BitString → BitString → ℕ)
    (ha : Computable (fun p : ℕ × BitString × BitString => a p.1 p.2.1 p.2.2)) :
    Computable (fun q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × BitString =>
      exists_const_limsup_KP_eq_KP_jump_test_decidable_w
        a q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  let Q := (List (ℕ × BitString × ℚ) × ℕ × ℕ) × BitString
  have hp : Computable (fun q : Q => q.1) := Computable.fst
  have hL : Computable (fun q : Q => q.1.1) := Computable.fst.comp hp
  have hn : Computable (fun q : Q => q.1.2.1) := Computable.fst.comp (Computable.snd.comp hp)
  have hs : Computable (fun q : Q => q.1.2.2) := Computable.snd.comp (Computable.snd.comp hp)
  have hz : Computable (fun q : Q => q.2) := Computable.snd
  have hbn : Computable (fun q : Q => Nat.bits q.1.2.1) := natBits_computable.comp hn
  have htriple : Computable (fun q : Q => (q.1.2.2, q.2, Nat.bits q.1.2.1)) :=
    Computable.pair hs (Computable.pair hz hbn)
  have h1 : Computable (fun q : Q => a q.1.2.2 q.2 (Nat.bits q.1.2.1)) :=
    ha.comp htriple
  have h2 : Computable (fun q : Q => ((a q.1.2.2 q.2 (Nat.bits q.1.2.1) : ℕ) : ℚ)) :=
    computable_nat_to_rat.comp h1
  have h3 : Computable (fun q : Q => (1 / 2 : ℚ) ^ q.1.2.2) :=
    exists_const_limsup_KP_eq_KP_jump_test_decidable_half_pow.comp hs
  have htr : Computable (fun q : Q => (q.1.1, q.2, q.1.2.1)) :=
    Computable.pair hL (Computable.pair hz hn)
  have h4 :=
    exists_const_limsup_KP_eq_KP_jump_test_decidable_rL_computable.comp
      htr
  have h5 : Computable (fun q : Q => ((a q.1.2.2 q.2 (Nat.bits q.1.2.1) : ℕ) : ℚ) *
      (1 / 2 : ℚ) ^ q.1.2.2) :=
    computable₂_ratMul.comp h2 h3
  have h6 := computable₂_ratMax.comp h5 h4
  refine h6.of_eq fun q => ?_
  simp only [exists_const_limsup_KP_eq_KP_jump_test_decidable_w]

private lemma exists_const_limsup_KP_eq_KP_jump_test_decidable_wo_computable
    (a : ℕ → BitString → BitString → ℕ)
    (ha : Computable (fun p : ℕ × BitString × BitString => a p.1 p.2.1 p.2.2)) :
    Computable (fun q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × ℕ =>
      exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
        a q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hw :=
    exists_const_limsup_KP_eq_KP_jump_test_decidable_w_computable
      a ha
  have hg : Computable₂ (fun (q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × ℕ) (z : BitString) =>
      exists_const_limsup_KP_eq_KP_jump_test_decidable_w
        a q.1.1 q.1.2.1 q.1.2.2 z) :=
    (hw.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).to₂
  exact Computable.option_getD
    (Computable.option_map (Computable.decode.comp Computable.snd) hg) (Computable.const 0)

private lemma exists_const_limsup_KP_eq_KP_jump_test_decidable_S_computable
    (a : ℕ → BitString → BitString → ℕ)
    (ha : Computable (fun p : ℕ × BitString × BitString => a p.1 p.2.1 p.2.2)) :
    Computable (fun q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × ℕ =>
      exists_const_limsup_KP_eq_KP_jump_test_decidable_S
        a q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hwo :=
    exists_const_limsup_KP_eq_KP_jump_test_decidable_wo_computable
      a ha
  have hstep : Computable₂ (fun (q : List (ℕ × BitString × ℚ) × ℕ × ℕ) (p : ℕ × ℚ) =>
      p.2 +
        exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
          a q.1 q.2.1 q.2.2 p.1) :=
    (computable₂_ratAdd.comp (Computable.snd.comp Computable.snd)
      (hwo.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))).to₂
  have := Computable.nat_rec
    (f := fun q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × ℕ => q.2)
    (g := fun _ => (0 : ℚ))
    (h := fun (q : (List (ℕ × BitString × ℚ) × ℕ × ℕ) × ℕ) (p : ℕ × ℚ) =>
      p.2 +
        exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
          a q.1.1 q.1.2.1 q.1.2.2 p.1)
    Computable.snd (Computable.const 0)
    (hstep.comp (Computable.fst.comp Computable.fst) Computable.snd)
  refine this.of_eq fun q => ?_
  obtain ⟨⟨L, n, s⟩, K⟩ := q
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [exists_const_limsup_KP_eq_KP_jump_test_decidable_S]
    rw [← ih]

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_canonB
    (n : ℕ) (b : Bool) (h : Encodable.decode (α := Bool) n = some b) :
    Encodable.encode b = n := by
  rcases n with _ | _ | n
  · cases b <;> simp_all
  · cases b <;> simp_all
  · rw [Encodable.decode_ge_two _ (by omega)] at h
    cases h

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_canon :
    ∀ (n : ℕ) (z : BitString), Encodable.decode n = some z → Encodable.encode z = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z h
    rcases n with _ | v
    · rw [Encodable.decode_list_zero] at h
      cases h
      rfl
    · rw [Encodable.decode_list_succ] at h
      cases h1 : Encodable.decode (α := Bool) v.unpair.1 with
      | none => simp [h1, Seq.seq] at h
      | some b =>
        cases h2 : Encodable.decode (α := BitString) v.unpair.2 with
        | none => simp [h1, h2, Seq.seq] at h
        | some l =>
          have h' : b :: l = z := by simpa [h1, h2, Seq.seq] using h
          subst h'
          have hb :=
            exists_const_limsup_KP_eq_KP_jump_good_iff_aux_canonB
              _ b h1
          have hl := ih v.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le v)) l h2
          rw [Encodable.encode_list_cons, hb, hl, Nat.pair_unpair]

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_rL_nonneg
    (L : List (ℕ × BitString × ℚ)) (z : BitString) (n : ℕ) :
    0 ≤ exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
      L z n := by
  simp only [exists_const_limsup_KP_eq_KP_jump_test_decidable_rL]
  induction L with
  | nil => exact le_rfl
  | cons τ L ih =>
    simp only [List.foldr_cons]
    split_ifs
    · exact ih.trans (le_max_right _ _)
    · exact ih

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_mstar_eq
    (m : BitString → BitString → ℝ≥0∞) (L : List (ℕ × BitString × ℚ)) (z : BitString) (n : ℕ) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z
        (Nat.bits n) =
      max (m z (Nat.bits n))
        (ENNReal.ofReal
          (exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
            L z n : ℝ)) := by
  induction L with
  | nil =>
    simp [exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar,
      exists_const_limsup_KP_eq_KP_jump_test_decidable_rL]
  | cons τ L ih =>
    have hr : exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
        (τ :: L) z n =
        if τ.2.1 = z ∧ τ.1 ≤ n then
          max τ.2.2
            (exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
              L z n)
        else
          exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
            L z n := rfl
    have hiff : (τ.2.1 = z ∧ ∃ n', τ.1 ≤ n' ∧ Nat.bits n = Nat.bits n') ↔
        (τ.2.1 = z ∧ τ.1 ≤ n) := by
      refine and_congr_right fun _ => ⟨?_, fun h => ⟨n, h, rfl⟩⟩
      rintro ⟨n', hn', he⟩
      rw [natBits_injective he]
      exact hn'
    simp only [exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar]
    rw [hr]
    by_cases hc : τ.2.1 = z ∧ τ.1 ≤ n
    · rw [ite_eq_left (hiff.2 hc), ite_eq_left hc, ih, Rat.cast_max, ENNReal.ofReal_max,
        max_left_comm]
    · rw [ite_eq_right (fun h => hc (hiff.1 h)), ite_eq_right hc, ih]

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_dyadic
    (k s : ℕ) :
    ENNReal.ofReal (((k : ℚ) * (1 / 2 : ℚ) ^ s : ℚ) : ℝ) = dyadicValue k s := by
  unfold dyadicValue
  have h : (((k : ℚ) * (1 / 2 : ℚ) ^ s : ℚ) : ℝ) = (k : ℝ) / (2 : ℝ) ^ s := by
    push_cast
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [h, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  simp

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_eq
    (a : ℕ → BitString → BitString → ℕ) (L : List (ℕ × BitString × ℚ)) (n s : ℕ)
    (z : BitString) :
    ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
          a L n s z : ℝ) =
      max (dyadicValue (a s z (Nat.bits n)) s)
        (ENNReal.ofReal
          (exists_const_limsup_KP_eq_KP_jump_test_decidable_rL
            L z n : ℝ)) := by
  unfold exists_const_limsup_KP_eq_KP_jump_test_decidable_w
  rw [Rat.cast_max, ENNReal.ofReal_max,
    exists_const_limsup_KP_eq_KP_jump_good_iff_aux_dyadic]

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_mstar_iSup
    {m : BitString → BitString → ℝ≥0∞} (a : ℕ → BitString → BitString → ℕ)
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (a s out ctx) s = m out ctx)
    (L : List (ℕ × BitString × ℚ)) (n : ℕ) (z : BitString) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z
        (Nat.bits n) =
      ⨆ s, ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
          a L n s z : ℝ) := by
  rw [exists_const_limsup_KP_eq_KP_jump_good_iff_aux_mstar_eq,
    ← hsup z (Nat.bits n)]
  simp_rw [exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_eq]
  exact iSup_sup

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_mono
    (a : ℕ → BitString → BitString → ℕ)
    (hmono : ∀ s out ctx, dyadicValue (a s out ctx) s ≤ dyadicValue (a (s + 1) out ctx) (s + 1))
    (L : List (ℕ × BitString × ℚ)) (n s : ℕ) (z : BitString) :
    ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
          a L n s z : ℝ) ≤
      ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
          a L n (s + 1) z : ℝ) := by
  rw [exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_eq,
    exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_eq]
  exact max_le_max (hmono s z (Nat.bits n)) le_rfl

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_ofReal_S
    (a : ℕ → BitString → BitString → ℕ) (L : List (ℕ × BitString × ℚ)) (n s K : ℕ) :
    ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_S
          a L n s K : ℝ) =
      ∑ i ∈ Finset.range K,
        ((Encodable.decode (α := BitString) i).map (fun z => ENNReal.ofReal
          (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
            a L n s z : ℝ))).getD 0 := by
  have hwo : ∀ i,
      0 ≤ exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
        a L n s i := by
    intro i
    unfold exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
    cases Encodable.decode (α := BitString) i with
    | none => simp
    | some z =>
      simp only [Option.map_some, Option.getD_some]
      unfold exists_const_limsup_KP_eq_KP_jump_test_decidable_w
      exact le_max_of_le_left (by positivity)
  have hS : exists_const_limsup_KP_eq_KP_jump_test_decidable_S
      a L n s K = ∑ i ∈ Finset.range K,
        exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
          a L n s i := by
    induction K with
    | zero => rfl
    | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  rw [hS]
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by exact_mod_cast hwo i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold exists_const_limsup_KP_eq_KP_jump_test_decidable_wo
  cases Encodable.decode (α := BitString) i <;> simp

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_sum_le_tsum
    (f : BitString → ℝ≥0∞) (K : ℕ) :
    ∑ i ∈ Finset.range K, ((Encodable.decode (α := BitString) i).map f).getD 0 ≤ ∑' z, f z := by
  set g : ℕ → ℝ≥0∞ := fun i => ((Encodable.decode (α := BitString) i).map f).getD 0 with hg
  have hsupp : Function.support g ⊆ Set.range (Encodable.encode (α := BitString)) := by
    intro i hi
    simp only [Function.mem_support, hg] at hi
    cases hd : Encodable.decode (α := BitString) i with
    | none => simp [hd] at hi
    | some z =>
      exact ⟨z,
        exists_const_limsup_KP_eq_KP_jump_good_iff_aux_canon
          i z hd⟩
  have hinj := Encodable.encode_injective (α := BitString)
  calc ∑ i ∈ Finset.range K, g i ≤ ∑' i, g i := ENNReal.sum_le_tsum _
    _ = ∑' z, g (Encodable.encode z) := (hinj.tsum_eq hsupp).symm
    _ = ∑' z, f z := by simp [hg, Encodable.encodek]

private lemma exists_const_limsup_KP_eq_KP_jump_good_iff_aux_finset_le_sum
    (f : BitString → ℝ≥0∞) (F : Finset BitString) :
    ∃ K, ∑ z ∈ F, f z ≤
      ∑ i ∈ Finset.range K, ((Encodable.decode (α := BitString) i).map f).getD 0 := by
  refine ⟨F.sup Encodable.encode + 1, ?_⟩
  have hinj := Encodable.encode_injective (α := BitString)
  calc ∑ z ∈ F, f z
      = ∑ i ∈ F.image Encodable.encode,
          ((Encodable.decode (α := BitString) i).map f).getD 0 := by
        rw [Finset.sum_image fun x _ y _ h => hinj h]
        simp [Encodable.encodek]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun i hi => ?_
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hi
        exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := Encodable.encode) hz))

/-- Step 2 of the proof of
`exists_const_limsup_KP_eq_KP_jump_test_decidable`:
with the approximation `a_s(z, y)` of `m` (numerators of the dyadic values `a_s(z, y) / 2^s`,
monotone in `s` with supremum `m z y`), the list `L` is `good` iff every rational partial sum
`∑_{i < K} max (a_s(z_i, Nat.bits n) / 2^s) (raise of z_i)` is at most `1`, where `z_i` is the
string with code `i` (nothing if `i` codes no string); this is `..._S a L n s K ≤ 1`.

Proof idea: `m*_L(z | Nat.bits n) = max (m z (Nat.bits n)) (ofReal (raise of z))` (the raise is a
rational `≥ 0`; `Nat.bits` is injective), `= ⨆_s max (a_s/2^s) (ofReal raise)`; a `tsum` in `[0,∞]`
is the supremum of its finite partial sums, a finite sum of monotone suprema is the supremum of the
sums (`ENNReal.finsetSum_iSup_of_monotone`), and every finite set of strings is contained in the
strings with code `< K` for some `K`; conversely the sums over codes `< K` are finite sums over
distinct strings (`Encodable.encode` is injective), hence at most the `tsum`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_good_iff
    {m : BitString → BitString → ℝ≥0∞} (a : ℕ → BitString → BitString → ℕ)
    (hmono : ∀ s out ctx, dyadicValue (a s out ctx) s ≤ dyadicValue (a (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (a s out ctx) s = m out ctx)
    (L : List (ℕ × BitString × ℚ)) :
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_good m L ↔
      ∀ n s K,
        exists_const_limsup_KP_eq_KP_jump_test_decidable_S
          a L n s K ≤ 1 := by
  classical
  let W : ℕ → ℕ → BitString → ℝ≥0∞ := fun n s z => ENNReal.ofReal
    (exists_const_limsup_KP_eq_KP_jump_test_decidable_w
      a L n s z : ℝ)
  have hWsup : ∀ n z,
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m L z
        (Nat.bits n) = ⨆ s, W n s z := fun n z =>
    exists_const_limsup_KP_eq_KP_jump_good_iff_aux_mstar_iSup
      a hsup L n z
  have hWmono : ∀ n z, Monotone (fun s => W n s z) := fun n z =>
    monotone_nat_of_le_succ fun s =>
      exists_const_limsup_KP_eq_KP_jump_good_iff_aux_W_mono
        a hmono L n s z
  have hS : ∀ n s K,
      ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_S
          a L n s K : ℝ) =
        ∑ i ∈ Finset.range K, ((Encodable.decode (α := BitString) i).map (W n s)).getD 0 :=
    fun n s K =>
    exists_const_limsup_KP_eq_KP_jump_good_iff_aux_ofReal_S
      a L n s K
  constructor
  · intro hgood n s K
    have h1 : ENNReal.ofReal
        (exists_const_limsup_KP_eq_KP_jump_test_decidable_S
          a L n s K : ℝ) ≤ 1 := by
      rw [hS]
      calc _ ≤ ∑' z, W n s z :=
            exists_const_limsup_KP_eq_KP_jump_good_iff_aux_sum_le_tsum
              (W n s) K
        _ ≤ ∑' z,
            exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m
              L z (Nat.bits n) :=
            ENNReal.tsum_le_tsum fun z => by rw [hWsup]; exact le_iSup (fun s => W n s z) s
        _ ≤ 1 := hgood n
    exact_mod_cast ENNReal.ofReal_le_one.1 h1
  · intro hall n
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    simp_rw [hWsup n]
    rw [ENNReal.finsetSum_iSup_of_monotone fun z => hWmono n z]
    refine iSup_le fun s => ?_
    obtain ⟨K, hK⟩ :=
      exists_const_limsup_KP_eq_KP_jump_good_iff_aux_finset_le_sum
        (W n s) F
    refine hK.trans ?_
    rw [← hS]
    exact ENNReal.ofReal_le_one.2 (by exact_mod_cast hall n s K)

/-- Step 1 of the proof of
`exists_const_limsup_KP_eq_KP_jump_accepted_triples`: the `Π₁` test of
the greedy construction is decidable with the oracle `0'`.

For a lower-semicomputable conditional semimeasure `m` (an `IsLSC` computable monotone dyadic
approximation `a_s(z, y)` with supremum `m z y`) and a finite list `L` of triples `⟨N, x, q⟩`, let
`m*_L` be `m` with, for each `⟨N, x, q⟩ ∈ L`, the value `m(x | Nat.bits n)` raised to at least
`ofReal q` for all `n ≥ N` (`..._mstar`). Then the property "`∑_z m*_L(z | Nat.bits n) ≤ 1` for
every `n`" (`..._good m L`) is decided by a function computable relative to `0'`.

Proof idea: the property fails iff there are `n`, a stage `s` and a finite set `F` of strings such
that `∑_{z∈F} max(a_s(z, Nat.bits n), raises of z by L) > 1` (all quantities rational): this is a
`Σ₁` condition on `L`, hence decidable relative to `0'` (halting oracle). Here
`max(m z y, r) = sup_s max(a_s z y, r)` and the finitely many raises are rational. -/
private theorem exists_const_limsup_KP_eq_KP_jump_test_decidable
    {m : BitString → BitString → ℝ≥0∞} (hlsc : IsLSC m) :
    ∃ d : List (ℕ × BitString × ℚ) → Bool, ComputableIn {charOracle jumpSet} d ∧
      ∀ L, d L = true ↔
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_good m
          L := by
  classical
  obtain ⟨a, hmono, hsup, hcomp⟩ := hlsc
  have hn : Computable (fun p : List (ℕ × BitString × ℚ) × ℕ => (Nat.unpair p.2).1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have hs : Computable (fun p : List (ℕ × BitString × ℚ) × ℕ =>
      (Nat.unpair (Nat.unpair p.2).2).1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hK : Computable (fun p : List (ℕ × BitString × ℚ) × ℕ =>
      (Nat.unpair (Nat.unpair p.2).2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp.comp
      Computable.snd
  have hq : Computable (fun p : List (ℕ × BitString × ℚ) × ℕ =>
      ((p.1, (Nat.unpair p.2).1, (Nat.unpair (Nat.unpair p.2).2).1),
        (Nat.unpair (Nat.unpair p.2).2).2)) :=
    Computable.pair (Computable.pair Computable.fst (Computable.pair hn hs)) hK
  have hSq :=
    (exists_const_limsup_KP_eq_KP_jump_test_decidable_S_computable
      a hcomp).comp hq
  have hle := computable_ratLeOne.comp hSq
  have hnot := Primrec.not.to_comp.comp hle
  let g : List (ℕ × BitString × ℚ) → ℕ → Bool := fun L k =>
    !decide
      (exists_const_limsup_KP_eq_KP_jump_test_decidable_S
        a L (Nat.unpair k).1 (Nat.unpair (Nat.unpair k).2).1 (Nat.unpair (Nat.unpair k).2).2 ≤ 1)
  have hg : Computable₂ g := hnot.of_eq fun p => rfl
  obtain ⟨h, hh, hspec⟩ := Kolmogorov.exists_computableInJump_semidecide hg
  have hhalt : haltingChi = charOracle jumpSet := by
    funext n
    simp only [haltingChi, charOracle, jumpSet, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({charOracle jumpSet} : Set (ℕ →. ℕ)) h := by
    simpa [ComputableInJump, hhalt] using hh
  refine ⟨fun L => !h L,
    ComputableIn.comp (f := fun x : Bool => !x) (Primrec.not.to_comp.computableIn) hh',
    fun L => ?_⟩
  rw [exists_const_limsup_KP_eq_KP_jump_good_iff
    a hmono hsup L]
  constructor
  · intro hL n s K
    by_contra hlt
    have hk : g L (Nat.pair n (Nat.pair s K)) = true := by
      simp only [g, Nat.unpair_pair]
      simpa using hlt
    have := (hspec L).2 ⟨_, hk⟩
    simp [this] at hL
  · intro hall
    cases hb : h L
    · simp [hb]
    · exfalso
      obtain ⟨k, hk⟩ := (hspec L).1 hb
      have := hall (Nat.unpair k).1 (Nat.unpair (Nat.unpair k).2).1
        (Nat.unpair (Nat.unpair k).2).2
      simp only [g] at hk
      simp [this] at hk

/-- Step 1 of the proof of `exists_const_limsup_KP_eq_KP_jump_jump_semimeasure`:
the greedy `0'`-enumerable set of accepted triples.

Let `m` be a lower-semicomputable conditional semimeasure. There is a `0'`-enumerable set `T` of
triples `⟨N, x, ε⟩` (`ε` rational) such that
* (completeness) every triple with `ε ≤ m(x | n)` for all `n ≥ N` belongs to `T`;
* (soundness) accepted triples are jointly consistent: for finitely many `x ∈ s`, if
  `⟨N x, x, e x⟩ ∈ T` for each `x ∈ s`, then `∑_{x ∈ s} max(e x, 0) ≤ 1`.

Proof idea: enumerate all triples `⟨N, x, ε⟩`, process them in turn maintaining a family `m*`
(initially `m`); accept the triple if raising `m*(x | n)` to `max(m*(x | n), ε)` for all `n ≥ N`
leaves `∑ₓ m*(x | n) ≤ 1` for every `n` (a `Π₁` test, since each `m(x | n)` is the supremum of
a computable monotone approximation, hence decidable with the oracle `0'`), and in that case
perform the raise. Then `T` is the set of accepted triples (together with all triples with
`ε ≤ 0`, which change nothing). Completeness: if `ε ≤ m(x | n)` for `n ≥ N` then `m* ≥ m` makes the
raise a no-op, so the test passes by the invariant. Soundness: for `n ≥ max N x` all
`m*(x | n) ≥ e x`, so `∑_{x ∈ s} e x ≤ ∑ₓ m*(x | n) ≤ 1`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_accepted_triples
    {m : BitString → BitString → ℝ≥0∞} (hm : IsConditionalSemimeasure m) (hlsc : IsLSC m) :
    ∃ T : ℕ × BitString × ℚ → Prop, PointToSet.IsREIn jumpSet T ∧
      (∀ (N : ℕ) (x : BitString) (q : ℚ),
        (∀ n, N ≤ n → ENNReal.ofReal (q : ℝ) ≤ m x (Nat.bits n)) → T (N, x, q)) ∧
      ∀ (s : Finset BitString) (N : BitString → ℕ) (e : BitString → ℚ),
        (∀ x ∈ s, T (N x, x, e x)) → ∑ x ∈ s, max ((e x : ℝ)) 0 ≤ 1 := by
  classical
  obtain ⟨d, hd, hdg⟩ :=
    exists_const_limsup_KP_eq_KP_jump_test_decidable
      hlsc
  have hgood :=
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_good m hm d
      hdg
  have hseqc :=
    exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_computable
      d hd
  refine ⟨fun τ => d (τ ::
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq
    d (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code τ))
      = true, ?_, ?_, ?_⟩
  · refine PointToSet.isREIn_of_computableIn_decide jumpSet _ ?_
    have hcons := exists_const_limsup_KP_eq_KP_jump_accepted_triples_cons_computable
      _ hseqc
    exact (ComputableIn.comp hd hcons).of_eq fun τ => by simp
  · intro N x q hq
    refine (hdg _).2 ?_
    intro n
    have hc :=
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_cons_of_le
        m
        (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d
          (exists_const_limsup_KP_eq_KP_jump_accepted_triples_code
            (N, x, q))) N x q hq
    simp only [hc]
    exact hgood _ n
  · intro s N e hs
    let k : BitString → ℕ := fun x =>
      exists_const_limsup_KP_eq_KP_jump_accepted_triples_code
        (N x, x, e x)
    let K : ℕ := s.sup fun x => k x + 1
    let n0 : ℕ := s.sup N
    have hmem : ∀ x ∈ s, (N x, x, e x) ∈
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq d K :=
            by
      intro x hx
      have h1 :=
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_mem_of_test
          d (k x) (by
            rw [show
              exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
                (k x) = (N x, x, e x) from
              exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum_code
                _]
            exact hs x hx)
      have h2 :
          exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum
            (k x) = (N x, x, e x) :=
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_enum_code _
      rw [h2] at h1
      exact
        exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq_mono
          d (Finset.le_sup (f := fun x => k x + 1) hx) h1
    have hsum : ∑ x ∈ s, ENNReal.ofReal (e x : ℝ) ≤ 1 := by
      calc ∑ x ∈ s, ENNReal.ofReal (e x : ℝ)
          ≤ ∑ x ∈ s,
            exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m
              (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq
                d K) x (Nat.bits n0) :=
            Finset.sum_le_sum fun x hx =>
              exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar_mem
                m _ (N x) x (e x) n0 (hmem x hx) (Finset.le_sup (f := N) hx)
        _ ≤ ∑' z,
            exists_const_limsup_KP_eq_KP_jump_accepted_triples_mstar m
              (exists_const_limsup_KP_eq_KP_jump_accepted_triples_seq
                d K) z (Nat.bits n0) :=
            ENNReal.sum_le_tsum s
        _ ≤ 1 := hgood K n0
    calc ∑ x ∈ s, max ((e x : ℝ)) 0
        = ∑ x ∈ s, (ENNReal.ofReal (e x : ℝ)).toReal :=
          Finset.sum_congr rfl fun x _ => ENNReal.toReal_ofReal'.symm
      _ = (∑ x ∈ s, ENNReal.ofReal (e x : ℝ)).toReal :=
          (ENNReal.toReal_sum fun _ _ => ENNReal.ofReal_ne_top).symm
      _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hsum
      _ = 1 := by simp

/-- Step 2 of the proof of `exists_const_limsup_KP_eq_KP_jump_jump_semimeasure`:
from the `0'`-enumerable set `T` of accepted triples (complete and sound, see Step 1) get the
`0'`-lower-semicomputable semimeasure `ν(x) = sup {ε | ∃ N, ⟨N, x, ε⟩ ∈ T}`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_jump_semimeasure_sup
    {m : BitString → BitString → ℝ≥0∞} {T : ℕ × BitString × ℚ → Prop}
    (hT : PointToSet.IsREIn jumpSet T)
    (hcomp : ∀ (N : ℕ) (x : BitString) (q : ℚ),
        (∀ n, N ≤ n → ENNReal.ofReal (q : ℝ) ≤ m x (Nat.bits n)) → T (N, x, q))
    (hsound : ∀ (s : Finset BitString) (N : BitString → ℕ) (e : BitString → ℚ),
        (∀ x ∈ s, T (N x, x, e x)) → ∑ x ∈ s, max ((e x : ℝ)) 0 ≤ 1) :
    ∃ ν : BitString → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet ν ∧ (∀ x, 0 ≤ ν x) ∧
      (∀ s : Finset BitString, ∑ x ∈ s, ν x ≤ 1) ∧
      ∀ x, (Filter.liminf (fun n => m x (Nat.bits n)) Filter.atTop).toReal ≤ ν x := by
  classical
  have hT1 : ∀ N x (q : ℚ), T (N, x, q) → (q : ℝ) ≤ 1 := by
    intro N x q h
    have := hsound {x} (fun _ => N) (fun _ => q) (by simpa using h)
    simp only [Finset.sum_singleton] at this
    exact (le_max_left _ _).trans this
  let S : BitString → Set ℝ := fun x => {r | ∃ (N : ℕ) (q : ℚ), T (N, x, q) ∧ r = q}
  have hSne : ∀ x, (S x).Nonempty := fun x =>
    ⟨((0 : ℚ) : ℝ), 0, 0, hcomp 0 x 0 (fun n _ => by simp), rfl⟩
  have hSbdd : ∀ x, BddAbove (S x) := fun x =>
    ⟨1, by rintro r ⟨N, q, hq, rfl⟩; exact hT1 N x q hq⟩
  let ν : BitString → ℝ := fun x => sSup (S x)
  have hνle : ∀ x N (q : ℚ), T (N, x, q) → (q : ℝ) ≤ ν x := fun x N q h =>
    le_csSup (hSbdd x) ⟨N, q, h, rfl⟩
  have hν0 : ∀ x, 0 ≤ ν x := fun x => by simpa using hνle x 0 0 (hcomp 0 x 0 (fun n _ => by simp))
  refine ⟨ν, ?_, hν0, ?_, ?_⟩
  · -- lower cut is `0'`-c.e.
    have hF : PointToSet.IsREIn jumpSet
        (fun z : (BitString × ℚ) × (ℕ × ℚ) => T (z.2.1, z.1.1, z.2.2) ∧ z.1.2 < z.2.2) := by
      refine PointToSet.IsREIn.and ?_ ?_
      · have hf : Computable
            (fun z : (BitString × ℚ) × (ℕ × ℚ) => ((z.2.1, z.1.1, z.2.2) : ℕ × BitString × ℚ)) :=
          Computable.pair (Computable.fst.comp Computable.snd)
            (Computable.pair (Computable.fst.comp Computable.fst)
              (Computable.snd.comp Computable.snd))
        exact PointToSet.IsREIn.comp hT hf.computableIn
      · refine PointToSet.isREIn_of_computable_decide ?_
        exact computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
          (Computable.snd.comp Computable.snd)
    have hE := PointToSet.IsREIn.exists hF
    unfold PointToSet.IsLowerSemicomputableIn
    convert hE using 1
    funext w
    apply propext
    constructor
    · intro h
      obtain ⟨r, ⟨N, q, hq, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hSne w.1) h
      exact ⟨(N, q), hq, by exact_mod_cast hlt⟩
    · rintro ⟨⟨N, q⟩, hq, hlt⟩
      exact lt_of_lt_of_le (by exact_mod_cast hlt) (hνle w.1 N q hq)
  · intro s
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hex : ∀ x, ∃ (N : ℕ) (q : ℚ), T (N, x, q) ∧ ν x - δ / (s.card + 1) < q := by
      intro x
      have hpos : (0 : ℝ) < δ / (s.card + 1) := by positivity
      obtain ⟨r, ⟨N, q, hq, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hSne x)
        (show ν x - δ / (s.card + 1) < sSup (S x) by simp only [ν]; linarith)
      exact ⟨N, q, hq, hlt⟩
    choose N e hTe hlt using hex
    have h1 := hsound s N e (fun x _ => hTe x)
    have h2 : ∑ x ∈ s, ν x ≤ ∑ x ∈ s, (max ((e x : ℝ)) 0 + δ / (s.card + 1)) :=
      Finset.sum_le_sum fun x _ => by
        have := hlt x
        have := le_max_left ((e x : ℝ)) 0
        linarith
    rw [Finset.sum_add_distrib] at h2
    have h3 : ∑ x ∈ s, δ / (s.card + 1) ≤ δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (0 : ℝ) < s.card + 1 := by positivity
      rw [mul_div_assoc', div_le_iff₀ this]
      nlinarith
    linarith
  · intro x
    by_cases htop : Filter.liminf (fun n => m x (Nat.bits n)) Filter.atTop = ⊤
    · rw [htop]; simpa using hν0 x
    · refine le_of_forall_rat_lt_imp_le fun q hq => ?_
      by_cases hq0 : (q : ℝ) ≤ 0
      · exact hq0.trans (hν0 x)
      replace hq0 := not_le.mp hq0
      have hlt : ENNReal.ofReal (q : ℝ) <
          Filter.liminf (fun n => m x (Nat.bits n)) Filter.atTop := by
        rw [← ENNReal.ofReal_toReal htop]
        exact (ENNReal.ofReal_lt_ofReal_iff (hq0.trans hq)).mpr hq
      have hev := Filter.eventually_lt_of_lt_liminf hlt (by isBoundedDefault)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      exact hνle x N q (hcomp N x q fun n hn => (hN n hn).le)

/-- Step 4 of the proof of `exists_const_limsup_KP_eq_KP_jump` (the `≤` half,
the `0'`-semimeasure bound): the function `x ↦ liminf_n 2^{-K(x | n)}` is bounded by a
`0'`-lower-semicomputable semimeasure `ν` (nonnegative real-valued, every finite partial sum at
most `1`).

Proof idea: let `m(x | n) = 2^{-K_U(x | n)}` (or the a priori semimeasure of `U`); it is a
lower-semicomputable family with `∑ₓ m(x | n) ≤ 1` for every `n`. Enumerate all triples
`⟨N, x, ε⟩` (`ε` rational). Process them in turn, maintaining a family `m*` (initially `m`): the
triple is accepted if raising `m*(x | n)` to `max(m*(x | n), ε)` for all `n ≥ N` leaves
`∑ₓ m*(x | n) ≤ 1` for all `n` (a `Π₁` test, decidable with the oracle `0'`; the `m(x | n)` are
suprema of computable approximations). Let `ν(x)` be the supremum of the `ε` over accepted
triples with that `x`; it is `0'`-lower-semicomputable. For every finite set `S` take accepted
triples with `ε` close to `ν(x)` for each `x ∈ S` and `n` beyond all their `N`: then
`∑_{x ∈ S} ν(x) ≤ ∑ₓ m*(x | n) ≤ 1` (up to arbitrarily small slack). Finally if `ε < liminf_n
m(x | n)` and `m(x | n) ≥ ε` for `n ≥ N` then raising to `ε` changes nothing (`m* ≥ m`), so the
triple is accepted and `ν(x) ≥ ε`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_jump_semimeasure {U : Map}
    (hU : IsOptimalPrefixConditional U) :
    ∃ ν : BitString → ℝ, PointToSet.IsLowerSemicomputableIn jumpSet ν ∧ (∀ x, 0 ≤ ν x) ∧
      (∀ s : Finset BitString, ∑ x ∈ s, ν x ≤ 1) ∧
      ∀ x, (Filter.liminf (fun n => complexityWeight (KP U x (Nat.bits n))) Filter.atTop).toReal
        ≤ ν x := by
  have hsemi : IsConditionalSemimeasure (aprioriMeasure U) :=
    aprioriMeasure_isConditionalSemimeasure U hU.isPrefixMachine
  have hlsc : IsLSC (aprioriMeasure U) := aprioriMeasure_isLSC U hU.isPrefixDecompressor
  obtain ⟨T, hT, hcomp, hsound⟩ :=
    exists_const_limsup_KP_eq_KP_jump_accepted_triples hsemi hlsc
  obtain ⟨ν, hν, hν0, hνs, hνle⟩ :=
    exists_const_limsup_KP_eq_KP_jump_jump_semimeasure_sup hT hcomp hsound
  refine ⟨ν, hν, hν0, hνs, fun x => le_trans ?_ (hνle x)⟩
  have hle : Filter.liminf (fun n => complexityWeight (KP U x (Nat.bits n))) Filter.atTop ≤
      Filter.liminf (fun n => aprioriMeasure U x (Nat.bits n)) Filter.atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n =>
      complexityWeight_KP_le_aprioriMeasure U x (Nat.bits n))
  have hne : Filter.liminf (fun n => aprioriMeasure U x (Nat.bits n)) Filter.atTop ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (Filter.liminf_le_of_frequently_le'
        (Filter.Eventually.of_forall fun n =>
          (ENNReal.le_tsum x).trans (hsemi (Nat.bits n))).frequently)
  exact ENNReal.toReal_mono hne hle

/-- Step 5 of the proof of `exists_const_limsup_KP_eq_KP_jump` (relativized coding
theorem, upper bound for `K^{0'}`): if `ν : BitString → ℝ` is nonnegative,
`0'`-lower-semicomputable and every finite partial sum is at most `1`, then
`ν(x) ≤ 2^c · 2^{-K^{0'}(x)}` for an optimal prefix-free `0'`-decompressor `V`.

Proof idea: for `ν x > 0` the integer cost `g x = ⌊-log₂ ν x⌋ + 1` is upper semicomputable
relative to `0'` and `∑ₓ 2^{-g x} ≤ ∑ₓ ν x ≤ 1`; apply `PointToSet.oracle_coding_finite_mass`
(Kraft–Chaitin relative to `0'`) on the domain `{x | 0 < ν x}`, then pass from the chosen optimal
machine to `V` by optimality of `V`. For `ν x = 0` there is nothing to prove. -/
private theorem exists_const_limsup_KP_eq_KP_jump_jump_coding {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) {ν : BitString → ℝ}
    (hν : PointToSet.IsLowerSemicomputableIn jumpSet ν) (hν0 : ∀ x, 0 ≤ ν x)
    (hsum : ∀ s : Finset BitString, ∑ x ∈ s, ν x ≤ 1) :
    ∃ c : ℕ, ∀ x, ((2 : ℝ≥0∞)⁻¹) ^ c * ENNReal.ofReal (ν x) ≤ complexityWeight (KP V x []) := by
  classical
  -- the integer cost: least `n` with `2^{-n} < ν x`
  let gn : BitString → ℕ := fun x => sInf {n : ℕ | ((1 / 2 : ℝ)) ^ n < ν x}
  have hmem : ∀ x, 0 < ν x → ((1 / 2 : ℝ)) ^ gn x < ν x := by
    intro x hx
    have hne : {n : ℕ | ((1 / 2 : ℝ)) ^ n < ν x}.Nonempty := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨n, hn⟩
    exact Nat.sInf_mem hne
  have hmin : ∀ x, ∀ m < gn x, ν x ≤ ((1 / 2 : ℝ)) ^ m := by
    intro x m hm
    have := Nat.notMem_of_lt_sInf (s := {n : ℕ | ((1 / 2 : ℝ)) ^ n < ν x}) hm
    simpa using this
  have hle : ∀ x n, ((1 / 2 : ℝ)) ^ n < ν x → gn x ≤ n := fun x n hn => Nat.sInf_le hn
  let F : BitString → Prop := fun x => 0 < ν x
  let g : Subtype F → ℝ := fun w => (gn w.1 : ℝ)
  have hg : PointToSet.IsUpperSemicomputableOnIn jumpSet F g := by
    refine ⟨fun p : BitString × ℚ => ∃ n : ℕ, (n : ℚ) < p.2 ∧ (((1 / 2 : ℚ) ^ n : ℚ) : ℝ) < ν p.1,
      ?_, ?_, ?_⟩
    · have h1 : PointToSet.IsREIn jumpSet (fun t : (BitString × ℚ) × ℕ =>
          (((1 / 2 : ℚ) ^ t.2 : ℚ) : ℝ) < ν t.1.1) :=
        hν.comp (f := fun t : (BitString × ℚ) × ℕ => (t.1.1, (1 / 2 : ℚ) ^ t.2))
          ((Computable.fst.comp Computable.fst).pair
            (computable_half_pow.comp Computable.snd)).computableIn
      have h2 : Computable (fun t : (BitString × ℚ) × ℕ => decide ((t.2 : ℚ) < t.1.2)) :=
        computable₂_ratLt.comp (computable_nat_to_rat.comp Computable.snd)
          (Computable.snd.comp Computable.fst)
      exact ((PointToSet.isREIn_of_computable_decide h2).and h1).exists
    · rintro w q ⟨n, hnq, hn⟩
      have hn' : ((1 / 2 : ℝ)) ^ n < ν w := by simpa using hn
      have hpos : 0 < ν w := lt_of_le_of_lt (by positivity) hn'
      refine ⟨hpos, ?_⟩
      have h1 : (gn w : ℝ) ≤ n := by exact_mod_cast hle w n hn'
      have h2 : (n : ℝ) < q := by exact_mod_cast hnq
      exact h1.trans_lt h2
    · intro w ε hε
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show g w < g w + ε by linarith)
      refine ⟨q, ⟨gn w.1, ?_, ?_⟩, hq2⟩
      · have : (gn w.1 : ℝ) < q := hq1
        exact_mod_cast this
      · simpa using hmem w.1 w.2
  have hmass : (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w)) ≤ 1 := by
    calc (∑' w : Subtype F, (2 : ℝ≥0∞) ^ (-g w))
        ≤ ∑' w : Subtype F, ENNReal.ofReal (ν w.1) := by
          refine ENNReal.tsum_le_tsum fun w => ?_
          have h1 : (2 : ℝ≥0∞) ^ (-g w) = ENNReal.ofReal (((1 / 2 : ℝ)) ^ gn w.1) := by
            simp only [g]
            rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by norm_num),
              one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
            simp [ENNReal.inv_pow]
          rw [h1]
          exact ENNReal.ofReal_le_ofReal (hmem w.1 w.2).le
      _ ≤ ∑' x : BitString, ENNReal.ofReal (ν x) :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun x => ENNReal.ofReal (ν x))
      _ ≤ 1 := by
          rw [ENNReal.tsum_eq_iSup_sum]
          refine iSup_le fun s => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν0 x)]
          calc ENNReal.ofReal (∑ x ∈ s, ν x) ≤ ENNReal.ofReal 1 :=
                ENNReal.ofReal_le_ofReal (hsum s)
            _ = 1 := ENNReal.ofReal_one
  obtain ⟨c, hc⟩ := PointToSet.oracle_coding_finite_mass jumpSet F g hg 1 hmass
    ENNReal.one_lt_top
  have hspec := PointToSet.exists_optimalOraclePrefix_spec jumpSet
  obtain ⟨c', hc'⟩ := hV.2.2 _ hspec.1 hspec.2.1
  refine ⟨c + c' + 1, fun x => ?_⟩
  by_cases hx : 0 < ν x
  · have h1 : (PointToSet.oracleComplexity jumpSet x : ℝ) ≤ gn x + c := hc ⟨x, hx⟩
    have h2 : PointToSet.oracleComplexity jumpSet x ≤ gn x + c := by exact_mod_cast h1
    have h3 : KP V x [] ≤ ((gn x + c + c' : ℕ) : ℕ∞) := by
      refine (hc' x []).trans ?_
      have h4 : KP (PointToSet.optimalOraclePrefix jumpSet) x [] =
          (PointToSet.oracleComplexity jumpSet x : ENat) :=
        (PointToSet.oraclePrefixComplexity_coe jumpSet x []).symm
      rw [h4]
      exact_mod_cast Nat.add_le_add_right h2 c'
    have hgn : 1 ≤ gn x := by
      by_contra h0
      have h0' : gn x = 0 := by omega
      have := hmem x hx
      rw [h0', pow_zero] at this
      have h5 := hsum {x}
      simp only [Finset.sum_singleton] at h5
      linarith
    have hν_le : ν x ≤ ((1 / 2 : ℝ)) ^ (gn x - 1) := hmin x _ (by omega)
    have h6 : ENNReal.ofReal (ν x) ≤ 2 * ((2 : ℝ≥0∞)⁻¹) ^ gn x := by
      refine (ENNReal.ofReal_le_ofReal hν_le).trans ?_
      obtain ⟨k, hk⟩ : ∃ k, gn x = k + 1 := ⟨gn x - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, ENNReal.ofReal_pow (by norm_num), one_div,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      have h2' : ENNReal.ofReal 2 = 2 := by simp
      have h3' : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
      rw [h2', pow_succ, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ k), ← mul_assoc, h3', one_mul]
    calc ((2 : ℝ≥0∞)⁻¹) ^ (c + c' + 1) * ENNReal.ofReal (ν x)
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (c + c' + 1) * (2 * ((2 : ℝ≥0∞)⁻¹) ^ gn x) :=
          mul_le_mul' le_rfl h6
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (gn x + c + c') := by
          have h2' : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
          have e : ((2 : ℝ≥0∞)⁻¹) ^ (c + c' + 1) * (2 * ((2 : ℝ≥0∞)⁻¹) ^ gn x) =
              (2 * 2⁻¹) * (((2 : ℝ≥0∞)⁻¹) ^ (c + c') * ((2 : ℝ≥0∞)⁻¹) ^ gn x) := by
            rw [pow_succ]; ring
          rw [e, h2', one_mul, ← pow_add]
          congr 1; omega
      _ = complexityWeight (((gn x + c + c' : ℕ)) : ℕ∞) := (complexityWeight_coe _).symm
      _ ≤ complexityWeight (KP V x []) := complexityWeight_antitone h3
  · have : ν x = 0 := le_antisymm (not_lt.mp hx) (hν0 x)
    rw [this]; simp

/-- Step 2 of the proof of `exists_const_limsup_KP_eq_KP_jump` (conditional coding
theorem): a lower-semicomputable conditional semimeasure is dominated by `2^{-K_U}`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_coding {U : Map}
    (hU : IsOptimalPrefixConditional U) {m : BitString → BitString → ℝ≥0∞}
    (hm : IsConditionalSemimeasure m) (hlsc : IsLSC m) :
    ∃ c : ℕ, ∀ x z, ((2 : ℝ≥0∞)⁻¹) ^ c * m x z ≤ complexityWeight (KP U x z) := by
  obtain ⟨M, hM, c₀, hM_bound⟩ :=
    kraftChaitin_realization_bound hlsc 0 (fun z => by simpa using hm z)
  exact complexityWeight_dominates_of_prefix_realization hU hM hM_bound

/-- Weights to complexities: `2^{-n} · 2^{-a} ≤ 2^{-b}` with `a` finite gives `b ≤ a + n`. -/
private theorem exists_const_limsup_KP_eq_KP_jump_aux_le_of_weight (a b : ℕ∞) (n : ℕ)
    (ha : a ≠ ⊤) (h : ((2 : ℝ≥0∞)⁻¹) ^ n * complexityWeight a ≤ complexityWeight b) :
    b ≤ a + n := by
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  induction b using ENat.recTopCoe with
  | top =>
    simp only [complexityWeight_top, nonpos_iff_eq_zero] at h
    rw [← Nat.cast_add]
    simp [complexityWeight_coe] at h
  | coe j =>
    simp only [complexityWeight_coe, ← pow_add] at h
    have h2 : (2 : ℝ≥0∞)⁻¹ ^ (n + k) ≤ (2 : ℝ≥0∞)⁻¹ ^ j := h
    have : j ≤ n + k := by
      by_contra hlt
      have hlt : n + k < j := not_le.mp hlt
      rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_inv] at h2
      have h3 : (2 : ℝ≥0∞) ^ (n + k) < 2 ^ j :=
        by exact_mod_cast Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
      exact absurd h2 (not_le.mpr h3)
    exact_mod_cast (by omega : j ≤ k + n)

/-- **SUV Theorem 133 (Section 6.4.2, printed p. 206).**
`limsup_{n → ∞} K(x | n) = K^{0'}(x) + O(1)`.

Proof idea: by the coding theorem this is `liminf_n m(x | n) = m^{0'}(x)` up to a bounded factor.
`≥` — run a `0'`-probabilistic machine with output distribution `m^{0'}` using the `n`-step
approximation of `0'`. Each interval of random bits uses a finite part of the oracle.
`≤` — `x ↦ liminf_n m(x | n)` is a semimeasure (`tsum_liminf_le_one`). Bound it by a
`0'`-lower-semicomputable semimeasure: go through the triples `⟨N, x, ε⟩` and raise `m(x | n)`
to `ε` on the ray `n ≥ N` whenever the result is still a family of semimeasures (a
co-enumerable test). -/
theorem exists_const_limsup_KP_eq_KP_jump {U : Map} (hU : IsOptimalPrefixConditional U) {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) :
    ∃ c : ℕ, ∀ x,
      Filter.limsup (fun n => KP U x (Nat.bits n)) Filter.atTop ≤ KP V x [] + c ∧
        KP V x [] ≤ Filter.limsup (fun n => KP U x (Nat.bits n)) Filter.atTop + c := by
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_const_limsup_KP_eq_KP_jump_approx_semimeasure hV
  obtain ⟨c1, hc1⟩ := exists_const_limsup_KP_eq_KP_jump_coding hU hm1 hm2
  obtain ⟨ν, hν, hν0, hνsum, hνle⟩ := exists_const_limsup_KP_eq_KP_jump_jump_semimeasure hU
  obtain ⟨c2, hc2⟩ := exists_const_limsup_KP_eq_KP_jump_jump_coding hV hν hν0 hνsum
  refine ⟨c1 + c2, fun x => ⟨?_, ?_⟩⟩
  · by_cases ha : KP V x [] = ⊤
    · rw [ha]; simp
    · have hev : ∀ᶠ n in Filter.atTop,
          KP U x (Nat.bits n) ≤ KP V x [] + (c1 : ℕ∞) := by
        filter_upwards [hm3 x] with n hn
        refine exists_const_limsup_KP_eq_KP_jump_aux_le_of_weight _ _ c1 ha ?_
        exact (mul_le_mul' le_rfl hn).trans (hc1 x (Nat.bits n))
      refine (Filter.limsup_le_of_le (by isBoundedDefault) hev).trans ?_
      gcongr
      exact le_self_add
  · by_cases hL : Filter.limsup (fun n => KP U x (Nat.bits n)) Filter.atTop = ⊤
    · rw [hL]; simp
    · set L := Filter.limsup (fun n => KP U x (Nat.bits n)) Filter.atTop with hLdef
      obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp hL
      have hlt : L < ((ℓ + 1 : ℕ) : ℕ∞) := by
        rw [← hℓ]; exact_mod_cast Nat.lt_succ_self ℓ
      have hev : ∀ᶠ n in Filter.atTop, KP U x (Nat.bits n) ≤ L := by
        filter_upwards [Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)] with n hn
        rw [← hℓ]
        have h5 : KP U x (Nat.bits n) < ((ℓ + 1 : ℕ) : ℕ∞) := hn
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h5)
        rw [← hk] at h5 ⊢
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h5)
      have h1 : complexityWeight L ≤
          Filter.liminf (fun n => complexityWeight (KP U x (Nat.bits n))) Filter.atTop :=
        Filter.le_liminf_of_le (by isBoundedDefault)
          (hev.mono fun n hn => complexityWeight_antitone hn)
      have hne : Filter.liminf (fun n => complexityWeight (KP U x (Nat.bits n))) Filter.atTop
          ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (Filter.liminf_le_of_frequently_le'
            (Filter.Eventually.of_forall fun n => complexityWeight_le_one _).frequently)
      have h2 : Filter.liminf (fun n => complexityWeight (KP U x (Nat.bits n))) Filter.atTop ≤
          ENNReal.ofReal (ν x) := by
        rw [← ENNReal.ofReal_toReal hne]
        exact ENNReal.ofReal_le_ofReal (hνle x)
      have h3 : ((2 : ℝ≥0∞)⁻¹) ^ c2 * complexityWeight L ≤ complexityWeight (KP V x []) :=
        (mul_le_mul' le_rfl (h1.trans h2)).trans (hc2 x)
      have h4 := exists_const_limsup_KP_eq_KP_jump_aux_le_of_weight L _ c2 hL h3
      refine h4.trans ?_
      push_cast
      gcongr
      exact_mod_cast Nat.le_add_left c2 c1

/-- **SUV Section 6.4.2 (printed p. 207), unnumbered.** There is an optimal prefix-stable
decompressor for set conditions. Its complexity is `K(x ‖ A)`.

Proof idea: as for Problem 206. Make each partial computable `D_z` prefix-stable in `p`
uniformly in `z` (Theorem 48, `Prefix.StableDecompressors`) and let `U(ẑ p, y) = D_z(p, y)`;
prefixing `ẑ` keeps prefix-stability, and "`D_z(p, y) = x` for all `y ∈ A`" transfers to
`ẑ p`. -/
theorem exists_isOptimalPrefixStableSetCond : ∃ U, IsOptimalPrefixStableSetCond U := by
  refine ⟨stabUniversal, ⟨stabUniversal_partrec, stabUniversal_isPrefixStableMachine⟩, ?_⟩
  intro D hD
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  refine ⟨(unaryPrefix (Encodable.encode code)).length, fun x A => ?_⟩
  apply sInfLeSInfAdd
  rintro l ⟨p, hp, rfl⟩
  refine ⟨((unaryPrefix (Encodable.encode code) ++ p).length : ℕ∞),
    ⟨unaryPrefix (Encodable.encode code) ++ p, fun y hy => ?_, rfl⟩, ?_⟩
  · obtain ⟨m, htriple⟩ := exists_stabTriple_of_produces hc (hp y hy)
    have hfind : stabFind code p y m = some x :=
      stabFind_eq_some_iff.mpr ⟨p, htriple, stabOK_of_prefixStable hc hD.2 m, List.prefix_refl p⟩
    change x ∈ stabUniversal _
    rw [stabUniversal_apply]
    exact stabMap_mem_of_find hfind
  · rw [List.length_append]
    push_cast
    rw [add_comm]

/-- **SUV Section 6.4.2 (printed p. 207), unnumbered.** There is an optimal prefix-free
decompressor for set conditions. Its complexity is `K'(x ‖ A)`.

Proof idea: as for the optimal prefix-free conditional decompressor (`IsOptimalPrefixConditional`).
Trim each partial computable `D_z` to a prefix-free machine, for every condition, without
changing it if it is already prefix-free, and let `U(ẑ p, y) = D_z(p, y)`. -/
theorem exists_isOptimalPrefixFreeSetCond : ∃ U, IsOptimalPrefixFreeSetCond U := by
  have hEnum : ∀ i, IsPrefixDecompressor (enumeratedPrefixMachine i) := by
    intro i
    unfold enumeratedPrefixMachine
    cases (Encodable.decode i : Option Nat.Partrec.Code) with
    | none =>
      exact ⟨Partrec.none, fun y p hp q hq hpre => False.elim hp⟩
    | some c => exact prefixFiltered_isPrefixDecompressor c
  have hU : IsPrefixDecompressor universalPrefixMachine :=
    ⟨universalPrefixMachine_isDecompressor,
      taggedUnion_isPrefixMachine (fun i => (hEnum i).isPrefixMachine)⟩
  refine ⟨universalPrefixMachine, hU, fun D hD => ?_⟩
  obtain ⟨code, hcode⟩ := exists_code_of_isDecompressor D hD.isDecompressor
  have hi : enumeratedPrefixMachine (Encodable.encode code) = D := by
    unfold enumeratedPrefixMachine
    rw [Encodable.encodek]
    exact prefixFiltered_eq_of_isPrefixDecompressor code hD hcode
  refine ⟨Encodable.encode code + 1, fun x A => ?_⟩
  have hsim := taggedUnionSimulation enumeratedPrefixMachine (Encodable.encode code)
  rw [hi] at hsim
  have hle : setCondK universalPrefixMachine x A ≤
      setCondK D x A + ((Encodable.encode code + 1 : ℕ) : ℕ∞) := by
    rcases Set.eq_empty_or_nonempty
        {l : ℕ∞ | ∃ p, (∀ y ∈ A, produces D p y x) ∧ l = p.length} with he | hne
    · have : setCondK D x A = ⊤ := by unfold setCondK; rw [he, sInf_empty]
      rw [this]; simp
    · obtain ⟨p, hp, hl⟩ := csInf_mem (s := _) hne
      have h1 : setCondK universalPrefixMachine x A ≤
          ((hsim.translate p).length : ℕ∞) :=
        sInf_le ⟨_, fun y hy => hsim.simulates p y x (hp y hy), rfl⟩
      have h2 : ((hsim.translate p).length : ℕ∞) ≤
          (p.length : ℕ∞) + ((Encodable.encode code + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast hsim.length_le p
      have hl' : setCondK D x A = (p.length : ℕ∞) := hl
      rw [hl']
      exact h1.trans h2
  exact_mod_cast hle

/-- The prefix extension of a machine with code `code` produces everything the machine itself
produces. -/
private lemma exists_const_prefixStableSetCond_le_prefixFreeSetCond_aux_mem {V : Map}
    {code : Nat.Partrec.Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    (hV : IsPrefixMachine V) {p c z : BitString} (hz : produces V p c z) :
    z ∈ prefixExtensionMap code (p, c) := by
  have hmem : Encodable.encode z ∈ code.eval (Encodable.encode (p, c)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, c), by simp, Part.mem_map Encodable.encode hz⟩
  obtain ⟨t, ht⟩ : ∃ t, Nat.Partrec.Code.evaln t code (Encodable.encode (p, c))
      = some (Encodable.encode z) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    exact ⟨k, Option.mem_def.mp hk⟩
  have hn_out : prefixExtensionOut code p c (Nat.pair p.length t) = some z := by
    unfold prefixExtensionOut
    simp only [Nat.unpair_pair]
    have hdec : decide (p.length ≤ p.length) = true := decide_eq_true (le_refl _)
    rw [hdec]
    simp only [ite_true, List.take_length, ht, Option.bind_some, Encodable.encodek]
  have hcheck : prefixExtensionCheck code p c (Nat.pair p.length t) = true := by
    unfold prefixExtensionCheck; rw [hn_out]; rfl
  have hrdom : (Nat.rfind (show ℕ →. Bool from fun m =>
      Part.some (prefixExtensionCheck code p c m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length t, by rw [Part.mem_some_iff, hcheck], fun {m} _ => Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : prefixExtensionCheck code p c n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hcheck'
  have hmem_p : x' ∈ prefixExtensionMap code (p, c) := by
    unfold prefixExtensionMap
    rw [Part.mem_bind_iff]
    exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hx'⟩
  obtain ⟨p', hp'p, hp'prod⟩ := prefixExtensionMap_mem_imp_produces hc hmem_p
  have hp_eq : p' = p := IsPrefixMachine.eq_of_prefix hV hp'prod hz hp'p
  subst hp_eq
  rw [Part.mem_unique hz hp'prod]
  exact hmem_p

/-- **SUV Section 6.4.2 (printed p. 208), unnumbered.** `K(x ‖ A) ≤ K'(x ‖ A) + O(1)`, the
second of the inequalities `-log m(k ‖ A) ≤ K(k ‖ A) + O(1) ≤ K'(k ‖ A) + O(1)`. The first one
needs probabilistic machines with input and is not stated. Kalinina's result that the second
inequality is not an equality is cited, not proved, and is not stated.

Proof idea: extend a prefix-free decompressor to a prefix-stable one by letting `p` produce
what its unique halting prefix produces. -/
theorem exists_const_prefixStableSetCond_le_prefixFreeSetCond {U : Map}
    (hU : IsOptimalPrefixStableSetCond U) {V : Map} (hV : IsOptimalPrefixFreeSetCond V) :
    ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK V x A + c := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.1.1
  have hW : IsPrefixStableDecompressor (prefixExtensionMap code) :=
    ⟨prefixExtensionMap_partrec code, prefixExtensionMap_isPrefixStableMachine hc hV.1.2⟩
  obtain ⟨c, hcW⟩ := hU.2 _ hW
  refine ⟨c, fun x A => (hcW x A).trans (add_le_add ?_ le_rfl)⟩
  exact sInf_le_sInf fun _ ⟨p, hp, hl⟩ =>
    ⟨p, fun y hy => exists_const_prefixStableSetCond_le_prefixFreeSetCond_aux_mem hc hV.1.2
      (hp y hy), hl⟩

/-- The stage-`s` count: the number of strings `w` of length `s` having a prefix `q` such that
the code `code` halts within `s` steps on `(q, y)` with output `x`. -/
private def exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
    (code : Nat.Partrec.Code) (s : ℕ) (x y : BitString) : ℕ :=
  ((exactLengthPrograms s).filter (fun w =>
    (List.range (s + 1)).any (fun i =>
      decide (Nat.Partrec.Code.evaln s code (Encodable.encode (w.take i, y))
        = some (Encodable.encode x))))).length

/-- Step 1 of the proof of
`exists_const_iSup_KP_le_prefixStableSetCond_semimeasure`:
the stage-`s` counts `a(s,x,y)` of the cylinder union are computable in `(s, x, y)`
(bounded simulation of the code via `evaln`). -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_computable
    (code : Nat.Partrec.Code) :
    Computable (fun r : ℕ × BitString × BitString =>
      exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
        code r.1 r.2.1 r.2.2) := by
  unfold exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
  have hs : Primrec (fun r : ℕ × BitString × BitString => r.1) := Primrec.fst
  have hlist : Primrec (fun r : ℕ × BitString × BitString => exactLengthPrograms r.1) :=
    primrec_exactLengthPrograms.comp hs
  have hbody : Primrec₂ (fun (r : ℕ × BitString × BitString) (w : BitString) =>
      (List.range (r.1 + 1)).any (fun i =>
        decide (Nat.Partrec.Code.evaln r.1 code (Encodable.encode (w.take i, r.2.2))
          = some (Encodable.encode r.2.1)))) := by
    refine list_any_primrec (f := fun q : (ℕ × BitString × BitString) × BitString =>
      List.range (q.1.1 + 1)) (Primrec.list_range.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))) ?_
    have hq1 : Primrec (fun q : ((ℕ × BitString × BitString) × BitString) × ℕ => q.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hev : Primrec (fun q : ((ℕ × BitString × BitString) × BitString) × ℕ =>
        Nat.Partrec.Code.evaln q.1.1.1 code
          (Encodable.encode (q.1.2.take q.2, q.1.1.2.2))) :=
      (evaln_primrec code).comp hq1
        (Primrec.encode.comp (Primrec.pair
          (Primrec.list_take.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
    have hrhs : Primrec (fun q : ((ℕ × BitString × BitString) × BitString) × ℕ =>
        some (Encodable.encode q.1.1.2.1)) :=
      Primrec.option_some.comp (Primrec.encode.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
    exact ((PrimrecRel.decide Primrec.eq).comp hev hrhs).to₂
  exact (Primrec.list_length.comp (Primrec.list_filter hlist hbody)).to_comp

/-- Step 2 of the proof of
`exists_const_iSup_KP_le_prefixStableSetCond_semimeasure`:
monotonicity: every string counted at stage `s` yields two counted extensions at stage `s + 1`
(the run that halted within `s` steps also halts within `s + 1` steps), so
`2 * a(s,x,y) ≤ a(s+1,x,y)`. -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_mono
    (code : Nat.Partrec.Code) (s : ℕ) (x y : BitString) :
    2 * exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
        code s x y ≤
      exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
        code (s + 1) x y := by
  classical
  unfold exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
  set A := (exactLengthPrograms s).filter (fun w =>
    (List.range (s + 1)).any (fun i =>
      decide (Nat.Partrec.Code.evaln s code (Encodable.encode (w.take i, y))
        = some (Encodable.encode x)))) with hAdef
  set B := (exactLengthPrograms (s + 1)).filter (fun w =>
    (List.range (s + 1 + 1)).any (fun i =>
      decide (Nat.Partrec.Code.evaln (s + 1) code (Encodable.encode (w.take i, y))
        = some (Encodable.encode x)))) with hBdef
  have hA : A.Nodup := (exactLengthPrograms_nodup s).filter _
  have hB : B.Nodup := (exactLengthPrograms_nodup (s + 1)).filter _
  have key : (A.toFinset ×ˢ (Finset.univ : Finset Bool)).card ≤ B.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun q => q.1 ++ [q.2]) ?_ ?_
    · intro q hq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset,
        Finset.coe_univ, Set.mem_univ, and_true, hAdef, List.mem_filter] at hq
      obtain ⟨hq1, hq2⟩ := hq
      have hlen := exactLengthPrograms_length_eq _ _ hq1
      simp only [Finset.mem_coe, List.mem_toFinset, hBdef, List.mem_filter]
      refine ⟨?_, ?_⟩
      · have := mem_exactLengthPrograms_self (q.1 ++ [q.2])
        simpa [hlen] using this
      · rw [List.any_eq_true] at hq2 ⊢
        obtain ⟨i, hi, hi2⟩ := hq2
        refine ⟨i, ?_, ?_⟩
        · simp only [List.mem_range] at hi ⊢; omega
        · have hi' : i ≤ s := by simp only [List.mem_range] at hi; omega
          have hi3 : Nat.Partrec.Code.evaln s code (Encodable.encode (q.1.take i, y))
              = some (Encodable.encode x) := of_decide_eq_true hi2
          have hlen' : i ≤ q.1.length := by omega
          rw [List.take_append_of_le_length hlen']
          have := Nat.Partrec.Code.evaln_mono (Nat.le_succ s)
            (Option.mem_def.mpr hi3)
          exact decide_eq_true (Option.mem_def.mp this)
    · intro q hq q' hq' h
      have h1 : q.1 ++ [q.2] = q'.1 ++ [q'.2] := h
      have h2 : q.1 = q'.1 ∧ [q.2] = [q'.2] := List.append_inj h1 (by
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset,
          hAdef, List.mem_filter] at hq hq'
        have := exactLengthPrograms_length_eq _ _ hq.1.1
        have := exactLengthPrograms_length_eq _ _ hq'.1.1
        omega)
      exact Prod.ext h2.1 (by simpa using h2.2)
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    List.toFinset_card_of_nodup hA, List.toFinset_card_of_nodup hB] at key
  omega

/-- Step 3 of the proof of
`exists_const_iSup_KP_le_prefixStableSetCond_semimeasure`:
disjointness. If `code` computes a prefix-stable decompressor `D`, then for every stage `s`,
condition `y` and finite set `F` of outputs, `∑_{x ∈ F} a(s,x,y) ≤ 2^s`: a string `w` counted for
`x₁` and for `x₂` has prefixes `q₁, q₂` with `D(q₁,y) = x₁`, `D(q₂,y) = x₂`; they are comparable,
so by prefix stability the longer one produces both, whence `x₁ = x₂`. The counted sets for
different `x` are thus disjoint subsets of the `2^s` strings of length `s`. -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_sum
    {D : Map} (hD : IsPrefixStableDecompressor D) (code : Nat.Partrec.Code)
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (D a)))
    (s : ℕ) (y : BitString) (F : Finset BitString) :
    ∑ x ∈ F,
      exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
        code s x y ≤ 2 ^ s := by
  classical
  unfold exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
  set P : BitString → BitString → Prop := fun x w =>
    ∃ i ∈ List.range (s + 1), Nat.Partrec.Code.evaln s code
      (Encodable.encode (w.take i, y)) = some (Encodable.encode x) with hP
  have hmem : ∀ x w, P x w → ∃ i, x ∈ D (w.take i, y) := by
    intro x w ⟨i, _, hi⟩
    refine ⟨i, ?_⟩
    have h1 := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hi)
    rw [hc] at h1
    simp only [Encodable.encodek, Part.ofOption] at h1
    rw [Part.mem_bind_iff] at h1
    obtain ⟨a, ha, hx⟩ := h1
    rw [Part.mem_map_iff] at hx
    obtain ⟨x', hx', hxe⟩ := hx
    have := Encodable.encode_injective hxe
    subst this
    rw [Part.mem_some_iff] at ha
    subst ha
    exact hx'
  have hdisj : ∀ x₁ x₂ w, P x₁ w → P x₂ w → x₁ = x₂ := by
    intro x₁ x₂ w h1 h2
    obtain ⟨i, hi⟩ := hmem _ _ h1
    obtain ⟨j, hj⟩ := hmem _ _ h2
    rcases le_total i j with hij | hij
    · have hpre : w.take i <+: w.take j := by
        have h := List.take_prefix i (w.take j)
        rwa [List.take_take, min_eq_left hij] at h
      have := hD.2 y (w.take i) (w.take j) x₁ hi hpre
      exact Part.mem_unique this hj
    · have hpre : w.take j <+: w.take i := by
        have h := List.take_prefix j (w.take i)
        rwa [List.take_take, min_eq_left hij] at h
      have := hD.2 y (w.take j) (w.take i) x₂ hj hpre
      exact Part.mem_unique hi this
  have hsum : ∑ x ∈ F, ((exactLengthPrograms s).filter (fun w =>
      (List.range (s + 1)).any (fun i =>
        decide (Nat.Partrec.Code.evaln s code (Encodable.encode (w.take i, y))
          = some (Encodable.encode x))))).length
      = ∑ x ∈ F, ((exactLengthPrograms s).toFinset.filter (P x)).card := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← List.toFinset_card_of_nodup (((exactLengthPrograms_nodup s)).filter _),
      List.toFinset_filter]
    congr 1
    ext w
    simp only [Finset.mem_filter, List.mem_toFinset, hP, List.any_eq_true, decide_eq_true_eq]
  rw [hsum, ← Finset.card_biUnion]
  · calc _ ≤ (exactLengthPrograms s).toFinset.card :=
          Finset.card_le_card (Finset.biUnion_subset.mpr fun x _ => Finset.filter_subset _ _)
      _ = 2 ^ s := by
          rw [List.toFinset_card_of_nodup (exactLengthPrograms_nodup s),
            length_exactLengthPrograms]
  · intro x₁ _ x₂ _ hne
    refine Finset.disjoint_left.mpr fun w h1 h2 => hne ?_
    exact hdisj _ _ w (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2

/-- Step 4 of the proof of
`exists_const_iSup_KP_le_prefixStableSetCond_semimeasure`:
the lower bound. If `code` computes `D` and `D(p, y) = x`, then for all large `s` all `2^(s-l(p))`
extensions of `p` of length `s` are counted, i.e. `2^s ≤ a(s,x,y) * 2^{l(p)}`. -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_lower
    {D : Map} (code : Nat.Partrec.Code)
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (D a)))
    {p y x : BitString} (hp : produces D p y x) :
    ∃ s₀, ∀ s ≥ s₀, 2 ^ s ≤
      exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
        code s x y * 2 ^ p.length := by
  classical
  have hmem : Encodable.encode x ∈ code.eval (Encodable.encode (p, y)) := by
    rw [hc]
    rw [Part.mem_bind_iff]
    exact ⟨(p, y), by rw [Part.mem_ofOption]; simp, Part.mem_map _ hp⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨max k p.length, fun s hs => ?_⟩
  have hks : k ≤ s := le_trans (le_max_left _ _) hs
  have hps : p.length ≤ s := le_trans (le_max_right _ _) hs
  have hk' : Nat.Partrec.Code.evaln s code (Encodable.encode (p, y))
      = some (Encodable.encode x) :=
    Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hks hk)
  set A := (exactLengthPrograms s).filter (fun w =>
    (List.range (s + 1)).any (fun i =>
      decide (Nat.Partrec.Code.evaln s code (Encodable.encode (w.take i, y))
        = some (Encodable.encode x)))) with hAdef
  have hA : A.Nodup := (exactLengthPrograms_nodup s).filter _
  have key : (Finset.image (fun u => p ++ u) (exactLengthPrograms (s - p.length)).toFinset).card
      ≤ A.toFinset.card := by
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_image, List.mem_toFinset] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hulen := exactLengthPrograms_length_eq _ _ hu
    simp only [List.mem_toFinset, hAdef, List.mem_filter]
    refine ⟨mem_exactLengthPrograms_of_length _ _ (by simp [hulen]; omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨p.length, by simp only [List.mem_range]; omega, ?_⟩
    rw [List.take_left]
    exact decide_eq_true hk'
  rw [Finset.card_image_of_injective _ (List.append_right_injective p),
    List.toFinset_card_of_nodup (exactLengthPrograms_nodup _), length_exactLengthPrograms,
    List.toFinset_card_of_nodup hA] at key
  calc 2 ^ s = 2 ^ (s - p.length) * 2 ^ p.length := by
        rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul_right _ key

/-- Step 1 of the proof of
`exists_const_iSup_KP_le_prefixStableSetCond_KP_le_condK_stable`: for a prefix-stable
decompressor `D` there is a lower semicomputable conditional semimeasure `m` with
`2^{-l(p)} ≤ m x y` whenever `D(p, y) = x`.

Proof idea: `m(x | y) = λ{ω : some prefix of ω is mapped to x by D(·, y)}`, the measure of the
union of the cylinders `Ω_p` over all `p` with `D(p, y) = x`. For fixed `y` the sets for different
`x` are disjoint (if `ω` has prefixes `p₁, p₂` with `D(p₁, y) = x₁`, `D(p₂, y) = x₂`, the longer
one extends both, so by prefix stability `D` outputs both `x₁` and `x₂` on it, hence `x₁ = x₂`),
so `∑ₓ m(x | y) ≤ 1`. It is lower semicomputable (uniformly in `x, y`): enumerate the graph of `D`
and add up the (dyadic) measure of the finite unions of cylinders found so far. If `D(p, y) = x`
then the cylinder `Ω_p` has measure `2^{-l(p)}`, so `m(x | y) ≥ 2^{-l(p)}`. -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_semimeasure
    {D : Map} (hD : IsPrefixStableDecompressor D) :
    ∃ m : BitString → BitString → ℝ≥0∞, IsConditionalSemimeasure m ∧ IsLSC m ∧
      ∀ x y p, produces D p y x → complexityWeight (programLength p) ≤ m x y := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hD.1
  have step2 :=
    exists_const_iSup_KP_le_prefixStableSetCond_mono
      code
  have step3 :=
    exists_const_iSup_KP_le_prefixStableSetCond_sum
      hD code hc
  have step4 := fun (p y x : BitString) (hp : produces D p y x) =>
    exists_const_iSup_KP_le_prefixStableSetCond_lower
      (D := D) code hc hp
  have step1 :=
    exists_const_iSup_KP_le_prefixStableSetCond_computable
      code
  generalize
    exists_const_iSup_KP_le_prefixStableSetCond_semimeasure_stableApprox
      code = a at step1 step2 step3 step4
  have h2s : ∀ s : ℕ, (2 : ℝ≥0∞) ^ s ≠ 0 := fun s => pow_ne_zero _ (by norm_num)
  have h2t : ∀ s : ℕ, (2 : ℝ≥0∞) ^ s ≠ ⊤ := fun s => ENNReal.pow_ne_top (by norm_num)
  have hmono : ∀ s x y, dyadicValue (a s x y) s ≤ dyadicValue (a (s + 1) x y) (s + 1) := by
    intro s x y
    have h : (2 : ℝ≥0∞) * (a s x y : ℝ≥0∞) ≤ (a (s + 1) x y : ℝ≥0∞) := by
      exact_mod_cast step2 s x y
    unfold dyadicValue
    calc (a s x y : ℝ≥0∞) / 2 ^ s = (2 * (a s x y : ℝ≥0∞)) / 2 ^ (s + 1) := by
          rw [pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl (h2s s)) (Or.inr (by norm_num)),
            mul_assoc ((2 ^ s : ℝ≥0∞)⁻¹), ← mul_assoc ((2 : ℝ≥0∞)⁻¹),
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (a (s + 1) x y : ℝ≥0∞) / 2 ^ (s + 1) := ENNReal.div_le_div_right h _
  have hlsc : IsLSC (fun x y => ⨆ s, dyadicValue (a s x y) s) :=
    ⟨a, hmono, fun _ _ => rfl, step1⟩
  refine ⟨fun x y => ⨆ s, dyadicValue (a s x y) s, ?_, hlsc, ?_⟩
  · intro y
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    rw [ENNReal.finsetSum_iSup_of_monotone (f := fun x s => dyadicValue (a s x y) s)
      (fun x => monotone_nat_of_le_succ (fun s => hmono s x y))]
    refine iSup_le fun s => ?_
    have h : (∑ x ∈ F, (a s x y : ℝ≥0∞)) ≤ 2 ^ s := by exact_mod_cast step3 s y F
    calc ∑ x ∈ F, dyadicValue (a s x y) s = (∑ x ∈ F, (a s x y : ℝ≥0∞)) / 2 ^ s := by
          unfold dyadicValue
          simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]
      _ ≤ 2 ^ s / 2 ^ s := ENNReal.div_le_div_right h _
      _ = 1 := ENNReal.div_self (h2s s) (h2t s)
  · intro x y p hp
    obtain ⟨s₀, hs₀⟩ := step4 p y x hp
    refine le_iSup_of_le (max s₀ p.length) ?_
    have h : (2 : ℝ≥0∞) ^ (max s₀ p.length) ≤ (a (max s₀ p.length) x y : ℝ≥0∞) * 2 ^ p.length := by
      exact_mod_cast hs₀ _ (le_max_left _ _)
    unfold dyadicValue
    rw [complexityWeight_programLength, progWeight, ENNReal.le_div_iff_mul_le (Or.inl (h2s _))
      (Or.inl (h2t _))]
    calc ((2 : ℝ≥0∞)⁻¹) ^ programLength p * 2 ^ (max s₀ p.length)
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ programLength p * ((a (max s₀ p.length) x y : ℝ≥0∞) * 2 ^ p.length) :=
          mul_le_mul_right h _
      _ = a (max s₀ p.length) x y := by
          have h1 : ((2 : ℝ≥0∞)⁻¹) ^ programLength p * 2 ^ p.length = 1 := by
            rw [programLength, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
              one_pow]
          rw [mul_left_comm, h1, mul_one]

/-- Step 1 of the proof of `exists_const_iSup_KP_le_prefixStableSetCond`: the
converse direction of Theorem 55 (`Prefix.PrefixStableComplexity`). For an optimal prefix-free
conditional decompressor `V` and any prefix-stable decompressor `D`, the prefix-free complexity
is at most the `D`-complexity plus a constant: `KP V x y ≤ condK D x y + c`.

Proof idea: `m_D(x | y) = λ{ω : some prefix of ω is mapped to x by D(·, y)}` is a conditional
lower semicomputable semimeasure (the sets for different `x` are disjoint by prefix-stability,
and a `D`-program `p` for `x` gives measure at least `2^{-l(p)}`); apply the conditional coding
theorem (`conditional_coding_equivalence`). -/
private theorem exists_const_iSup_KP_le_prefixStableSetCond_KP_le_condK_stable
    {V : Map} (hV : IsOptimalPrefixConditional V) {D : Map}
    (hD : IsPrefixStableDecompressor D) :
    ∃ c : ℕ, ∀ x y, KP V x y ≤ condK D x y + (c : ℕ∞) := by
  obtain ⟨m, hs, hl, hge⟩ :=
    exists_const_iSup_KP_le_prefixStableSetCond_semimeasure hD
  obtain ⟨M, hM, c₀, hM'⟩ := kraftChaitin_realization_bound hl 0 (fun z => by simpa using hs z)
  obtain ⟨c, hc⟩ := complexityWeight_dominates_of_prefix_realization hV hM hM'
  refine ⟨c, fun x y => ?_⟩
  by_cases hne : (candidateLengths D x y).Nonempty
  · obtain ⟨p, hp, hpl⟩ := csInf_mem hne
    have hcK : condK D x y = (p.length : ℕ∞) := hpl.symm
    rw [hcK]
    exact le_add_nat_of_complexityWeight_le (by simp)
      ((mul_le_mul_right (hge x y p hp) _).trans (hc x y))
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have : condK D x y = ⊤ := by unfold condK; rw [hne]; exact sInf_empty
    rw [this]; simp

/-- **SUV Section 6.4.2 (printed p. 208), unnumbered.** `K(x ‖ A)` is at least
`sup_{a ∈ A} K(x | a)` up to `O(1)`. `K(x | a)` is the library's prefix-free conditional
complexity `KP`.

Proof idea: a prefix-stable set-condition decompressor is in particular a prefix-stable
conditional decompressor. Prefix-stable and prefix-free conditional complexities agree up to
`O(1)`. -/
theorem exists_const_iSup_KP_le_prefixStableSetCond {U : Map}
    (hU : IsOptimalPrefixStableSetCond U) {V : Map} (hV : IsOptimalPrefixConditional V) :
    ∃ c : ℕ, ∀ x A, (⨆ a ∈ A, KP V x a) ≤ setCondK U x A + c := by
  obtain ⟨c, hc⟩ :=
    exists_const_iSup_KP_le_prefixStableSetCond_KP_le_condK_stable hV hU.1
  refine ⟨c, fun x A => iSup₂_le fun a ha => (hc x a).trans (add_le_add_left ?_ _)⟩
  exact le_sInf fun l ⟨p, hp, hl⟩ => hl ▸ sInf_le ⟨p, hp a ha, rfl⟩

/-- Step 1 of the proof of `exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump`: the
finite approximations of a `0'`-computable map (the analogue, for the condition `[]`, of the
limit lemma of Theorem 131). For every map `V` computable relative to `0'` there is a computable
list-valued function `L` of the stage `m` whose entries `(p, u, z)` (read: "at stage `m`, with an
oracle prefix of length `u`, the program `p` gives `z`") satisfy:

* soundness for short oracle prefixes: for every `u`, from some stage on every entry with
  `u' ≤ u` is a true computation, `V (p, []) = z`;
* completeness: if `V (p, []) = x`, then from some stage on `(p, u, x)` is an entry, for one
  fixed `u`.

Proof idea: take the exact string operator `Φ` of `V` (`exists_exact_string_operator`):
`V (p, []) = x` iff `Φ (0'|u, (p, [])) = x` for some `u`. Let `0'_m` be the set of `e` such that
`φ_e (e)` halts within `m` steps, and let `L m` list the `(p, u, z)` with `encode p < m`, `u < m`
and `Φ (0'_m|u, (p, [])) = z` within `m` steps. For a fixed `u` the prefixes `0'_m|u` are
eventually equal to `0'|u`, and then every entry with `u' ≤ u` is a true computation. -/
private theorem exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_approx {V : Map}
    (hV : IsDecompressorIn (charOracle jumpSet) V) :
    ∃ L : ℕ → List (BitString × ℕ × BitString), Computable L ∧
      (∀ u, ∃ M, ∀ m ≥ M, ∀ p u' z, (p, u', z) ∈ L m → u' ≤ u → produces V p [] z) ∧
      (∀ p x, produces V p [] x → ∃ u M, ∀ m ≥ M, (p, u, x) ∈ L m) := by
  classical
  obtain ⟨Φ, hΦ, -, hex⟩ := PointToSet.exists_exact_string_operator
    (fun k => if k ∈ jumpSet then 1 else 0) (mapToNatFun V) hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hΦ
  have hceval : ∀ w : List ℕ × ℕ, c.eval (Encodable.encode w) = Φ w := by
    intro w
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.map_id' (fun _ => rfl) _
  -- the stage-`m` approximation of the first `u` bits of `0'`
  let pre : ℕ → ℕ → List ℕ := fun m u =>
    (List.range u).map fun k => bif (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k)
        k).isSome then 1 else 0
  let entry : ℕ → ℕ → Option (BitString × ℕ × BitString) := fun m r =>
    (Encodable.decode (α := BitString) r.unpair.1).bind fun p =>
      (Nat.Partrec.Code.evaln m c (Encodable.encode (pre m r.unpair.2,
        Encodable.encode (p, ([] : BitString))))).bind fun v =>
        (Encodable.decode (α := BitString) v).map fun z => (p, r.unpair.2, z)
  have hpre_prim : Primrec₂ pre := by
    have hg : Primrec₂ (fun (a : ℕ × ℕ) (k : ℕ) =>
        bif (Nat.Partrec.Code.evaln a.1 (Denumerable.ofNat Nat.Partrec.Code k) k).isSome then 1 else
            0) := by
      have hev : Primrec (fun b : (ℕ × ℕ) × ℕ =>
          Nat.Partrec.Code.evaln b.1.1 (Denumerable.ofNat Nat.Partrec.Code b.2) b.2) :=
        Nat.Partrec.Code.primrec_evaln.comp (((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.snd)).pair Primrec.snd)
      exact (Primrec.cond (Primrec.option_isSome.comp hev) (Primrec.const 1)
        (Primrec.const 0)).to₂
    exact (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hg).to₂
  have hentry_prim : Primrec₂ entry := by
    have hdec : Primrec (fun a : ℕ × ℕ => Encodable.decode (α := BitString) a.2.unpair.1) :=
      Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
    have hu : Primrec (fun b : (ℕ × ℕ) × BitString => b.1.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
    have hin : Primrec (fun b : (ℕ × ℕ) × BitString => Encodable.encode (pre b.1.1 b.1.2.unpair.2,
        Encodable.encode (b.2, ([] : BitString)))) :=
      Primrec.encode.comp ((hpre_prim.comp (Primrec.fst.comp Primrec.fst) hu).pair
        (Primrec.encode.comp (Primrec.snd.pair (Primrec.const ([] : BitString)))))
    have hev : Primrec (fun b : (ℕ × ℕ) × BitString => Nat.Partrec.Code.evaln b.1.1 c
        (Encodable.encode (pre b.1.1 b.1.2.unpair.2, Encodable.encode (b.2, ([] : BitString))))) :=
      Nat.Partrec.Code.primrec_evaln.comp (((Primrec.fst.comp Primrec.fst).pair (Primrec.const
          c)).pair hin)
    have hlast : Primrec₂ (fun (b : (ℕ × ℕ) × BitString) (v : ℕ) =>
        (Encodable.decode (α := BitString) v).map fun z => (b.2, b.1.2.unpair.2, z)) :=
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((hu.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂).to₂
    exact (Primrec.option_bind hdec (Primrec.option_bind hev hlast).to₂).to₂
  -- the approximations of `0'` converge on `[0, u)`
  have hconv : ∀ u, ∃ M, ∀ m ≥ M, ∀ k < u,
      (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome = true ↔
        k ∈ jumpSet := by
    intro u
    induction u with
    | zero => exact ⟨0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ u ih =>
      obtain ⟨M, hM⟩ := ih
      by_cases hu : u ∈ jumpSet
      · have hu' : ((Denumerable.ofNat Nat.Partrec.Code u).eval u).Dom := hu
        obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hu'
        obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
        refine ⟨max M s, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m (le_of_max_le_left hm) k hk
        · refine ⟨fun _ => hu, fun _ => ?_⟩
          exact Option.isSome_iff_exists.mpr
            ⟨v, Nat.Partrec.Code.evaln_mono (le_of_max_le_right hm) hs⟩
      · refine ⟨M, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m hm k hk
        · refine ⟨fun h => ?_, fun h => absurd h hu⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩
  have hpre_eq : ∀ u, ∃ M, ∀ m ≥ M, ∀ u' ≤ u,
      pre m u' = (List.range u').map (fun k => if k ∈ jumpSet then 1 else 0) := by
    intro u
    obtain ⟨M, hM⟩ := hconv u
    refine ⟨M, fun m hm u' hu' => List.map_congr_left fun k hk => ?_⟩
    have hiff := hM m hm k (lt_of_lt_of_le (List.mem_range.mp hk) hu')
    by_cases hj : k ∈ jumpSet
    · simp [hj, hiff.mpr hj]
    · have hf : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome =
          false := by
        cases h : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome
        · rfl
        · exact absurd (hiff.mp h) hj
      simp [hj, hf]
  refine ⟨fun m => (List.range m).filterMap (entry m),
    (Primrec.listFilterMap Primrec.list_range hentry_prim).to_comp, ?_, ?_⟩
  · intro u
    obtain ⟨M, hM⟩ := hpre_eq u
    refine ⟨M, fun m hm p u' z hmem hu' => ?_⟩
    obtain ⟨r, -, hr⟩ := List.mem_filterMap.mp hmem
    simp only [entry, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨p', hp', v, hv, z', hz', heq⟩ := hr
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rw [hM m hm _ hu'] at hv
    have hvΦ := Nat.Partrec.Code.evaln_sound hv
    rw [hceval] at hvΦ
    have hvf := (hex _ v).mpr ⟨_, hvΦ⟩
    simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some,
      Part.mem_map_iff] at hvf
    obtain ⟨z'', hz'', rfl⟩ := hvf
    rw [Encodable.encodek, Option.some_inj] at hz'
    rw [← hz']
    exact hz''
  · intro p x hpx
    have hmemf : Encodable.encode x ∈ mapToNatFun V (Encodable.encode (p, ([] : BitString))) := by
      simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some]
      exact Part.mem_map _ hpx
    obtain ⟨u, hu⟩ := (hex _ _).mp hmemf
    rw [← hceval] at hu
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hu
    obtain ⟨M, hM⟩ := hpre_eq u
    refine ⟨u, max (max M t) (Nat.pair (Encodable.encode p) u + 1), fun m hm => ?_⟩
    have hmM : M ≤ m := le_trans (le_max_left _ _) (le_of_max_le_left hm)
    have hmt : t ≤ m := le_trans (le_max_right _ _) (le_of_max_le_left hm)
    have hmr : Nat.pair (Encodable.encode p) u < m := le_of_max_le_right hm
    refine List.mem_filterMap.mpr ⟨Nat.pair (Encodable.encode p) u, List.mem_range.mpr hmr, ?_⟩
    have hev := Nat.Partrec.Code.evaln_mono hmt ht
    rw [← hM m hmM u le_rfl] at hev
    simp only [entry, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    rw [Option.mem_def.mp hev]
    simp [Encodable.encodek]

/-- Comparability of two programs (one is a prefix of the other), as a Boolean. -/
private def exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp (p q : BitString) : Bool :=
  decide (p = q.take p.length) || decide (q = p.take q.length)

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp_iff (p q : BitString) :
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp p q = true ↔ p <+: q ∨ q <+: p := by
  simp [exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp, List.prefix_iff_eq_take]

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp_primrec :
    Primrec (fun a : BitString × BitString =>
      exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp a.1 a.2) := by
  have h1 : Primrec (fun a : BitString × BitString => decide (a.1 = a.2.take a.1.length)) :=
    primrec_decideEq.comp Primrec.fst
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
  have h2 : Primrec (fun a : BitString × BitString => decide (a.2 = a.1.take a.2.length)) :=
    primrec_decideEq.comp Primrec.snd
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
  exact Primrec.or.comp h1 h2

/-- The entries kept at a stage: every other entry whose program is comparable has a strictly
larger oracle length. -/
private def exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep
    (l : List (BitString × ℕ × BitString)) : List (BitString × ℕ × BitString) :=
  l.filter fun E => !(l.any fun E' =>
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp E'.1 E.1 && !decide (E' = E) &&
      !decide (E.2.1 < E'.2.1))

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_keep
    {l : List (BitString × ℕ × BitString)} {E : BitString × ℕ × BitString} :
    E ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep l ↔
      E ∈ l ∧ ∀ E' ∈ l, (E'.1 <+: E.1 ∨ E.1 <+: E'.1) → E' = E ∨ E.2.1 < E'.2.1 := by
  unfold exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep
  rw [List.mem_filter]
  refine and_congr Iff.rfl ?_
  rw [Bool.not_eq_true', List.any_eq_false]
  refine forall₂_congr fun E' _ => ?_
  rw [← exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp_iff]
  cases exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp E'.1 E.1 <;>
    by_cases h1 : E' = E <;> by_cases h2 : E.2.1 < E'.2.1 <;> simp [h1, h2]

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep_eq
    {l : List (BitString × ℕ × BitString)} {E₁ E₂ : BitString × ℕ × BitString}
    (h₁ : E₁ ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep l)
    (h₂ : E₂ ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep l)
    (hc : E₁.1 <+: E₂.1 ∨ E₂.1 <+: E₁.1) : E₁ = E₂ := by
  rw [exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_keep] at h₁ h₂
  rcases h₁.2 E₂ h₂.1 hc.symm with h | h
  · exact h.symm
  rcases h₂.2 E₁ h₁.1 hc with h' | h'
  · exact h'
  · omega

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep_computable :
    Computable exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep := by
  have hP : Computable₂ (fun (a : List (BitString × ℕ × BitString) × (BitString × ℕ × BitString))
      (E' : BitString × ℕ × BitString) =>
      exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp E'.1 a.2.1 &&
        !decide (E' = a.2) && !decide (a.2.2.1 < E'.2.1)) := by
    have hc : Primrec (fun b : (List (BitString × ℕ × BitString) × (BitString × ℕ × BitString)) ×
        (BitString × ℕ × BitString) =>
        exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp b.2.1 b.1.2.1) :=
      exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp_primrec.comp
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    have he : Primrec (fun b : (List (BitString × ℕ × BitString) × (BitString × ℕ × BitString)) ×
        (BitString × ℕ × BitString) => decide (b.2 = b.1.2)) :=
      primrec_decideEq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
    have hlt : Primrec (fun b : (List (BitString × ℕ × BitString) × (BitString × ℕ × BitString)) ×
        (BitString × ℕ × BitString) => decide (b.1.2.2.1 < b.2.2.1)) := by
      obtain ⟨_, hp⟩ := (Primrec.nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop))
      exact (hp.comp ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).of_eq fun b => by simp
    exact (Primrec.and.comp (Primrec.and.comp hc (Primrec.not.comp he))
      (Primrec.not.comp hlt)).to_comp
  have hany := computable_list_any (f := fun a : List (BitString × ℕ × BitString) ×
    (BitString × ℕ × BitString) => a.1) Computable.fst hP
  have hp : Computable₂ (fun (l : List (BitString × ℕ × BitString))
      (E : BitString × ℕ × BitString) => !(l.any fun E' =>
        exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_cmp E'.1 E.1 &&
          !decide (E' = E) && !decide (E.2.1 < E'.2.1))) :=
    (Primrec.not.to_comp.comp hany).to₂
  exact computable_list_filter Computable.id hp

/-- The selection at stage `decodeBits c`: the output of the kept entry whose program is a prefix
of `q`. -/
private def exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_sel
    (L : ℕ → List (BitString × ℕ × BitString)) (q c : BitString) : Option BitString :=
  (((exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep (L (decodeBits c))).filter
    fun E => decide (E.1 = q.take E.1.length)).head?).map fun E => E.2.2

/-- The prefix-stable decompressor of Step 2. -/
private def exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G
    (L : ℕ → List (BitString × ℕ × BitString)) : Map := fun qc =>
  (exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_sel L qc.1 qc.2 : Part BitString)

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_G
    {L : ℕ → List (BitString × ℕ × BitString)} {q c z : BitString} :
    z ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G L (q, c) ↔
      ∃ E ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep (L (decodeBits c)),
        E.1 <+: q ∧ E.2.2 = z := by
  unfold exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_sel
  rw [Part.mem_ofOption, Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨E, hE, rfl⟩
    have hmem := List.mem_of_mem_head? hE
    rw [List.mem_filter] at hmem
    exact ⟨E, hmem.1, List.prefix_iff_eq_take.mpr (of_decide_eq_true hmem.2), rfl⟩
  · rintro ⟨E, hE, hpre, rfl⟩
    have hEl : E ∈ (exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep
        (L (decodeBits c))).filter fun E => decide (E.1 = q.take E.1.length) :=
      List.mem_filter.mpr ⟨hE, decide_eq_true (List.prefix_iff_eq_take.mp hpre)⟩
    obtain ⟨E₀, hE₀⟩ := Option.isSome_iff_exists.mp
      (List.isSome_head?.mpr (List.ne_nil_of_mem hEl))
    have hmem := List.mem_of_mem_head? hE₀
    rw [List.mem_filter] at hmem
    have hpre₀ : E₀.1 <+: q := List.prefix_iff_eq_take.mpr (of_decide_eq_true hmem.2)
    have heq : E₀ = E := exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep_eq hmem.1 hE
      (List.prefix_or_prefix_of_prefix hpre₀ hpre)
    exact ⟨E₀, hE₀, by rw [heq]⟩

private lemma exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G_decompressor
    {L : ℕ → List (BitString × ℕ × BitString)} (hL : Computable L) :
    IsPrefixStableDecompressor (exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G L) := by
  refine ⟨?_, fun c x y z hz hxy => ?_⟩
  · have hl : Computable (fun qc : BitString × BitString =>
        exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep (L (decodeBits qc.2))) :=
      exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep_computable.comp
        (hL.comp (decodeBits_computable.comp Computable.snd))
    have hp : Computable₂ (fun (qc : BitString × BitString) (E : BitString × ℕ × BitString) =>
        decide (E.1 = qc.1.take E.1.length)) :=
      (primrec_decideEq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst))).to_comp.to₂
    have hh := Primrec.list_head?.to_comp.comp (computable_list_filter hl hp)
    have hsel : Computable (fun qc : BitString × BitString =>
        exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_sel L qc.1 qc.2) :=
      Computable.option_map hh (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to_comp.to₂
    exact Computable.ofOption hsel
  · rw [exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_G] at hz ⊢
    obtain ⟨E, hE, hpre, hEz⟩ := hz
    exact ⟨E, hE, hpre.trans hxy, hEz⟩

/-- Step 2 of the proof of `exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump`: the
prefix-free selection. Let `V` be a prefix machine and let `L` be a computable list-valued
function of the stage with the soundness and completeness properties of Step 1. Then there is a
prefix-stable decompressor `G` such that `V (p, []) = x` implies `G (p, bits m) = x` for all large
`m`.

Proof idea: at stage `m` keep the entries `(p, u, z)` of `L m` such that every other entry whose
program is comparable with `p` has a strictly larger `u`; the kept programs form a prefix-free
set. `G (q, bits m)` is the output of the kept entry whose program is a prefix of `q`. If
`V (p, []) = x` with the entry `(p, u, x)`, then from some stage on all entries with `u' ≤ u` are
true; the true programs comparable with `p` are `p` itself, so the comparable entry with the least
`u` is kept and has output `x`. -/
private theorem exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_select {V : Map}
    (hVp : IsPrefixMachine V) {L : ℕ → List (BitString × ℕ × BitString)} (hL : Computable L)
    (hsound : ∀ u, ∃ M, ∀ m ≥ M, ∀ p u' z, (p, u', z) ∈ L m → u' ≤ u → produces V p [] z)
    (hcomplete : ∀ p x, produces V p [] x → ∃ u M, ∀ m ≥ M, (p, u, x) ∈ L m) :
    ∃ G : Map, IsPrefixStableDecompressor G ∧
      ∀ p x, produces V p [] x → ∃ N, ∀ m ≥ N, produces G p (Nat.bits m) x := by
  refine ⟨exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G L,
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G_decompressor hL, fun p x hpx => ?_⟩
  obtain ⟨u, M₁, hM₁⟩ := hcomplete p x hpx
  obtain ⟨M₀, hM₀⟩ := hsound u
  refine ⟨max M₀ M₁, fun m hm => ?_⟩
  have hm₀ : M₀ ≤ m := le_of_max_le_left hm
  have hpe : (p, u, x) ∈ L m := hM₁ m (le_of_max_le_right hm)
  -- an entry `E` with `E.2.1 ≤ u` whose program is comparable with `p` is true, for `p` itself
  have htrue : ∀ E ∈ L m, (E.1 <+: p ∨ p <+: E.1) → E.2.1 ≤ u → E.1 = p ∧ E.2.2 = x := by
    intro E hE hc hu
    have hEV : produces V E.1 [] E.2.2 := hM₀ m hm₀ E.1 E.2.1 E.2.2 hE hu
    have hEp : E.1 = p := by
      rcases hc with hc | hc
      · exact hVp.eq_of_prefix hEV hpx hc
      · exact (hVp.eq_of_prefix hpx hEV hc).symm
    subst hEp
    exact ⟨rfl, Part.mem_unique hEV hpx⟩
  classical
  have hex : ∃ k, ∃ E ∈ L m, (E.1 <+: p ∨ p <+: E.1) ∧ E.2.1 = k :=
    ⟨u, (p, u, x), hpe, Or.inl (List.prefix_refl p), rfl⟩
  obtain ⟨E, hE, hEc, hEk⟩ := Nat.find_spec hex
  have hmin : ∀ E' ∈ L m, (E'.1 <+: p ∨ p <+: E'.1) → Nat.find hex ≤ E'.2.1 :=
    fun E' hE' hc => Nat.find_min' hex ⟨E', hE', hc, rfl⟩
  have hku : Nat.find hex ≤ u :=
    Nat.find_min' hex ⟨(p, u, x), hpe, Or.inl (List.prefix_refl p), rfl⟩
  obtain ⟨hE1, hE2⟩ := htrue E hE hEc (hEk ▸ hku)
  have hkeep : E ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_keep (L m) := by
    rw [exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_keep]
    refine ⟨hE, fun E' hE' hc => ?_⟩
    rw [hE1] at hc
    have hc' : E'.1 <+: p ∨ p <+: E'.1 := hc
    rcases (hmin E' hE' hc').lt_or_eq with hlt | heq
    · exact Or.inr (hEk ▸ hlt)
    · obtain ⟨hE'1, hE'2⟩ := htrue E' hE' hc' (heq ▸ hku)
      left
      ext
      · rw [hE'1, hE1]
      · rw [← heq, hEk]
      · rw [hE'2, hE2]
  change x ∈ exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_G L (p, Nat.bits m)
  rw [exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_mem_G, decodeBits_natBits]
  exact ⟨E, hkeep, hE1 ▸ List.prefix_refl _, hE2⟩

/-- **SUV Theorem 134 (Section 6.4.2, printed p. 208).**
`lim_{n → ∞} K(x ‖ ≥ n) = K^{0'}(x) + O(1)`.
The sequence is non-increasing (`antitone_setCondK_atLeast`), so its limit is the infimum.

Proof idea: as for Theorem 131. `≥` uses the previous lower bound together with Theorem 133. -/
theorem exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump {U : Map}
    (hU : IsOptimalPrefixStableSetCond U) {V : Map}
    (hV : PointToSet.IsOptimalOraclePrefix jumpSet V) :
    ∃ c : ℕ, ∀ x,
      (⨅ n, setCondK U x (atLeast n)) ≤ KP V x [] + c ∧
        KP V x [] ≤ (⨅ n, setCondK U x (atLeast n)) + c := by
  obtain ⟨L, hLc, hsound, hcomplete⟩ :=
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_approx hV.1
  obtain ⟨G, hG, hGprop⟩ :=
    exists_const_iInf_prefixSetCondK_atLeast_eq_KP_jump_select hV.2.1 hLc hsound hcomplete
  obtain ⟨c₁, h₁⟩ := hU.2 G hG
  obtain ⟨W, hW⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c₂, h₂⟩ := exists_const_limsup_KP_eq_KP_jump hW hV
  obtain ⟨c₃, h₃⟩ := exists_const_iSup_KP_le_prefixStableSetCond hU hW
  refine ⟨c₁ + c₂ + c₃, fun x => ⟨?_, ?_⟩⟩
  · by_cases htop : KP V x [] = ⊤
    · rw [htop, top_add]; exact le_top
    obtain ⟨p, hp, hpl⟩ := exists_program_of_KP_ne_top htop
    obtain ⟨N, hN⟩ := hGprop p x hp
    have h3 : setCondK G x (atLeast N) ≤ p.length := by
      refine sInf_le ⟨p, ?_, rfl⟩
      rintro y ⟨m, hm, rfl⟩
      exact hN m hm
    have hc : (c₁ : ℕ∞) ≤ ((c₁ + c₂ + c₃ : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : c₁ ≤ c₁ + c₂ + c₃)
    calc (⨅ n, setCondK U x (atLeast n)) ≤ setCondK U x (atLeast N) := iInf_le _ N
      _ ≤ setCondK G x (atLeast N) + c₁ := h₁ x (atLeast N)
      _ ≤ KP V x [] + ((c₁ + c₂ + c₃ : ℕ) : ℕ∞) := by
        rw [← hpl]; exact add_le_add h3 hc
  · have hne : (Set.range fun n => setCondK U x (atLeast n)).Nonempty := Set.range_nonempty _
    obtain ⟨N, hN⟩ := csInf_mem hne
    have hinf : (⨅ n, setCondK U x (atLeast n)) = setCondK U x (atLeast N) := by
      rw [iInf, ← hN]
    have hlim : Filter.limsup (fun n => KP W x (Nat.bits n)) Filter.atTop ≤
        setCondK U x (atLeast N) + c₃ := by
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      refine (iInf_le _ N).trans ?_
      refine le_trans ?_ (h₃ x (atLeast N))
      exact iSup₂_le fun m hm => le_iSup₂_of_le (Nat.bits m) ⟨m, hm, rfl⟩ le_rfl
    have hc : ((c₃ + c₂ : ℕ) : ℕ∞) ≤ ((c₁ + c₂ + c₃ : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : c₃ + c₂ ≤ c₁ + c₂ + c₃)
    calc KP V x [] ≤ Filter.limsup (fun n => KP W x (Nat.bits n)) Filter.atTop + c₂ :=
          (h₂ x).2
      _ ≤ setCondK U x (atLeast N) + c₃ + c₂ := add_le_add hlim le_rfl
      _ = setCondK U x (atLeast N) + ((c₃ + c₂ : ℕ) : ℕ∞) := by
          push_cast; rw [add_assoc]
      _ ≤ (⨅ n, setCondK U x (atLeast n)) + ((c₁ + c₂ + c₃ : ℕ) : ℕ∞) := by
          rw [hinf]; exact add_le_add le_rfl hc

/-- **SUV Problem 208 (Section 6.4.2, printed p. 208), part 1.** `C(x ‖ A) ≤ K(x ‖ A) + O(1)`:
prefix-stable decompressors are decompressors. Parts 1–3 together say that `C(k ‖ A)`,
`K(k ‖ A)` and `K'(k ‖ A)` differ by `O(log C(k ‖ A))`. -/
theorem exists_const_setCondK_le_prefixStableSetCond {U : Map} (hU : IsOptimalSetCond U)
    {W : Map} (hW : IsOptimalPrefixStableSetCond W) :
    ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK W x A + c :=
  hU.2 W hW.1.1

/-- **SUV Problem 208 (Section 6.4.2, printed p. 208), part 2.** `K(x ‖ A) ≤ K'(x ‖ A) + O(1)`.
This is the unnumbered inequality `exists_const_prefixStableSetCond_le_prefixFreeSetCond`. -/
theorem problem208_prefixStable_le_prefixFree {U : Map} (hU : IsOptimalPrefixStableSetCond U)
    {V : Map} (hV : IsOptimalPrefixFreeSetCond V) :
    ∃ c : ℕ, ∀ x A, setCondK U x A ≤ setCondK V x A + c :=
  exists_const_prefixStableSetCond_le_prefixFreeSetCond hU hV

/-- The self-delimiting code of a plain program `b`: the pair code of the binary length of `b` and
`b` (`|b| + O(log |b|)` bits). -/
private def exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode (b : BitString) :
    BitString :=
  pairCode (Nat.bits b.length) b

/-- The prefix-free decompressor reading a length-coded program and running `U` on it. -/
private noncomputable def exists_const_prefixFreeSetCond_le_setCondK_add_log_machine (U : Map) :
    Map := fun qy =>
  bif decide (qy.1 = exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode
      (decodeSecond qy.1)) then U (decodeSecond qy.1, qy.2) else Part.none

private lemma exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode_prefix
    {b₁ b₂ : BitString}
    (h : exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode b₁ <+:
      exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode b₂) : b₁ = b₂ := by
  unfold exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode at h
  obtain ⟨r, hr⟩ := h
  simp only [pairCode, List.append_assoc] at hr
  obtain ⟨hm, hrest⟩ := natCode_append_inj hr
  have hl : (Nat.bits b₂.length).length = (Nat.bits b₁.length).length := by
    simpa using hm.symm
  have hrest' : Nat.bits b₁.length ++ (b₁ ++ r) = Nat.bits b₂.length ++ b₂ := hrest
  have h1 : Nat.bits b₁.length = Nat.bits b₂.length :=
    List.append_inj_left hrest' hl.symm
  have hn : b₁.length = b₂.length := natBits_injective h1
  rw [h1] at hrest'
  have h2 : b₁ ++ r = b₂ := List.append_cancel_left hrest'
  have : r.length = 0 := by
    have := congrArg List.length h2
    simp at this
    omega
  have hr0 : r = [] := List.eq_nil_of_length_eq_zero this
  rw [hr0] at h2
  simpa using h2

private lemma exists_const_prefixFreeSetCond_le_setCondK_add_log_machine_isPrefixDecompressor
    {U : Map} (hU : isDecompressor U) :
    IsPrefixDecompressor (exists_const_prefixFreeSetCond_le_setCondK_add_log_machine U) := by
  refine ⟨?_, ?_⟩
  · unfold exists_const_prefixFreeSetCond_le_setCondK_add_log_machine isDecompressor
    have hsec : Computable (fun pr : BitString × BitString => decodeSecond pr.1) :=
      decodeSecond_computable.comp Computable.fst
    have hlc : Computable
        exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode := by
      unfold exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode
      have hlen : Computable (fun y : BitString => Nat.bits y.length) :=
        natBits_computable.comp Computable.list_length
      exact (CodedFiniteDistribution.pairCode_primrec.to_comp).comp hlen Computable.id
    have hcond : Computable (fun pr : BitString × BitString =>
        decide (pr.1 = exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode
          (decodeSecond pr.1))) :=
      (Primrec.eq.decide.to_comp).comp Computable.fst (hlc.comp hsec)
    have hbody : Partrec (fun pr : BitString × BitString => U (decodeSecond pr.1, pr.2)) :=
      hU.comp (hsec.pair Computable.snd)
    exact Partrec.cond hcond hbody Partrec.none
  · intro y p hp q hq hpre
    have key : ∀ s, s ∈ domainAt
        (exists_const_prefixFreeSetCond_le_setCondK_add_log_machine U) y →
        s = exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode (decodeSecond s) := by
      intro s hs
      unfold domainAt exists_const_prefixFreeSetCond_le_setCondK_add_log_machine at hs
      by_contra hne
      simp [hne] at hs
    have hp' := key p hp
    have hq' := key q hq
    have hb : decodeSecond p = decodeSecond q := by
      apply exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode_prefix
      rw [← hp', ← hq']
      exact hpre
    rw [hp', hq', hb]

private lemma exists_const_prefixFreeSetCond_le_setCondK_add_log_machine_produces
    (U : Map) {p y x : BitString} (h : produces U p y x) :
    produces (exists_const_prefixFreeSetCond_le_setCondK_add_log_machine U)
      (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p) y x := by
  have hs : decodeSecond (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p) = p :=
    decodeSecond_pairCode _ _
  change x ∈ (bif decide (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p =
      exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode
        (decodeSecond (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p)))
    then U (decodeSecond (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p), y)
    else Part.none)
  rw [hs]
  simpa using h

private lemma exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode_length (b : BitString) :
    (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode b).length ≤
      b.length + 2 * Nat.log 2 b.length + 3 := by
  unfold exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode
  rw [length_pairCode]
  have hL : (Nat.bits b.length).length ≤ Nat.log 2 b.length + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  omega

/-- **SUV Problem 208 (Section 6.4.2, printed p. 208), part 3.**
`K'(x ‖ A) ≤ C(x ‖ A) + O(log C(x ‖ A))`. The `toNat` is harmless because `C(x ‖ A) ≤ C(x) + O(1)`
is finite (`exists_const_setCondK_le_plainK`).

Proof idea: a prefix-free decompressor reads a self-delimiting code of the length of a plain
description `p` (`O(log l(p))` bits) and then `p`. -/
theorem exists_const_prefixFreeSetCond_le_setCondK_add_log {U : Map} (hU : IsOptimalSetCond U)
    {V : Map} (hV : IsOptimalPrefixFreeSetCond V) :
    ∃ c : ℕ, ∀ x A,
      setCondK V x A ≤ setCondK U x A + ((c * Nat.log 2 (setCondK U x A).toNat + c : ℕ) : ℕ∞) := by
  set D := exists_const_prefixFreeSetCond_le_setCondK_add_log_machine U with hDdef
  have hD : IsPrefixDecompressor D :=
    exists_const_prefixFreeSetCond_le_setCondK_add_log_machine_isPrefixDecompressor hU.1
  obtain ⟨c₀, hc₀⟩ := hV.2 D hD
  refine ⟨c₀ + 3, fun x A => ?_⟩
  by_cases htop : setCondK U x A = ⊤
  · rw [htop]
    simp
  · obtain ⟨p, hp, hl⟩ : ∃ p, (∀ y ∈ A, produces U p y x) ∧ setCondK U x A = p.length := by
      have hne : {l : ℕ∞ | ∃ p, (∀ y ∈ A, produces U p y x) ∧ l = p.length}.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        apply htop
        unfold setCondK
        rw [hempty]
        exact sInf_empty
      obtain ⟨p, hp, hl⟩ := csInf_mem hne
      exact ⟨p, hp, hl⟩
    have hDle : setCondK D x A ≤
        ((exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p).length : ℕ∞) :=
      sInf_le ⟨_, fun y hy =>
        exists_const_prefixFreeSetCond_le_setCondK_add_log_machine_produces U (hp y hy), rfl⟩
    have hlen := exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode_length p
    have htn : (setCondK U x A).toNat = p.length := by rw [hl]; rfl
    rw [htn]
    refine (hc₀ x A).trans ?_
    rw [hl]
    refine (add_le_add hDle le_rfl).trans ?_
    have : (exists_const_prefixFreeSetCond_le_setCondK_add_log_lenCode p).length + c₀ ≤
        p.length + ((c₀ + 3) * Nat.log 2 p.length + (c₀ + 3)) := by
      nlinarith [Nat.zero_le (Nat.log 2 p.length), Nat.zero_le (c₀ * Nat.log 2 p.length)]
    exact_mod_cast this

end GeneralScheme

end Kolmogorov
