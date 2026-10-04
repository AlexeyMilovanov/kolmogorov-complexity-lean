import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.Optimal
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore.RealizationEngine

/-!
# Kraft bound for the geometric request stream, and the realization theorem

The geometric request stream of `RealizationEngine` emits, for each output, the levels its
approximation crosses.  `geomReq_kraft_le_perOutput_sum` reindexes its Kraft sum by output —
each stage is the first crossing of one level of one output — and `geomReq_kraft_le_one` sums
the resulting geometric tails to at most one, so the online allocator of
`KraftChaitinAllocator` may be applied to it.

`extract_request_stream_geometric` packages the stream with its bound,
`realization_bound_of_machine` turns a matched allocator into a bound on prefix complexity,
and the two theorems of the module follow: `kraftChaitin_realization_bound_unit` at unit mass,
and `kraftChaitin_realization_bound` for a function whose conditional masses are bounded by
`2 ^ d`, which is the hard direction of the coding theorem.
-/

namespace Kolmogorov
open scoped ENNReal

open Classical in
/-- **Reindexing the geometric Kraft sum by output.** Every index `n` emitting a
request `(o, l)` corresponds (injectively) to a crossed level `l ≥ 1` of output `o`
(the unique first-crossing stage), so the total Kraft weight is bounded by the
double sum over outputs and their crossed levels. -/
lemma geomReq_kraft_le_perOutput_sum {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) := by
  have h_reindex :
      (∑' n : ℕ, (match geomReq approx ctx n with | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)) =
      (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)) := by
    have h_reindex : ∀ (f : ℕ → ℝ≥0∞), (∑' n : ℕ, f n) =
        (∑' a : ℕ, ∑' s : ℕ, ∑' l : ℕ, f (Nat.pair (Nat.pair a s) l)) := by
      intro f;
      rw [ ← ENNReal.tsum_prod, ← ENNReal.tsum_prod ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective
        ( fun p : ( ℕ × ℕ ) × ℕ => Nat.pair ( Nat.pair p.1.1 p.1.2 ) p.2 )
        ⟨ fun p => ?_, fun p => ?_ ⟩ ) ];
      · congr! 1;
      · simp only [Nat.pair_eq_pair, Prod.forall, Prod.mk.eta, and_imp,
          forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂, forall_eq']
      · exact ⟨ ⟨ ⟨ Nat.unpair p |>.1 |> Nat.unpair |>.1,
            Nat.unpair p |>.1 |> Nat.unpair |>.2 ⟩,
          Nat.unpair p |>.2 ⟩, by simp only [Nat.pair_unpair] ⟩;
    exact h_reindex _;
  -- By `tsum_eq_tsum_of_ne_zero_bij`, we can restrict the sum over `a` to outputs.
  have h_restrict :
      (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)))) ≤
      (∑' o : BitString, (∑' s : ℕ, (∑' l : ℕ,
        (match geomReq approx ctx (Nat.pair (Nat.pair (Encodable.encode o) s) l) with
          | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
          | none => 0)))) := by
    have h_restrict :
        (∑' a : ℕ, (∑' s : ℕ, (∑' l : ℕ,
          (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
            | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
            | none => 0)))) =
        (∑' a : ℕ, if a ∈ Set.range (Encodable.encode : BitString → ℕ) then
          (∑' s : ℕ, (∑' l : ℕ,
            (match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
              | some (_, l') => (2 : ℝ≥0∞)⁻¹ ^ l'
              | none => 0))) else 0) := by
      congr;
      ext a
      split_ifs <;>
        simp_all only [ENNReal.tsum_eq_zero, Nat.unpair_pair, Set.mem_range, geomReq,
          not_exists]
      unfold evOut
      simp only [*, Encodable.decode₂, Nat.unpair_pair, Option.bind_fun_none,
        Option.bind_none, Option.guard_false, decide_false, implies_true]
    rw [h_restrict]
    let F : Nat → ENNReal := fun a =>
      ∑' s : Nat, ∑' l : Nat,
        match geomReq approx ctx (Nat.pair (Nat.pair a s) l) with
        | some (_, length) => (2 : ENNReal)⁻¹ ^ length
        | none => 0
    change (∑' a : Nat,
      if a ∈ Set.range (Encodable.encode : BitString → Nat) then F a else 0) ≤
        ∑' o : BitString, F (Encodable.encode o)
    have hsubtype :
        (∑' a : Nat,
          if a ∈ Set.range (Encodable.encode : BitString → Nat) then F a else 0) =
          ∑' x : Set.range (Encodable.encode : BitString → Nat), F x.1 := by
      simpa only [Set.indicator_apply] using
        (tsum_subtype (Set.range (Encodable.encode : BitString → Nat)) F).symm
    have hequiv :
        (∑' x : Set.range (Encodable.encode : BitString → Nat), F x.1) =
          ∑' o : BitString, F (Encodable.encode o) := by
      simpa using
        (Equiv.tsum_eq
          (Equiv.ofInjective (Encodable.encode : BitString → Nat)
            Encodable.encode_injective)
          (fun x : Set.range (Encodable.encode : BitString → Nat) => F x.1)).symm
    exact (hsubtype.trans hequiv).le
  refine le_trans h_reindex.le <| h_restrict.trans ?_;
  refine ENNReal.tsum_le_tsum fun o => ?_;
  rw [ ENNReal.tsum_comm ];
  refine ENNReal.tsum_le_tsum fun l => ?_;
  split_ifs with h;
  · obtain ⟨ s₀, hs₀ ⟩ := Nat.findX h.2;
    rw [ tsum_eq_single s₀ ];
    · rw [geomReq_pair]; split_ifs <;> simp;
    · intro b' hb'
      by_cases hb'_lt : b' < s₀;
      · rw [ geomReq_pair ] ; simp only [false_and, hs₀.2 b' hb'_lt, ↓reduceIte];
      · rw [ geomReq_pair ];
        split_ifs <;> norm_num;
        rename_i h;
        exact h.2.elim
          ( fun h => by
            linarith [ Nat.pos_of_ne_zero ( show s₀ ≠ 0 from by
              rintro rfl
              exact hs₀.2 0 ( Nat.pos_of_ne_zero ( by aesop ) ) hs₀.1 ) ] )
          fun h => h ( by
            exact Nat.le_induction ( by tauto )
              ( fun k hk ih => by exact geomCross_succ_of_geomCross hmono o ctx l k ih ) _
              ( show b' - 1 ≥ s₀ from Nat.le_sub_one_of_lt
                ( lt_of_le_of_ne ( le_of_not_gt hb'_lt ) ( Ne.symm hb' ) ) ) );
  · convert tsum_nonpos _;
    · infer_instance;
    · infer_instance;
    · intro s; rw [ geomReq_pair ] ;
      split_ifs <;> norm_num;
      exact h ⟨ by unfold geomCross at *; aesop, s, by tauto ⟩

open Classical in
/-- **Kraft bound for the geometric request stream.** Because each output's emitted
lengths form an upward-closed set `{ l ≥ L }` with `2 · 2^{-L} ≤ f o ctx`, the total
Kraft weight is bounded by `∑_o f o ctx ≤ 1`. -/
lemma geomReq_kraft_le_one {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx : BitString) :
    (∑' n, match geomReq approx ctx n with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 := by
  calc (∑' n, match geomReq approx ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0)
      ≤ ∑' o : BitString, ∑' l : ℕ,
          (if 1 ≤ l ∧ (∃ s, geomCross approx o ctx l s) then (2 : ℝ≥0∞)⁻¹ ^ l else 0) :=
        geomReq_kraft_le_perOutput_sum hmono ctx
    _ ≤ ∑' o : BitString, f o ctx :=
        ENNReal.tsum_le_tsum (fun o => geomReq_crossed_kraft_perOutput hsup o ctx)
    _ ≤ 1 := h_sum ctx

/-
**Geometric domination for the geometric request stream.** Each output's mass
`f out ctx` is within a factor `2^2` of its largest single emitted request weight.

The mass bound `h_sum` (hence `f out ctx ≤ 1`) is genuinely needed: the smallest
emitted length is `1` (weight `2⁻¹`), so an output with `f out ctx ≥ 2` would
violate the `2^2`-domination. With `f out ctx ≤ 1` the largest crossed level `L`
satisfies `2⁻¹^L ≤ f out ctx < 2^2 · 2⁻¹^L`.
-/
lemma geomReq_geometric_bound {f : BitString → BitString → ℝ≥0∞}
    {approx : ℕ → BitString → BitString → ℕ}
    (_hmono : ∀ s out ctx, dyadicValue (approx s out ctx) s
        ≤ dyadicValue (approx (s + 1) out ctx) (s + 1))
    (hsup : ∀ out ctx, ⨆ s, dyadicValue (approx s out ctx) s = f out ctx)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1)
    (ctx out : BitString) :
    f out ctx ≤ (2 : ℝ≥0∞) ^ 2 *
      (⨆ n, match geomReq approx ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
  by_contra h_contra;
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃ s'
      : ℕ, geomCross approx out ctx l' s' := by
    have hL : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s := by
      -- Since $f(out, ctx) > 0$, there exists some $s$ such that $dyadicValue (approx s out ctx) s
      --   > 0$.
      obtain ⟨s, hs⟩ : ∃ s : ℕ, dyadicValue (approx s out ctx) s > 0 := by
        have h_pos : f out ctx > 0 := by
          exact lt_of_not_ge fun h => h_contra <| le_trans h <| by positivity;
        exact not_forall_not.mp fun h => h_pos.ne' <| hsup out ctx ▸ by
          simp +decide [ show ∀ s : ℕ, dyadicValue ( approx s out ctx ) s = 0 from
            fun s => le_antisymm (le_of_not_gt (h s)) bot_le ]
      refine ⟨ s + 1, ?_, s, ?_, ?_ ⟩ <;> norm_num [ geomCross ] at *;
      exact Nat.pos_of_ne_zero fun h => hs.ne' <| by unfold dyadicValue; simp +decide [ h ] ;
    obtain ⟨l, hl⟩ : ∃ l : ℕ, 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s ∧ ∀ l' : ℕ, l' < l → ¬∃
        s' : ℕ, geomCross approx out ctx l' s' := by
      have h_well_founded : WellFounded (fun l l' : ℕ => l < l') := by
        exact wellFounded_lt
      obtain ⟨l, hl⟩ : ∃ l : ℕ, l ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} ∧ ∀ l' :
          ℕ, l' ∈ {l : ℕ | 1 ≤ l ∧ ∃ s : ℕ, geomCross approx out ctx l s} → ¬l' < l := by
        have := h_well_founded.has_min
          { l | 1 ≤ l ∧ ∃ s, geomCross approx out ctx l s } ⟨ _, hL.choose_spec ⟩
        tauto
      exact ⟨ l, hl.1.1, hl.1.2.choose, hl.1.2.choose_spec,
        fun l' hl' hl'' => hl.2 l'
          ⟨ Nat.pos_of_ne_zero fun h => by
              subst h
              exact absurd hl'' ( by
                rintro ⟨ s', hs' ⟩
                exact absurd hs'.1 ( by norm_num ) ), hl'' ⟩ hl' ⟩;
    use l;
  obtain ⟨s, hs⟩ := hl.right
  have h_emitted :
      ⨆ n, (match geomReq approx ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
        | none => 0) ≥ (2 : ℝ≥0∞)⁻¹ ^ l := by
    obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, geomCross approx out ctx l s₀ ∧ ∀ s' : ℕ, s' < s₀ → ¬geomCross
        approx out ctx l s' := by
      exact ⟨ Nat.find ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ),
        Nat.find_spec ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ),
        fun s' hs' =>
          Nat.find_min ( ⟨ s, hs.1 ⟩ : ∃ s, geomCross approx out ctx l s ) hs' ⟩;
    refine le_trans ?_
      ( le_ciSup ?_ ( Nat.pair ( Nat.pair ( Encodable.encode out ) s₀ ) l ) )
    · simp +decide only [geomReq_pair, hs₀, true_and]
      rcases s₀ with ( _ | s₀ ) <;> simp +decide [ hs₀ ] at hs₀ ⊢;
    · refine ⟨ 1, Set.forall_mem_range.2 fun n => ?_ ⟩
      rcases geomReq approx ctx n with ( _ | ⟨ o, l ⟩ ) <;> norm_num;
      split_ifs <;> norm_num;
      exact pow_le_one₀ ( by norm_num ) ( by norm_num );
  -- Since $l$ is the smallest level where the cross condition holds, for any $s$, we have
  --   $dyadicValue (approx s out ctx) s < 2⁻¹^(l-2)$.
  have h_dyadic_lt : ∀ s, dyadicValue (approx s out ctx) s < (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    intro s
    by_cases hl_ge_2 : 2 ≤ l;
    · have h_dyadic_lt : ¬geomCross approx out ctx (l - 1) s := by
        exact fun h => hs.2 ( l - 1 ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) ⟨ s, h ⟩;
      unfold geomCross at h_dyadic_lt; norm_num at h_dyadic_lt;
      unfold dyadicValue; norm_num [ ENNReal.div_lt_iff ] ;
      rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
      · rw [ div_pow, div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast;
        · norm_num
          exact h_dyadic_lt ( Nat.le_sub_one_of_lt hl_ge_2 );
        · positivity;
      · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
    · interval_cases l ; norm_num at *;
      contrapose! h_contra;
      refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
      refine le_trans
        ( h_sum ctx |> le_trans ( ENNReal.le_tsum (f := fun out => f out ctx) out ) ) ?_ ; norm_num;
      rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
      norm_num [ ENNReal.mul_eq_top ];
  -- Therefore, $f out ctx \leq 2⁻¹^(l-2)$.
  have h_f_le : f out ctx ≤ (2 : ℝ≥0∞)⁻¹ ^ (l - 2) := by
    exact hsup out ctx ▸ iSup_le fun s => le_of_lt ( h_dyadic_lt s );
  refine h_contra <| h_f_le.trans ?_;
  refine le_trans ?_ ( mul_le_mul_right h_emitted _ );
  rcases l with ( _ | _ | l ) <;> norm_num [ pow_succ' ] at *;
  · rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ];
  · ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    norm_num [ ENNReal.mul_eq_top ]

/-- **Geometric dyadic request extraction.** A unit-mass lower-semicomputable `f`
admits a computable request stream of total Kraft weight `≤ 1` together with a
constant `K` such that, for every output `out`, the total mass `f out ctx` is
within a factor `2^K` of the *largest single* request weight for `out`
(`⨆ n, …`). This is the threshold-crossing decomposition (one request per dyadic
level crossed, so the per-output requested lengths are strictly decreasing and the
shortest dominates the geometric tail). Unlike the unit-increment
`extract_request_stream` (which realizes `f` exactly but may split one output's
mass into arbitrarily many equal-length requests), this geometric form is exactly
what `realization_bound_of_machine` needs: `2^{-KP}` only sees the largest single
request, so the realization bound is provable iff `f out` is geometrically
dominated by that largest request. -/
lemma extract_request_stream_geometric {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ (req : BitString → ℕ → Option (BitString × ℕ)) (K : ℕ),
      Computable (fun p : BitString × ℕ => req p.1 p.2) ∧
      (∀ ctx : BitString,
        (∑' n, match req ctx n with
          | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l
          | none => 0) ≤ 1) ∧
      (∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
        (⨆ n, match req ctx n with
          | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
          | none => 0)) := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := hlsc
  exact ⟨geomReq approx, 2, geomReq_computable approx hcomp,
    geomReq_kraft_le_one hmono hsup h_sum,
    geomReq_geometric_bound hmono hsup h_sum⟩

/-- **Realization bound from a matched allocator (geometric form).** If a request
stream is realized by a prefix machine `M'` (each requested `(out, l)` gets an
allocated code of length `l` that `M'` maps back to `out`), and each output's mass
`f out` is within a factor `2^K` of its *largest single* request weight, then `M'`
achieves the multiplicative coding bound `2^{-K} · f(out|ctx) ≤ 2^{-KP_{M'}(out|ctx)}`.

An exact identity `∑ requests = f` alone would be insufficient: with many
equal-length requests, `f out` can be arbitrarily larger than the single largest
request weight `= 2^{-KP}`. -/
lemma realization_bound_of_machine (f : BitString → BitString → ℝ≥0∞)
    (req : BitString → ℕ → Option (BitString × ℕ))
    (alloc : BitString → ℕ → Option BitString)
    (M' : Map) (K : ℕ)
    (hmatch : ∀ ctx n o l, req ctx n = some (o, l) → ∃ c, alloc ctx n = some c ∧ c.length = l)
    (hmachine : ∀ ctx n o l c, req ctx n = some (o, l) → alloc ctx n = some c →
      M' (c, ctx) = Part.some o)
    (hgeo : ∀ ctx out : BitString, f out ctx ≤ (2 : ℝ≥0∞) ^ K *
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0
        | none => 0)) :
    ∃ c₀ : ℕ, ∀ out ctx : BitString, (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight
        (KP M' out ctx) := by
  -- The supremum of the per-request weights for `out` is `≤ 2^{-KP M' out ctx}`,
  -- since every realized request gives a code of its length producing `out`.
  have hS : ∀ ctx out : BitString,
      (⨆ n, match req ctx n with
        | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)
        ≤ complexityWeight (KP M' out ctx) := by
    intro ctx out
    apply iSup_le
    intro n
    rcases h : req ctx n with _ | ⟨o, l⟩
    · simp
    · by_cases ho : o = out
      · subst ho
        obtain ⟨c, hc₁, hc₂⟩ := hmatch ctx n o l h
        have hprod : produces M' c ctx o := by
          have := hmachine ctx n o l c h hc₁
          simp [produces, this]
        have hKP : KP M' o ctx ≤ (programLength c : ENat) :=
          KP_le_programLength_of_produces hprod
        simpa [complexityWeight_programLength, progWeight, programLength, hc₂]
          using complexityWeight_le_of_le hKP
      · simp [ho]
  refine ⟨K, fun out ctx => ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ K * f out ctx
      ≤ (2 : ℝ≥0∞)⁻¹ ^ K * ((2 : ℝ≥0∞) ^ K *
          (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0)) := by
        gcongr
        exact hgeo ctx out
    _ = (⨆ n, match req ctx n with
            | some (o, l) => if o = out then (2 : ℝ≥0∞)⁻¹ ^ l else 0 | none => 0) := by
        rw [← mul_assoc, ← mul_pow,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
    _ ≤ complexityWeight (KP M' out ctx) := hS ctx out

/-- **The abstract Kraft–Chaitin realization engine, unit-mass interface.**

This is the genuinely hard online prefix-free allocator, stated at the *unit mass*
level: a lower-semicomputable `f` whose per-context total mass is `≤ 1` is realized
by a genuine prefix decompressor up to an additive coding constant.

The general `2^d`-mass theorem below reduces to this unit-mass interface through
`IsLSC.div_two_pow` and the corresponding `ℝ≥0∞` exponent algebra. The online
leftmost-free construction is supplied above by `exists_online_prefixFree_family`. -/
theorem kraftChaitin_realization_bound_unit {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ 1) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- The genuinely hard online allocator (leftmost-free-dyadic-interval) at mass ≤ 1:
  -- 1. Extract the dyadic increments from `hlsc` as a computable request stream.
  obtain ⟨req, K, hreq_comp, hreq_wt, hgeo⟩ := extract_request_stream_geometric hlsc h_sum
  -- 2 & 3. Allocate prefix-free programs of the requested lengths online.
  obtain ⟨alloc, halloc_comp, halloc_match, halloc_pref⟩ :=
    exists_online_prefixFree_family req hreq_comp hreq_wt
  -- 4. Construct `M'` via `Partrec` combinators from the resulting computable allocator.
  obtain ⟨M', hM', hM_match⟩ :=
    construct_prefix_machine req alloc hreq_comp halloc_comp halloc_match halloc_pref
  obtain ⟨c₀, hc₀⟩ := realization_bound_of_machine f req alloc M' K halloc_match hM_match hgeo
  exact ⟨M', hM', c₀, hc₀⟩

/-- A lower semicomputable `f` whose conditional masses are bounded by `2^d` is dominated, up to
one multiplicative constant `2^{-c₀}`, by the prefix-complexity weight of a single prefix
decompressor.  This is the Kraft–Chaitin coding theorem in its bounded-mass form. -/
theorem kraftChaitin_realization_bound {f : BitString → BitString → ℝ≥0∞}
    (hlsc : IsLSC f) (d : ℕ)
    (h_sum : ∀ ctx : BitString, (∑' out : BitString, f out ctx) ≤ (2 : ℝ≥0∞) ^ d) :
    ∃ M' : Map, IsPrefixDecompressor M' ∧ ∃ c₀ : ℕ, ∀ out ctx : BitString,
      (2 : ℝ≥0∞)⁻¹ ^ c₀ * f out ctx ≤ complexityWeight (KP M' out ctx) := by
  -- Reduce the `2^d`-mass case to the unit-mass interface by dividing `f` by `2^d`.
  have hg_lsc : IsLSC (fun out ctx => f out ctx / (2 : ℝ≥0∞) ^ d) := hlsc.div_two_pow d
  have hg_sum : ∀ ctx : BitString,
      (∑' out : BitString, f out ctx / (2 : ℝ≥0∞) ^ d) ≤ 1 := by
    intro ctx
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [ENNReal.tsum_mul_left]
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
    exact h_sum ctx
  obtain ⟨M', hM', c₀, hc₀⟩ := kraftChaitin_realization_bound_unit hg_lsc hg_sum
  refine ⟨M', hM', c₀ + d, fun out ctx => ?_⟩
  have hkey := hc₀ out ctx
  have hrw : (2 : ℝ≥0∞)⁻¹ ^ (c₀ + d) * f out ctx
      = (2 : ℝ≥0∞)⁻¹ ^ c₀ * (f out ctx / (2 : ℝ≥0∞) ^ d) := by
    rw [pow_add, div_eq_mul_inv]
    simp only [← ENNReal.inv_pow]
    ring
  rw [hrw]
  exact hkey

end Kolmogorov
