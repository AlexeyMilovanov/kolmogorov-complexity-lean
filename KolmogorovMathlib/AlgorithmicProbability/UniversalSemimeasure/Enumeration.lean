/-
Copyright (c) 2024 Alexey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey
-/
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure.Basic

namespace Kolmogorov

open scoped ENNReal

/-! ### The Hard Theorem -/

/-! #### Canonical dyadic weights

The weights used in the universal mixture are the canonical strictly-positive
dyadic weights `dyadicWeight i = 2^{-(i+1)}` (defined in `UniversalMixture`),
whose total mass is exactly `1`. These weights supply the geometric-series algebra
(`tsum_dyadicWeight`, `dyadicWeight_pos`) used to assemble the universal mixture
from the dovetailed enumeration `approxEnum`. -/

/-
Computability of a stagewise `Finset.range` supremum: if `g` and the
two-argument family `f` are computable, then so is `a ↦ (Finset.range (g a)).sup (f a)`.
Proved by rewriting the `Finset.range` sup as a `List.range` fold.
-/
lemma computable_finset_range_sup {α : Type*} [Primcodable α]
    (g : α → ℕ) (f : α → ℕ → ℕ)
    (hg : Computable g) (hf : Computable (fun p : α × ℕ => f p.1 p.2)) :
  Computable (fun a => (Finset.range (g a)).sup (f a)) := by
  have hstep : Computable (fun p : α × ℕ × ℕ => max (f p.1 p.2.1) p.2.2) := by
    exact Primrec.nat_max.to_comp.comp
      (hf.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
  have hrec : Computable (fun a : α =>
      Nat.rec (motive := fun _ => ℕ) 0 (fun n acc => max (f a n) acc) (g a)) :=
    Computable.nat_rec hg (Computable.const 0) hstep.to₂
  exact hrec.of_eq (fun a => by
    induction g a with
    | zero => simp
    | succ n ih =>
      rw [Finset.range_add_one, Finset.sup_insert, ← ih])

/-- **The dovetailed `evaln`-budget enumeration of all lower-semicomputable
approximations.**

The `i`-th component runs the `i`-th partial-recursive `Code` (decoded from `i`)
with time budget `s` on every input `Encodable.encode (s', out, ctx)` for `s' ≤ s`,
and reports, scaled to the common denominator `2^s`, the largest dyadic value
`v · 2^(s-s')` it observes. Because `evaln` is monotone in the budget and complete
(`evaln_complete`/`evaln_mono`), the stage supremum
`⨆ s, dyadicValue (approxEnum i s out ctx) s` reproduces the limit
`⨆ s, dyadicValue (approx s out ctx) s` of *any* jointly computable `approx`, once
`i` is the code of (the totalisation of) `approx` (see `exists_approxEnum`). It is
a genuine computable family (`approxEnum_computable`), built from `primrec_evaln`.

Marked `irreducible` so the heavy `evaln`/`Finset.sup` body never participates in
downstream definitional unfolding (only its computability and sup-preservation
lemmas are used). -/
@[irreducible] def approxEnum : ℕ → ℕ → BitString → BitString → ℕ :=
  fun i s out ctx =>
    (Finset.range (s + 1)).sup (fun s' =>
      match Nat.Partrec.Code.evaln s
          ((Encodable.decode (α := Nat.Partrec.Code) i).getD Nat.Partrec.Code.zero)
          (Encodable.encode (s', out, ctx)) with
      | some v => v * 2 ^ (s - s')
      | none => 0)

lemma approxEnum_computable :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      approxEnum p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply Computable.of_eq;
  rotate_right;
  exact fun p => ( Finset.range ( p.2.1 + 1 ) ).sup fun s' => match Nat.Partrec.Code.evaln p.2.1 ( ( Encodable.decode ( α := Nat.Partrec.Code ) p.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( s', p.2.2.1, p.2.2.2 ) ) with | some v => v * 2 ^ ( p.2.1 - s' ) | none => 0;
  · convert computable_finset_range_sup _ _ _ _;
    · exact Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) );
    · convert Computable.option_casesOn _ _ _ using 1;
      rotate_left;
      exact ℕ;
      exact inferInstance;
      exact fun p => Nat.Partrec.Code.evaln p.1.2.1 ( ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) );
      exact fun p => 0;
      exact fun p v => v * 2 ^ ( p.1.2.1 - p.2 );
      · convert Nat.Partrec.Code.primrec_evaln.to_comp.comp _ using 1;
        rotate_left;
        exact fun p => ( ( p.1.2.1, ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ), Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) );
        · apply Computable.pair;
          · apply Computable.pair;
            · exact Computable.fst.comp ( Computable.snd.comp Computable.fst );
            · convert Computable.option_getD ( Computable.decode.comp ( Computable.fst.comp Computable.fst ) ) ( Computable.const Nat.Partrec.Code.zero ) using 1;
          · apply Computable.pair;
            · exact Computable.snd;
            · exact Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) ) ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) ) );
        · rfl;
      · exact Computable.const 0;
      · refine Computable.of_eq
          (f := fun p : ((ℕ × (ℕ × BitString × BitString)) × ℕ) × ℕ =>
            p.2 * 2 ^ ( p.1.1.2.1 - p.1.2 )) ?_ ?_;
        · have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => p.2.2.2.2 * 2 ^ (p.2.1 - p.1)) := by
            have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => p.2.2.2.2) := by
              exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) );
            have h_primrec : Primrec (fun p : ℕ × ℕ × BitString × BitString × ℕ => 2 ^ (p.2.1 - p.1)) := by
              have h_primrec : Primrec (fun p : ℕ × ℕ => 2 ^ (p.2 - p.1)) := by
                have h_primrec : Primrec (fun p : ℕ × ℕ => p.2 - p.1) := by
                  exact Primrec.nat_sub.comp ( Primrec.snd ) ( Primrec.fst );
                have h_primrec : Primrec (fun p : ℕ => 2 ^ p) := by
                  convert primrec_two_pow using 1;
                exact h_primrec.comp ‹_›;
              convert h_primrec.comp ( show Primrec ( fun p : ℕ × ℕ × BitString × BitString × ℕ => ( p.1, p.2.1 ) ) from ?_ ) using 1;
              exact Primrec.pair ( Primrec.fst ) ( Primrec.fst.comp ( Primrec.snd ) );
            exact Primrec.nat_mul.comp ( by assumption ) ( by assumption );
          convert h_primrec.to_comp.comp _ using 1;
          rotate_left;
          exact fun p => ( p.1.2, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2, p.2 );
          · exact Computable.pair ( Computable.snd.comp Computable.fst ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ) ( Computable.pair ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp ( Computable.fst.comp Computable.fst ) ) ) ) ( Computable.snd ) ) ) );
          · exact funext fun p => by cases p; rfl;
        · aesop;
      · exact funext fun p => by cases Nat.Partrec.Code.evaln p.1.2.1 ( ( Encodable.decode p.1.1 ).getD Nat.Partrec.Code.zero ) ( Encodable.encode ( p.2, p.1.2.2.1, p.1.2.2.2 ) ) <;> rfl;
  · grind +locals

/-
**Sup-preservation of the dovetailed enumeration (SUV/LV universality core).**

For any jointly computable approximation `approx`, the enumeration `approxEnum`
contains an index `i` whose stage supremum reproduces that of `approx`. This is the
correct *limit/sup-preservation* statement (it does **not** demand exact stagewise
reproduction, which is genuinely impossible for a total computable family): only
the suprema must agree.

Proof idea. Totalise `approx` to `h : ℕ → ℕ`, `h (Encodable.encode (s', out, ctx)) =
approx s' out ctx`; `h` is computable, so by `Nat.Partrec.Code.exists_code` there is
a code `c` with `c.eval = h`; set `i := Encodable.encode c`.
* `≤` : every observed `evaln s c n = some v` is sound (`evaln_sound`), so
  `v = approx s' out ctx`, giving `dyadicValue (approxEnum i s out ctx) s =
  ⨆_{s' ≤ s, observed} dyadicValue (approx s' out ctx) s' ≤ ⨆ s', dyadicValue ...`.
* `≥` : for each `s'`, `approx s' out ctx ∈ c.eval (encode (s', out, ctx))`, so by
  `evaln_complete` there is a budget `k` with `evaln k c ... = some (approx s')`;
  taking `s := max s' k` and `evaln_mono` puts that dyadic value into
  `dyadicValue (approxEnum i s out ctx) s`, so `⨆ s, ... ≥ dyadicValue (approx s') s'`.
-/
lemma exists_approxEnum (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    ∃ i, ∀ out ctx,
      (⨆ s, dyadicValue (approxEnum i s out ctx) s) =
      (⨆ s, dyadicValue (approx s out ctx) s) := by
        revert hcomp;
        intro hcomp
        obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, ∀ s out ctx, Nat.Partrec.Code.eval c (Encodable.encode (s, out, ctx)) = some (approx s out ctx) := by
          have h_total : ∃ h : ℕ → ℕ, Computable h ∧ ∀ s out ctx, h (Encodable.encode (s, out, ctx)) = approx s out ctx := by
            use fun n => approx (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).1 (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).2.1 (Encodable.decode (α := ℕ × BitString × BitString) n |>.getD (0, [], [])).2.2;
            convert hcomp.comp ( Computable.option_getD ( Computable.decode ) ( Computable.const ( 0, [ ], [ ] ) ) ) using 1;
            simp +decide [ Encodable.encodek ];
          obtain ⟨ h, hh₁, hh₂ ⟩ := h_total;
          have := @Nat.Partrec.Code.exists_code;
          obtain ⟨ c, hc ⟩ := this.mp (by
            simpa [Computable, Partrec] using hh₁);
          exact ⟨ c, fun s out ctx => by simp +decide [ ← hh₂, hc ] ⟩;
        refine ⟨ Encodable.encode c, fun out ctx => le_antisymm ?_ ?_ ⟩ <;> simp_all +decide [ approxEnum ];
        · intro i
          have h_term : ∀ s' ∈ Finset.range (i + 1), dyadicValue (match Nat.Partrec.Code.evaln i c (Nat.pair s' (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) with
            | some v => v * 2 ^ (i - s')
            | none => 0) i ≤ ⨆ s, dyadicValue (approx s out ctx) s := by
              intro s' hs'
              have h_term : Nat.Partrec.Code.evaln i c (Nat.pair s' (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = some (approx s' out ctx) ∨ Nat.Partrec.Code.evaln i c (Nat.pair s' (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = none := by
                cases h : Nat.Partrec.Code.evaln i c ( Nat.pair s' ( Nat.pair ( Encodable.encode out ) ( Encodable.encode ctx ) ) ) <;> simp_all +decide [ Part.eq_some_iff ];
                have := Nat.Partrec.Code.evaln_sound h; simp_all +decide [ Part.mem_eq ] ;
                cases hc s' out ctx ; aesop
              generalize_proofs at *; (
              cases h_term <;> simp +decide [ *, dyadicValue ];
              refine le_trans ?_ ( le_ciSup ?_ s' ) <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add ];
              rw [ show ( 2 ^ i : ℝ≥0∞ ) = 2 ^ ( i - s' ) * 2 ^ s' by rw [ ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hs' ) ] ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
              simp +decide [    ENNReal.mul_inv ];
              simp +decide [ mul_left_comm ( 2 ^ ( i - s' ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ]);
          have h_sup : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ s' ∈ S, dyadicValue (f s') i ≤ ⨆ s, dyadicValue (approx s out ctx) s) → dyadicValue (S.sup f) i ≤ ⨆ s, dyadicValue (approx s out ctx) s := by
            intro S f
            induction S using Finset.induction with
            | empty => intro hf; simp_all +decide [ dyadicValue ]
            | @insert s' S' hs' ih =>
              intro hf
              cases max_cases ( f s' ) ( S'.sup f ) <;> simp +decide [ * ]
              exact ih fun s' hs' => hf s' ( Finset.mem_insert_of_mem hs' )
          exact h_sup h_term;
        · intro s;
          -- By definition of `Nat.Partrec.Code.evaln`, there exists some `k` such that `Nat.Partrec.Code.evaln k c (Nat.pair s (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = some (approx s out ctx)`.
          obtain ⟨k, hk⟩ : ∃ k, Nat.Partrec.Code.evaln k c (Nat.pair s (Nat.pair (Encodable.encode out) (Encodable.encode ctx))) = some (approx s out ctx) := by
            simp_all +decide [ Part.eq_some_iff ];
            obtain ⟨ h, hh ⟩ := hc s out ctx;
            exact Nat.Partrec.Code.evaln_complete.mp (hc s out ctx);
          refine le_trans ?_ ( le_iSup _ ( Max.max s k ) );
          refine le_trans ?_ ( ENNReal.div_le_div ( Nat.cast_le.mpr <| Finset.le_sup <| Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_max_left s k ) le_rfl );
          rw [ show Nat.Partrec.Code.evaln ( Max.max s k ) c ( Nat.pair s ( Nat.pair ( Encodable.encode out ) ( Encodable.encode ctx ) ) ) = some ( approx s out ctx ) from ?_ ];
          · unfold dyadicValue; norm_num [ pow_add, pow_one, pow_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
            rw [ show ( 2 : ℝ≥0∞ ) ^ max s k = ( 2 : ℝ≥0∞ ) ^ ( max s k - s ) * ( 2 : ℝ≥0∞ ) ^ s by rw [ ← pow_add, Nat.sub_add_cancel ( le_max_left _ _ ) ] ] ; ring_nf ;
            simp +decide [  mul_comm, mul_left_comm, ENNReal.mul_inv ];
            rw [ mul_left_comm ( 2 ^ ( max s k - s ) : ℝ≥0∞ ), ENNReal.mul_inv_cancel ( by norm_num ) ( by norm_num ), mul_one ];
          · exact Nat.Partrec.Code.evaln_mono ( le_max_right _ _ ) hk

/-- The monotonic wrapper for an approximation to ensure `dyadicValue` is non-decreasing. -/
def makeMono (approx : ℕ → BitString → BitString → ℕ) : ℕ → BitString → BitString → ℕ
  | 0, out, ctx => approx 0 out ctx
  | (s+1), out, ctx => max (2 * makeMono approx s out ctx) (approx (s+1) out ctx)

lemma makeMono_mono (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (out ctx : BitString) :
    dyadicValue (makeMono approx s out ctx) s ≤ dyadicValue (makeMono approx (s + 1) out ctx) (s + 1) := by
  change dyadicValue (makeMono approx s out ctx) s
      ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx)) (s + 1)
  calc
    dyadicValue (makeMono approx s out ctx) s
        = dyadicValue (2 * makeMono approx s out ctx) (s + 1) := by
          unfold dyadicValue
          rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
          rw [ENNReal.mul_inv]
          · norm_num
            rw [show (2 : ℝ≥0∞) * (makeMono approx s out ctx : ℝ≥0∞) *
                  ((2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ s)⁻¹)
                = (makeMono approx s out ctx : ℝ≥0∞) *
                  (((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ s)⁻¹) by ring,
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
          · exact Or.inl two_ne_zero
          · exact Or.inl ENNReal.ofNat_ne_top
    _ ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx)) (s + 1) := by
          unfold dyadicValue
          gcongr
          exact_mod_cast Nat.le_max_left (2 * makeMono approx s out ctx)
            (approx (s + 1) out ctx)

lemma makeMono_ge (approx : ℕ → BitString → BitString → ℕ) (s : ℕ) (out ctx : BitString) :
    dyadicValue (approx s out ctx) s ≤ dyadicValue (makeMono approx s out ctx) s := by
  cases s with
  | zero =>
      rfl
  | succ s =>
      change dyadicValue (approx (s + 1) out ctx) (s + 1)
        ≤ dyadicValue (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx))
          (s + 1)
      unfold dyadicValue
      gcongr
      exact_mod_cast Nat.le_max_right (2 * makeMono approx s out ctx)
        (approx (s + 1) out ctx)

lemma dyadicValue_two_mul_succ (n s : ℕ) :
    dyadicValue (2 * n) (s + 1) = dyadicValue n s := by
  unfold dyadicValue
  rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
  rw [ENNReal.mul_inv]
  · norm_num
    rw [show (2 : ℝ≥0∞) * (n : ℝ≥0∞) *
          ((2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) ^ s)⁻¹)
        = (n : ℝ≥0∞) *
          (((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ s)⁻¹) by ring,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  · exact Or.inl two_ne_zero
  · exact Or.inl ENNReal.ofNat_ne_top

lemma makeMono_computable (approx : ℕ → BitString → BitString → ℕ)
    (hcomp : Computable (fun p : ℕ × BitString × BitString => approx p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString × BitString => makeMono approx p.1 p.2.1 p.2.2) := by
  let base : ℕ × BitString × BitString → ℕ := fun p => approx 0 p.2.1 p.2.2
  let step : ℕ × BitString × BitString → ℕ × ℕ → ℕ :=
    fun p q => max (2 * q.2) (approx (q.1 + 1) p.2.1 p.2.2)
  have hbase : Computable base := by
    exact hcomp.comp ((Computable.const 0).pair Computable.snd)
  have hmul_two : Computable (fun n : ℕ => 2 * n) := by
    exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp
  have hstep_uncurried :
      Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        step r.1 r.2) := by
    have hleft : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        2 * r.2.2) :=
      hmul_two.comp (Computable.snd.comp Computable.snd)
    have hstage : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        r.2.1 + 1) := by
      exact (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).to_comp
    have hright : Computable (fun r : (ℕ × BitString × BitString) × (ℕ × ℕ) =>
        approx (r.2.1 + 1) r.1.2.1 r.1.2.2) := by
      exact hcomp.comp (hstage.pair (Computable.snd.comp Computable.fst))
    exact (Primrec.nat_max.to_comp.comp hleft hright).of_eq (fun r => by rfl)
  have hrec :
      Computable (fun p : ℕ × BitString × BitString =>
        Nat.rec (motive := fun _ => ℕ) (base p) (fun y ih => step p (y, ih)) p.1) :=
    Computable.nat_rec Computable.fst hbase hstep_uncurried.to₂
  exact hrec.of_eq (fun p => by
    induction p.1 with
    | zero => rfl
    | succ s ih =>
        change Nat.rec (motive := fun _ => ℕ) (base p)
            (fun y ih => step p (y, ih)) (s + 1)
          = makeMono approx (s + 1) p.2.1 p.2.2
        simp [makeMono, step, ih])

/-
Uniform (index-parameterized) computability of `makeMono`: a jointly
computable family of approximations `b i` yields a jointly computable family
`fun (i, s, out, ctx) => makeMono (b i) s out ctx`. Mirrors `makeMono_computable`
with the index `i` carried as the leading coordinate.
-/
lemma makeMono_computable_uniform (b : ℕ → ℕ → BitString → BitString → ℕ)
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      makeMono (b p.1) p.2.1 p.2.2.1 p.2.2.2) := by
  apply Computable.of_eq;
  apply Computable.nat_rec;
  exact Computable.fst.comp Computable.snd;
  convert hb.comp _;
  exact fun p => ( p.1, 0, p.2.2.1, p.2.2.2 );
  exact Computable.pair ( Computable.fst ) ( Computable.pair ( Computable.const 0 ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) ) ( Computable.snd.comp ( Computable.snd.comp ( Computable.snd ) ) ) ) );
  rotate_left;
  exact fun p q => max ( 2 * q.2 ) ( b p.1 ( q.1 + 1 ) p.2.2.1 p.2.2.2 );
  · intro n; induction n.2.1 <;> simp +decide [ *, makeMono ] ;
  · apply Computable.of_eq;
    rotate_right;
    exact fun p => max ( 2 * p.2.2 ) ( b p.1.1 ( p.2.1 + 1 ) p.1.2.2.1 p.1.2.2.2 );
    · apply Computable.of_eq;
      apply Computable.comp (Primrec.nat_max.to_comp);
      rotate_left;
      exact fun p => ( 2 * p.2.2, b p.1.1 ( p.2.1 + 1 ) p.1.2.2.1 p.1.2.2.2 );
      · grind;
      · apply Computable.pair;
        · apply Computable.comp (Primrec.nat_mul.to_comp) (Computable.const 2 |> Computable.pair <| Computable.snd.comp Computable.snd);
        · convert hb.comp _ using 1;
          rotate_left;
          exact fun p => ( p.1.1, p.2.1 + 1, p.1.2.2.1, p.1.2.2.2 );
          · apply Computable.pair;
            · exact Computable.fst.comp Computable.fst;
            · apply Computable.pair;
              · exact Computable.succ.comp ( Computable.fst.comp ( Computable.snd ) );
              · apply Computable.pair;
                · exact Computable.fst.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
                · exact Computable.snd.comp ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
          · rfl;
    · grind +extAll

/-- A sanitised LSC approximation generated by truncating `makeMono (approxEnum i)` to unit mass. -/
noncomputable def lscEnum (i : ℕ) : BitString → BitString → ℝ≥0∞ :=
  truncG (makeMono (approxEnum i)) 0

lemma lscEnum_isLSC (i : ℕ) : IsLSC (lscEnum i) := by
  refine ⟨truncGapprox (makeMono (approxEnum i)) 0, ?_, ?_, ?_⟩
  · intro S out ctx; exact truncGapprox_mono 0 S out ctx
  · intro out ctx; rfl
  · apply truncGapprox_computable
    exact makeMono_computable (approxEnum i)
      (approxEnum_computable.comp
        ((Computable.const i).pair (Computable.fst.pair Computable.snd)))

lemma lscEnum_isSemimeasure (i : ℕ) : IsSemimeasure (fun x => lscEnum i x []) := by
  change (∑' x, truncG (makeMono (approxEnum i)) 0 x []) ≤ 1
  exact tsum_truncG_le 0 []

lemma iSup_makeMono_eq_iSup (approx : ℕ → BitString → BitString → ℕ) (out ctx : BitString) :
    (⨆ s, dyadicValue (makeMono approx s out ctx) s) = (⨆ s, dyadicValue (approx s out ctx) s) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    induction s with
    | zero =>
        exact le_iSup (fun t => dyadicValue (approx t out ctx) t) 0
    | succ s ih =>
        change dyadicValue
            (max (2 * makeMono approx s out ctx) (approx (s + 1) out ctx))
            (s + 1) ≤ ⨆ t, dyadicValue (approx t out ctx) t
        by_cases h :
            2 * makeMono approx s out ctx ≤ approx (s + 1) out ctx
        · rw [max_eq_right h]
          exact le_iSup (fun t => dyadicValue (approx t out ctx) t) (s + 1)
        · have h' : approx (s + 1) out ctx ≤ 2 * makeMono approx s out ctx := by
            exact le_of_not_ge h
          rw [max_eq_left h']
          rw [dyadicValue_two_mul_succ]
          exact ih
  · apply iSup_le
    intro s
    exact le_trans (makeMono_ge approx s out ctx)
      (le_iSup (fun t => dyadicValue (makeMono approx t out ctx) t) s)

/-- **Diagonal dyadic numerator of a uniform mixture approximation.**

Given a uniform stagewise numerator family `a i s out ctx` for a countable family
of l.s.c. functions, the stage-`S` numerator of the `dyadicWeight`-mixture is the
diagonal partial sum (over the first `S/2` components, each read at substage `S/2`)
rescaled to the common denominator `2^S`. The exponent `S - (i+1) - S/2` is
nonnegative because `i < S/2` forces `(i+1) + S/2 ≤ 2*(S/2) ≤ S`. -/
def mixtureDyadicApprox (a : ℕ → ℕ → BitString → BitString → ℕ) :
    ℕ → BitString → BitString → ℕ :=
  fun S out ctx =>
    ∑ i ∈ Finset.range (S / 2), a i (S / 2) out ctx * 2 ^ (S - (i + 1) - S / 2)

/-
The dyadic value of `mixtureDyadicApprox` at stage `S` is exactly the partial
`dyadicWeight`-weighted sum (over the first `S/2` components at substage `S/2`)
of the component dyadic values. This is the key algebraic identity behind the
mixture LSC closure.
-/
lemma dyadicValue_mixtureDyadicApprox
    (a : ℕ → ℕ → BitString → BitString → ℕ) (S : ℕ) (out ctx : BitString) :
    dyadicValue (mixtureDyadicApprox a S out ctx) S
      = ∑ i ∈ Finset.range (S / 2),
          dyadicWeight i * dyadicValue (a i (S / 2) out ctx) (S / 2) := by
  unfold dyadicValue mixtureDyadicApprox dyadicWeight;
  rw [ Nat.cast_sum, ENNReal.div_eq_inv_mul ];
  rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_congr rfl fun i hi => ?_ ; rw [ show ( 2 : ENNReal ) ^ S = ( 2 : ENNReal ) ^ ( i + 1 ) * ( 2 : ENNReal ) ^ ( S / 2 ) * ( 2 : ENNReal ) ^ ( S - ( i + 1 ) - S / 2 ) from _ ] ; ring_nf;
  · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ENNReal.mul_inv, ENNReal.inv_pow ];
    simp +decide [ ← mul_assoc ];
    simp +decide [ mul_assoc, ← mul_pow ];
    rw [ ENNReal.mul_inv_cancel ] <;> norm_num;
  · rw [ ← pow_add, ← pow_add ] ; congr 1 ; norm_num at * ; omega;

/-
**Uniform computable dyadic-mixture closure (LSC).**

If a countable family `μ i` of conditional functions has a *jointly computable*,
stagewise-monotone dyadic approximation `a i s` (numerators over the denominator
`2^s`) converging to `μ i`, then the canonical `dyadicWeight`-weighted mixture
`fun out ctx => ∑' i, dyadicWeight i * μ i out ctx` is lower-semicomputable.

The witnessing approximation is the diagonal numerator `mixtureDyadicApprox a`,
whose stage-`S` dyadic value is the partial mixture over the first `S/2`
components at substage `S/2` (see `dyadicValue_mixtureDyadicApprox`). Monotonicity
in `S` comes from the per-component monotonicity (more components, each read
later); the supremum is the double monotone limit, which equals the mixture by
the monotone convergence theorem for `ℝ≥0∞` sums; computability is a finite
`Finset.range` sum of a jointly computable term (`computable_range_sum`).
-/
lemma isLSC_unaryMixture_dyadicWeight_of_uniform
    (μ : ℕ → BitString → BitString → ℝ≥0∞)
    (a : ℕ → ℕ → BitString → BitString → ℕ)
    (hmono : ∀ i s out ctx,
      dyadicValue (a i s out ctx) s ≤ dyadicValue (a i (s + 1) out ctx) (s + 1))
    (hsup : ∀ i out ctx, ⨆ s, dyadicValue (a i s out ctx) s = μ i out ctx)
    (hcomp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
      a p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    IsLSC (fun out ctx => ∑' i, dyadicWeight i * μ i out ctx) := by
  revert μ a hmono hsup hcomp;
  -- Define the mixture approximation `a' S out ctx` as `mixtureDyadicApprox a S out ctx`.
  intro μ a hmono hsup hcomp
  set a' : ℕ → BitString → BitString → ℕ := fun S out ctx => mixtureDyadicApprox a S out ctx;
  -- Prove that `a'` is monotone in `S`.
  have ha'_mono : ∀ S out ctx, dyadicValue (a' S out ctx) S ≤ dyadicValue (a' (S + 1) out ctx) (S + 1) := by
    intros S out ctx
    simp [a', dyadicValue_mixtureDyadicApprox];
    refine le_trans ?_ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.div_le_div_right ( Nat.le_succ _ ) ) ) fun _ _ _ => by positivity );
    gcongr;
    cases Nat.mod_two_eq_zero_or_one S <;> simp_all +decide [ Nat.add_div ];
  -- Prove that `a'` converges to the mixture.
  have ha'_sup : ∀ out ctx, ⨆ S, dyadicValue (a' S out ctx) S = ∑' i, dyadicWeight i * μ i out ctx := by
    intro out ctx
    have h_double_sup : ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i k out ctx) k = ∑' i, dyadicWeight i * μ i out ctx := by
      have h_double_sup : ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i k out ctx) k = ⨆ k, ∑ i ∈ Finset.range k, dyadicWeight i * (⨆ s, dyadicValue (a i s out ctx) s) := by
        apply le_antisymm;
        · refine iSup_mono fun k => Finset.sum_le_sum fun i hi => mul_le_mul_right ?_ _;
          exact le_iSup_of_le k le_rfl;
        · refine iSup_le fun k => ?_;
          refine le_of_forall_lt_imp_le_of_dense fun x hx => ?_;
          -- Since $x < \sum_{i=0}^{k-1} \text{dyadicWeight}(i) \cdot \sup_{s} \text{dyadicValue}(a(i, s, out, ctx))$, there exists some $N$ such that $x < \sum_{i=0}^{k-1} \text{dyadicWeight}(i) \cdot \text{dyadicValue}(a(i, N, out, ctx))$.
          obtain ⟨N, hN⟩ : ∃ N, x < ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i N out ctx) N := by
            have h_lim : Filter.Tendsto (fun N => ∑ i ∈ Finset.range k, dyadicWeight i * dyadicValue (a i N out ctx) N) Filter.atTop (nhds (∑ i ∈ Finset.range k, dyadicWeight i * ⨆ s, dyadicValue (a i s out ctx) s)) := by
              refine tendsto_finsetSum _ fun i _ => ?_;
              refine ENNReal.Tendsto.const_mul ?_ ?_;
              · exact tendsto_atTop_iSup fun s t hst => monotone_nat_of_le_succ ( fun s => hmono i s out ctx ) hst;
              · exact Or.inr ( by simp +decide [ dyadicWeight ] );
            exact ( h_lim.eventually ( lt_mem_nhds hx ) ) |> fun h => h.exists;
          refine le_trans hN.le ( le_trans ?_ ( le_iSup _ ( Max.max k N ) ) );
          refine le_trans ?_ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( le_max_left k N ) ) fun _ _ _ => by positivity );
          gcongr;
          exact monotone_nat_of_le_succ ( fun s => hmono _ s _ _ ) ( le_max_right _ _ );
      simp_all +decide [ ENNReal.tsum_eq_iSup_nat ];
    rw [ ← h_double_sup, iSup_eq_of_forall_le_of_forall_lt_exists_gt ];
    · intro S;
      refine le_trans ?_ ( le_iSup _ ( S / 2 ) );
      rw [ dyadicValue_mixtureDyadicApprox ];
    · intro w hw;
      obtain ⟨ k, hk ⟩ := exists_lt_of_lt_ciSup hw;
      use 2 * k;
      refine hk.trans_le ?_;
      rw [ dyadicValue_mixtureDyadicApprox ];
      norm_num;
  -- Prove that `a'` is computable.
  have ha'_comp : Computable (fun p : ℕ × BitString × BitString => a' p.1 p.2.1 p.2.2) := by
    apply Computable.of_eq;
    convert computable_range_sum _ _ _ _ using 1;
    use fun p i => a i ( p.1 / 2 ) p.2.1 p.2.2 * 2 ^ ( p.1 - ( i + 1 ) - p.1 / 2 );
    rotate_left;
    use fun p => p.1 / 2;
    · convert Primrec.to_comp ( Primrec.nat_div.comp ( Primrec.fst ) ( Primrec.const 2 ) ) using 1;
    · aesop;
    · apply Computable₂.comp;
      · exact Primrec.to_comp ( Primrec.nat_mul.comp ( Primrec.fst ) ( Primrec.snd ) );
      · convert hcomp.comp _ using 1;
        rotate_left;
        exact fun p => ( p.2, p.1.1 / 2, p.1.2.1, p.1.2.2 );
        · apply Computable.pair;
          · exact Computable.snd;
          · apply Computable.pair;
            · have h_div : Primrec (fun n : ℕ => n / 2) := by
                exact Primrec.nat_div.comp ( Primrec.id ) ( Primrec.const 2 );
              exact h_div.to_comp.comp ( Computable.fst.comp Computable.fst );
            · exact Computable.pair ( Computable.fst.comp ( Computable.snd.comp Computable.fst ) ) ( Computable.snd.comp ( Computable.snd.comp Computable.fst ) );
        · rfl;
      · apply Computable.of_eq;
        rotate_right;
        exact fun p => 2 ^ ( p.1.1 - ( p.2 + 1 ) - p.1.1 / 2 );
        · convert Primrec.to_comp _;
          convert Primrec.comp ( primrec_two_pow ) ( Primrec.nat_sub.comp ( Primrec.nat_sub.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.succ.comp ( Primrec.snd ) ) ) ( Primrec.nat_div.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.const 2 ) ) ) using 1;
        · exact fun _ => rfl;
  use a'

/-
**Uniform computability of the sanitized enumeration approximation.**

The stage-`s` numerators of the sanitized components `lscEnum i` form a jointly
computable family in `(i, s, out, ctx)`. This is the only remaining effective
ingredient of the mixture LSC closure: it reduces precisely to the joint
computability of the enumeration core `approxEnum` (`approxEnum_computable`),
threaded through `makeMono` and `truncGapprox` (via the uniform
`makeMono_computable_uniform` and `truncGapprox_computable_uniform`).
-/
lemma lscEnumApprox_uniform_computable :
    Computable (fun p : ℕ × ℕ × BitString × BitString =>
      truncGapprox (makeMono (approxEnum p.1)) 0 p.2.1 p.2.2.1 []) := by
  convert Computable.comp ( show Computable ( fun p : ℕ × ℕ × BitString × BitString => truncGapprox ( makeMono ( approxEnum p.1 ) ) 0 p.2.1 p.2.2.1 p.2.2.2 ) from ?_ ) ( show Computable ( fun p : ℕ × ℕ × BitString × BitString => ( p.1, p.2.1, p.2.2.1, [] ) ) from ?_ ) using 1;
  · convert truncGapprox_computable_uniform ( fun i => makeMono ( approxEnum i ) ) ( makeMono_computable_uniform _ _ ) 0 using 1;
    exact approxEnum_computable;
  · exact Computable.pair ( Computable.fst ) ( Computable.pair ( Computable.fst.comp ( Computable.snd ) ) ( Computable.pair ( Computable.fst.comp ( Computable.snd.comp ( Computable.snd ) ) ) ( Computable.const [] ) ) )

/-- The dyadic mixture of the sanitized enumeration is a lower-semicomputable
unary semimeasure. The mass bound is immediate from the generic mixture theorem;
the LSC half is the general `isLSC_unaryMixture_dyadicWeight_of_uniform` closure
applied to the sanitized family, whose uniform approximation is
`lscEnumApprox_uniform_computable`. -/
lemma unaryMixture_dyadicWeight_lscEnum_isLowerSemicomputable :
    IsLowerSemicomputableSemimeasure
      (unaryMixture dyadicWeight (fun i x => lscEnum i x [])) := by
  refine ⟨?_, ?_⟩
  · exact unaryMixture_isSemimeasure dyadicWeight (fun i x => lscEnum i x [])
      tsum_dyadicWeight.le (fun i => lscEnum_isSemimeasure i)
  · have h :=
      isLSC_unaryMixture_dyadicWeight_of_uniform
        (fun i out _ => lscEnum i out [])
        (fun i s out _ => truncGapprox (makeMono (approxEnum i)) 0 s out [])
        (fun i s out ctx => truncGapprox_mono 0 s out [])
        (fun i out ctx => rfl)
        lscEnumApprox_uniform_computable
    exact h

/-- **The hard SUV enumeration/sanitization core (family only).**
...
-/
theorem exists_lsc_semimeasure_family :
    ∃ μ : ℕ → BitString → ℝ≥0∞,
      (∀ i, IsSemimeasure (μ i)) ∧
      IsLowerSemicomputableSemimeasure (unaryMixture dyadicWeight μ) ∧
      ∀ m' : BitString → ℝ≥0∞, IsLowerSemicomputableSemimeasure m' →
        ∃ (i : ℕ) (c : ℝ≥0∞), 0 < c ∧ DominatesUnary (μ i) m' c := by
  refine ⟨fun i x => lscEnum i x [], ?_, ?_, ?_⟩
  · intro i; exact lscEnum_isSemimeasure i
  · exact unaryMixture_dyadicWeight_lscEnum_isLowerSemicomputable
  · intro m' hm'
    obtain ⟨hm'_semi, hm'_lsc⟩ := hm'
    obtain ⟨approx, hmono, hsup, hcomp⟩ := hm'_lsc
    obtain ⟨i, hi⟩ := exists_approxEnum approx hcomp
    refine ⟨i, 1, by norm_num, fun x => ?_⟩
    rw [one_mul]
    have hmono_i : ∀ s out ctx, dyadicValue (makeMono (approxEnum i) s out ctx) s
        ≤ dyadicValue (makeMono (approxEnum i) (s + 1) out ctx) (s + 1) :=
      makeMono_mono (approxEnum i)
    have hsup_i : ∀ out ctx, ⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s =
        (⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s) := fun _ _ => rfl
    have hle_i : (∑' out, ⨆ s, dyadicValue (makeMono (approxEnum i) s out []) s) ≤ (2 : ℝ≥0∞) ^ 0 := by
      rw [pow_zero]
      calc
        (∑' out, ⨆ s, dyadicValue (makeMono (approxEnum i) s out []) s)
          = ∑' out, ⨆ s, dyadicValue (approxEnum i s out []) s := by
            congr 1
            ext out
            exact iSup_makeMono_eq_iSup (approxEnum i) out []
        _ = ∑' out, ⨆ s, dyadicValue (approx s out []) s := by
            congr 1
            ext out
            exact hi out []
        _ = ∑' out, m' out := by
            congr 1
            ext out
            exact hsup out []
        _ ≤ 1 := hm'_semi
    have h_trunc := truncG_eq_f_of_le (approx := makeMono (approxEnum i)) (f := fun out ctx => ⨆ s, dyadicValue (makeMono (approxEnum i) s out ctx) s) hmono_i hsup_i 0 [] hle_i x
    have h_lsc : lscEnum i x [] = truncG (makeMono (approxEnum i)) 0 x [] := rfl
    change m' x ≤ lscEnum i x []
    rw [h_lsc, h_trunc, iSup_makeMono_eq_iSup, hi x []]
    exact (hsup x []).symm.le

/-- Existence of the canonically-weighted sanitized enumeration. The weights are
the canonical dyadic weights `dyadicWeight`, whose positivity and subnormalization
are proved (`dyadicWeight_pos`, `tsum_dyadicWeight_le_one`); the family is the one
from `exists_lsc_semimeasure_family`. -/
theorem exists_lsc_semimeasure_enumeration :
    ∃ (w : ℕ → ℝ≥0∞) (μ : ℕ → BitString → ℝ≥0∞),
      (∑' i, w i) ≤ 1 ∧ (∀ i, 0 < w i) ∧ (∀ i, IsSemimeasure (μ i)) ∧
      IsLowerSemicomputableSemimeasure (unaryMixture w μ) ∧
      ∀ m' : BitString → ℝ≥0∞, IsLowerSemicomputableSemimeasure m' →
        ∃ (i : ℕ) (c : ℝ≥0∞), 0 < c ∧ DominatesUnary (μ i) m' c := by
  obtain ⟨μ, hsemi, hlsc, hdom⟩ := exists_lsc_semimeasure_family
  exact ⟨dyadicWeight, μ, tsum_dyadicWeight.le, dyadicWeight_pos, hsemi, hlsc, hdom⟩

/-- Existence of a universal lower-semicomputable semimeasure.

The maximal semimeasure is the dyadically weighted mixture of the sanitized
enumeration provided by `exists_lsc_semimeasure_enumeration`. Universality is then
pure mixture algebra: the mixture dominates each component `μ i` by its weight
`w i`, each component dominates an arbitrary l.s.c. semimeasure by a positive
constant, and unary domination composes transitively. -/
theorem exists_universalSemimeasure :
    ∃ m : BitString → ℝ≥0∞, IsUniversalSemimeasure m := by
  obtain ⟨w, μ, _hw_sum, hw_pos, _hμ, hlsc, hdom⟩ := exists_lsc_semimeasure_enumeration
  refine ⟨unaryMixture w μ, hlsc, fun m' hm' => ?_⟩
  obtain ⟨i, c, hc_pos, hci⟩ := hdom m' hm'
  refine ⟨w i * c, ENNReal.mul_pos (hw_pos i).ne' hc_pos.ne', ?_⟩
  exact (unaryMixture_dominates_component w μ i).trans hci


end Kolmogorov
