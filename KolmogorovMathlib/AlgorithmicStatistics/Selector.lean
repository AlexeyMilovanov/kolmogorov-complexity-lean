/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import KolmogorovMathlib.AlgorithmicStatistics.NonStochastic
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Constructive selector for non-stochastic strings (SUV Theorem 248 core)

This module builds the genuinely partial-recursive dovetailing selector behind
`KPPlain_uncovered_string`/`first_nonstochastic_existence`.

Given the canonical encoding `selectorInput n alpha max_k h`, the selector:
* parses `(n, alpha, max_k, h)`;
* dovetails the universal map `U` over `boundedPrograms alpha`, running `evaln`
  of a fixed code for `U` until exactly `h` of those programs halt;
* collects their outputs as candidate model codes;
* keeps the codes that round-trip through the rational-list decoder and code a
  genuine probability distribution, and tests rational level-set membership;
* returns the first length-`n` string outside all those level sets.

The correctness rests on the already-proved counting core
`exists_uncovered_nbit_string` and the coding bound `KPPlain_partrec_map_le`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-! ### Inverting `Nat.bits` -/

/-- Decode a little-endian bit list back to a natural number. Left inverse of
`Nat.bits`. -/
def bitsToNat (l : List Bool) : ℕ :=
  l.foldr (fun b acc ↦ 2 * acc + (if b then 1 else 0)) 0

theorem bitsToNat_bits (n : ℕ) : bitsToNat (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; cases b <;> rfl
    · rw [Nat.bits_append_bit _ _ (by omega)]
      simp only [bitsToNat, List.foldr_cons]
      rw [show (Nat.bits m).foldr (fun b acc ↦ 2 * acc + (if b then 1 else 0)) 0
            = bitsToNat (Nat.bits m) from rfl, ih, Nat.bit_val]
      cases b <;> simp

theorem bitsToNat_primrec : Primrec bitsToNat := by
  unfold bitsToNat
  have hstep : Primrec₂ (fun (_ : List Bool) (p : Bool × ℕ) ↦ 2 * p.2 + (if p.1 then 1 else 0)) := by
    apply Primrec.nat_add.comp₂
    · exact (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂
    · exact (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hstep

theorem bitsToNat_computable : Computable bitsToNat := bitsToNat_primrec.to_comp

/-! ### Parsing the selector input -/

/-- The first packed component: `n`. -/
def selNat (s : BitString) : ℕ := bitsToNat (decodeFirst s)
/-- The second packed component: `alpha`. -/
def selAlpha (s : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond s))
/-- The third packed component: `max_k`. -/
def selMaxK (s : BitString) : ℕ := bitsToNat (decodeFirst (decodeSecond (decodeSecond s)))
/-- The fourth packed component: the halting count `h`. -/
def selH (s : BitString) : ℕ := bitsToNat (decodeSecond (decodeSecond (decodeSecond s)))

@[simp] theorem selNat_selectorInput (n alpha max_k h : ℕ) :
    selNat (selectorInput n alpha max_k h) = n := by
  simp [selNat, selectorInput, pack4, decodeFirst_pairCode, bitsToNat_bits]

@[simp] theorem selAlpha_selectorInput (n alpha max_k h : ℕ) :
    selAlpha (selectorInput n alpha max_k h) = alpha := by
  simp [selAlpha, selectorInput, pack4, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem selMaxK_selectorInput (n alpha max_k h : ℕ) :
    selMaxK (selectorInput n alpha max_k h) = max_k := by
  simp [selMaxK, selectorInput, pack4, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

@[simp] theorem selH_selectorInput (n alpha max_k h : ℕ) :
    selH (selectorInput n alpha max_k h) = h := by
  simp [selH, selectorInput, pack4, decodeSecond_pairCode, bitsToNat_bits]

theorem selNat_computable : Computable selNat :=
  bitsToNat_computable.comp decodeFirst_computable
theorem selAlpha_computable : Computable selAlpha :=
  bitsToNat_computable.comp (decodeFirst_computable.comp decodeSecond_computable)
theorem selMaxK_computable : Computable selMaxK :=
  bitsToNat_computable.comp (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
theorem selH_computable : Computable selH :=
  bitsToNat_computable.comp (decodeSecond_computable.comp (decodeSecond_computable.comp decodeSecond_computable))

theorem selNat_primrec : Primrec selNat :=
  bitsToNat_primrec.comp decodeFirst_primrec
theorem selAlpha_primrec : Primrec selAlpha :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp decodeSecond_primrec)
theorem selMaxK_primrec : Primrec selMaxK :=
  bitsToNat_primrec.comp (decodeFirst_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))
theorem selH_primrec : Primrec selH :=
  bitsToNat_primrec.comp (decodeSecond_primrec.comp (decodeSecond_primrec.comp decodeSecond_primrec))

/-! ### Computable level-set / probability tests on raw codes -/

/-- Computable test of `x ∈ levelSet (decode w) k`, on the raw code `w`. -/
def levelSetMemBool (w : BitString) (k : ℕ) (x : BitString) : Bool :=
  RatMass.geInvPow2 (combinePointMass x (decodeDistributionData w)) k

/-- Total rational mass of a coded distribution's data. -/
def totalMassRat (data : List CodedDistributionEntry) : RatMass :=
  data.foldr (fun e acc ↦ e.mass.add acc) RatMass.zero

/-- Computable test that the decoded distribution is a probability distribution. -/
def isProbBool (w : BitString) : Bool :=
  let q := totalMassRat (decodeDistributionData w)
  decide (q.num = q.den)

/-- Computable test that `w` is a canonical list code (round-trips through the decoder). -/
def isValidCodeBool (w : BitString) : Bool :=
  decide (codedDistributionDataCode (decodeDistributionData w) = w)

/-- A length-`n` string is "covered" by the snapshot if some round-tripping
probability-model code in it has `x` in a level set at threshold `≤ max_k`. -/
def coveredBool (codes : List BitString) (max_k : ℕ) (x : BitString) : Bool :=
  codes.any (fun w ↦ isValidCodeBool w && isProbBool w &&
    (List.range (max_k + 1)).any (fun k ↦ levelSetMemBool w k x))

theorem levelSetMemBool_iff (w : BitString) (k : ℕ) (x : BitString) :
    levelSetMemBool w k x = true ↔ x ∈ levelSet (decodeCodedFiniteDistribution w) k := by
  convert RatMass.ge_invPow2_iff ( combinePointMass x ( decodeDistributionData w ) ) k using 1;
  · unfold levelSetMemBool RatMass.geInvPow2;
    rw [ RatMass.ge_invPow2_iff ];
    grind;
  · unfold levelSet; simp +decide only [mass_eq_combinePointMass, Finset.mem_filter];
    rw [ ← RatMass.ge_invPow2_iff ];
      by_cases h : x ∈ ( decodeCodedFiniteDistribution w ).support <;>
        simp_all +decide only [true_and, false_and, false_iff, not_le];
    · rfl;
    · rw [ ← CodedFiniteDistribution.mass_eq_combinePointMass ];
      rw [ CodedFiniteDistribution.mass_eq_zero_of_not_mem_support ];
      · exact ENNReal.pow_pos ( by norm_num ) _;
      · exact h

/-
The probability mass over the support equals the total rational mass value.
-/
theorem mass_total (Q : CodedFiniteDistribution) :
    ∑ x ∈ Q.support, Q.mass x = (totalMassRat Q.data).value := by
  unfold CodedFiniteDistribution.mass CodedFiniteDistribution.support totalMassRat;
  induction Q.data with
  | nil => simp_all +decide
  | cons e l ih =>
    simp_all +decide only [List.foldr_cons, RatMass.add_value]
    by_cases h : e.point ∈ List.foldr ( fun e acc ↦ insert e.point acc ) Finset.empty l <;>
      simp_all +decide only [Finset.insert_eq_of_mem, Finset.sum_add_distrib, Finset.sum_ite_eq,
        Finset.mem_insert, or_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte];
    rw [ show List.foldr ( fun e_1 acc ↦ ( if e_1.point = e.point then e_1.mass.value else 0 ) + acc ) 0 l = 0 from ?_ ]; ring;
    have h_foldr_zero : ∀ {l : List CodedDistributionEntry}, e.point ∉ List.foldr (fun e_1 acc ↦ insert e_1.point acc) Finset.empty l → List.foldr (fun e_1 acc ↦ (if e_1.point = e.point then e_1.mass.value else 0) + acc) 0 l = 0 := by
      intros l hl; induction l <;> simp_all +decide [ Finset.mem_insert ];
      lia;
    exact h_foldr_zero h

theorem isProbBool_iff (w : BitString) :
    isProbBool w = true ↔ (decodeCodedFiniteDistribution w).IsProbability := by
  rw [ isProbBool, CodedFiniteDistribution.IsProbability ];
  rw [ mass_total ]; simp only [ RatMass.value, decide_eq_true_eq ];
  rw [ ENNReal.div_eq_one_iff ] <;> norm_cast;
  · exact Nat.ne_of_gt ( RatMass.den_pos _ );
  · exact ENNReal.coe_ne_top

theorem isValidCodeBool_code (P : CodedFiniteDistribution) : isValidCodeBool P.code = true := by
  simp only [isValidCodeBool, decide_eq_true_eq, CodedFiniteDistribution.code,
    decodeDistributionData_code]

theorem isProbBool_code (P : CodedFiniteDistribution) (hP : P.IsProbability) :
    isProbBool P.code = true := by
  rw [isProbBool_iff, decodeCodedFiniteDistribution_code]; exact hP

theorem levelSetMemBool_primrec :
    Primrec (fun p : (BitString × ℕ) × BitString ↦ levelSetMemBool p.1.1 p.1.2 p.2) := by
  have h_ge_invPow2_primrec : Primrec₂ (fun (q : RatMass) (k : ℕ) ↦ q.geInvPow2 k) := by
    grind +suggestions;
  have h1 : Primrec (fun p : (BitString × ℕ) × BitString ↦ combinePointMass p.2 (decodeDistributionData p.1.1)) :=
    combinePointMass_primrec.comp Primrec.snd (decodeDistributionData_primrec.comp (Primrec.fst.comp Primrec.fst))
  have h2 : Primrec (fun p : (BitString × ℕ) × BitString ↦ p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.of_eq (h_ge_invPow2_primrec.comp h1 h2) (fun _ ↦ rfl)

theorem isValidCodeBool_primrec : Primrec isValidCodeBool := by
  have h_primrec : Primrec (fun w : BitString ↦ codedDistributionDataCode (decodeDistributionData w)) :=
    CodedFiniteDistribution.codedDistributionDataCode_primrec.comp decodeDistributionData_primrec
  have h_eq : Primrec₂ (fun w v : BitString ↦ decide (w = v)) := by
    obtain ⟨_, hx⟩ := (Primrec.eq : PrimrecRel (α := BitString) Eq)
    exact Primrec.of_eq hx (fun a ↦ by by_cases h : a.1 = a.2 <;> simp [h])
  exact Primrec.of_eq (h_eq.comp h_primrec Primrec.id) (fun _ ↦ rfl)

theorem isProbBool_primrec : Primrec isProbBool := by
  have totalMassRat_primrec : Primrec totalMassRat := by
    have h_proj : Primrec (fun (e : CodedDistributionEntry) ↦ e.mass) := by grind +suggestions;
    have h_add : Primrec₂ (fun (e : CodedDistributionEntry) (acc : RatMass) ↦ e.mass.add acc) :=
      ratMass_add_primrec.comp (h_proj.comp Primrec.fst) Primrec.snd
    exact Primrec.list_foldr Primrec.id (Primrec.const RatMass.zero) (Primrec.comp h_add Primrec.snd).to₂
  have h_eq : Primrec₂ (fun (a b : RatMass) ↦ decide (a.num = b.den)) := by
    have h_eq_nat : Primrec₂ (fun (a b : ℕ) ↦ decide (a = b)) := by
      obtain ⟨_, hx⟩ := (Primrec.eq : PrimrecRel (α := ℕ) Eq)
      exact Primrec.of_eq hx (fun a ↦ by by_cases h : a.1 = a.2 <;> simp [h])
    exact h_eq_nat.comp (ratMass_num_primrec.comp Primrec.fst) (ratMass_den_primrec.comp Primrec.snd)
  have h1 : Primrec (fun w ↦ totalMassRat (decodeDistributionData w)) :=
    totalMassRat_primrec.comp decodeDistributionData_primrec
  exact Primrec.of_eq (h_eq.comp h1 h1) (fun _ ↦ rfl)

/-- `List.any` with a primrec list and primrec predicate is primrec. -/
theorem list_any_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a ↦ (f a).any (p a)) := by
  have heq : (fun a ↦ (f a).any (p a)) = (fun a ↦ (f a).foldr (fun b acc ↦ p a b || acc) false) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => simp [List.any_cons, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Bool) ↦ p a q.1 || q.2) :=
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const true)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const false) hstep

theorem coveredBool_primrec :
    Primrec (fun p : (List BitString × ℕ) × BitString ↦ coveredBool p.1.1 p.1.2 p.2) := by
  have h1 : Primrec (fun p : (List BitString × ℕ) × BitString ↦ p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec₂ (fun (p : (List BitString × ℕ) × BitString) (w : BitString) ↦ isValidCodeBool w && isProbBool w) :=
    Primrec.and.comp (isValidCodeBool_primrec.comp Primrec.snd) (isProbBool_primrec.comp Primrec.snd)
  have hrange : Primrec (fun p : ((List BitString × ℕ) × BitString) × BitString ↦ List.range (p.1.1.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hany : Primrec₂ (fun (p : ((List BitString × ℕ) × BitString) × BitString) (k : ℕ) ↦ levelSetMemBool p.2 k p.1.2) := by
    have hw : Primrec (fun (p : (((List BitString × ℕ) × BitString) × BitString) × ℕ) ↦ p.1.2) := Primrec.snd.comp Primrec.fst
    have hk : Primrec (fun (p : (((List BitString × ℕ) × BitString) × BitString) × ℕ) ↦ p.2) := Primrec.snd
    have hx : Primrec (fun (p : (((List BitString × ℕ) × BitString) × BitString) × ℕ) ↦ p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hm : Primrec (fun (p : (((List BitString × ℕ) × BitString) × BitString) × ℕ) ↦ ((p.1.2, p.2), p.1.1.2)) :=
      Primrec.pair (Primrec.pair hw hk) hx
    exact levelSetMemBool_primrec.comp hm
  have hb : Primrec₂ (fun (p : (List BitString × ℕ) × BitString) (w : BitString) ↦ (List.range (p.1.2 + 1)).any (fun k ↦ levelSetMemBool w k p.2)) :=
    list_any_primrec hrange hany
  have h_inner : Primrec₂ (fun (p : (List BitString × ℕ) × BitString) (w : BitString) ↦
      isValidCodeBool w && isProbBool w && (List.range (p.1.2 + 1)).any (fun k ↦ levelSetMemBool w k p.2)) :=
    Primrec.and.comp ha hb
  exact list_any_primrec h1 h_inner

/-! ### Dovetailing snapshot -/

/-- A natural-number code `c` computes the map `U` (via the standard encode/decode
graph). -/
def IsCodeFor (c : Code) (U : Map) : Prop :=
  c.eval = fun n ↦ (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
    (fun a ↦ Part.map Encodable.encode (U a))

/-- Output of program `p` (in empty context) within step budget `t`, decoded back
to a bit string. -/
def runOut (c : Code) (t : ℕ) (p : BitString) : Option BitString :=
  (Code.evaln t c (Encodable.encode ((p, []) : BitString × BitString))).bind
    (fun r ↦ (Encodable.decode r : Option BitString))

/-- Whether program `p` halts within step budget `t`. -/
def haltsWithin (c : Code) (t : ℕ) (p : BitString) : Bool :=
  (Code.evaln t c (Encodable.encode ((p, []) : BitString × BitString))).isSome

/-- Number of length-`≤ alpha` programs that halt within budget `t`. -/
def countHalts (c : Code) (alpha t : ℕ) : ℕ :=
  (boundedPrograms alpha).countP (haltsWithin c t)

/-- The outputs of all length-`≤ alpha` programs that halt within budget `t`. -/
def snapshotCodes (c : Code) (alpha t : ℕ) : List BitString :=
  (boundedPrograms alpha).filterMap (runOut c t)

/-- `List.countP` with a primrec list and primrec predicate is primrec. -/
theorem list_countP_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a ↦ (f a).countP (p a)) := by
  have heq : (fun a ↦ (f a).countP (p a))
      = (fun a ↦ (f a).foldr (fun b n ↦ bif p a b then n+1 else n) 0) := by
    funext a
    rw [List.countP_eq_length_filter]
    induction f a with
    | nil => rfl
    | cons b t ih => cases h : p a b <;> simp [List.filter, h, List.foldr, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × ℕ) ↦ bif p a q.1 then q.2+1 else q.2) :=
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const 0) hstep

/-- For a fixed code, `evaln` is primrec in the step budget and the input. -/
theorem evaln_primrec (c : Code) : Primrec₂ (fun (t : ℕ) (x : ℕ) ↦ Code.evaln t c x) :=
  (Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd) :
    Primrec (fun p : ℕ × ℕ ↦ Code.evaln p.1 c p.2))

theorem countHalts_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ ↦ countHalts c p.1 p.2) := by
  have hp_lst : Primrec (fun (p : ℕ × ℕ) ↦ boundedPrograms p.1) := primrec_boundedPrograms.comp Primrec.fst
  have hp_eval : Primrec (fun (a : (ℕ × ℕ) × BitString) ↦ Code.evaln a.1.2 c (Encodable.encode (a.2, ([] : List BitString)))) :=
    (evaln_primrec c).comp (Primrec.snd.comp Primrec.fst) (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const [])))
  have hp_some : Primrec₂ (fun (p : ℕ × ℕ) (y : BitString) ↦ (Code.evaln p.2 c (Encodable.encode (y, ([] : List BitString)))).isSome) :=
    Primrec.option_isSome.comp hp_eval
  exact Primrec.of_eq (list_countP_primrec hp_lst hp_some) (fun _ ↦ rfl)

theorem countHalts_computable (c : Code) :
    Computable (fun p : ℕ × ℕ ↦ countHalts c p.1 p.2) := (countHalts_primrec c).to_comp

theorem snapshotCodes_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ ↦ snapshotCodes c p.1 p.2) := by
  apply Primrec.listFilterMap (primrec_boundedPrograms.comp Primrec.fst);
  apply Primrec.option_bind;
  · exact (evaln_primrec c).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const [])));
  · exact Primrec.decode.comp Primrec.snd

theorem snapshotCodes_computable (c : Code) :
    Computable (fun p : ℕ × ℕ ↦ snapshotCodes c p.1 p.2) := (snapshotCodes_primrec c).to_comp

/-
`(boundedPrograms n).length = 2^(n+1) - 1`, in the additive form.
-/
theorem length_boundedPrograms_succ_eq (n : ℕ) :
    (boundedPrograms n).length + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [boundedPrograms, length_exactLengthPrograms]
  | succ n ih =>
    rw [boundedPrograms_succ, List.length_append, length_exactLengthPrograms]
    rw [Nat.pow_succ] at ih ⊢
    omega

theorem length_boundedPrograms_lt (n : ℕ) : (boundedPrograms n).length < 2 ^ (n + 1) := by
  have := length_boundedPrograms_succ_eq n; omega

theorem haltsWithin_mono (c : Code) {t t' : ℕ} (h : t ≤ t') (p : BitString) :
    haltsWithin c t p = true → haltsWithin c t' p = true := by
  intro h';
  obtain ⟨ x, hx ⟩ := Option.isSome_iff_exists.mp h';
  exact Option.isSome_iff_exists.mpr ⟨ x, by exact Nat.Partrec.Code.evaln_mono h hx ⟩

theorem countHalts_mono (c : Code) (alpha : ℕ) {t t' : ℕ} (h : t ≤ t') :
    countHalts c alpha t ≤ countHalts c alpha t' := by
  unfold countHalts;
  induction ( boundedPrograms alpha ) using List.reverseRecOn <;> simp_all +decide [ List.countP_cons ];
  grind +suggestions

theorem countHalts_le_length (c : Code) (alpha t : ℕ) :
    countHalts c alpha t ≤ (boundedPrograms alpha).length :=
  List.countP_le_length

/-
The dovetailing count attains a maximum over all step budgets.
-/
theorem exists_max_countHalts (c : Code) (alpha : ℕ) :
    ∃ t, ∀ t', countHalts c alpha t' ≤ countHalts c alpha t := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ Set.range (fun t ↦ countHalts c alpha t) ∧ ∀ t' ∈ Set.range (fun t ↦ countHalts c alpha t), t' ≤ t := by
    apply_rules [ Set.exists_max_image ];
    · exact Set.finite_iff_bddAbove.mpr ⟨ _, Set.forall_mem_range.mpr fun t ↦ countHalts_le_length c alpha t ⟩;
    · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
  aesop

theorem runOut_sound {c : Code} {U : Map} (hc : IsCodeFor c U) {t : ℕ} {p w : BitString}
    (h : runOut c t p = some w) : produces U p [] w := by
  unfold runOut at h;
  rw [ Option.bind_eq_some_iff ] at h;
  obtain ⟨ a, ha₁, ha₂ ⟩ := h;
  have := Nat.Partrec.Code.evaln_sound ha₁;
  unfold IsCodeFor at hc; aesop;

theorem runOut_complete {c : Code} {U : Map} (hc : IsCodeFor c U) {p out : BitString}
    (h : produces U p [] out) : ∃ t, runOut c t p = some out := by
  obtain ⟨t, ht⟩ : ∃ t, Encodable.encode out ∈ Code.evaln t c (Encodable.encode ((p, []) : BitString × BitString)) := by
    have h_evaln : Encodable.encode out ∈ c.eval (Encodable.encode ((p, []) : BitString × BitString)) := by
      simp_all +decide [ produces, IsCodeFor ];
    grind +suggestions;
  -- By definition of `runOut`, we have `runOut c t p = (Code.evaln t c (Encodable.encode ((p, []) : BitString × BitString))).bind (fun r ↦ (Encodable.decode r : Option BitString))`.
  use t
  simp [runOut];
  simp_all +decide [ Encodable.encodek ]

/-
At a step budget achieving the maximal halting count, every output of a
halting length-`≤ alpha` program is already in the snapshot.
-/
theorem code_mem_snapshot_of_max {c : Code} {U : Map} (hc : IsCodeFor c U) (alpha t : ℕ)
    (hmax : ∀ t', countHalts c alpha t' ≤ countHalts c alpha t)
    {p out : BitString} (hp : p ∈ boundedPrograms alpha) (hout : produces U p [] out) :
    out ∈ snapshotCodes c alpha t := by
  contrapose! hmax;
  obtain ⟨ t', ht' ⟩ := runOut_complete hc hout; use t'; simp_all +decide only [ countHalts ];
  have h_countP_mono : ∀ {l : List BitString} {p : BitString}, p ∈ l → haltsWithin c t p = false → haltsWithin c t' p = true → List.countP (haltsWithin c t) l < List.countP (haltsWithin c t') l := by
    intros l p hp ht ht'; induction l <;>
      simp_all +decide only [ List.not_mem_nil, List.mem_cons, List.countP_cons ];
    cases hp <;>
      simp_all +decide only [ Bool.false_eq_true, ↓reduceIte, add_zero, Order.lt_add_one_iff,
        forall_const ];
    · rename_i k hk₁ hk₂ hk₃;
      by_cases hk₄ : k ∈ hk₁ <;> simp_all +decide only [ forall_const, IsEmpty.forall_iff ];
      · grind;
      · induction hk₁ <;>
          simp_all +decide only [ List.not_mem_nil, not_false_eq_true, List.countP_nil, Std.le_refl,
            List.mem_cons, not_or, List.countP_cons, forall_const ];
        split_ifs <;>
          simp_all +decide only [ add_zero, Order.add_one_le_iff, Order.lt_add_one_iff,
            Bool.not_eq_true ];
        · exact absurd ( haltsWithin_mono c ( show t ≤ t' from Nat.le_of_not_lt fun h ↦ by
                                                exact absurd ( haltsWithin_mono c h.le _ ) ( by aesop ) ) _ ) ( by aesop );
        · bv_omega;
    · split_ifs <;>
        simp_all +decide only [ Order.lt_add_one_iff, Order.add_one_le_iff, Bool.not_eq_true, add_zero ];
      · exact absurd ( haltsWithin_mono c ( show t ≤ t' from le_of_not_gt fun h ↦ by have := haltsWithin_mono c h.le p; aesop ) _ ) ( by aesop );
      · grind;
  unfold runOut at ht'; simp_all +decide only [ Encodable.encode_prod_val, Encodable.encode_list_nil, Option.bind_eq_some_iff, gt_iff_lt ];
  obtain ⟨ a, ha₁, ha₂ ⟩ := ht'; specialize @h_countP_mono ( boundedPrograms alpha ) p hp;
    simp_all +decide only [ haltsWithin, Encodable.encode_prod_val, Encodable.encode_list_nil,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, Option.isSome_some, forall_const ];
  apply h_countP_mono; exact (by
  unfold snapshotCodes at hmax; simp_all +decide only [ List.mem_filterMap, not_exists, not_and ];
  unfold runOut at hmax; simp_all +decide only [ Encodable.encode_prod_val, Encodable.encode_list_nil, Option.bind_eq_some_iff, not_exists, not_and ];
  exact Option.eq_none_iff_forall_not_mem.mpr fun x hx ↦
    hmax p hp x hx <| by
      have := Nat.Partrec.Code.evaln_mono (show t ≤ t' from
        Nat.le_of_not_lt fun h ↦ by
          have := Nat.Partrec.Code.evaln_mono (show t' ≤ t from le_of_lt h) ha₁
          simp_all +decide only [ Option.mem_def, Option.some.injEq, reduceCtorEq, IsEmpty.forall_iff ]
          exact hmax p hp a
            (by simpa [this] using Nat.Partrec.Code.evaln_mono (show t' ≤ t from le_of_lt h) ha₁)
            ha₂) hx
      aesop;)

/-
A probability model of complexity `≤ alpha` is the output of some
length-`≤ alpha` program.
-/
theorem exists_halting_program_of_complexity_le (U : Map) (P : CodedFiniteDistribution)
    (alpha : ℕ) (hcomp : P.complexity U ≤ (alpha : ENat)) :
    ∃ p, p ∈ boundedPrograms alpha ∧ produces U p [] P.code := by
  by_cases h : KP U P.code [] = ⊤;
  · simp_all +decide [ complexity, KPPlain_eq_KP ];
  · obtain ⟨p, hp_prod, hp_len⟩ : ∃ p, produces U p [] P.code ∧ (programLength p : ENat) = KP U P.code [] :=
      exists_program_of_KP_ne_top h
    have h_len : (programLength p : ENat) ≤ alpha := by
      exact hp_len.trans_le hcomp
    exact ⟨ p, by rw [ mem_boundedPrograms_iff ]; exact_mod_cast h_len, hp_prod ⟩

/-! ### The selector and its partial recursiveness -/

/-- The dovetailing selector for a fixed code `c` of `U`. -/
noncomputable def selectorFn (c : Code) : BitString →. BitString := fun s ↦
  (Nat.rfind (fun t ↦ Part.some (decide (countHalts c (selAlpha s) t = selH s)))).bind
    (fun t ↦ Part.ofOption
      ((allStrings (selNat s)).find?
        (fun x ↦ ! coveredBool (snapshotCodes c (selAlpha s) t) (selMaxK s) x)))

/-- `List.find?` with a primrec list and primrec predicate is primrec. -/
theorem list_find?_primrec {α β} [Primcodable α] [Primcodable β] {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) : Primrec (fun a ↦ (f a).find? (p a)) := by
  have heq : (fun a ↦ (f a).find? (p a))
      = (fun a ↦ (f a).foldr (fun b acc ↦ bif p a b then some b else acc) none) := by
    funext a; induction f a with
    | nil => rfl
    | cons b t ih => cases h : p a b <;> simp [h, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (a : α) (q : β × Option β) ↦ bif p a q.1 then some q.1 else q.2) :=
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const none) hstep

theorem eq_decide_computable : Computable (fun p : ℕ × ℕ ↦ decide (p.1 = p.2)) := by
  obtain ⟨ _, h ⟩ := ( Primrec.eq : PrimrecRel ( α := ℕ ) Eq )
  exact h.to_comp.of_eq (fun p ↦ by congr 1)

theorem selector_check_computable (c : Code) : Computable (fun st : BitString × ℕ ↦ decide (countHalts c (selAlpha st.1) st.2 = selH st.1)) := by
  have h_count : Computable (fun st : BitString × ℕ ↦ countHalts c (selAlpha st.1) st.2) :=
    @Computable.comp (BitString × ℕ) (ℕ × ℕ) ℕ _ _ _
      (fun p ↦ countHalts c p.1 p.2) (fun st ↦ (selAlpha st.1, st.2))
      (countHalts_computable c)
      (@Computable.pair (BitString × ℕ) ℕ ℕ _ _ _
        (fun st ↦ selAlpha st.1) (fun st ↦ st.2)
        (@Computable.comp (BitString × ℕ) BitString ℕ _ _ _ selAlpha Prod.fst selAlpha_computable Computable.fst)
        Computable.snd)
  have h_selH : Computable (fun st : BitString × ℕ ↦ selH st.1) :=
    @Computable.comp (BitString × ℕ) BitString ℕ _ _ _ selH Prod.fst selH_computable Computable.fst
  exact (@Computable.comp (BitString × ℕ) (ℕ × ℕ) Bool _ _ _
    (fun p ↦ decide (p.1 = p.2)) (fun st ↦ (countHalts c (selAlpha st.1) st.2, selH st.1))
    eq_decide_computable (@Computable.pair (BitString × ℕ) ℕ ℕ _ _ _ _ _ h_count h_selH)).of_eq (fun _ ↦ rfl)

theorem selector_post_computable (c : Code) : Computable (fun st : BitString × ℕ ↦ (allStrings (selNat st.1)).find? (fun x ↦ ! coveredBool (snapshotCodes c (selAlpha st.1) st.2) (selMaxK st.1) x)) := by
  have h_allStrings : Primrec (fun st : BitString × ℕ ↦ allStrings (selNat st.1)) :=
    allStrings_primrec.comp (selNat_primrec.comp Primrec.fst)
  have h_snapshot : Primrec (fun st : BitString × ℕ ↦ snapshotCodes c (selAlpha st.1) st.2) :=
    (snapshotCodes_primrec c).comp (Primrec.pair (selAlpha_primrec.comp Primrec.fst) Primrec.snd)
  have h_maxK : Primrec (fun st : BitString × ℕ ↦ selMaxK st.1) :=
    selMaxK_primrec.comp Primrec.fst
  have h_covered : Primrec₂ (fun (st : BitString × ℕ) (x : BitString) ↦ ! coveredBool (snapshotCodes c (selAlpha st.1) st.2) (selMaxK st.1) x) := by
    have hw : Primrec (fun p : (BitString × ℕ) × BitString ↦ (snapshotCodes c (selAlpha p.1.1) p.1.2, selMaxK p.1.1)) :=
      Primrec.pair (h_snapshot.comp Primrec.fst) (h_maxK.comp Primrec.fst)
    have hx : Primrec (fun p : (BitString × ℕ) × BitString ↦ p.2) := Primrec.snd
    have hp : Primrec (fun p : (BitString × ℕ) × BitString ↦ ((snapshotCodes c (selAlpha p.1.1) p.1.2, selMaxK p.1.1), p.2)) :=
      Primrec.pair hw hx
    exact Primrec.not.comp (coveredBool_primrec.comp hp)
  exact (list_find?_primrec h_allStrings h_covered).to_comp

theorem partrec_selectorFn (c : Code) : Partrec (selectorFn c) := by
  have h_check := selector_check_computable c
  have h_post := selector_post_computable c
  have hf : Partrec (fun s : BitString ↦ Nat.rfind (fun t ↦ Part.some (decide (countHalts c (selAlpha s) t = selH s)))) :=
    Partrec.rfind h_check
  exact Partrec.bind hf (Computable.ofOption h_post)

/-
Membership characterization of the `coveredBool` test.
-/
theorem coveredBool_iff (codes : List BitString) (max_k : ℕ) (x : BitString) :
    coveredBool codes max_k x = true ↔
      ∃ w ∈ codes, isValidCodeBool w = true ∧ isProbBool w = true ∧
        ∃ k ≤ max_k, levelSetMemBool w k x = true := by
  unfold coveredBool;
  grind

theorem complexity_decode_of_mem_snapshot {c : Code} {U : Map} (hc : IsCodeFor c U)
    {alpha t : ℕ} {w : BitString} (hw : w ∈ snapshotCodes c alpha t) :
    KPPlain U w ≤ (alpha : ENat) := by
  -- By definition of `snapshotCodes`, there exists a program `p` with `p ∈ boundedPrograms alpha` and `runOut c t p = some w`.
  obtain ⟨p, hp⟩ : ∃ p ∈ boundedPrograms alpha, runOut c t p = some w := by
    unfold snapshotCodes at hw; aesop;
  have h_complexity_le_alpha : KP U w [] ≤ (programLength p : ENat) := by
    apply KP_le_programLength_of_produces;
    exact runOut_sound hc hp.2;
  exact h_complexity_le_alpha.trans ( by exact_mod_cast by have := mem_boundedPrograms_iff p alpha; aesop )

/-! ### Main constructive theorem -/

theorem exists_partrec_uncovered_selector (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ n alpha max_k : ℕ,
        2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n →
        ∃ h : ℕ, h < 2 ^ (alpha + 1) ∧
          ∃ x, x ∈ f (selectorInput n alpha max_k h) ∧ x.length = n ∧
            (∀ P : CodedFiniteDistribution, P.IsProbability →
              P.complexity U ≤ (alpha : ENat) → ∀ k ≤ max_k, x ∉ levelSet P k) := by
  -- By definition of `IsOptimalPrefixConditional`, there exists a code `c` such that `IsCodeFor c U`.
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor;
  refine ⟨ ?_, ?_, ?_ ⟩;
  exact selectorFn c;
  · exact partrec_selectorFn c;
  · intro n alpha max_k hcov
    obtain ⟨t_star, hmax⟩ := exists_max_countHalts c alpha
    set h := countHalts c alpha t_star
    have h_lt : h < 2 ^ (alpha + 1) := by
      exact lt_of_le_of_lt ( countHalts_le_length c alpha t_star ) ( length_boundedPrograms_lt alpha )
    obtain ⟨t₀, ht0, ht0_min⟩ : ∃ t₀, countHalts c alpha t₀ = h ∧ ∀ m < t₀, countHalts c alpha m ≠ h := by
      exact ⟨ Nat.find ( ⟨ t_star, rfl ⟩ : ∃ t₀, countHalts c alpha t₀ = h ), Nat.find_spec ( ⟨ t_star, rfl ⟩ : ∃ t₀, countHalts c alpha t₀ = h ), fun m mn ↦ Nat.find_min ( ⟨ t_star, rfl ⟩ : ∃ t₀, countHalts c alpha t₀ = h ) mn ⟩
    have hmax0 : ∀ t', countHalts c alpha t' ≤ countHalts c alpha t₀ := by
      grind
    set s := selectorInput n alpha max_k h
    set snap := snapshotCodes c alpha t₀
    set pred := fun x ↦ ! coveredBool snap max_k x
    obtain ⟨x0, hx0len, hx0unc⟩ := exists_uncovered_nbit_string U n alpha max_k hcov
    have hpred : pred x0 = true := by
      by_contra h_contra
      obtain ⟨w, hw⟩ : ∃ w ∈ snap, isValidCodeBool w = true ∧ isProbBool w = true ∧ ∃ k ≤ max_k, levelSetMemBool w k x0 = true := by
        grind +locals;
      obtain ⟨k, hk₁, hk₂⟩ := hw.2.2.2
      have hQ : (decodeCodedFiniteDistribution w).IsProbability := by
        exact isProbBool_iff w |>.1 hw.2.2.1
      have hQcode : (decodeCodedFiniteDistribution w).code = w := by
        unfold isValidCodeBool at hw; aesop;
      have hQcomp : (decodeCodedFiniteDistribution w).complexity U ≤ alpha := by
        convert complexity_decode_of_mem_snapshot hc hw.1 using 1;
        exact congr_arg _ hQcode
      have hQlevel : x0 ∈ levelSet (decodeCodedFiniteDistribution w) k := by
        exact levelSetMemBool_iff w k x0 |>.1 hk₂ |> fun h ↦ by simpa [ hQcode ] using h;
      exact hx0unc (decodeCodedFiniteDistribution w) hQ hQcomp k hk₁ hQlevel
    have hx0snap : x0 ∈ allStrings n := by
      exact mem_allStrings n x0 |>.2 hx0len
    obtain ⟨y, hy⟩ : ∃ y, (allStrings n).find? pred = some y := by
      exact Option.isSome_iff_exists.mp ( List.find?_isSome.mpr ⟨ x0, hx0snap, hpred ⟩ ) |> fun ⟨ y, hy ⟩ ↦ ⟨ y, hy ⟩
    have hylen : y.length = n := by
      exact mem_allStrings n y |>.1 ( List.mem_of_find?_eq_some hy )
    have hxy : y ∈ selectorFn c s := by
      unfold selectorFn; aesop;
    use h, h_lt, y;
    refine ⟨ hxy, hylen, ?_ ⟩;
    intro P hP hcomp k hk hyk
    have hPcode : P.code ∈ snap := by
      have := exists_halting_program_of_complexity_le U P alpha hcomp; obtain ⟨ p, hp₁, hp₂ ⟩ := this; exact code_mem_snapshot_of_max hc alpha t₀ hmax0 hp₁ hp₂;
    have hPvalid : isValidCodeBool P.code = true := by
      exact isValidCodeBool_code P
    have hPprob : isProbBool P.code = true := by
      exact isProbBool_code P hP
    have hPlevel : levelSetMemBool P.code k y = true := by
      convert levelSetMemBool_iff P.code k y |>.2 _ using 1;
      convert hyk using 1;
      rw [ decodeCodedFiniteDistribution_code ]
    have hPcovered : coveredBool snap max_k y = true := by
      exact coveredBool_iff _ _ _ |>.2 ⟨ P.code, hPcode, hPvalid, hPprob, k, hk, hPlevel ⟩
    have hPpred : pred y = false := by
      grind +revert
    exact absurd hPpred (by
    have := List.find?_some hy; aesop;)

theorem KPPlain_uncovered_string (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n alpha max_k : ℕ,
      2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n →
      ∃ x : BitString, x.length = n ∧
        (∀ P : CodedFiniteDistribution, P.IsProbability →
          P.complexity U ≤ (alpha : ENat) →
          ∀ k ≤ max_k, x ∉ levelSet P k) ∧
        KPPlain U x ≤ (alpha : ENat) + (c : ENat) * (Nat.bits n).length := by
  obtain ⟨f, hf_partrec, hf_correct⟩ := exists_partrec_uncovered_selector U hU
  obtain ⟨c_partrec, hc_partrec⟩ := KPPlain_partrec_map_le U hU f hf_partrec
  obtain ⟨c, hc⟩ := KPPlain_selectorInput_le U hU c_partrec
  use c
  intro n alpha max_k h_cov
  obtain ⟨h, hh, x, hx_some, hx_len, hx_cov⟩ := hf_correct n alpha max_k h_cov
  refine ⟨x, hx_len, hx_cov, ?_⟩
  calc
    KPPlain U x ≤ KPPlain U (selectorInput n alpha max_k h) + (c_partrec : ENat) := hc_partrec _ _ hx_some
    _ ≤ (alpha : ENat) + (c : ENat) * (Nat.bits n).length := hc n alpha max_k h hh h_cov

/-- The first paper-level non-stochastic existence theorem with explicit constants. -/
theorem first_nonstochastic_existence (U : Map) (hU : IsOptimalPrefixConditional U) :
  ∃ c : ℕ, ∀ n alpha beta : ℕ,
    2 * alpha + beta + c * (Nat.bits n).length < n →
      ∃ x : BitString, x.length = n ∧ IsNonStochastic U x alpha beta := by
  obtain ⟨c_1, hc1⟩ := KPPlain_uncovered_string U hU
  obtain ⟨c_2, hc2⟩ := stochastic_mem_levelSet_of_KPPlain_bound U hU
  let c := c_1 + c_2 + 4
  refine ⟨c, fun n alpha beta hgap ↦ ?_⟩
  let max_k := alpha + beta + c_1 * (Nat.bits n).length + c_2
  have h_size : 2 ^ (alpha + 1) * (max_k + 1) * 2 ^ max_k < 2 ^ n :=
    nonstochastic_arithmetic_bridge n alpha beta c_1 c_2 c (le_refl _) hgap
  obtain ⟨x, hx_len, hx_not_mem, hx_KPPlain⟩ := hc1 n alpha max_k h_size
  refine ⟨x, hx_len, ?_⟩
  intro hstoch
  let kxBound := alpha + c_1 * (Nat.bits n).length
  have hx_KPPlain_bound : KPPlain U x ≤ (kxBound : ENat) := by
    simpa [kxBound] using hx_KPPlain
  have h_threshold : kxBound + beta + c_2 ≤ max_k := by
    simp [kxBound, max_k]
    omega
  obtain ⟨P, hprob, hcomp, k, hk_max, hk_mem⟩ :=
    hc2 x alpha beta kxBound max_k hstoch hx_KPPlain_bound h_threshold
  have hx_not_mem_k := hx_not_mem P hprob hcomp k hk_max
  exact hx_not_mem_k hk_mem

end Kolmogorov
