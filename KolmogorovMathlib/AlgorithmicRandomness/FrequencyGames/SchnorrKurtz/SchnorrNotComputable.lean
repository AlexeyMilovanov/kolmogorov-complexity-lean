/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.SchnorrKurtz.SchnorrMartingaleGrowth

/-!
# Schnorr randomness is strictly weaker than computable randomness

This module constructs a Schnorr random sequence that is not Mises-Church random, by inserting
zeros into the binary expansion of Chaitin's `Ω` at positions governed by a partial computable
waiting map.  The inserted zeros are selected by a decidable rule, but they are so sparse that the
sequence still satisfies Schnorr's complexity criterion.

## Main declarations

* `exists_isSchnorrRandom_not_isMisesChurchRandom`: there is a Schnorr random sequence that is
  not Mises-Church random (Problem 271 of Shen, Uspensky and Vereshchagin).
* `exists_isSchnorrRandom_not_isComputablyRandom`: Schnorr randomness is strictly weaker than
  computable randomness.
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Problem 271: the construction

We take for `a` the binary expansion of Chaitin's `Ω` (Martin-Löf random) and for the "waiting
oracle" the partial computable map of Theorem 116 (`exists_computable_gt_BP_of_omegaPrefix`): on
`a↾n` it halts with a number `t > BP U (n - d)`.  The sequence `w` is obtained from `a` by inserting
zeros: the state `(y, i)` after `j` positions of `w` consists of the part `y = a↾m` of `a` consumed
so far and the number `i` of inserted zeros; position `j` is an inserted zero iff `y` is long enough
(`i + 1 + d ≤ |y|`) and the step-bounded evaluation `T` (a computable `Option`-valued
approximation of the partial map) halts on `a↾(i + 1 + d)` within `j` steps with a value `t ≤ j`.
This is decidable from the prefix of `w` (decode it by replaying the process), so the set `R` of
strings after which a zero is inserted is a decidable selection rule that selects only zeros. -/

/-- The insertion decision at position `j` in the state `s = (y, i)`: `y` is long enough and the
step-bounded run `T` halts within `j` steps on `y↾(i + 1 + d)` with a value `t ≤ j`. -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_ins (T : BitString → ℕ → Option ℕ)
    (d : ℕ) (s : BitString × ℕ) (j : ℕ) : Bool :=
  decide (s.2 + 1 + d ≤ s.1.length) &&
    (match T (s.1.take (s.2 + 1 + d)) j with
      | some t => decide (t ≤ j)
      | none => false)

/-- One step of the decoding of `w`: at position `j`, in the state `s = (y, i)`, either the bit is
an inserted zero (`i` increases, `y` is unchanged) or it is the next bit `b` of `a` (appended to
`y`). -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_step (T : BitString → ℕ → Option ℕ)
    (d : ℕ) (s : BitString × ℕ) (j : ℕ) (b : Bool) : BitString × ℕ :=
  bif exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d s j then (s.1, s.2 + 1)
  else (s.1 ++ [b], s.2)

/-- The state reached after reading the string `x` as the first `|x|` bits of `w`. -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_dec (T : BitString → ℕ → Option ℕ)
    (d : ℕ) (x : BitString) : BitString × ℕ :=
  (x.foldl (fun (p : (BitString × ℕ) × ℕ) (b : Bool) =>
    (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d p.1 p.2 b, p.2 + 1))
    (([], 0), 0)).1

/-- The state after `j` positions of the sequence built from `a`. -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_state (T : BitString → ℕ → Option ℕ)
    (d : ℕ) (a : CantorSeq) : ℕ → BitString × ℕ
  | 0 => ([], 0)
  | j + 1 =>
    exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
      (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
      (a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length)

/-- The constructed sequence `w`: an inserted zero, or the next unread bit of `a`. -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_seq (T : BitString → ℕ → Option ℕ)
    (d : ℕ) (a : CantorSeq) : CantorSeq := fun j =>
  bif exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
      (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j then false
  else a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length

/-- The selection rule: the strings after which the next term of `w` is an inserted zero. -/
private def exists_isSchnorrRandom_not_isMisesChurchRandom_rule (T : BitString → ℕ → Option ℕ)
    (d : ℕ) : Set BitString :=
  {x | exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
    (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x) x.length = true}

/-- Step 1 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the binary
expansion `a` of `Ω` is Martin-Löf random, and (Theorem 116,
`exists_computable_gt_BP_of_omegaPrefix`)
a partial computable `f` and a constant `d` give on every prefix `a↾n` a value `t > BP U (n - d)`.
This replaces the Kučera-Gács theorem of the book. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_omega (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ (a : CantorSeq) (f : BitString →. ℕ) (d : ℕ), IsMartinLofRandom uniformMeasure a ∧
      Partrec f ∧ ∀ n, ∃ t, t ∈ f (cantorPrefix a n) ∧ BP U (n - d) < t := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  obtain ⟨a, ha, -⟩ := exists_cantorReal_eq (omegaReal_pos hm) (omegaReal_le_one hm)
  have hrand : IsMartinLofRandom uniformMeasure a := by
    rw [← isMartinLofRandomReal_iff_isMartinLofRandom_cantorReal, ha]
    exact isMartinLofRandomReal_omegaReal hm
  obtain ⟨f, d, hf, hfd⟩ := exists_computable_gt_BP_of_omegaPrefix hm hU ha
  exact ⟨a, f, d, hrand, hf, hfd⟩

/-- Step 2 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: a partial
computable `f : BitString →. ℕ` has a computable step-bounded evaluation `T x s : Option ℕ`, which
is sound, complete and monotone in the number of steps `s`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_eval (f : BitString →. ℕ)
    (hf : Partrec f) :
    ∃ T : BitString → ℕ → Option ℕ, Computable₂ T ∧
      (∀ x s t, T x s = some t → t ∈ f x) ∧ (∀ x t, t ∈ f x → ∃ s, T x s = some t) ∧
      (∀ x s s' t, s ≤ s' → T x s = some t → T x s' = some t) := by
  have hg : Partrec
      (fun n : ℕ => (Part.ofOption (Encodable.decode (α := BitString) n)).bind f) := by
    refine Partrec.bind (Computable.ofOption Computable.decode) ?_
    exact hf.comp Computable.snd
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hg)
  have heval : ∀ x : BitString, Nat.Partrec.Code.eval c (Encodable.encode x) = f x := by
    intro x
    rw [hc]
    change (Part.ofOption (Encodable.decode (α := BitString) (Encodable.encode x))).bind f = f x
    rw [Encodable.encodek]
    exact Part.bind_some x f
  refine ⟨fun x s => Nat.Partrec.Code.evaln s c (Encodable.encode x), ?_, ?_, ?_, ?_⟩
  · have h : Computable
        (fun p : BitString × ℕ => Nat.Partrec.Code.evaln p.2 c (Encodable.encode p.1)) :=
      (evalnCoreComputable c).comp
        (Computable.pair Computable.snd (Computable.encode.comp Computable.fst))
    exact h
  · intro x s t ht
    rw [← heval x]
    exact Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr ht)
  · intro x t ht
    rw [← heval x] at ht
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp ht
    exact ⟨k, Option.mem_def.mp hk⟩
  · intro x s s' t hss ht
    exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hss (Option.mem_def.mpr ht))

/-- Step 3 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the prefix
busy beaver `BP U` eventually dominates every total computable function (`K(g i) ≤ K(i) + O(1)`
and `K(i) ≤ 2 log i + O(1) ≤ i` for large `i`). -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_dominate (U : Map)
    (hU : IsOptimalPrefixConditional U) (g : ℕ → ℕ) (hg : Computable g) :
    ∃ i₀, ∀ i ≥ i₀, g i ≤ BP U i := by
  obtain ⟨c₀, hc₀⟩ := exists_const_KPPlain_le_KPNat U hU
    (e := fun n : ℕ => natToBitString (g n)) (computable_natToBitString.comp hg)
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_two_mul_length U hU
  set C : ℕ := c₂ + c₀ with hCdef
  have hexp : ∀ k, C + 4 ≤ k → 2 * k + C + 2 < 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      have hCpow : C + 1 ≤ 2 ^ C := Nat.lt_two_pow_self
      have h16 : (2 : ℕ) ^ (C + 4) = 16 * 2 ^ C := by rw [pow_add]; ring
      omega
    | succ k hk ih =>
      have h2 : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]
      omega
  refine ⟨3 * C + 8, fun i hi => ?_⟩
  set k : ℕ := (i - C) / 2 with hk
  have hk1 : C + 4 ≤ k := by omega
  have hk2 : 2 * k + C ≤ i := by omega
  have hk3 : i + 1 ≤ 2 * k + C + 2 := by omega
  have hsize : Nat.size (i + 1) ≤ k := Nat.size_le.2 (lt_of_le_of_lt hk3 (hexp k hk1))
  have hlen : (natToBitString i).length ≤ k := by
    have h1 : (natToBitString i).length = (Nat.bits (i + 1)).length - 1 := by
      simp [natToBitString]
    have h2 : (Nat.bits (i + 1)).length = Nat.size (i + 1) := Nat.size_eq_bits_len _
    omega
  have hKi : KPNat U i ≤ ((2 * k + c₂ : ℕ) : ENat) := by
    refine le_trans (hc₂ (natToBitString i)) ?_
    have hcast : ((natToBitString i).length : ENat) ≤ (k : ENat) := by exact_mod_cast hlen
    calc (2 : ENat) * ((natToBitString i).length : ENat) + (c₂ : ENat)
        ≤ 2 * (k : ENat) + (c₂ : ENat) := by gcongr
      _ = ((2 * k + c₂ : ℕ) : ENat) := by push_cast; ring
  have hKg : KPNat U (g i) ≤ ((2 * k + C : ℕ) : ENat) := by
    have h := hc₀ i
    rw [← KPNat_def] at h
    refine le_trans h ?_
    calc KPNat U i + (c₀ : ENat) ≤ ((2 * k + c₂ : ℕ) : ENat) + (c₀ : ENat) := by gcongr
      _ = ((2 * k + C : ℕ) : ENat) := by rw [hCdef]; push_cast; ring
  exact le_trans (le_BP_of_KPNat_le hKg) (BP_mono U hk2)

/-- Auxiliary for step 4: the position counter of the decoding fold advances by one per bit. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_aux1
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (x : BitString) (p₀ : (BitString × ℕ) × ℕ) :
    (x.foldl (fun (p : (BitString × ℕ) × ℕ) (b : Bool) =>
      (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d p.1 p.2 b, p.2 + 1)) p₀).2 =
      p₀.2 + x.length := by
  induction x generalizing p₀ with
  | nil => simp
  | cons b x ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    omega

/-- Auxiliary for step 4: reading one more bit performs one decoding step. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_aux2
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (x : BitString) (b : Bool) :
    exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d (x ++ [b]) =
      exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
        (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x) x.length b := by
  have h := exists_isSchnorrRandom_not_isMisesChurchRandom_aux1 T d x (([], 0), 0)
  simp only [zero_add] at h
  unfold exists_isSchnorrRandom_not_isMisesChurchRandom_dec
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only []
  rw [h]

/-- Step 4 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: decoding the
first `j` bits of `w` gives the state after `j` positions. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_dec_seq
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (j : ℕ) :
    exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d
        (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j) =
      exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j := by
  induction j with
  | zero =>
    simp [exists_isSchnorrRandom_not_isMisesChurchRandom_dec,
      exists_isSchnorrRandom_not_isMisesChurchRandom_state, cantorPrefix]
  | succ j ih =>
    rw [cantorPrefix_succ, exists_isSchnorrRandom_not_isMisesChurchRandom_aux2,
      cantorPrefix_length, ih]
    have hstate : exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1) =
        exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
          (a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length) := rfl
    rw [hstate]
    have hseq : exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a j =
        bif exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
            (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j then false
        else a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length := rfl
    rw [hseq]
    unfold exists_isSchnorrRandom_not_isMisesChurchRandom_step
    cases h : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j <;> simp

/-- Step 5 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the consumed
part `y` of `a` is a prefix of `a`, and `|y| + (number of inserted zeros) = j`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_state_inv
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (j : ℕ) :
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1 =
        cantorPrefix a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length ∧
      (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length +
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 = j := by
  induction j with
  | zero =>
    simp [exists_isSchnorrRandom_not_isMisesChurchRandom_state, cantorPrefix]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hstate : exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1) =
        exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
          (a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length) := rfl
    rw [hstate]
    unfold exists_isSchnorrRandom_not_isMisesChurchRandom_step
    cases h : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
    · simp only [Bool.cond_false, List.length_append, List.length_singleton]
      refine ⟨?_, by omega⟩
      rw [cantorPrefix_succ, ← h1]
    · simp only [Bool.cond_true]
      exact ⟨h1, by omega⟩

/-- The insertion test is computable in the state and the position. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_step6_aux1
    (T : BitString → ℕ → Option ℕ) (hT : Computable₂ T) (d : ℕ) :
    Computable (fun q : (BitString × ℕ) × ℕ =>
      exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d q.1 q.2) := by
  have hk : Primrec (fun q : (BitString × ℕ) × ℕ => q.1.2 + 1 + d) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
      (Primrec.const d)
  have hlen : Primrec (fun q : (BitString × ℕ) × ℕ => q.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hc1 : Computable
      (fun q : (BitString × ℕ) × ℕ => decide (q.1.2 + 1 + d ≤ q.1.1.length)) :=
    (Primrec.nat_le.comp hk hlen).decide.to_comp
  have htake : Primrec (fun q : (BitString × ℕ) × ℕ => q.1.1.take (q.1.2 + 1 + d)) :=
    Primrec.list_take.comp hk (Primrec.fst.comp Primrec.fst)
  have hcall : Computable
      (fun q : (BitString × ℕ) × ℕ => T (q.1.1.take (q.1.2 + 1 + d)) q.2) :=
    Computable₂.comp (f := T) (g := fun q : (BitString × ℕ) × ℕ => q.1.1.take (q.1.2 + 1 + d))
      (h := fun q : (BitString × ℕ) × ℕ => q.2) hT htake.to_comp Computable.snd
  have hg : Computable₂ (fun (q : (BitString × ℕ) × ℕ) (t : ℕ) => decide (t ≤ q.2)) :=
    (Primrec.nat_le.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide.to_comp
  have hm : Computable (fun q : (BitString × ℕ) × ℕ =>
      match T (q.1.1.take (q.1.2 + 1 + d)) q.2 with
      | some t => decide (t ≤ q.2)
      | none => false) :=
    (Computable.option_casesOn hcall (Computable.const false) hg).of_eq (fun q => by
      cases T (q.1.1.take (q.1.2 + 1 + d)) q.2 <;> rfl)
  exact (Computable.cond hc1 hm (Computable.const false)).of_eq (fun q => by
    unfold exists_isSchnorrRandom_not_isMisesChurchRandom_ins
    cases decide (q.1.2 + 1 + d ≤ q.1.1.length) <;> rfl)

/-- One decoding step is computable in the state, the position and the bit. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_step6_aux2
    (T : BitString → ℕ → Option ℕ) (hT : Computable₂ T) (d : ℕ) :
    Computable (fun u : (BitString × ℕ) × ℕ × Bool =>
      exists_isSchnorrRandom_not_isMisesChurchRandom_step T d u.1 u.2.1 u.2.2) := by
  have hins : Computable (fun u : (BitString × ℕ) × ℕ × Bool =>
      exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d u.1 u.2.1) :=
    Computable.comp (f := fun q : (BitString × ℕ) × ℕ =>
        exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d q.1 q.2)
      (g := fun u : (BitString × ℕ) × ℕ × Bool => (u.1, u.2.1))
      (exists_isSchnorrRandom_not_isMisesChurchRandom_step6_aux1 T hT d)
      (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
  have hthen : Computable (fun u : (BitString × ℕ) × ℕ × Bool => (u.1.1, u.1.2 + 1)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)).to_comp
  have helse : Computable (fun u : (BitString × ℕ) × ℕ × Bool => (u.1.1 ++ [u.2.2], u.1.2)) :=
    Computable.pair
      (Primrec.list_append.to_comp.comp (Computable.fst.comp Computable.fst)
        (Computable.list_cons.comp (Computable.snd.comp Computable.snd) (Computable.const [])))
      (Computable.snd.comp Computable.fst)
  exact (Computable.cond hins hthen helse).of_eq (fun u => rfl)

/-- Step 6 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the decoder
and the insertion test (hence the selection rule) are computable. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_computable
    (T : BitString → ℕ → Option ℕ) (hT : Computable₂ T) (d : ℕ) :
    Computable (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d) ∧
      Computable (fun x : BitString => exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
        (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x) x.length) := by
  have hstep := exists_isSchnorrRandom_not_isMisesChurchRandom_step6_aux2 T hT d
  have hh : Computable₂ (fun (_ : BitString) (u : ((BitString × ℕ) × ℕ) × Bool) =>
      (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d u.1.1 u.1.2 u.2, u.1.2 + 1)) :=
    Computable.pair
      (Computable.comp
        (f := fun v : (BitString × ℕ) × ℕ × Bool =>
          exists_isSchnorrRandom_not_isMisesChurchRandom_step T d v.1 v.2.1 v.2.2)
        (g := fun p : BitString × (((BitString × ℕ) × ℕ) × Bool) => (p.2.1.1, p.2.1.2, p.2.2))
        hstep
        (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.snd))
          (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.snd))
            (Computable.snd.comp Computable.snd))))
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const 1)).to_comp
  have hfold := computable_list_foldl (f := fun x : BitString => x)
    (g := fun _ : BitString => ((([] : BitString), (0 : ℕ)), (0 : ℕ)))
    (h := fun (_ : BitString) (u : ((BitString × ℕ) × ℕ) × Bool) =>
      (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d u.1.1 u.1.2 u.2, u.1.2 + 1))
    Computable.id (Computable.const _) hh
  have hdec : Computable (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d) :=
    (Computable.fst.comp hfold).of_eq (fun x => rfl)
  exact ⟨hdec,
    Computable.comp (f := fun q : (BitString × ℕ) × ℕ =>
        exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d q.1 q.2)
      (g := fun x : BitString =>
        (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x, x.length))
      (exists_isSchnorrRandom_not_isMisesChurchRandom_step6_aux1 T hT d)
      (Computable.pair hdec Computable.list_length)⟩

/-- Step 7 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the selection
rule selects exactly the inserted zeros. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_selected
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (j : ℕ) :
    selectedBits (exists_isSchnorrRandom_not_isMisesChurchRandom_rule T d)
        (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j) =
      List.replicate (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 false := by
  induction j with
  | zero =>
    simp [cantorPrefix, selectedBits, selectedAux,
      exists_isSchnorrRandom_not_isMisesChurchRandom_state]
  | succ j ih =>
    rw [cantorPrefix_succ, selectedBits_append_singleton, ih]
    have hmem : (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j ∈
        exists_isSchnorrRandom_not_isMisesChurchRandom_rule T d) ↔
        exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j = true := by
      change exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d
            (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j))
          (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j).length =
          true ↔ _
      rw [exists_isSchnorrRandom_not_isMisesChurchRandom_dec_seq, cantorPrefix_length]
    by_cases hins : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j = true
    · have hm := hmem.mpr hins
      simp only [hm, ↓reduceIte]
      have hseq : exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a j = false := by
        simp [exists_isSchnorrRandom_not_isMisesChurchRandom_seq, hins]
      have hstate : exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1) =
          ((exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1,
            (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 + 1) := by
        simp [exists_isSchnorrRandom_not_isMisesChurchRandom_state,
          exists_isSchnorrRandom_not_isMisesChurchRandom_step, hins]
      rw [hseq, hstate, List.replicate_succ']
    · have hm : ¬ (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) j ∈
          exists_isSchnorrRandom_not_isMisesChurchRandom_rule T d) := fun h => hins (hmem.mp h)
      simp only [hm, ↓reduceIte]
      have hstate : (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1)).2 =
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 := by
        simp [exists_isSchnorrRandom_not_isMisesChurchRandom_state,
          exists_isSchnorrRandom_not_isMisesChurchRandom_step, hins]
      rw [hstate, List.append_nil]

/-- Step 8 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: if a rule
selects from the first `j` terms of `w` exactly `z j` zeros, with `z` unbounded, then the selected
sequence is infinite and has no limit frequency `1/2`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_not_freq (R : Set BitString)
    (w : CantorSeq) (z : ℕ → ℕ)
    (hsel : ∀ j, selectedBits R (cantorPrefix w j) = List.replicate (z j) false)
    (hunb : ∀ i, ∃ j, i ≤ z j) : ¬ FiniteOrFreq (1 / 2) (selectStream R w) := by
  intro hfin
  have hmem : ∀ j, List.replicate (z j) false ∈ chainPrefixSet (selectChain R w) := fun j =>
    ⟨j, by rw [selectChain, hsel j]⟩
  have key : ∀ x, BitStream.finite x ≤ selectStream R w ↔ x ∈ chainPrefixSet (selectChain R w) :=
    fun x => BitStream.finite_le_ofPrefixSet_iff
      (isStreamPrefixSet_chainPrefixSet (selectChain_prefix R w)) x
  rcases hs : selectStream R w with u | u
  · obtain ⟨j, hj⟩ := hunb (u.length + 1)
    have h1 : BitStream.finite (List.replicate (z j) false) ≤ selectStream R w :=
      (key _).2 (hmem j)
    rw [hs] at h1
    have h2 : List.replicate (z j) false <+: u := h1
    have h3 := h2.length_le
    rw [List.length_replicate] at h3
    omega
  · have hu : ∀ k, u k = false := by
      intro k
      obtain ⟨j, hj⟩ := hunb (k + 1)
      have h1 : BitStream.finite (List.replicate (z j) false) ≤ selectStream R w :=
        (key _).2 (hmem j)
      rw [hs] at h1
      have h2 : IsCantorPrefix (List.replicate (z j) false) u := h1
      have h3 := h2 k (by rw [List.length_replicate]; omega)
      simpa using h3
    rw [hs] at hfin
    have hlim : HasLimitFreq (1 / 2) u := hfin
    have hzero : ∀ n, (freqOne u n : ℝ) = 0 := by
      intro n
      rw [freqOne_eq]
      have h0 : ∀ i ∈ Finset.range n, bitVal (u i) = 0 := by
        intro i _
        simp [hu i, bitVal]
      rw [Finset.sum_eq_zero h0]
      simp
    have hlim0 : Tendsto (fun n => (freqOne u n : ℝ)) atTop (𝓝 0) := by
      have hfun : (fun n => (freqOne u n : ℝ)) = fun _ => 0 := funext hzero
      rw [hfun]
      exact tendsto_const_nhds
    have h12 := tendsto_nhds_unique hlim hlim0
    norm_num at h12

/-- The number of inserted zeros after `j + 1` positions: it grows by one exactly when the
insertion test fires at position `j`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_step9_aux1
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (j : ℕ) :
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1)).2 =
      if exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j = true then
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 + 1
      else (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 := by
  change (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
    (a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length)).2 = _
  unfold exists_isSchnorrRandom_not_isMisesChurchRandom_step
  cases hins : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j <;> simp

/-- The number of inserted zeros is monotone in the position. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_step9_aux2
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) :
    Monotone (fun j => (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2) := by
  refine monotone_nat_of_le_succ fun j => ?_
  change _ ≤ (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1)).2
  rw [exists_isSchnorrRandom_not_isMisesChurchRandom_step9_aux1]
  split_ifs <;> omega

/-- The insertion test fires once the state is long enough and the step-bounded run has halted
with a value `t ≤ j`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_aux3
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq)
    (hTm : ∀ x s s' t, s ≤ s' → T x s = some t → T x s' = some t)
    (st : BitString × ℕ) (j s t : ℕ) (hy : st.1 = cantorPrefix a st.1.length)
    (hge : st.2 + 1 + d ≤ st.1.length) (hs : T (cantorPrefix a (st.2 + 1 + d)) s = some t)
    (hsj : s ≤ j) (htj : t ≤ j) :
    exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d st j = true := by
  have htake : st.1.take (st.2 + 1 + d) = cantorPrefix a (st.2 + 1 + d) := by
    have h1 := cantorPrefix_take a (st.2 + 1 + d) st.1.length hge
    rw [← hy] at h1
    exact h1
  unfold exists_isSchnorrRandom_not_isMisesChurchRandom_ins
  rw [htake, hTm _ _ _ _ hsj hs]
  simp [hge, htj]

/-- The number of inserted zeros cannot stay constant from some position on. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_aux4
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (f : BitString →. ℕ)
    (hTc : ∀ x t, t ∈ f x → ∃ s, T x s = some t)
    (hTm : ∀ x s s' t, s ≤ s' → T x s = some t → T x s' = some t)
    (hf : ∀ n, ∃ t, t ∈ f (cantorPrefix a n)) (M j₀ : ℕ)
    (hconst : ∀ j ≥ j₀, (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 = M) :
    False := by
  obtain ⟨t, ht⟩ := hf (M + 1 + d)
  obtain ⟨s, hs⟩ := hTc _ _ ht
  obtain ⟨j, hj0, hjs, hjt, hjn⟩ : ∃ j, j₀ ≤ j ∧ s ≤ j ∧ t ≤ j ∧ M + 1 + d + M ≤ j :=
    ⟨j₀ + s + t + (M + 1 + d + M), by omega, by omega, by omega, by omega⟩
  have hzj := hconst j hj0
  obtain ⟨hy, hlen⟩ := exists_isSchnorrRandom_not_isMisesChurchRandom_state_inv T d a j
  have hins := exists_isSchnorrRandom_not_isMisesChurchRandom_aux3 T d a hTm
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j s t hy (by omega)
    (by rw [hzj]; exact hs) hjs hjt
  have h1 := exists_isSchnorrRandom_not_isMisesChurchRandom_step9_aux1 T d a j
  simp only [hins, ↓reduceIte] at h1
  have h2 := hconst (j + 1) (by omega)
  omega

/-- Step 9 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: infinitely
many zeros are inserted (the wait for the value of `f` on `a↾(i + 1 + d)` ends). -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_unbounded
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (f : BitString →. ℕ)
    (hTc : ∀ x t, t ∈ f x → ∃ s, T x s = some t)
    (hTm : ∀ x s s' t, s ≤ s' → T x s = some t → T x s' = some t)
    (hf : ∀ n, ∃ t, t ∈ f (cantorPrefix a n)) :
    ∀ i, ∃ j, i ≤ (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 := by
  intro i
  induction i with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ i ih =>
    obtain ⟨j₀, hj₀⟩ := ih
    by_contra hcon
    refine exists_isSchnorrRandom_not_isMisesChurchRandom_aux4 T d a f hTc hTm hf i j₀
      (fun j hj => ?_)
    have hmono : (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j₀).2 ≤
        (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 :=
      exists_isSchnorrRandom_not_isMisesChurchRandom_step9_aux2 T d a hj
    have hlt : (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 < i + 1 :=
      not_le.mp (not_exists.mp hcon j)
    omega

/-- Step 10 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the `i`-th
inserted zero is placed at a position after `BP U i`, i.e. after `j` positions at most `i` zeros
have been inserted where `BP U i < j`. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_bp_inv (U : Map)
    (T : BitString → ℕ → Option ℕ) (d : ℕ) (a : CantorSeq) (f : BitString →. ℕ)
    (hTs : ∀ x s t, T x s = some t → t ∈ f x)
    (hf : ∀ n, ∃ t, t ∈ f (cantorPrefix a n) ∧ BP U (n - d) < t) (j : ℕ) :
    (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 = 0 ∨
      BP U (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).2 < j := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    obtain ⟨hy, -⟩ := exists_isSchnorrRandom_not_isMisesChurchRandom_state_inv T d a j
    have hstate : exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a (j + 1) =
        exists_isSchnorrRandom_not_isMisesChurchRandom_step T d
          (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j) j
          (a (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j).1.length) := rfl
    rw [hstate]
    generalize exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a j = s at ih hy ⊢
    by_cases hins : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d s j = true
    · right
      have hs2 : (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d s j
          (a s.1.length)).2 = s.2 + 1 := by
        simp [exists_isSchnorrRandom_not_isMisesChurchRandom_step, hins]
      rw [hs2]
      have hins' := hins
      unfold exists_isSchnorrRandom_not_isMisesChurchRandom_ins at hins'
      rw [Bool.and_eq_true] at hins'
      obtain ⟨hlen, hmatch⟩ := hins'
      have hlen' : s.2 + 1 + d ≤ s.1.length := of_decide_eq_true hlen
      cases hT : T (s.1.take (s.2 + 1 + d)) j with
      | none =>
        rw [hT] at hmatch
        simp at hmatch
      | some t =>
        rw [hT] at hmatch
        have htj : t ≤ j := of_decide_eq_true hmatch
        have htake : s.1.take (s.2 + 1 + d) = cantorPrefix a (s.2 + 1 + d) := by
          have h1 := cantorPrefix_take a (s.2 + 1 + d) s.1.length hlen'
          rw [← hy] at h1
          exact h1
        have hmem : t ∈ f (cantorPrefix a (s.2 + 1 + d)) := by
          rw [← htake]
          exact hTs _ j t hT
        obtain ⟨t', ht', hlt⟩ := hf (s.2 + 1 + d)
        have htt : t = t' := Part.mem_unique hmem ht'
        have hsub : s.2 + 1 + d - d = s.2 + 1 := Nat.add_sub_cancel _ _
        rw [hsub] at hlt
        omega
    · have hins' : exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d s j = false := by
        simpa using hins
      have hs2 : (exists_isSchnorrRandom_not_isMisesChurchRandom_step T d s j
          (a s.1.length)).2 = s.2 := by
        simp [exists_isSchnorrRandom_not_isMisesChurchRandom_step, hins']
      rw [hs2]
      exact ih.imp_right (fun h => Nat.lt_succ_of_lt h)

/-- Step 11 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: a counting
function `z` with `z j = 0 ∨ BP U (z j) < j` is eventually below every computable non-decreasing
unbounded function. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_slow (U : Map)
    (hU : IsOptimalPrefixConditional U) (z : ℕ → ℕ) (hz : ∀ j, z j = 0 ∨ BP U (z j) < j)
    (h' : ℕ → ℕ) (hh' : IsComputableGrowth h') : ∃ N, ∀ n ≥ N, z n ≤ h' n := by
  have hunb : ∀ B, ∃ n, B ≤ h' n := hh'.unbounded
  -- `g i` is the least `n` with `i ≤ h' n`; it is computable
  have hg : Computable (fun i => Nat.find (hunb i)) := by
    have hP : Computable (fun p : ℕ × ℕ => decide ((fun i n => i ≤ h' n) p.1 p.2)) :=
      (PrimrecRel.decide Primrec.nat_le).to_comp.comp Computable.fst
        (hh'.computable.comp Computable.snd)
    exact Computable.natFind (P := fun i n => i ≤ h' n) hP hunb
  obtain ⟨i₀, hi₀⟩ := exists_isSchnorrRandom_not_isMisesChurchRandom_dominate U hU _ hg
  obtain ⟨N, hN⟩ := hunb i₀
  refine ⟨N, fun n hn => ?_⟩
  by_contra hlt
  have hlt : h' n < z n := not_le.mp hlt
  have hzn : z n ≠ 0 := by omega
  have hBP : BP U (z n) < n := (hz n).resolve_left hzn
  have hi_le : h' n + 1 ≤ z n := hlt
  have hBPi : BP U (h' n + 1) ≤ BP U (z n) := BP_mono U hi_le
  have hi0 : i₀ ≤ h' n + 1 := by
    have := hh'.monotone hn
    omega
  have hdom : Nat.find (hunb (h' n + 1)) ≤ BP U (h' n + 1) := hi₀ (h' n + 1) hi0
  have hlt_find : n < Nat.find (hunb (h' n + 1)) := by
    by_contra hge
    have hge : Nat.find (hunb (h' n + 1)) ≤ n := not_lt.mp hge
    have hspec : h' n + 1 ≤ h' (Nat.find (hunb (h' n + 1))) := Nat.find_spec (hunb (h' n + 1))
    have := hh'.monotone hge
    omega
  omega

/-- Step 12 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: the prefix
complexity of `w↾n` is at least `n` minus the number of inserted zeros, up to a constant (the
decoder is computable and `a` is Martin-Löf random). -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_complexity (U : Map)
    (hU : IsOptimalPrefixConditional U) (a : CantorSeq) (ha : IsMartinLofRandom uniformMeasure a)
    (T : BitString → ℕ → Option ℕ) (hT : Computable₂ T) (d : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤
      KPPlain U (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) n) +
        ((exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a n).2 : ℕ∞) + (c : ℕ∞) := by
  obtain ⟨c₀, hc₀⟩ := (isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU a).mp ha
  have hdec : Computable (fun x : BitString =>
      (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x).1) :=
    Computable.fst.comp (exists_isSchnorrRandom_not_isMisesChurchRandom_computable T hT d).1
  obtain ⟨c₁, hc₁⟩ := KPPlain_map_le U hU _ hdec
  refine ⟨c₀ + c₁, fun n => ?_⟩
  have h4 := exists_isSchnorrRandom_not_isMisesChurchRandom_dec_seq T d a n
  obtain ⟨h1, h2⟩ := exists_isSchnorrRandom_not_isMisesChurchRandom_state_inv T d a n
  have hk := hc₁ (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) n)
  rw [h4] at hk
  generalize exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a n = S at h1 h2 hk ⊢
  generalize KPPlain U
    (cantorPrefix (exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a) n) = K at hk ⊢
  obtain ⟨y, z⟩ := S
  simp only at h1 h2 hk ⊢
  have hm : (y.length : ℕ∞) ≤ KPPlain U y + (c₀ : ℕ∞) := by
    have := hc₀ y.length
    rwa [← h1] at this
  have hn : (n : ℕ∞) = (y.length : ℕ∞) + (z : ℕ∞) := by
    rw [← h2, Nat.cast_add]
  calc (n : ℕ∞) = (y.length : ℕ∞) + (z : ℕ∞) := hn
    _ ≤ (KPPlain U y + (c₀ : ℕ∞)) + (z : ℕ∞) := add_le_add hm le_rfl
    _ ≤ ((K + (c₁ : ℕ∞)) + (c₀ : ℕ∞)) + (z : ℕ∞) :=
        add_le_add (add_le_add hk le_rfl) le_rfl
    _ = K + (z : ℕ∞) + ((c₀ + c₁ : ℕ) : ℕ∞) := by
        rw [Nat.cast_add]
        ring

/-- Step 13 of the proof of `exists_isSchnorrRandom_not_isMisesChurchRandom`: Schnorr's
criterion (Problem 270, `isSchnorrRandom_iff_forall_computable_bound`): `K(w↾n) ≥ n - z n - O(1)`
with `z` eventually below every computable non-decreasing unbounded function implies Schnorr
randomness. -/
private theorem exists_isSchnorrRandom_not_isMisesChurchRandom_criterion (U : Map)
    (hU : IsOptimalPrefixConditional U) (w : CantorSeq) (z : ℕ → ℕ)
    (hbound : ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ KPPlain U (cantorPrefix w n) + (z n : ℕ∞) + (c : ℕ∞))
    (hslow : ∀ h' : ℕ → ℕ, IsComputableGrowth h' → ∃ N, ∀ n ≥ N, z n ≤ h' n) :
    IsSchnorrRandom uniformMeasure w := by
  have hpos : ∀ x, 0 < cantorMass uniformMeasure x := fun x => by
    rw [cantorMass_uniformMeasure]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by decide)) _
  refine isSchnorrRandom_iff_forall_computable_bound_rtl U hU isComputableMeasure_uniform
    hpos w ?_
  intro k hk_comp ⟨c0, hk0⟩ h' hh'
  obtain ⟨c, hc⟩ := hbound
  obtain ⟨N, hN⟩ := hslow h' hh'
  refine ⟨((c0 + c + N : ℕ) : ℝ), fun n => ?_⟩
  have mass_eq : -Real.logb 2 (massR uniformMeasure (cantorPrefix w n)) = (n : ℝ) := by
    rw [massR_uniformMeasure, cantorPrefix_length, Real.logb, Real.log_pow, Real.log_inv]
    have h1 : -(n * -Real.log 2 / Real.log 2) = n * (Real.log 2 / Real.log 2) := by ring
    rw [h1, div_self (by positivity)]
    ring
  rw [mass_eq]
  have key : ∀ m : ℕ, m ≤ k (cantorPrefix w m) + c0 + h' m + c + N := by
    intro m
    have h1 : (m : ℕ∞) ≤ ((k (cantorPrefix w m) + c0 + z m + c : ℕ) : ℕ∞) := by
      calc
        (m : ℕ∞) ≤ KPPlain U (cantorPrefix w m) + (z m : ℕ∞) + (c : ℕ∞) := hc m
        _ ≤ (k (cantorPrefix w m) + c0 : ℕ∞) + (z m : ℕ∞) + (c : ℕ∞) := by
          gcongr; exact hk0 _
        _ = ((k (cantorPrefix w m) + c0 + z m + c : ℕ) : ℕ∞) := by push_cast; rfl
    have h2 : m ≤ k (cantorPrefix w m) + c0 + z m + c := by exact_mod_cast h1
    by_cases hm : N ≤ m
    · have h3 : z m ≤ h' m := hN m hm
      omega
    · omega
  have h3 := key n
  have h4 : (n : ℝ) ≤ (k (cantorPrefix w n) : ℝ) + (c0 : ℝ) + (h' n : ℝ) + (c : ℝ) + (N : ℝ) := by
    exact_mod_cast h3
  push_cast
  linarith

/-- **SUV Problem 271, p. 284.**  There is a Schnorr random sequence, with respect to the uniform
measure, that is not Mises-Church random. -/
theorem exists_isSchnorrRandom_not_isMisesChurchRandom :
    ∃ w, IsSchnorrRandom uniformMeasure w ∧ ¬ IsMisesChurchRandom w := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨a, f, d, ha, hfp, hf⟩ :=
    exists_isSchnorrRandom_not_isMisesChurchRandom_omega U hU
  obtain ⟨T, hTc, hTs, hTcomp, hTm⟩ :=
    exists_isSchnorrRandom_not_isMisesChurchRandom_eval f hfp
  have hz := exists_isSchnorrRandom_not_isMisesChurchRandom_bp_inv U T d a f hTs hf
  refine ⟨exists_isSchnorrRandom_not_isMisesChurchRandom_seq T d a,
    exists_isSchnorrRandom_not_isMisesChurchRandom_criterion U hU _
      (fun n => (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a n).2)
      (exists_isSchnorrRandom_not_isMisesChurchRandom_complexity U hU a ha T hTc d)
      (fun h' hh' => exists_isSchnorrRandom_not_isMisesChurchRandom_slow U hU _ hz h' hh'),
    ?_⟩
  intro hmc
  have hR : IsDecidableSet (exists_isSchnorrRandom_not_isMisesChurchRandom_rule T d) :=
    ⟨fun x => exists_isSchnorrRandom_not_isMisesChurchRandom_ins T d
      (exists_isSchnorrRandom_not_isMisesChurchRandom_dec T d x) x.length,
      (exists_isSchnorrRandom_not_isMisesChurchRandom_computable T hTc d).2,
      fun x => Iff.rfl⟩
  exact exists_isSchnorrRandom_not_isMisesChurchRandom_not_freq _ _
    (fun n => (exists_isSchnorrRandom_not_isMisesChurchRandom_state T d a n).2)
    (exists_isSchnorrRandom_not_isMisesChurchRandom_selected T d a)
    (exists_isSchnorrRandom_not_isMisesChurchRandom_unbounded T d a f hTcomp hTm
      (fun n => (hf n).imp fun t ht => ht.1))
    (hmc _ hR)

/-- **SUV p. 284, after Problem 271.**  So Schnorr randomness is strictly weaker than computable
randomness. -/
theorem exists_isSchnorrRandom_not_isComputablyRandom :
    ∃ w, IsSchnorrRandom uniformMeasure w ∧ ¬ IsComputablyRandom uniformMeasure w := by
  obtain ⟨w, hw1, hw2⟩ := exists_isSchnorrRandom_not_isMisesChurchRandom
  exact ⟨w, hw1, fun h => hw2 (isMisesChurchRandom_of_isComputablyRandom h)⟩

end Kolmogorov.FrequencyGames
