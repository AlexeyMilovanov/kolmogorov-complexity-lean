/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.FrequencyGames.ComputableMartingale.RandomnessBasics

/-!
# Log Complexity Construction

For a computable probability measure `π` on Cantor space with positive cylinders, we construct a
computably random sequence all of whose prefixes have plain complexity logarithmic in their length.
The construction diagonalizes against a universal enumeration of partial computable rational
martingales, keeping a bounded budget of capital for each candidate.

The main declaration is `exists_isComputablyRandom_plainK_log`, which formalizes part (b) of
Theorem 182 in Chapter 13 of Shen, Uspensky and Vereshchagin, "Kolmogorov complexity and
algorithmic randomness".
-/

namespace Kolmogorov.FrequencyGames
open MeasureTheory Filter Topology ComputableReals

/-! ### Auxiliary development for `exists_isComputablyRandom_plainK_log` -/

/-- Runs `code` on `Encodable.encode a` and decodes the answer (undefined if it diverges or
does not decode). -/
private def exists_isComputablyRandom_plainK_log_codeEval {α β : Type} [Primcodable α]
    [Primcodable β] (code : Nat.Partrec.Code) (a : α) : Part β :=
  (code.eval (Encodable.encode a)).bind fun n => Part.ofOption (Encodable.decode (α := β) n)

/-- The universal partial oracle: `Qp (i, x, s)` is the `i`-th partial recursive function
applied to `(x, s)`, decoded as a rational. -/
private def exists_isComputablyRandom_plainK_log_Qp (p : ℕ × BitString × ℕ) : Part ℚ :=
  exists_isComputablyRandom_plainK_log_codeEval (β := ℚ)
    (Denumerable.ofNat Nat.Partrec.Code p.1) p.2

open Classical in
/-- The value of the oracle (`0` if undefined). -/
private noncomputable def exists_isComputablyRandom_plainK_log_Qv (i : ℕ) (x : BitString)
    (s : ℕ) : ℚ :=
  (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).getOrElse 0

/-- The flagged oracles `i` (`b i = true`) approximate the fair capitals `mm i`. -/
private def exists_isComputablyRandom_plainK_log_Spec (π : Measure CantorSeq) (b : ℕ → Bool)
    (mm : ℕ → BitString → ℝ) : Prop :=
  ∀ i, b i = true → IsFairCapital π (mm i) ∧
    ∀ x s, |((exists_isComputablyRandom_plainK_log_Qv i x s : ℚ) : ℝ) - mm i x| ≤ (2 : ℝ)⁻¹ ^ s

/-- The normalising exponent of an activation value `q`: `q ≤ 2 ^ shift q` for `q ≥ 0`. -/
private def exists_isComputablyRandom_plainK_log_shift (q : ℚ) : ℕ := Nat.size q.num.toNat

/-- The weight of the index `i` introduced at the string `z`: `0` if the flag is off, else
the power of two `2^{-(i + shift (Qv i z 0))}`. -/
private noncomputable def exists_isComputablyRandom_plainK_log_wt (b : ℕ → Bool) (i : ℕ)
    (z : BitString) : ℚ :=
  if b i = true then
    (1 / 2 : ℚ) ^ (i + exists_isComputablyRandom_plainK_log_shift
      (exists_isComputablyRandom_plainK_log_Qv i z 0))
  else 0

/-- The `i`-th term of the (rational) potential at `y`, precision `s`, for the current prefix `x`;
the weight of `i` is fixed at `x.take (2^i)`. -/
private noncomputable def exists_isComputablyRandom_plainK_log_term (b : ℕ → Bool)
    (x y : BitString) (s i : ℕ) : ℚ :=
  exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) *
    exists_isComputablyRandom_plainK_log_Qv i y s

/-- The rational potential: sum of the first `m` terms. -/
private noncomputable def exists_isComputablyRandom_plainK_log_pot (b : ℕ → Bool)
    (x y : BitString) (s m : ℕ) : ℚ :=
  ∑ i ∈ Finset.range m, exists_isComputablyRandom_plainK_log_term b x y s i

/-- The next bit: the child with the smaller approximate potential (ties: `false`). -/
private noncomputable def exists_isComputablyRandom_plainK_log_rule (b : ℕ → Bool)
    (x : BitString) : Bool :=
  decide (exists_isComputablyRandom_plainK_log_pot b x (x ++ [true]) (x.length + 3)
      (Nat.size x.length) <
    exists_isComputablyRandom_plainK_log_pot b x (x ++ [false]) (x.length + 3)
      (Nat.size x.length))

/-- The prefix of length `n` of the constructed sequence. -/
private noncomputable def exists_isComputablyRandom_plainK_log_state (b : ℕ → Bool) :
    ℕ → BitString
  | 0 => []
  | n + 1 => exists_isComputablyRandom_plainK_log_state b n ++
      [exists_isComputablyRandom_plainK_log_rule b (exists_isComputablyRandom_plainK_log_state b n)]

/-- The constructed sequence. -/
private noncomputable def exists_isComputablyRandom_plainK_log_seq (b : ℕ → Bool) : CantorSeq :=
  fun n => exists_isComputablyRandom_plainK_log_rule b
    (exists_isComputablyRandom_plainK_log_state b n)

/-- The real potential (a fair capital in `y`): the weights are fixed at `x.take (2^i)`. -/
private noncomputable def exists_isComputablyRandom_plainK_log_Phi (b : ℕ → Bool)
    (mm : ℕ → BitString → ℝ) (x y : BitString) : ℝ :=
  ∑ i ∈ Finset.range (Nat.size x.length),
    ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y

/-- The total weighted capital along the sequence. -/
private noncomputable def exists_isComputablyRandom_plainK_log_S (b : ℕ → Bool)
    (mm : ℕ → BitString → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Nat.size n),
    ((exists_isComputablyRandom_plainK_log_wt b i
      ((exists_isComputablyRandom_plainK_log_state b n).take (2 ^ i)) : ℚ) : ℝ) *
      mm i (exists_isComputablyRandom_plainK_log_state b n)

/-- The `i`-th term of the potential, computed from the advice `adv`: `0` if the advice does not
flag `i`, else the weight (fixed at `x.take (2^i)`) times the oracle value at `y`. -/
private def exists_isComputablyRandom_plainK_log_sim_term (adv : List Bool) (x y : BitString)
    (s i : ℕ) : Part ℚ :=
  cond (adv.getD i false)
    ((exists_isComputablyRandom_plainK_log_Qp (i, x.take (2 ^ i), 0)).bind fun q0 =>
      (exists_isComputablyRandom_plainK_log_Qp (i, y, s)).map fun qy =>
        (1 / 2 : ℚ) ^ (i + exists_isComputablyRandom_plainK_log_shift q0) * qy)
    (Part.some 0)

/-- The potential (sum of the first `m` terms), computed in the `Part` monad. -/
private def exists_isComputablyRandom_plainK_log_sim_pot (adv : List Bool) (x y : BitString)
    (s m : ℕ) : Part ℚ :=
  Nat.rec (Part.some 0)
    (fun i IH => IH.bind fun acc =>
      (exists_isComputablyRandom_plainK_log_sim_term adv x y s i).map fun t => acc + t) m

/-- The next bit, computed in the `Part` monad. -/
private def exists_isComputablyRandom_plainK_log_sim_bit (adv : List Bool) (x : BitString) :
    Part Bool :=
  (exists_isComputablyRandom_plainK_log_sim_pot adv x (x ++ [true]) (x.length + 3)
      (Nat.size x.length)).bind fun a1 =>
    (exists_isComputablyRandom_plainK_log_sim_pot adv x (x ++ [false]) (x.length + 3)
      (Nat.size x.length)).map fun a0 => decide (a1 < a0)

/-- The prefix of length `n`, computed in the `Part` monad. -/
private def exists_isComputablyRandom_plainK_log_sim_iter (adv : List Bool) (n : ℕ) :
    Part BitString :=
  Nat.rec (Part.some ([] : BitString))
    (fun _ IH => IH.bind fun x =>
      (exists_isComputablyRandom_plainK_log_sim_bit adv x).map fun bt => x ++ [bt]) n

/-- The program: decode `n` and the advice from the input, run the construction. -/
private def exists_isComputablyRandom_plainK_log_sim_prog (a : BitString) : Part BitString :=
  exists_isComputablyRandom_plainK_log_sim_iter (decodeSecond a)
    (bitStringToNat (decodeFirst a))

/-- (A aux) The generic partial oracle is partial recursive, jointly in the code and the input. -/
private lemma exists_isComputablyRandom_plainK_log_Aaux_codeEval_partrec {α β : Type}
    [Primcodable α] [Primcodable β] :
    Partrec fun x : Nat.Partrec.Code × α =>
      exists_isComputablyRandom_plainK_log_codeEval (β := β) x.1 x.2 := by
  have heval : Partrec fun x : Nat.Partrec.Code × α => x.1.eval (Encodable.encode x.2) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst
      (Computable.encode.comp Computable.snd)
  have hdec : Partrec fun x : (Nat.Partrec.Code × α) × ℕ =>
      Part.ofOption (Encodable.decode (α := β) x.2) :=
    Computable.ofOption (Computable.decode.comp Computable.snd)
  exact heval.bind hdec.to₂

/-- The oracle is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_Qp_partrec :
    Partrec exists_isComputablyRandom_plainK_log_Qp := by
  have hcode : Computable
      (fun p : ℕ × BitString × ℕ => Denumerable.ofNat Nat.Partrec.Code p.1) :=
    (Primrec.ofNat Nat.Partrec.Code).to_comp.comp Computable.fst
  have h := (exists_isComputablyRandom_plainK_log_Aaux_codeEval_partrec
    (α := BitString × ℕ) (β := ℚ)).comp (hcode.pair Computable.snd)
  exact h

/-- (A aux) Every computable function has a code (generic in the primcodable types). -/
private lemma exists_isComputablyRandom_plainK_log_Aaux_exists_code {α σ : Type}
    [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code,
      ∀ a : α, c.eval (Encodable.encode a) = Part.some (Encodable.encode (f a)) := by
  have hnat : Nat.Partrec fun n => Part.bind (Encodable.decode (α := α) n) fun a =>
      Part.map Encodable.encode (Part.some (f a)) := hf
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hnat
  refine ⟨c, fun a => ?_⟩
  rw [show c.eval = _ from hc]
  simp

/-- (A aux) On a code that really computes `f`, the generic oracle converges to `f a`. -/
private lemma exists_isComputablyRandom_plainK_log_Aaux_codeEval_of_code {α β : Type}
    [Primcodable α] [Primcodable β] {c : Nat.Partrec.Code} {f : α → β}
    (h : ∀ a : α, c.eval (Encodable.encode a) = Part.some (Encodable.encode (f a))) (a : α) :
    exists_isComputablyRandom_plainK_log_codeEval (β := β) c a = Part.some (f a) := by
  simp [exists_isComputablyRandom_plainK_log_codeEval, h a, Encodable.encodek]

/-- Every computable real function on strings is approximated by some oracle `i`. -/
private lemma exists_isComputablyRandom_plainK_log_enum :
    ∀ m : BitString → ℝ, IsComputableOnStrings m →
      ∃ i : ℕ, ∀ x s, ∃ q ∈ exists_isComputablyRandom_plainK_log_Qp (i, x, s),
        |(q : ℝ) - m x| ≤ (2 : ℝ)⁻¹ ^ s := by
  intro m hm
  obtain ⟨q, hq, hbound⟩ := hm
  obtain ⟨c, hc⟩ := exists_isComputablyRandom_plainK_log_Aaux_exists_code hq
  refine ⟨Encodable.encode c, fun x s => ⟨q (x, s), ?_, hbound x s⟩⟩
  have h2 : exists_isComputablyRandom_plainK_log_codeEval (β := ℚ) c (x, s) =
      Part.some (q (x, s)) :=
    exists_isComputablyRandom_plainK_log_Aaux_codeEval_of_code hc (x, s)
  have h3 : exists_isComputablyRandom_plainK_log_Qp (Encodable.encode c, x, s) =
      Part.some (q (x, s)) := by
    unfold exists_isComputablyRandom_plainK_log_Qp
    simp only [Denumerable.ofNat_encode]
    exact h2
  rw [h3]
  exact Part.mem_some _

/-- Where the oracle is defined it equals `Qv`. -/
private lemma exists_isComputablyRandom_plainK_log_Qv_spec (i : ℕ) (x : BitString) (s : ℕ)
    (h : (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) :
    exists_isComputablyRandom_plainK_log_Qp (i, x, s) =
      Part.some (exists_isComputablyRandom_plainK_log_Qv i x s) := by
  classical
  have hq : exists_isComputablyRandom_plainK_log_Qv i x s =
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).get h := by
    unfold exists_isComputablyRandom_plainK_log_Qv
    exact Part.getOrElse_of_dom _ h 0
  rw [hq]
  exact Part.eq_some_iff.mpr (Part.get_mem h)

/-- (A aux) The oracle `i` is good for `π`: it approximates a fair capital. -/
private def exists_isComputablyRandom_plainK_log_Aaux_Good (π : Measure CantorSeq) (i : ℕ) :
    Prop :=
  ∃ m : BitString → ℝ, IsFairCapital π m ∧
    ∀ x s, ∃ q ∈ exists_isComputablyRandom_plainK_log_Qp (i, x, s),
      |(q : ℝ) - m x| ≤ (2 : ℝ)⁻¹ ^ s

/-- (A aux) Two reals with `|u - v| ≤ 2 * 2⁻ˢ` for all `s` are equal. -/
private lemma exists_isComputablyRandom_plainK_log_Aaux_eq_of_forall (u v : ℝ)
    (h : ∀ s : ℕ, |u - v| ≤ 2 * (2 : ℝ)⁻¹ ^ s) : u = v := by
  by_contra hne
  have hpos : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (half_pos hpos) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have := h s
  linarith

/-- Correct flags exist, and they cover every computable fair capital. -/
private lemma exists_isComputablyRandom_plainK_log_flags (π : Measure CantorSeq) :
    ∃ (b : ℕ → Bool) (mm : ℕ → BitString → ℝ),
      (∀ i, b i = true → ∀ x s, (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) ∧
      exists_isComputablyRandom_plainK_log_Spec π b mm ∧
      ∀ m, IsFairCapital π m → IsComputableOnStrings m → ∃ i, b i = true ∧ mm i = m := by
  classical
  let b : ℕ → Bool := fun i => decide (exists_isComputablyRandom_plainK_log_Aaux_Good π i)
  let mm : ℕ → BitString → ℝ := fun i =>
    if h : exists_isComputablyRandom_plainK_log_Aaux_Good π i then h.choose else fun _ => 0
  have hb : ∀ i, b i = true ↔ exists_isComputablyRandom_plainK_log_Aaux_Good π i := fun i => by
    simp [b]
  have hmm : ∀ i, exists_isComputablyRandom_plainK_log_Aaux_Good π i →
      IsFairCapital π (mm i) ∧ ∀ x s, ∃ q ∈ exists_isComputablyRandom_plainK_log_Qp (i, x, s),
        |(q : ℝ) - mm i x| ≤ (2 : ℝ)⁻¹ ^ s := by
    intro i hi
    have h : mm i = hi.choose := by
      simp [mm, hi]
    rw [h]
    exact hi.choose_spec
  have hdom : ∀ i, exists_isComputablyRandom_plainK_log_Aaux_Good π i →
      ∀ x s, (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom := by
    intro i hi x s
    obtain ⟨q, hq, _⟩ := (hmm i hi).2 x s
    exact Part.dom_iff_mem.mpr ⟨q, hq⟩
  refine ⟨b, mm, fun i hi => hdom i ((hb i).mp hi), ?_, ?_⟩
  · intro i hi
    have hgi := (hb i).mp hi
    refine ⟨(hmm i hgi).1, fun x s => ?_⟩
    obtain ⟨q, hq, hqb⟩ := (hmm i hgi).2 x s
    have hd := hdom i hgi x s
    have hqv : q = exists_isComputablyRandom_plainK_log_Qv i x s := by
      have h1 := exists_isComputablyRandom_plainK_log_Qv_spec i x s hd
      rw [h1] at hq
      exact Part.mem_some_iff.mp hq
    rw [← hqv]
    exact hqb
  · intro m hm hc
    obtain ⟨i, hi⟩ := exists_isComputablyRandom_plainK_log_enum m hc
    have hgi : exists_isComputablyRandom_plainK_log_Aaux_Good π i := ⟨m, hm, hi⟩
    refine ⟨i, (hb i).mpr hgi, ?_⟩
    funext x
    refine exists_isComputablyRandom_plainK_log_Aaux_eq_of_forall _ _ (fun s => ?_)
    obtain ⟨q1, hq1, hb1⟩ := (hmm i hgi).2 x s
    obtain ⟨q2, hq2, hb2⟩ := hi x s
    have hq : q1 = q2 := Part.mem_unique hq1 hq2
    subst hq
    have h3 := abs_sub_le (mm i x) (q1 : ℝ) (m x)
    rw [abs_sub_comm (mm i x) (q1 : ℝ)] at h3
    linarith

/-! ### Pure facts -/

/-- `state b n` is the prefix of length `n` of `seq b`, and has length `n`. -/
private lemma exists_isComputablyRandom_plainK_log_state_prefix (b : ℕ → Bool) (n : ℕ) :
    cantorPrefix (exists_isComputablyRandom_plainK_log_seq b) n =
      exists_isComputablyRandom_plainK_log_state b n := by
  induction n with
  | zero => simp [cantorPrefix, exists_isComputablyRandom_plainK_log_state]
  | succ n ih =>
    rw [cantorPrefix_succ, ih]
    rfl

private lemma exists_isComputablyRandom_plainK_log_state_length (b : ℕ → Bool) (n : ℕ) :
    (exists_isComputablyRandom_plainK_log_state b n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (exists_isComputablyRandom_plainK_log_state b n ++
      [exists_isComputablyRandom_plainK_log_rule b
        (exists_isComputablyRandom_plainK_log_state b n)]).length = n + 1
    rw [List.length_append, ih]
    rfl

/-- A prefix of a state is a state. -/
private lemma exists_isComputablyRandom_plainK_log_state_take (b : ℕ → Bool) {m n : ℕ}
    (h : m ≤ n) :
    (exists_isComputablyRandom_plainK_log_state b n).take m =
      exists_isComputablyRandom_plainK_log_state b m := by
  induction n, h using Nat.le_induction with
  | base =>
    exact List.take_of_length_le
      (le_of_eq (exists_isComputablyRandom_plainK_log_state_length b m))
  | succ n hmn ih =>
    change (exists_isComputablyRandom_plainK_log_state b n ++
      [exists_isComputablyRandom_plainK_log_rule b
        (exists_isComputablyRandom_plainK_log_state b n)]).take m =
      exists_isComputablyRandom_plainK_log_state b m
    rw [List.take_append_of_le_length
      (by rw [exists_isComputablyRandom_plainK_log_state_length]; exact hmn), ih]

/-- Weights are nonnegative. -/
private lemma exists_isComputablyRandom_plainK_log_wt_nonneg (b : ℕ → Bool) (i : ℕ)
    (z : BitString) : 0 ≤ exists_isComputablyRandom_plainK_log_wt b i z := by
  unfold exists_isComputablyRandom_plainK_log_wt
  split_ifs
  · positivity
  · exact le_refl _

/-- Weights are at most `2^{-i}`. -/
private lemma exists_isComputablyRandom_plainK_log_wt_le (b : ℕ → Bool) (i : ℕ)
    (z : BitString) : exists_isComputablyRandom_plainK_log_wt b i z ≤ (1 / 2 : ℚ) ^ i := by
  unfold exists_isComputablyRandom_plainK_log_wt
  split_ifs
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
  · positivity

/-- Flagged weights are positive. -/
private lemma exists_isComputablyRandom_plainK_log_wt_pos (b : ℕ → Bool) (i : ℕ)
    (z : BitString) (h : b i = true) : 0 < exists_isComputablyRandom_plainK_log_wt b i z := by
  simp only [exists_isComputablyRandom_plainK_log_wt, h, ↓reduceIte]
  positivity

/-- (B1 aux) `q + 1 ≤ 2 ^ shift q`, for every rational `q`. -/
private lemma exists_isComputablyRandom_plainK_log_B1aux_shift_bound (q : ℚ) :
    q + 1 ≤ (2 : ℚ) ^ exists_isComputablyRandom_plainK_log_shift q := by
  unfold exists_isComputablyRandom_plainK_log_shift
  by_cases hq : 0 ≤ q
  · have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have h1 : q ≤ (q.num : ℚ) := by
      have hden : (1 : ℚ) ≤ q.den := by exact_mod_cast Rat.den_pos q
      calc q = q * 1 := by ring
        _ ≤ q * q.den := mul_le_mul_of_nonneg_left hden hq
        _ = q.num := Rat.mul_den_eq_num q
    have h2 : (q.num : ℚ) = ((q.num.toNat : ℕ) : ℚ) := by
      have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum
      exact_mod_cast this.symm
    have h3 : q.num.toNat < 2 ^ Nat.size q.num.toNat := Nat.lt_size_self _
    have h4 : q.num.toNat + 1 ≤ 2 ^ Nat.size q.num.toNat := h3
    have h5 : ((q.num.toNat + 1 : ℕ) : ℚ) ≤ ((2 ^ Nat.size q.num.toNat : ℕ) : ℚ) := by
      exact_mod_cast h4
    push_cast at h5
    linarith
  · have hq' : q < 0 := not_le.mp hq
    have h6 : (1 : ℚ) ≤ 2 ^ Nat.size q.num.toNat := one_le_pow₀ (by norm_num)
    linarith

/-- The activation bound: `wt_i(z) * m_i(z) ≤ 2^{-i}`. -/
private lemma exists_isComputablyRandom_plainK_log_wt_mul_le {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (i : ℕ) (z : BitString) :
    ((exists_isComputablyRandom_plainK_log_wt b i z : ℚ) : ℝ) * mm i z ≤ (2 : ℝ)⁻¹ ^ i := by
  by_cases hb : b i = true
  · obtain ⟨_, happrox⟩ := hS i hb
    have h0 := happrox z 0
    have hmm : mm i z ≤ ((exists_isComputablyRandom_plainK_log_Qv i z 0 : ℚ) : ℝ) + 1 := by
      have := (abs_le.mp h0).1
      simp only [pow_zero] at this
      linarith
    have hshift : ((exists_isComputablyRandom_plainK_log_Qv i z 0 : ℚ) : ℝ) + 1 ≤
        (2 : ℝ) ^ exists_isComputablyRandom_plainK_log_shift
          (exists_isComputablyRandom_plainK_log_Qv i z 0) := by
      exact_mod_cast exists_isComputablyRandom_plainK_log_B1aux_shift_bound
        (exists_isComputablyRandom_plainK_log_Qv i z 0)
    set t := exists_isComputablyRandom_plainK_log_shift
      (exists_isComputablyRandom_plainK_log_Qv i z 0) with ht
    have hwt : ((exists_isComputablyRandom_plainK_log_wt b i z : ℚ) : ℝ) =
        (2 : ℝ)⁻¹ ^ (i + t) := by
      simp only [exists_isComputablyRandom_plainK_log_wt, hb, ↓reduceIte]
      push_cast
      simp [ht]
    rw [hwt]
    have hpos : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (i + t) := by positivity
    calc (2 : ℝ)⁻¹ ^ (i + t) * mm i z ≤ (2 : ℝ)⁻¹ ^ (i + t) * 2 ^ t :=
          mul_le_mul_of_nonneg_left (hmm.trans hshift) hpos
      _ = (2 : ℝ)⁻¹ ^ i := by
          rw [pow_add, mul_assoc, ← mul_pow]
          norm_num
  · have hb' : b i = false := by simpa using hb
    have hwt : exists_isComputablyRandom_plainK_log_wt b i z = 0 := by
      simp [exists_isComputablyRandom_plainK_log_wt, hb']
    rw [hwt]
    simp

/-- Finite nonnegative combinations of fair capitals are fair capitals. -/
private lemma exists_isComputablyRandom_plainK_log_comb {π : Measure CantorSeq}
    (s : Finset ℕ) (a : ℕ → ℝ) (mm : ℕ → BitString → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hm : ∀ i ∈ s, IsFairCapital π (mm i)) :
    IsFairCapital π (fun y => ∑ i ∈ s, a i * mm i y) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) ((hm i hi).nonneg x)
  · show (∑ i ∈ s, a i * mm i x) * massR π x =
      (∑ i ∈ s, a i * mm i (x ++ [false])) * massR π (x ++ [false]) +
        (∑ i ∈ s, a i * mm i (x ++ [true])) * massR π (x ++ [true])
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := (hm i hi).fair x
    calc a i * mm i x * massR π x = a i * (mm i x * massR π x) := by ring
      _ = a i * (mm i (x ++ [false]) * massR π (x ++ [false]) +
            mm i (x ++ [true]) * massR π (x ++ [true])) := by rw [h]
      _ = a i * mm i (x ++ [false]) * massR π (x ++ [false]) +
            a i * mm i (x ++ [true]) * massR π (x ++ [true]) := by ring

/-- One greedy step: the child with the smaller approximation is at most `2δ` above the parent. -/
private lemma exists_isComputablyRandom_plainK_log_pick {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hpos : ∀ x, 0 < cantorMass π x) {Φ : BitString → ℝ}
    (hΦ : IsFairCapital π Φ) (A : BitString → ℚ) (x : BitString) (δ : ℝ)
    (hA : ∀ c : Bool, |((A (x ++ [c]) : ℚ) : ℝ) - Φ (x ++ [c])| ≤ δ) :
    Φ (x ++ [decide (A (x ++ [true]) < A (x ++ [false]))]) ≤ Φ x + 2 * δ := by
  have hx : 0 < massR π x := by
    unfold massR
    exact ENNReal.toReal_pos (hpos x).ne' (measure_ne_top π _)
  obtain ⟨c', -, hc'⟩ := exists_child_le hΦ.isSuperfairCapital hx
  -- the chosen child minimises `A`
  have hmin : ∀ c : Bool, A (x ++ [decide (A (x ++ [true]) < A (x ++ [false]))]) ≤ A (x ++ [c]) :=
      by
    intro c
    by_cases h : A (x ++ [true]) < A (x ++ [false])
    · rw [decide_eq_true h]
      cases c
      · exact h.le
      · exact le_rfl
    · rw [decide_eq_false h]
      cases c
      · exact le_rfl
      · exact not_lt.mp h
  set cs : Bool := decide (A (x ++ [true]) < A (x ++ [false])) with hcs
  have h1 := abs_le.mp (hA cs)
  have h2 := abs_le.mp (hA c')
  have h3 : ((A (x ++ [cs]) : ℚ) : ℝ) ≤ ((A (x ++ [c']) : ℚ) : ℝ) := by
    exact_mod_cast hmin c'
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The rational potential approximates the real one. -/
private lemma exists_isComputablyRandom_plainK_log_pot_err {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (x y : BitString) :
    |((exists_isComputablyRandom_plainK_log_pot b x y (x.length + 3) (Nat.size x.length) : ℚ) : ℝ)
        - exists_isComputablyRandom_plainK_log_Phi b mm x y| ≤ (2 : ℝ)⁻¹ ^ (x.length + 2) := by
  have hterm : ∀ i ∈ Finset.range (Nat.size x.length),
      |((exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i : ℚ) : ℝ)
        - ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y|
        ≤ (2 : ℝ)⁻¹ ^ i * (2 : ℝ)⁻¹ ^ (x.length + 3) := by
    intro i _
    by_cases hbi : b i = true
    · have hw0 : (0 : ℝ) ≤ ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ)
        := by
        exact_mod_cast exists_isComputablyRandom_plainK_log_wt_nonneg b i (x.take (2 ^ i))
      have hw1 : ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ)
          ≤ (2 : ℝ)⁻¹ ^ i := by
        have h := exists_isComputablyRandom_plainK_log_wt_le b i (x.take (2 ^ i))
        have h' : ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ)
            ≤ (((1 / 2 : ℚ) ^ i : ℚ) : ℝ) := by exact_mod_cast h
        have h'' : (((1 / 2 : ℚ) ^ i : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ i := by push_cast; norm_num
        rw [h''] at h'
        exact h'
      have hspec := (hS i hbi).2 y (x.length + 3)
      have hc : ((exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i : ℚ) : ℝ)
          = ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) *
            ((exists_isComputablyRandom_plainK_log_Qv i y (x.length + 3) : ℚ) : ℝ) := by
        unfold exists_isComputablyRandom_plainK_log_term
        push_cast
        rfl
      rw [hc, ← mul_sub, abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul hw1 hspec (abs_nonneg _) (by positivity)
    · have hw : exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) = 0 := by
        unfold exists_isComputablyRandom_plainK_log_wt
        simp [hbi]
      have hc : exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i = 0 := by
        unfold exists_isComputablyRandom_plainK_log_term
        rw [hw, zero_mul]
      rw [hc, hw]
      simp only [Rat.cast_zero, zero_mul, sub_zero, abs_zero]
      positivity
  have hdiff : ((exists_isComputablyRandom_plainK_log_pot b x y (x.length + 3)
      (Nat.size x.length) : ℚ) : ℝ) - exists_isComputablyRandom_plainK_log_Phi b mm x y =
      ∑ i ∈ Finset.range (Nat.size x.length),
        (((exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i : ℚ) : ℝ)
          - ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y) := by
    rw [exists_isComputablyRandom_plainK_log_pot, Rat.cast_sum,
      exists_isComputablyRandom_plainK_log_Phi, Finset.sum_sub_distrib]
  have hgeom : ∑ i ∈ Finset.range (Nat.size x.length), (2 : ℝ)⁻¹ ^ i ≤ 2 := by
    simpa [one_div] using sum_geometric_two_le (Nat.size x.length)
  have h2 : (2 : ℝ) * (2 : ℝ)⁻¹ ^ (x.length + 3) = (2 : ℝ)⁻¹ ^ (x.length + 2) := by
    have h : (2 : ℝ)⁻¹ ^ (x.length + 3) = (2 : ℝ)⁻¹ ^ (x.length + 2) * (2 : ℝ)⁻¹ := pow_succ _ _
    rw [h]
    field_simp
  rw [hdiff]
  calc |∑ i ∈ Finset.range (Nat.size x.length),
        (((exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i : ℚ) : ℝ)
          - ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y)|
      ≤ ∑ i ∈ Finset.range (Nat.size x.length),
        |(((exists_isComputablyRandom_plainK_log_term b x y (x.length + 3) i : ℚ) : ℝ)
          - ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (Nat.size x.length), (2 : ℝ)⁻¹ ^ i * (2 : ℝ)⁻¹ ^ (x.length + 3) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (Nat.size x.length), (2 : ℝ)⁻¹ ^ i) * (2 : ℝ)⁻¹ ^ (x.length + 3) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * (2 : ℝ)⁻¹ ^ (x.length + 3) :=
        mul_le_mul_of_nonneg_right hgeom (by positivity)
    _ = (2 : ℝ)⁻¹ ^ (x.length + 2) := h2

/-- The real potential is a fair capital. -/
private lemma exists_isComputablyRandom_plainK_log_Phi_fair {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (x : BitString) :
    IsFairCapital π (exists_isComputablyRandom_plainK_log_Phi b mm x) := by
  classical
  have hcomb := exists_isComputablyRandom_plainK_log_comb (π := π)
    ((Finset.range (Nat.size x.length)).filter (fun i => b i = true))
    (fun i => ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ)) mm
    (fun i _ => by
      exact_mod_cast exists_isComputablyRandom_plainK_log_wt_nonneg b i (x.take (2 ^ i)))
    (fun i hi => (hS i (Finset.mem_filter.mp hi).2).1)
  have heq : exists_isComputablyRandom_plainK_log_Phi b mm x =
      fun y => ∑ i ∈ (Finset.range (Nat.size x.length)).filter (fun i => b i = true),
        ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) * mm i y := by
    funext y
    unfold exists_isComputablyRandom_plainK_log_Phi
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hbi : b i = true
    · simp [hbi]
    · have hw : exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) = 0 := by
        unfold exists_isComputablyRandom_plainK_log_wt
        simp [hbi]
      simp [hbi, hw]
  rw [heq]
  exact hcomb

/-- The rule step: the real potential rises by at most `2^{-(|x|+1)}`. -/
private lemma exists_isComputablyRandom_plainK_log_rule_step {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hpos : ∀ x, 0 < cantorMass π x)
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (x : BitString) :
    exists_isComputablyRandom_plainK_log_Phi b mm x
        (x ++ [exists_isComputablyRandom_plainK_log_rule b x]) ≤
      exists_isComputablyRandom_plainK_log_Phi b mm x x + (2 : ℝ)⁻¹ ^ (x.length + 1) := by
  have hpick := exists_isComputablyRandom_plainK_log_pick hpos
    (exists_isComputablyRandom_plainK_log_Phi_fair hS x)
    (fun y => exists_isComputablyRandom_plainK_log_pot b x y (x.length + 3) (Nat.size x.length))
    x ((2 : ℝ)⁻¹ ^ (x.length + 2))
    (fun c => exists_isComputablyRandom_plainK_log_pot_err hS x (x ++ [c]))
  have h2 : 2 * (2 : ℝ)⁻¹ ^ (x.length + 2) = (2 : ℝ)⁻¹ ^ (x.length + 1) := by
    have h : (2 : ℝ)⁻¹ ^ (x.length + 2) = (2 : ℝ)⁻¹ ^ (x.length + 1) * (2 : ℝ)⁻¹ := pow_succ _ _
    rw [h]
    field_simp
  rw [h2] at hpick
  exact hpick

/-- (D aux) `Nat.size (n + 1)` is `Nat.size n` or `Nat.size n + 1`, and in the latter case
`n + 1 = 2 ^ Nat.size n`. -/
private lemma exists_isComputablyRandom_plainK_log_Daux_size_succ (n : ℕ) :
    Nat.size (n + 1) = Nat.size n ∨
      (Nat.size (n + 1) = Nat.size n + 1 ∧ n + 1 = 2 ^ Nat.size n) := by
  have h1 : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (Nat.le_succ n)
  have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
  have h3 : Nat.size (n + 1) ≤ Nat.size n + 1 := by
    rw [Nat.size_le]
    calc n + 1 ≤ 2 ^ Nat.size n := h2
      _ < 2 ^ (Nat.size n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases h : Nat.size (n + 1) = Nat.size n
  · exact Or.inl h
  · right
    have h4 : Nat.size (n + 1) = Nat.size n + 1 := by omega
    refine ⟨h4, ?_⟩
    have h5 : Nat.size n < Nat.size (n + 1) := by omega
    have h6 : 2 ^ Nat.size n ≤ n + 1 := Nat.lt_size.mp h5
    omega

/-- (D aux) One step of the drift, for an arbitrary string `x` of length `n`. -/
private lemma exists_isComputablyRandom_plainK_log_Daux_succ_sum {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (x : BitString) (c : Bool) (n : ℕ)
    (hn : x.length = n) :
    ∑ i ∈ Finset.range (Nat.size (n + 1)),
        ((exists_isComputablyRandom_plainK_log_wt b i ((x ++ [c]).take (2 ^ i)) : ℚ) : ℝ) *
          mm i (x ++ [c]) ≤
      exists_isComputablyRandom_plainK_log_Phi b mm x (x ++ [c]) +
        (if Nat.size (n + 1) = Nat.size n + 1 then (2 : ℝ)⁻¹ ^ Nat.size n else 0) := by
  subst hn
  have hcongr : ∀ i ∈ Finset.range (Nat.size x.length),
      ((exists_isComputablyRandom_plainK_log_wt b i ((x ++ [c]).take (2 ^ i)) : ℚ) : ℝ) *
          mm i (x ++ [c]) =
        ((exists_isComputablyRandom_plainK_log_wt b i (x.take (2 ^ i)) : ℚ) : ℝ) *
          mm i (x ++ [c]) := by
    intro i hi
    have hi' : i < Nat.size x.length := Finset.mem_range.mp hi
    have h2 : 2 ^ i ≤ x.length := Nat.lt_size.mp hi'
    rw [List.take_append_of_le_length h2]
  have hPhi : exists_isComputablyRandom_plainK_log_Phi b mm x (x ++ [c]) =
      ∑ i ∈ Finset.range (Nat.size x.length),
        ((exists_isComputablyRandom_plainK_log_wt b i ((x ++ [c]).take (2 ^ i)) : ℚ) : ℝ) *
          mm i (x ++ [c]) := by
    unfold exists_isComputablyRandom_plainK_log_Phi
    exact (Finset.sum_congr rfl hcongr).symm
  rcases exists_isComputablyRandom_plainK_log_Daux_size_succ x.length with h | ⟨h, hpow⟩
  · rw [h, hPhi]
    simp
  · have hif : (if Nat.size x.length + 1 = Nat.size x.length + 1 then
        (2 : ℝ)⁻¹ ^ Nat.size x.length else 0) = (2 : ℝ)⁻¹ ^ Nat.size x.length := by
      simp
    rw [h, Finset.sum_range_succ, hPhi, hif]
    have hlen : (x ++ [c]).length ≤ 2 ^ Nat.size x.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have htake : (x ++ [c]).take (2 ^ Nat.size x.length) = x ++ [c] :=
      List.take_of_length_le hlen
    rw [htake]
    have hnew := exists_isComputablyRandom_plainK_log_wt_mul_le hS (Nat.size x.length) (x ++ [c])
    linarith

/-- The drift of the total weighted capital along the sequence. -/
private lemma exists_isComputablyRandom_plainK_log_drift {π : Measure CantorSeq}
    [IsProbabilityMeasure π] (hpos : ∀ x, 0 < cantorMass π x)
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (n : ℕ) :
    exists_isComputablyRandom_plainK_log_S b mm (n + 1) ≤
      exists_isComputablyRandom_plainK_log_S b mm n + (2 : ℝ)⁻¹ ^ (n + 1) +
        (if Nat.size (n + 1) = Nat.size n + 1 then (2 : ℝ)⁻¹ ^ Nat.size n else 0) := by
  have hxlen := exists_isComputablyRandom_plainK_log_state_length b n
  have hrule := exists_isComputablyRandom_plainK_log_rule_step hpos hS
    (exists_isComputablyRandom_plainK_log_state b n)
  rw [hxlen] at hrule
  have hstep := exists_isComputablyRandom_plainK_log_Daux_succ_sum hS
    (exists_isComputablyRandom_plainK_log_state b n)
    (exists_isComputablyRandom_plainK_log_rule b (exists_isComputablyRandom_plainK_log_state b n))
    n hxlen
  have hS0 : exists_isComputablyRandom_plainK_log_S b mm n =
      exists_isComputablyRandom_plainK_log_Phi b mm (exists_isComputablyRandom_plainK_log_state b n)
        (exists_isComputablyRandom_plainK_log_state b n) := by
    unfold exists_isComputablyRandom_plainK_log_S exists_isComputablyRandom_plainK_log_Phi
    rw [hxlen]
  have hS1 : exists_isComputablyRandom_plainK_log_S b mm (n + 1) =
      ∑ i ∈ Finset.range (Nat.size (n + 1)),
        ((exists_isComputablyRandom_plainK_log_wt b i
          ((exists_isComputablyRandom_plainK_log_state b n ++
            [exists_isComputablyRandom_plainK_log_rule b
              (exists_isComputablyRandom_plainK_log_state b n)]).take (2 ^ i)) : ℚ) : ℝ) *
          mm i (exists_isComputablyRandom_plainK_log_state b n ++
            [exists_isComputablyRandom_plainK_log_rule b
              (exists_isComputablyRandom_plainK_log_state b n)]) := rfl
  rw [hS1, hS0]
  linarith

/-- The initial value of the total weighted capital. -/
private lemma exists_isComputablyRandom_plainK_log_S_zero (b : ℕ → Bool)
    (mm : ℕ → BitString → ℝ) : exists_isComputablyRandom_plainK_log_S b mm 0 = 0 := by
  unfold exists_isComputablyRandom_plainK_log_S
  simp

/-- The abstract budget: a sequence starting at `0` with these increments stays below `3`. -/
private lemma exists_isComputablyRandom_plainK_log_budget (S : ℕ → ℝ) (hS0 : S 0 = 0)
    (hS : ∀ n, S (n + 1) ≤ S n + (2 : ℝ)⁻¹ ^ (n + 1) +
      (if Nat.size (n + 1) = Nat.size n + 1 then (2 : ℝ)⁻¹ ^ Nat.size n else 0)) :
    ∀ n, S n ≤ 3 := by
  have key : ∀ n, S n + (2 : ℝ)⁻¹ ^ n + 2 * (2 : ℝ)⁻¹ ^ Nat.size n ≤ 3 := by
    intro n
    induction n with
    | zero => simp [hS0]; norm_num
    | succ n ih =>
      have h1 := hS n
      have hmono : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (Nat.le_succ n)
      have h2 : (2 : ℝ)⁻¹ ^ (n + 1) = (2 : ℝ)⁻¹ ^ n / 2 := by
        rw [pow_succ]; ring
      by_cases hc : Nat.size (n + 1) = Nat.size n + 1
      · rw [ite_eq_left hc] at h1
        rw [hc]
        have h3 : (2 : ℝ)⁻¹ ^ (Nat.size n + 1) = (2 : ℝ)⁻¹ ^ Nat.size n / 2 := by
          rw [pow_succ]; ring
        rw [h3]
        rw [h2] at h1 ⊢
        linarith
      · rw [ite_eq_right hc] at h1
        have h3 : (2 : ℝ)⁻¹ ^ Nat.size (n + 1) ≤ (2 : ℝ)⁻¹ ^ Nat.size n :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) hmono
        rw [h2] at h1 ⊢
        linarith
  intro n
  have h1 := key n
  have h2 : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have h3 : 0 ≤ (2 : ℝ)⁻¹ ^ Nat.size n := by positivity
  linarith

/-- Every term of the total weighted capital is nonnegative (unflagged terms vanish). -/
private lemma exists_isComputablyRandom_plainK_log_Eaux_term_nonneg {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm) (j : ℕ) (z y : BitString) :
    0 ≤ ((exists_isComputablyRandom_plainK_log_wt b j z : ℚ) : ℝ) * mm j y := by
  by_cases hj : b j = true
  · exact mul_nonneg (by exact_mod_cast exists_isComputablyRandom_plainK_log_wt_nonneg b j z)
      ((hS j hj).1.nonneg y)
  · have h0 : exists_isComputablyRandom_plainK_log_wt b j z = 0 := by
      simp [exists_isComputablyRandom_plainK_log_wt, hj]
    rw [h0]
    simp

/-- Every flagged capital is bounded along the sequence, hence no computable fair capital wins. -/
private lemma exists_isComputablyRandom_plainK_log_bounded {π : Measure CantorSeq}
    {b : ℕ → Bool} {mm : ℕ → BitString → ℝ}
    (hS : exists_isComputablyRandom_plainK_log_Spec π b mm)
    (hSle : ∀ n, exists_isComputablyRandom_plainK_log_S b mm n ≤ 3)
    (hcov : ∀ m, IsFairCapital π m → IsComputableOnStrings m → ∃ i, b i = true ∧ mm i = m)
    (m : BitString → ℝ) (hm : IsFairCapital π m) (hc : IsComputableOnStrings m) :
    ¬ Wins m (exists_isComputablyRandom_plainK_log_seq b) := by
  obtain ⟨i, hbi, hmi⟩ := hcov m hm hc
  subst hmi
  have hfair : IsFairCapital π (mm i) := (hS i hbi).1
  intro hwin
  apply hwin
  have hc0pos : 0 < ((exists_isComputablyRandom_plainK_log_wt b i
      (exists_isComputablyRandom_plainK_log_state b (2 ^ i)) : ℚ) : ℝ) := by
    exact_mod_cast exists_isComputablyRandom_plainK_log_wt_pos b i _ hbi
  set c0 : ℝ := ((exists_isComputablyRandom_plainK_log_wt b i
      (exists_isComputablyRandom_plainK_log_state b (2 ^ i)) : ℚ) : ℝ) with hc0
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range (2 ^ i),
      mm i (exists_isComputablyRandom_plainK_log_state b j) :=
    Finset.sum_nonneg (fun j _ => hfair.nonneg _)
  have hdiv_nonneg : 0 ≤ 3 / c0 := by positivity
  refine ⟨(∑ j ∈ Finset.range (2 ^ i), mm i (exists_isComputablyRandom_plainK_log_state b j))
    + 3 / c0, ?_⟩
  rintro _ ⟨n, rfl⟩
  change mm i (cantorPrefix (exists_isComputablyRandom_plainK_log_seq b) n) ≤ _
  rw [exists_isComputablyRandom_plainK_log_state_prefix]
  by_cases hn : 2 ^ i ≤ n
  · have hi : i < Nat.size n := Nat.lt_size.mpr hn
    have htake := exists_isComputablyRandom_plainK_log_state_take b hn
    have hterm : c0 * mm i (exists_isComputablyRandom_plainK_log_state b n) ≤
        exists_isComputablyRandom_plainK_log_S b mm n := by
      unfold exists_isComputablyRandom_plainK_log_S
      have h := Finset.single_le_sum
        (f := fun j => ((exists_isComputablyRandom_plainK_log_wt b j
          ((exists_isComputablyRandom_plainK_log_state b n).take (2 ^ j)) : ℚ) : ℝ) *
            mm j (exists_isComputablyRandom_plainK_log_state b n))
        (fun j _ => exists_isComputablyRandom_plainK_log_Eaux_term_nonneg hS j _ _)
        (Finset.mem_range.mpr hi)
      simpa [htake, hc0] using h
    have h3 : c0 * mm i (exists_isComputablyRandom_plainK_log_state b n) ≤ 3 :=
      hterm.trans (hSle n)
    have h4 : mm i (exists_isComputablyRandom_plainK_log_state b n) ≤ 3 / c0 := by
      rw [le_div_iff₀ hc0pos]
      linarith [mul_comm c0 (mm i (exists_isComputablyRandom_plainK_log_state b n))]
    linarith
  · have hn' : n < 2 ^ i := not_le.mp hn
    have h := Finset.single_le_sum
      (f := fun j => mm i (exists_isComputablyRandom_plainK_log_state b j))
      (fun j _ => hfair.nonneg _) (Finset.mem_range.mpr hn')
    linarith

/-- (F1 aux) `n ↦ (1/2)^n` is computable. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_halfpow :
    Computable (fun n : ℕ => (1 / 2 : ℚ) ^ n) := by
  have hpow : Computable (fun n : ℕ => 2 ^ n) := comp_pow
  refine computable_of_num_den (N := fun _ => (1 : ℤ)) (D := fun n => 2 ^ n)
    (Computable.const 1) hpow (fun n => by positivity) (fun n => ?_)
  rw [one_div_pow]
  push_cast
  rfl

/-- (F1 aux) `shift` is computable. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_shift :
    Computable exists_isComputablyRandom_plainK_log_shift :=
  computable_nat_size.comp (ComputableReals.primrec_intToNat.to_comp.comp computable_ratNum)

/-- (F1 aux) `sim_term` is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_term :
    Partrec (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      exists_isComputablyRandom_plainK_log_sim_term p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hadv : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.1) :=
    Computable.fst
  have hx : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hy : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hi : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hflag : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      p.1.getD p.2.2.2.2 false) :=
    (Primrec.list_getD false).to_comp.comp hadv hi
  have h2i : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => 2 ^ p.2.2.2.2) :=
    comp_pow.comp hi
  have htake : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      p.2.1.take (2 ^ p.2.2.2.2)) :=
    (Primrec.list_take (α := Bool)).to_comp.comp h2i hx
  have hq0 : Partrec (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.1.take (2 ^ p.2.2.2.2), 0)) :=
    Partrec.comp (f := exists_isComputablyRandom_plainK_log_Qp)
      (g := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
        ((p.2.2.2.2, p.2.1.take (2 ^ p.2.2.2.2), (0 : ℕ)) : ℕ × BitString × ℕ))
      exists_isComputablyRandom_plainK_log_Qp_partrec
      (hi.pair (htake.pair (Computable.const 0)))
  have hqy : Partrec (fun z : (List Bool × BitString × BitString × ℕ × ℕ) × ℚ =>
      exists_isComputablyRandom_plainK_log_Qp (z.1.2.2.2.2, z.1.2.2.1, z.1.2.2.2.1)) :=
    Partrec.comp (f := exists_isComputablyRandom_plainK_log_Qp)
      (g := fun z : (List Bool × BitString × BitString × ℕ × ℕ) × ℚ =>
        ((z.1.2.2.2.2, z.1.2.2.1, z.1.2.2.2.1) : ℕ × BitString × ℕ))
      exists_isComputablyRandom_plainK_log_Qp_partrec
      ((hi.comp Computable.fst).pair ((hy.comp Computable.fst).pair (hs.comp Computable.fst)))
  have hmul : Computable₂ (fun (z : (List Bool × BitString × BitString × ℕ × ℕ) × ℚ) (qy : ℚ) =>
      (1 / 2 : ℚ) ^ (z.1.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift z.2) * qy) := by
    have hexp : Computable (fun w : ((List Bool × BitString × BitString × ℕ × ℕ) × ℚ) × ℚ =>
        w.1.1.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift w.1.2) :=
      Primrec.nat_add.to_comp.comp (hi.comp (Computable.fst.comp Computable.fst))
        (exists_isComputablyRandom_plainK_log_F1aux_shift.comp (Computable.snd.comp Computable.fst))
    have hpw : Computable (fun w : ((List Bool × BitString × BitString × ℕ × ℕ) × ℚ) × ℚ =>
        (1 / 2 : ℚ) ^ (w.1.1.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift w.1.2)) :=
      exists_isComputablyRandom_plainK_log_F1aux_halfpow.comp hexp
    exact computable₂_ratMul.comp hpw Computable.snd
  have hbody : Partrec₂ (fun (p : List Bool × BitString × BitString × ℕ × ℕ) (q0 : ℚ) =>
      (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.2.1, p.2.2.2.1)).map
        fun qy => (1 / 2 : ℚ) ^ (p.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift q0) * qy) :=
    Partrec.map (f := fun z : (List Bool × BitString × BitString × ℕ × ℕ) × ℚ =>
        exists_isComputablyRandom_plainK_log_Qp (z.1.2.2.2.2, z.1.2.2.1, z.1.2.2.2.1))
      (g := fun (z : (List Bool × BitString × BitString × ℕ × ℕ) × ℚ) (qy : ℚ) =>
        (1 / 2 : ℚ) ^ (z.1.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift z.2) * qy)
      hqy hmul
  have hthen : Partrec (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.1.take (2 ^ p.2.2.2.2), 0)).bind
        fun q0 => (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.2.1, p.2.2.2.1)).map
          fun qy => (1 / 2 : ℚ) ^ (p.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift q0) *
            qy) :=
    Partrec.bind (f := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
        exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.1.take (2 ^ p.2.2.2.2), 0))
      (g := fun (p : List Bool × BitString × BitString × ℕ × ℕ) (q0 : ℚ) =>
        (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.2.1, p.2.2.2.1)).map
          fun qy => (1 / 2 : ℚ) ^ (p.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift q0) *
            qy)
      hq0 hbody
  exact Partrec.cond (c := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      p.1.getD p.2.2.2.2 false)
    (f := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.1.take (2 ^ p.2.2.2.2), 0)).bind
        fun q0 => (exists_isComputablyRandom_plainK_log_Qp (p.2.2.2.2, p.2.2.1, p.2.2.2.1)).map
          fun qy => (1 / 2 : ℚ) ^ (p.2.2.2.2 + exists_isComputablyRandom_plainK_log_shift q0) *
            qy)
    (g := fun _ => Part.some (0 : ℚ))
    hflag hthen (Partrec.const' (Part.some (0 : ℚ)))

/-- (F1 aux) `sim_pot` is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_pot :
    Partrec (fun p : List Bool × BitString × BitString × ℕ × ℕ =>
      exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hi : Computable (fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hterm : Partrec (fun z : (List Bool × BitString × BitString × ℕ × ℕ) × (ℕ × ℚ) =>
      exists_isComputablyRandom_plainK_log_sim_term z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.2.1) :=
    Partrec.comp (f := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
        exists_isComputablyRandom_plainK_log_sim_term p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (g := fun z : (List Bool × BitString × BitString × ℕ × ℕ) × (ℕ × ℚ) =>
        ((z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2.1, z.2.1) :
          List Bool × BitString × BitString × ℕ × ℕ))
      exists_isComputablyRandom_plainK_log_F1aux_term
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
              (Computable.snd.comp Computable.fst)))).pair
              (Computable.fst.comp Computable.snd)))))
  have hh : Partrec₂ (fun (p : List Bool × BitString × BitString × ℕ × ℕ) (iu : ℕ × ℚ) =>
      (exists_isComputablyRandom_plainK_log_sim_term p.1 p.2.1 p.2.2.1 p.2.2.2.1 iu.1).map
        fun t => iu.2 + t) :=
    Partrec.map (f := fun z : (List Bool × BitString × BitString × ℕ × ℕ) × (ℕ × ℚ) =>
        exists_isComputablyRandom_plainK_log_sim_term z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.2.1)
      (g := fun (z : (List Bool × BitString × BitString × ℕ × ℕ) × (ℕ × ℚ)) (t : ℚ) =>
        z.2.2 + t)
      hterm
      (computable₂_ratAdd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
        Computable.snd)
  have h := Partrec.nat_rec
    (f := fun p : List Bool × BitString × BitString × ℕ × ℕ => p.2.2.2.2)
    (g := fun _ => Part.some (0 : ℚ))
    (h := fun (p : List Bool × BitString × BitString × ℕ × ℕ) (iu : ℕ × ℚ) =>
      (exists_isComputablyRandom_plainK_log_sim_term p.1 p.2.1 p.2.2.1 p.2.2.2.1 iu.1).map
        fun t => iu.2 + t)
    hi (Partrec.const' (Part.some (0 : ℚ))) hh
  exact h.of_eq fun x => rfl

/-- (F1 aux) `sim_bit` is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_bit :
    Partrec (fun p : List Bool × BitString =>
      exists_isComputablyRandom_plainK_log_sim_bit p.1 p.2) := by
  have hlen : Computable (fun p : List Bool × BitString => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hP : ∀ c : Bool, Partrec (fun p : List Bool × BitString =>
      exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2 (p.2 ++ [c]) (p.2.length + 3)
        (Nat.size p.2.length)) := by
    intro c
    have hg : Computable (fun p : List Bool × BitString =>
        ((p.1, p.2, p.2 ++ [c], p.2.length + 3, Nat.size p.2.length) :
          List Bool × BitString × BitString × ℕ × ℕ)) :=
      Computable.fst.pair (Computable.snd.pair
        ((Primrec.list_concat.to_comp.comp Computable.snd (Computable.const c)).pair
          ((Primrec.nat_add.to_comp.comp hlen (Computable.const 3)).pair
            (computable_nat_size.comp hlen))))
    exact Partrec.comp (f := fun p : List Bool × BitString × BitString × ℕ × ℕ =>
        exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (g := fun p : List Bool × BitString =>
        ((p.1, p.2, p.2 ++ [c], p.2.length + 3, Nat.size p.2.length) :
          List Bool × BitString × BitString × ℕ × ℕ))
      exists_isComputablyRandom_plainK_log_F1aux_pot hg
  have hrest : Partrec₂ (fun (p : List Bool × BitString) (a1 : ℚ) =>
      (exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2 (p.2 ++ [false]) (p.2.length + 3)
        (Nat.size p.2.length)).map fun a0 => decide (a1 < a0)) :=
    Partrec.map (f := fun z : (List Bool × BitString) × ℚ =>
        exists_isComputablyRandom_plainK_log_sim_pot z.1.1 z.1.2 (z.1.2 ++ [false])
          (z.1.2.length + 3) (Nat.size z.1.2.length))
      (g := fun (z : (List Bool × BitString) × ℚ) (a0 : ℚ) => decide (z.2 < a0))
      (Partrec.comp (f := fun p : List Bool × BitString =>
          exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2 (p.2 ++ [false])
            (p.2.length + 3) (Nat.size p.2.length))
        (g := fun z : (List Bool × BitString) × ℚ => z.1) (hP false) Computable.fst)
      ((PrimrecRel.decide primrec_ratLt).to_comp.comp (Computable.snd.comp Computable.fst)
        Computable.snd)
  exact Partrec.bind (f := fun p : List Bool × BitString =>
      exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2 (p.2 ++ [true]) (p.2.length + 3)
        (Nat.size p.2.length))
    (g := fun (p : List Bool × BitString) (a1 : ℚ) =>
      (exists_isComputablyRandom_plainK_log_sim_pot p.1 p.2 (p.2 ++ [false]) (p.2.length + 3)
        (Nat.size p.2.length)).map fun a0 => decide (a1 < a0))
    (hP true) hrest

/-- (F1 aux) `sim_iter` is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_F1aux_iter :
    Partrec (fun p : List Bool × ℕ =>
      exists_isComputablyRandom_plainK_log_sim_iter p.1 p.2) := by
  have hbit : Partrec (fun z : (List Bool × ℕ) × (ℕ × BitString) =>
      exists_isComputablyRandom_plainK_log_sim_bit z.1.1 z.2.2) :=
    Partrec.comp (f := fun p : List Bool × BitString =>
        exists_isComputablyRandom_plainK_log_sim_bit p.1 p.2)
      (g := fun z : (List Bool × ℕ) × (ℕ × BitString) => ((z.1.1, z.2.2) : List Bool × BitString))
      exists_isComputablyRandom_plainK_log_F1aux_bit
      ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  have hh : Partrec₂ (fun (p : List Bool × ℕ) (jx : ℕ × BitString) =>
      (exists_isComputablyRandom_plainK_log_sim_bit p.1 jx.2).map fun bt => jx.2 ++ [bt]) :=
    Partrec.map (f := fun z : (List Bool × ℕ) × (ℕ × BitString) =>
        exists_isComputablyRandom_plainK_log_sim_bit z.1.1 z.2.2)
      (g := fun (z : (List Bool × ℕ) × (ℕ × BitString)) (bt : Bool) => z.2.2 ++ [bt])
      hbit
      (Primrec.list_concat.to_comp.comp
        (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd)
  have h := Partrec.nat_rec
    (f := fun p : List Bool × ℕ => p.2)
    (g := fun _ => Part.some ([] : BitString))
    (h := fun (p : List Bool × ℕ) (jx : ℕ × BitString) =>
      (exists_isComputablyRandom_plainK_log_sim_bit p.1 jx.2).map fun bt => jx.2 ++ [bt])
    Computable.snd (Partrec.const' (Part.some ([] : BitString))) hh
  exact h.of_eq fun x => rfl

/-- The program `sim_prog` is partial recursive. -/
private lemma exists_isComputablyRandom_plainK_log_sim_prog_partrec :
    Partrec exists_isComputablyRandom_plainK_log_sim_prog := by
  have hg : Computable (fun a : BitString =>
      ((decodeSecond a, bitStringToNat (decodeFirst a)) : List Bool × ℕ)) :=
    decodeSecond_computable.pair (computable_bitStringToNat.comp decodeFirst_computable)
  exact Partrec.comp (f := fun p : List Bool × ℕ =>
      exists_isComputablyRandom_plainK_log_sim_iter p.1 p.2)
    (g := fun a : BitString => ((decodeSecond a, bitStringToNat (decodeFirst a)) : List Bool × ℕ))
    exists_isComputablyRandom_plainK_log_F1aux_iter hg

/-- (F2 aux) Reading the advice `(List.range M).map b` at an index `i < M` returns `b i`. -/
private lemma exists_isComputablyRandom_plainK_log_F2aux_getD_map_range (b : ℕ → Bool) {M i : ℕ}
    (hi : i < M) : ((List.range M).map b).getD i false = b i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- (F2 aux) With total flagged oracles, the `i`-th simulated term is the rational `term`. -/
private lemma exists_isComputablyRandom_plainK_log_F2aux_term_eq (b : ℕ → Bool)
    (hb : ∀ i, b i = true → ∀ x s,
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) {M i : ℕ} (hi : i < M)
    (x y : BitString) (s : ℕ) :
    exists_isComputablyRandom_plainK_log_sim_term ((List.range M).map b) x y s i =
      Part.some (exists_isComputablyRandom_plainK_log_term b x y s i) := by
  unfold exists_isComputablyRandom_plainK_log_sim_term
  rw [exists_isComputablyRandom_plainK_log_F2aux_getD_map_range b hi]
  cases hbi : b i
  · simp [exists_isComputablyRandom_plainK_log_term, exists_isComputablyRandom_plainK_log_wt,
      hbi]
  · have h1 := exists_isComputablyRandom_plainK_log_Qv_spec i (x.take (2 ^ i)) 0
      (hb i hbi _ _)
    have h2 := exists_isComputablyRandom_plainK_log_Qv_spec i y s (hb i hbi _ _)
    simp only [Bool.cond_true]
    rw [h1, Part.bind_some, h2, Part.map_some]
    simp [exists_isComputablyRandom_plainK_log_term, exists_isComputablyRandom_plainK_log_wt,
      hbi]

/-- (F2 aux) With total flagged oracles, the simulated potential is the rational `pot`. -/
private lemma exists_isComputablyRandom_plainK_log_F2aux_pot_eq (b : ℕ → Bool)
    (hb : ∀ i, b i = true → ∀ x s,
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) {M : ℕ}
    (x y : BitString) (s : ℕ) :
    ∀ m, m ≤ M →
      exists_isComputablyRandom_plainK_log_sim_pot ((List.range M).map b) x y s m =
        Part.some (exists_isComputablyRandom_plainK_log_pot b x y s m) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : exists_isComputablyRandom_plainK_log_sim_pot ((List.range M).map b) x y s 0 =
        Part.some 0 := rfl
    rw [h0]
    simp [exists_isComputablyRandom_plainK_log_pot]
  | succ m ih =>
    intro hm
    have hstep : exists_isComputablyRandom_plainK_log_sim_pot ((List.range M).map b) x y s (m + 1)
        = (exists_isComputablyRandom_plainK_log_sim_pot ((List.range M).map b) x y s m).bind
          (fun acc => (exists_isComputablyRandom_plainK_log_sim_term ((List.range M).map b)
            x y s m).map fun t => acc + t) := rfl
    rw [hstep, ih (Nat.le_of_succ_le hm), Part.bind_some,
      exists_isComputablyRandom_plainK_log_F2aux_term_eq b hb (Nat.lt_of_succ_le hm) x y s,
      Part.map_some]
    congr 1
    simp [exists_isComputablyRandom_plainK_log_pot, Finset.sum_range_succ]

/-- (F2 aux) With total flagged oracles, the simulated next bit is `rule`. -/
private lemma exists_isComputablyRandom_plainK_log_F2aux_bit_eq (b : ℕ → Bool)
    (hb : ∀ i, b i = true → ∀ x s,
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) {M : ℕ} (x : BitString)
    (hx : Nat.size x.length ≤ M) :
    exists_isComputablyRandom_plainK_log_sim_bit ((List.range M).map b) x =
      Part.some (exists_isComputablyRandom_plainK_log_rule b x) := by
  unfold exists_isComputablyRandom_plainK_log_sim_bit
  rw [exists_isComputablyRandom_plainK_log_F2aux_pot_eq b hb x (x ++ [true]) (x.length + 3) _ hx,
    Part.bind_some,
    exists_isComputablyRandom_plainK_log_F2aux_pot_eq b hb x (x ++ [false]) (x.length + 3) _ hx,
    Part.map_some]
  rfl

/-- (F2 aux) With total flagged oracles, the simulated iteration is `state`. -/
private lemma exists_isComputablyRandom_plainK_log_F2aux_iter_eq (b : ℕ → Bool)
    (hb : ∀ i, b i = true → ∀ x s,
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) {M : ℕ} :
    ∀ n, (∀ j < n, Nat.size j ≤ M) →
      exists_isComputablyRandom_plainK_log_sim_iter ((List.range M).map b) n =
        Part.some (exists_isComputablyRandom_plainK_log_state b n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro hn
    have hstep : exists_isComputablyRandom_plainK_log_sim_iter ((List.range M).map b) (n + 1)
        = (exists_isComputablyRandom_plainK_log_sim_iter ((List.range M).map b) n).bind
          (fun x => (exists_isComputablyRandom_plainK_log_sim_bit ((List.range M).map b)
            x).map fun bt => x ++ [bt]) := rfl
    have hlen := exists_isComputablyRandom_plainK_log_state_length b n
    rw [hstep, ih (fun j hj => hn j (Nat.lt_succ_of_lt hj)), Part.bind_some,
      exists_isComputablyRandom_plainK_log_F2aux_bit_eq b hb
        (x := exists_isComputablyRandom_plainK_log_state b n)
        (by rw [hlen]; exact hn n (Nat.lt_succ_self n)),
      Part.map_some]
    rfl

/-- The program computes the prefix of length `n` from `n` and the flags
`b 0, …, b (size n - 1)`, provided every flagged oracle is total. -/
private lemma exists_isComputablyRandom_plainK_log_sim_prog_eq (b : ℕ → Bool)
    (hb : ∀ i, b i = true → ∀ x s,
      (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) (n : ℕ) :
    exists_isComputablyRandom_plainK_log_sim_prog
        (pairCode (natToBitString n) ((List.range (Nat.size n)).map b)) =
      Part.some (exists_isComputablyRandom_plainK_log_state b n) := by
  unfold exists_isComputablyRandom_plainK_log_sim_prog
  rw [decodeSecond_pairCode, decodeFirst_pairCode, bitStringToNat_natToBitString]
  exact exists_isComputablyRandom_plainK_log_F2aux_iter_eq b hb n
    (fun j hj => Nat.size_le_size hj.le)

/-- The simulation: a fixed partial recursive function computes the prefix of length `n` from
`n` and the flags `b 0, …, b (size n - 1)`, provided every flagged oracle is total. -/
private lemma exists_isComputablyRandom_plainK_log_simulation :
    ∃ F : BitString →. BitString, Partrec F ∧
      ∀ b : ℕ → Bool, (∀ i, b i = true → ∀ x s,
          (exists_isComputablyRandom_plainK_log_Qp (i, x, s)).Dom) →
        ∀ n : ℕ, F (pairCode (natToBitString n) ((List.range (Nat.size n)).map b)) =
          Part.some (exists_isComputablyRandom_plainK_log_state b n) :=
  ⟨exists_isComputablyRandom_plainK_log_sim_prog,
    exists_isComputablyRandom_plainK_log_sim_prog_partrec,
    fun b hb n => exists_isComputablyRandom_plainK_log_sim_prog_eq b hb n⟩

/-- The advice has logarithmic length. -/
private lemma exists_isComputablyRandom_plainK_log_len_le (b : ℕ → Bool) (n : ℕ) :
    (pairCode (natToBitString n) ((List.range (Nat.size n)).map b)).length ≤ 3 * Nat.log 2 n + 5 :=
        by
  have hsize : Nat.size (n + 1) ≤ Nat.log 2 n + 2 := by
    rw [Nat.size_le]
    have h1 : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
    calc n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := h1
      _ < 2 ^ (Nat.log 2 n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnat : (natToBitString n).length ≤ Nat.size (n + 1) - 1 := by
    simp [natToBitString, List.length_dropLast, Nat.size_eq_bits_len]
  have hact : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (Nat.le_succ n)
  have hpos : 1 ≤ Nat.size (n + 1) := Nat.size_pos.mpr (Nat.succ_pos n)
  rw [length_pairCode, List.length_map, List.length_range]
  omega

/-- **SUV Theorem 182(b), p. 279.**  For computable `π` with positive cylinders, there is a
computably random sequence whose prefixes have logarithmic complexity.  The paragraph before
Theorem 182 explicitly extends its first two parts to every computable `π` with positive cylinders;
this is the book's scope, not an extra generalization from the uniform measure. -/
theorem exists_isComputablyRandom_plainK_log {π : Measure CantorSeq} [IsProbabilityMeasure π]
    (_hπ : IsComputableMeasure π) (hpos : ∀ x, 0 < cantorMass π x) (V : Map)
    (hV : isOptimalConditional V) :
    ∃ w, IsComputablyRandom π w ∧ ∃ c : ℕ, ∀ n : ℕ,
      plainK V (cantorPrefix w n) ≤ ((c * Nat.log 2 n + c : ℕ) : ℕ∞) := by
  obtain ⟨b, mm, hdom, hS, hcov⟩ := exists_isComputablyRandom_plainK_log_flags π
  obtain ⟨F, hF, hFb⟩ := exists_isComputablyRandom_plainK_log_simulation
  obtain ⟨c1, hc1⟩ := plainK_le_length V hV
  obtain ⟨c2, hc2⟩ := plainK_partrec_map_le V hV F hF
  have hSle : ∀ n, exists_isComputablyRandom_plainK_log_S b mm n ≤ 3 :=
    exists_isComputablyRandom_plainK_log_budget _
      (exists_isComputablyRandom_plainK_log_S_zero b mm)
      (exists_isComputablyRandom_plainK_log_drift hpos hS)
  refine ⟨exists_isComputablyRandom_plainK_log_seq b, ?_, c1 + c2 + 5, fun n => ?_⟩
  · intro m hm hc
    exact exists_isComputablyRandom_plainK_log_bounded hS hSle hcov m hm hc
  · rw [exists_isComputablyRandom_plainK_log_state_prefix b n]
    have h1 := hc2 _ _ (show _ ∈ F _ by rw [hFb b hdom n]; exact Part.mem_some _)
    have h2 := hc1 (pairCode (natToBitString n) ((List.range (Nat.size n)).map b))
    have h3 := exists_isComputablyRandom_plainK_log_len_le b n
    refine h1.trans ?_
    have h4 : (plainK V (pairCode (natToBitString n)
        ((List.range (Nat.size n)).map b)) : ℕ∞)
        ≤ (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 : ℕ) : ℕ∞) := by
      refine h2.trans ?_
      have : programLength (pairCode (natToBitString n)
          ((List.range (Nat.size n)).map b)) + c1
            ≤ (c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 := by
        unfold programLength
        have : 3 * Nat.log 2 n ≤ (c1 + c2 + 5) * Nat.log 2 n :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      exact_mod_cast this
    calc plainK V (pairCode (natToBitString n)
        ((List.range (Nat.size n)).map b)) + (c2 : ℕ∞)
        ≤ (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) - c2 : ℕ) : ℕ∞) + (c2 : ℕ∞) := by
          gcongr
      _ = (((c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]
          congr 1
          have : 5 + c1 + c2 ≤ (c1 + c2 + 5) * Nat.log 2 n + (c1 + c2 + 5) := by omega
          omega

end Kolmogorov.FrequencyGames
