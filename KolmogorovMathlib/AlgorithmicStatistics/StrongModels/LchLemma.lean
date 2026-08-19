import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LchDescent
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.UpwardConditional

/-!
# Public LCH descent endpoint

This module records the exact frozen endpoint of VS40 Lemma `lch`.  The
one-round construction and its terminal arithmetic are in `LchDescent`; the
remaining task is to assemble the bounded iteration without changing the
public quantifier order or any of its four conclusions.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

structure LchIterates (V T : Map) (x : BitString) (n : Nat) (A : Finset BitString)
    (hA : A.Nonempty) (epsilon alpha c : Nat) (q : Nat.Partrec.Code) where
  A_seq : Nat → Finset BitString
  hA_seq : ∀ r, (A_seq r).Nonempty
  B_seq : Nat → Finset BitString
  hB_seq : ∀ r, (B_seq r).Nonempty
  h_x_in_A : ∀ r, x ∈ A_seq r
  h_x_in_B : ∀ r, x ∈ B_seq r
  h_strong_A : ∀ r, IsStrongSetModel T x (A_seq r) (hA_seq r) epsilon
  h_comp_A0 : plainSetComplexity V (A_seq 0) (hA_seq 0) ≤ plainSetComplexity V A hA + (alpha : ENat)
  h_card_A0 : finiteSetLogCard (A_seq 0) ≤ finiteSetLogCard A + alpha
  h_twoB : ∀ r, plainSetComplexity V (B_seq r) (hB_seq r) + (finiteSetLogCard (B_seq r) : ENat) ≤
    plainSetComplexity V (A_seq r) (hA_seq r) + (finiteSetLogCard (A_seq r) : ENat) +
      (logSlack c n : ENat)
  h_capB : ∀ r, plainSetComplexity V (B_seq r) (hB_seq r) + (finiteSetLogCard (B_seq r) : ENat) ≤
    (n + logSlack c n : ENat)
  h_condB_A : ∀ r, condK V (codedUniformOn (B_seq r) (hB_seq r)).code
    (codedUniformOn (A_seq r) (hA_seq r)).code ≤ (logSlack c n : ENat)
  h_condB_Omega : ∀ r, condK V (codedUniformOn (B_seq r) (hB_seq r)).code
    (omegaFixedCode q (plainSetComplexity V (B_seq r) (hB_seq r)).toNat) ≤ (logSlack c n : ENat)
  h_twoA : ∀ r, plainSetComplexity V (A_seq (r + 1)) (hA_seq (r + 1)) +
      (finiteSetLogCard (A_seq (r + 1)) : ENat) ≤
    plainSetComplexity V (A_seq r) (hA_seq r) + (finiteSetLogCard (A_seq r) : ENat) +
      (2 * alpha + logSlack c n : ENat)
  h_capA : ∀ r, plainSetComplexity V (A_seq (r + 1)) (hA_seq (r + 1)) ≤
    (n + alpha + logSlack c n : ENat)
  h_compA_B : ∀ r, plainSetComplexity V (A_seq (r + 1)) (hA_seq (r + 1)) ≤
    plainSetComplexity V (B_seq r) (hB_seq r) + (alpha : ENat)
  h_cardA_B : ∀ r, finiteSetLogCard (A_seq (r + 1)) ≤ finiteSetLogCard (B_seq r) + alpha

/-- **Corrected `logSlack`/`sqrt` bound.**  The logarithmic slack is dominated
by the square-root slack up to a constant factor.  This uses the exact
`(Nat.bits n).length ≤ Nat.sqrt n + 2` from the bounded-complexity theory.
(The naive `logSlack c n ≤ c * n.sqrt` is false, e.g. at `n = 2`.) -/
lemma logSlack_le_mul_sqrt (c n : Nat) :
    logSlack c n ≤ c * n.sqrt + 3 * c := by
  unfold logSlack
  have h := bits_length_le_sqrt_add_two n
  have h2 : c * (Nat.bits n).length ≤ c * (Nat.sqrt n + 2) :=
    Nat.mul_le_mul (le_refl c) h
  have h3 : c * (Nat.sqrt n + 2) = c * Nat.sqrt n + 2 * c := by ring
  omega

/-- Accumulating a per-step additive increase over `N` steps. -/
lemma nat_step_accumulate (f : Nat → Nat) (N step : Nat)
    (h : ∀ i < N, f (i + 1) ≤ f i + step) :
    f N ≤ f 0 + N * step := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hlast := h N (Nat.lt_succ_self N)
      have hih := ih (fun i hi => h i (hi.trans (Nat.lt_succ_self N)))
      calc
        f (N + 1) ≤ f N + step := hlast
        _ ≤ (f 0 + N * step) + step := by omega
        _ = f 0 + (N + 1) * step := by ring

/-- **Construction of the LCH descent sequence.**

Seeding the descent with the strong model produced by the normality step
(`exists_strong_model_near_of_normal`) and iterating one full descent round
(`exists_descent_round`) with `Function.iterate`/`choose`, we obtain the coupled
sequences `A_r, B_r` packaged in `LchIterates`.  The initial invariant
`C(A₀) ≤ C(A) + alpha` is exactly the normality-step bound, and each transition
invariant is exactly one descent round; the round constant `cR` is uniform. -/
lemma exists_lch_iterates
    (V T : Map) (hV : isOptimalConditional V)
    (q : Nat.Partrec.Code) (hq : IsCodeFor q V) :
    ∃ c : Nat, ∀ x n A (hA : A.Nonempty) epsilon alpha,
      x.length = n →
      x ∈ A →
      IsNormalString V T x epsilon alpha →
      Nonempty (LchIterates V T x n A hA epsilon alpha c q) := by
  obtain ⟨cR, hround⟩ := exists_descent_round V T hV q hq
  refine ⟨cR, ?_⟩
  intro x n A hA epsilon alpha hn hxA hnorm
  -- A "good state" is a strong model of `x`.
  let St := Σ' (S : Finset BitString) (hS : S.Nonempty),
      (x ∈ S) ∧ IsStrongSetModel T x S hS epsilon
  -- One descent round packaged as a step from `s` to `t` producing `B`.
  have hstepex : ∀ s : St, ∃ t : St, ∃ (B : Finset BitString) (hB : B.Nonempty),
      x ∈ B ∧
      plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
        plainSetComplexity V s.1 s.2.1 + (finiteSetLogCard s.1 : ENat) +
          (logSlack cR n : ENat) ∧
      plainSetComplexity V B hB + (finiteSetLogCard B : ENat) ≤
        (n + logSlack cR n : ENat) ∧
      condK V (codedUniformOn B hB).code (codedUniformOn s.1 s.2.1).code ≤
        (logSlack cR n : ENat) ∧
      condK V (codedUniformOn B hB).code
          (omegaFixedCode q (plainSetComplexity V B hB).toNat) ≤
        (logSlack cR n : ENat) ∧
      plainSetComplexity V t.1 t.2.1 + (finiteSetLogCard t.1 : ENat) ≤
        plainSetComplexity V s.1 s.2.1 + (finiteSetLogCard s.1 : ENat) +
          (2 * alpha + logSlack cR n : ENat) ∧
      plainSetComplexity V t.1 t.2.1 ≤ (n + alpha + logSlack cR n : ENat) ∧
      plainSetComplexity V t.1 t.2.1 ≤ plainSetComplexity V B hB + (alpha : ENat) ∧
      finiteSetLogCard t.1 ≤ finiteSetLogCard B + alpha := by
    intro s
    obtain ⟨B, hB, H, hH, hxB, hxH, hstrongH, hTwoB, hCapB, hBA, hOmegaB,
        hTwoH, hCapH, hcompH, hcardH⟩ :=
      hround x n s.1 s.2.1 epsilon alpha hn s.2.2.1 hnorm
    exact ⟨⟨H, hH, ⟨hxH, hstrongH⟩⟩, B, hB, hxB, hTwoB, hCapB, hBA, hOmegaB,
      hTwoH, hCapH, hcompH, hcardH⟩
  choose g Bg hBg hxBg hTwoBg hCapBg hBAg hOmegaBg hTwoAg hCapAg hcompABg hcardABg
    using hstepex
  -- Initial strong model, seeded from `A` via the normality step.
  obtain ⟨H0, hH0, hxH0, hstrongH0, hcompH0, hcardH0⟩ :=
    exists_strong_model_near_of_normal V T hV x A hA epsilon alpha hxA hnorm
  let s0 : St := ⟨H0, hH0, ⟨hxH0, hstrongH0⟩⟩
  let f : Nat → St := fun r => Nat.rec s0 (fun _ ih => g ih) r
  exact ⟨{
    A_seq := fun r => (f r).1
    hA_seq := fun r => (f r).2.1
    B_seq := fun r => Bg (f r)
    hB_seq := fun r => hBg (f r)
    h_x_in_A := fun r => (f r).2.2.1
    h_x_in_B := fun r => hxBg (f r)
    h_strong_A := fun r => (f r).2.2.2
    h_comp_A0 := hcompH0
    h_card_A0 := hcardH0
    h_twoB := fun r => hTwoBg (f r)
    h_capB := fun r => hCapBg (f r)
    h_condB_A := fun r => hBAg (f r)
    h_condB_Omega := fun r => hOmegaBg (f r)
    h_twoA := fun r => hTwoAg (f r)
    h_capA := fun r => hCapAg (f r)
    h_compA_B := fun r => hcompABg (f r)
    h_cardA_B := fun r => hcardABg (f r)
  }⟩

/-- Round-count bound: the number of nonterminal LCH rounds `N` is `O(√n)`.
From `N·√n ≤ 4n + 2·logSlack c_strong n` (the descent budget) and the sqrt
identities `n ≤ (√n)² + 2√n`, `bits ≤ √n + 2`. -/
private lemma lch_N_bound (n N s b c_strong : Nat) (hs : 1 ≤ s)
    (hn : n ≤ s * s + 2 * s) (hb : b ≤ s + 2)
    (hNs : N * s ≤ 4 * n + 2 * (c_strong * b + c_strong)) :
    N ≤ 4 * s + 8 + 8 * c_strong := by
  apply Nat.le_of_mul_le_mul_right _ hs
  nlinarith [hNs, hn, hb, hs, Nat.zero_le c_strong, Nat.mul_le_mul_right s hb]

/-- The conclusion-2 accumulation arithmetic of Lemma `lch`.  Given the
round-count bound `N ≤ 4√n + O(1)`, the accumulated two-part loss
`2α + N·(2α + logSlack cR n)` fits into `c·(α + logSlack c n)·√n` once `c`
dominates the fixed constants `cR, c_strong` (`s = √n`, `b = bits`,
`logSlack d n = d·b + d`). -/
private lemma lch_concl2_arith
    (alpha N cR c_strong s b c : Nat)
    (hs : 1 ≤ s) (hN : N ≤ 4 * s + 8 + 8 * c_strong)
    (hc1 : 26 + 16 * c_strong ≤ c)
    (hc2 : (12 + 8 * c_strong) * cR ≤ c * c) :
    2 * alpha + N * (2 * alpha + (cR * b + cR)) ≤ c * (alpha + (c * b + c)) * s := by
  have e1 : N * (2 * alpha + (cR * b + cR)) ≤
      (4 * s + 8 + 8 * c_strong) * (2 * alpha + (cR * b + cR)) :=
    Nat.mul_le_mul_right _ hN
  refine le_trans (Nat.add_le_add_left e1 (2 * alpha)) ?_
  have hsa : alpha ≤ s * alpha := Nat.le_mul_of_pos_left alpha hs
  have hA : 2 * alpha + 8 * s * alpha + 2 * (8 + 8 * c_strong) * alpha ≤ c * alpha * s := by
    have hh : 2 * alpha + 8 * s * alpha + 2 * (8 + 8 * c_strong) * alpha ≤
        (26 + 16 * c_strong) * (s * alpha) := by
      nlinarith [hsa, Nat.mul_le_mul_left c_strong hsa, Nat.zero_le c_strong]
    have hp1 : (26 + 16 * c_strong) * (s * alpha) ≤ c * (s * alpha) :=
      Nat.mul_le_mul_right _ hc1
    calc 2 * alpha + 8 * s * alpha + 2 * (8 + 8 * c_strong) * alpha
        ≤ (26 + 16 * c_strong) * (s * alpha) := hh
      _ ≤ c * (s * alpha) := hp1
      _ = c * alpha * s := by ring
  have hsb : b ≤ s * b := Nat.le_mul_of_pos_left b hs
  have hB1 : 4 * cR * s * b + (8 + 8 * c_strong) * cR * b ≤ (c * c) * b * s := by
    have hh : 4 * cR * s * b + (8 + 8 * c_strong) * cR * b ≤
        ((12 + 8 * c_strong) * cR) * (s * b) := by
      nlinarith [hsb, Nat.mul_le_mul_left (c_strong * cR) hsb,
        Nat.mul_le_mul_left cR hsb, Nat.zero_le c_strong, Nat.zero_le cR]
    have hp2 : ((12 + 8 * c_strong) * cR) * (s * b) ≤ (c * c) * (s * b) :=
      Nat.mul_le_mul_right _ hc2
    calc 4 * cR * s * b + (8 + 8 * c_strong) * cR * b
        ≤ ((12 + 8 * c_strong) * cR) * (s * b) := hh
      _ ≤ (c * c) * (s * b) := hp2
      _ = (c * c) * b * s := by ring
  have hB2 : 4 * cR * s + (8 + 8 * c_strong) * cR ≤ (c * c) * s := by
    have hcRs : cR ≤ cR * s := Nat.le_mul_of_pos_right cR hs
    have hh : 4 * cR * s + (8 + 8 * c_strong) * cR ≤ ((12 + 8 * c_strong) * cR) * s := by
      nlinarith [hcRs, Nat.mul_le_mul_left c_strong hcRs, Nat.zero_le c_strong, Nat.zero_le cR]
    exact le_trans hh (Nat.mul_le_mul_right _ hc2)
  nlinarith [hA, hB1, hB2]

/-- Worker form of VS40 Lemma `lch` retaining the membership fact carried by
the constructed iterate.  The frozen public interface predates this field, so
`lemma_lch` below forgets it. -/
def LemmaLchWithMemStatement (V T : Map) : Prop :=
  ∃ c : Nat,
    ∀ x n A (hA : A.Nonempty) epsilon alpha (q : Nat.Partrec.Code),
      IsCodeFor q V →
      x.length = n →
      x ∈ A →
      epsilon ≤ n →
      alpha * 2 < n.sqrt →
      IsNormalString V T x epsilon alpha →
      ∃ H, ∃ hH : H.Nonempty,
        x ∈ H ∧
        IsStrongSetModel T x H hH epsilon ∧
        plainSetComplexity V H hH + (finiteSetLogCard H : ENat) ≤
          plainSetComplexity V A hA + (finiteSetLogCard A : ENat) +
            (c * (alpha + logSlack c n) * Nat.sqrt n : ENat) ∧
        condK V (codedUniformOn H hH).code
          (omegaFixedCode q (plainK V (codedUniformOn H hH).code).toNat) ≤
            (c * Nat.sqrt n + logSlack c n : ENat) ∧
        plainSetComplexity V H hH ≤ plainSetComplexity V A hA + (alpha : ENat)

/-- VS40 Lemma `lch`, with the source's uniform constant and the corrected
direction `C(H | Ω_{C(H)})`, in the stronger worker form used by the
hereditary assembly. -/
theorem lemma_lch_with_mem
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    LemmaLchWithMemStatement V T := by
  obtain ⟨c_fix, hc_fix⟩ := Nat.Partrec.Code.exists_code.mp hV.1
  obtain ⟨cR, h_iter⟩ := exists_lch_iterates V T hV c_fix hc_fix
  obtain ⟨c_close, h_close⟩ := lch_closing_condK V hV c_fix hc_fix
  obtain ⟨c_strong, h_strong⟩ := plainK_strongModelCode_le V T hV hT.1
  obtain ⟨c_fwd, h_fwd⟩ := plainK_forward_gap_of_condK V hV
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound c_fwd (2 + c_strong + cR) (c_strong + cR)
  obtain ⟨C2, hC2⟩ := logSlack_linear_bound c_close (2 + c_strong + cR) (c_strong + cR)
  -- Choose the uniform constant abstractly so downstream `omega`/`nlinarith`
  -- never re-expand the (large) explicit witness.
  obtain ⟨c, hc_pos, hc1, hc2, hc3⟩ :
      ∃ c : Nat, 1 ≤ c ∧ 26 + 16 * c_strong ≤ c ∧
        (12 + 8 * c_strong) * cR ≤ c * c ∧ 7 * cR + 4 * C1 + C2 ≤ c := by
    refine ⟨26 + 16 * c_strong + (12 + 8 * c_strong) * cR + 7 * cR + 4 * C1 + C2 + 1,
      by omega, by omega, ?_, by omega⟩
    exact le_trans
      (show (12 + 8 * c_strong) * cR ≤
        26 + 16 * c_strong + (12 + 8 * c_strong) * cR + 7 * cR + 4 * C1 + C2 + 1 by omega)
      (Nat.le_mul_of_pos_left _ (by omega))
  refine ⟨c, ?_⟩
  intro x n A hA epsilon alpha q hq hn hxA heps halpha hnorm
  obtain ⟨iter⟩ := h_iter x n A hA epsilon alpha hn hxA hnorm
  have hfinP : ∀ (S : Finset BitString) (hS : S.Nonempty),
      plainSetComplexity V S hS ≠ ⊤ := fun S hS =>
    condK_ne_top_of_optimal V hV (codedUniformOn S hS).code []
  let f : Nat → Nat := fun r => (plainSetComplexity V (iter.A_seq r) (iter.hA_seq r)).toNat
  let gseq : Nat → Nat := fun r => (plainSetComplexity V (iter.B_seq r) (iter.hB_seq r)).toNat
  have hfval : ∀ r, plainSetComplexity V (iter.A_seq r) (iter.hA_seq r) = (f r : ENat) :=
    fun r => (ENat.coe_toNat (hfinP _ _)).symm
  have hgval : ∀ r, plainSetComplexity V (iter.B_seq r) (iter.hB_seq r) = (gseq r : ENat) :=
    fun r => (ENat.coe_toNat (hfinP _ _)).symm
  -- basic sqrt facts
  have hs_pos : 1 ≤ n.sqrt := by omega
  have hb_sqrt : (Nat.bits n).length ≤ n.sqrt + 2 := bits_length_le_sqrt_add_two n
  have hn_sqrt : n ≤ n.sqrt * n.sqrt + 2 * n.sqrt := by
    have h := Nat.lt_succ_sqrt n; nlinarith [h]
  -- `aA`, `jA` for `A`
  have haAfin : plainSetComplexity V A hA ≠ ⊤ := hfinP A hA
  set aA : Nat := (plainSetComplexity V A hA).toNat with haA_def
  have haAval : plainSetComplexity V A hA = (aA : ENat) := (ENat.coe_toNat haAfin).symm
  set jA : Nat := finiteSetLogCard A with hjA_def
  -- the descent step
  have hnext : ∀ r, f (r + 1) ≤ gseq r + alpha := by
    intro r
    have h := iter.h_compA_B r
    rw [hfval (r + 1), hgval r] at h
    exact_mod_cast h
  obtain ⟨i0, hi0le, hi0pred⟩ :=
    exists_lch_terminal_gap f gseq n.sqrt alpha halpha hnext
  have hex : ∃ i, f i - gseq i ≤ n.sqrt := ⟨i0, hi0pred⟩
  set N := Nat.find hex with hN_def
  have hNspec : f N - gseq N ≤ n.sqrt := Nat.find_spec hex
  have hNmin : ∀ m, m < N → ¬ (f m - gseq m ≤ n.sqrt) :=
    fun m hm => Nat.find_min hex hm
  set d : Nat := n.sqrt + 1 - alpha with hd_def
  have hstep_dec : ∀ m, m < N → f (m + 1) + d ≤ f m := by
    intro m hm
    have h1 := hNmin m hm
    have h2 := hnext m
    omega
  have h2d : n.sqrt ≤ 2 * d := by omega
  -- initial strong-model complexity bound
  have hf0 : f 0 ≤ n + epsilon + logSlack c_strong n := by
    have h := h_strong x (iter.A_seq 0) (iter.hA_seq 0) n epsilon hn (iter.h_strong_A 0)
    have h2 : (f 0 : ENat) ≤ ((n + epsilon + logSlack c_strong n : Nat) : ENat) := by
      rw [← hfval 0]; exact_mod_cast h
    exact_mod_cast h2
  -- N * √n bound
  have hNd : f N + N * d ≤ f 0 := descent_mul_le_of_step f N d hstep_dec
  have hNsqrt : N * n.sqrt ≤ 2 * (n + epsilon + logSlack c_strong n) := by
    calc N * n.sqrt ≤ N * (2 * d) := by gcongr
      _ = 2 * (N * d) := by ring
      _ ≤ 2 * f 0 := by omega
      _ ≤ 2 * (n + epsilon + logSlack c_strong n) := by omega
  have hNs : N * n.sqrt ≤ 4 * n + 2 * (c_strong * (Nat.bits n).length + c_strong) := by
    have : logSlack c_strong n = c_strong * (Nat.bits n).length + c_strong := rfl
    omega
  have hNfin : N ≤ 4 * n.sqrt + 8 + 8 * c_strong :=
    lch_N_bound n N n.sqrt (Nat.bits n).length c_strong hs_pos hn_sqrt hb_sqrt hNs
  -- monotonicity of the complexity sequence
  have hmono : ∀ j, j ≤ N → f j ≤ f 0 := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      have h1 : f (j + 1) ≤ f j := by have := hstep_dec j (by omega); omega
      have h2 : f j ≤ f 0 := ih (by omega)
      omega
  have hfN_le_f0 : f N ≤ f 0 := hmono N le_rfl
  refine ⟨iter.A_seq N, iter.hA_seq N, iter.h_x_in_A N, iter.h_strong_A N, ?_, ?_, ?_⟩
  · -- Conclusion 2: two-part growth
    have hFstep : ∀ r, f (r + 1) + finiteSetLogCard (iter.A_seq (r + 1)) ≤
        (f r + finiteSetLogCard (iter.A_seq r)) + (2 * alpha + logSlack cR n) := by
      intro r
      have h := iter.h_twoA r
      rw [hfval (r + 1), hfval r] at h
      exact_mod_cast h
    have hFacc : f N + finiteSetLogCard (iter.A_seq N) ≤
        (f 0 + finiteSetLogCard (iter.A_seq 0)) + N * (2 * alpha + logSlack cR n) :=
      nat_step_accumulate
        (fun r => f r + finiteSetLogCard (iter.A_seq r)) N (2 * alpha + logSlack cR n)
        (fun i _ => hFstep i)
    have hc0 : f 0 ≤ aA + alpha := by
      have h := iter.h_comp_A0
      rw [hfval 0, haAval] at h
      exact_mod_cast h
    have hd0 : finiteSetLogCard (iter.A_seq 0) ≤ jA + alpha := iter.h_card_A0
    have hkey : 2 * alpha + N * (2 * alpha + logSlack cR n) ≤
        c * (alpha + logSlack c n) * n.sqrt := by
      have h := lch_concl2_arith alpha N cR c_strong n.sqrt (Nat.bits n).length c
        hs_pos hNfin hc1 hc2
      simpa [logSlack] using h
    have haccum : f N + finiteSetLogCard (iter.A_seq N) ≤
        aA + jA + c * (alpha + logSlack c n) * n.sqrt := by omega
    rw [hfval N, haAval]
    calc (f N : ENat) + (finiteSetLogCard (iter.A_seq N) : ENat)
        = ((f N + finiteSetLogCard (iter.A_seq N) : Nat) : ENat) := by push_cast; ring
      _ ≤ ((aA + jA + c * (alpha + logSlack c n) * n.sqrt : Nat) : ENat) := by
          exact_mod_cast haccum
      _ = (aA : ENat) + (finiteSetLogCard A : ENat) +
            (c * (alpha + logSlack c n) * Nat.sqrt n : ENat) := by
          rw [hjA_def]; push_cast; ring
  · -- Conclusion 3: closing conditional-complexity bound
    have hHcode : plainK V (codedUniformOn (iter.A_seq N) (iter.hA_seq N)).code = (f N : ENat) :=
      hfval N
    have hBcode : plainK V (codedUniformOn (iter.B_seq N) (iter.hB_seq N)).code =
        (gseq N : ENat) := hgval N
    have hswap : omegaFixedCode q
        (plainK V (codedUniformOn (iter.A_seq N) (iter.hA_seq N)).code).toNat =
        omegaFixedCode c_fix (f N) := by
      rw [hHcode, ENat.toNat_coe]; exact omegaFixedCode_eq_of_isCodeFor hq hc_fix (f N)
    rw [hswap]
    set Nbnd := n + epsilon + logSlack (c_strong + cR) n with hNbnd_def
    have hmono_ls : logSlack cR n ≤ logSlack (c_strong + cR) n := logSlack_mono_left (by omega) n
    have hmono_ls2 : logSlack c_strong n ≤ logSlack (c_strong + cR) n :=
      logSlack_mono_left (by omega) n
    have ha_le : f N ≤ Nbnd := by omega
    have hs'_le : logSlack cR n ≤ Nbnd := by omega
    have hb_le : gseq N ≤ Nbnd := by
      have h := iter.h_capB N
      have h2 : plainSetComplexity V (iter.B_seq N) (iter.hB_seq N) ≤
          (n + logSlack cR n : ENat) := le_trans (le_add_of_nonneg_right (zero_le)) h
      rw [hgval N] at h2
      have h3 : gseq N ≤ n + logSlack cR n := by exact_mod_cast h2
      omega
    have hab : f N ≤ gseq N + n.sqrt := by omega
    have htau : gseq N ≤ f N + (logSlack cR n + logSlack c_fwd Nbnd) := by
      have h := h_fwd (codedUniformOn (iter.A_seq N) (iter.hA_seq N)).code
        (codedUniformOn (iter.B_seq N) (iter.hB_seq N)).code Nbnd (f N) (gseq N)
        (logSlack cR n) hHcode hBcode ha_le (iter.h_condB_A N)
      omega
    have hclose := h_close (codedUniformOn (iter.A_seq N) (iter.hA_seq N)).code
      (codedUniformOn (iter.B_seq N) (iter.hB_seq N)).code Nbnd (f N) (gseq N)
      n.sqrt (logSlack cR n + logSlack c_fwd Nbnd) (logSlack cR n)
      hHcode hBcode ha_le hb_le (iter.h_condB_A N) hs'_le hab htau (iter.h_condB_Omega N)
    refine le_trans hclose ?_
    have hNbnd_le : Nbnd ≤ (2 + c_strong + cR) * n + (c_strong + cR) := by
      have hbits : (Nat.bits n).length ≤ n := length_natBits_le_self n
      have hls : logSlack (c_strong + cR) n ≤ (c_strong + cR) * n + (c_strong + cR) := by
        unfold logSlack; gcongr
      have hdist : (2 + c_strong + cR) * n = 2 * n + (c_strong + cR) * n := by ring
      omega
    have hfwd_abs : logSlack c_fwd Nbnd ≤ logSlack C1 n :=
      le_trans (logSlack_mono_right c_fwd hNbnd_le) (hC1 n)
    have hclose_abs : logSlack c_close Nbnd ≤ logSlack C2 n :=
      le_trans (logSlack_mono_right c_close hNbnd_le) (hC2 n)
    have hs1 : n.sqrt ≤ c * n.sqrt := Nat.le_mul_of_pos_left n.sqrt hc_pos
    have hfinal : 4 * (logSlack cR n + logSlack c_fwd Nbnd) + n.sqrt +
        3 * logSlack cR n + logSlack c_close Nbnd ≤ c * n.sqrt + logSlack c n := by
      have h7 : 7 * logSlack cR n + 4 * logSlack C1 n + logSlack C2 n =
          logSlack (7 * cR + 4 * C1 + C2) n := by unfold logSlack; ring
      have hmono2 : logSlack (7 * cR + 4 * C1 + C2) n ≤ logSlack c n :=
        logSlack_mono_left hc3 n
      calc 4 * (logSlack cR n + logSlack c_fwd Nbnd) + n.sqrt +
            3 * logSlack cR n + logSlack c_close Nbnd
          ≤ 4 * (logSlack cR n + logSlack C1 n) + n.sqrt +
              3 * logSlack cR n + logSlack C2 n := by gcongr
        _ = n.sqrt + (7 * logSlack cR n + 4 * logSlack C1 n + logSlack C2 n) := by ring
        _ = n.sqrt + logSlack (7 * cR + 4 * C1 + C2) n := by rw [h7]
        _ ≤ c * n.sqrt + logSlack c n := Nat.add_le_add hs1 hmono2
    exact_mod_cast hfinal
  · -- Conclusion 4: complexity does not grow past `C(A) + alpha`
    rw [hfval N, haAval]
    have hc0 : f 0 ≤ aA + alpha := by
      have h := iter.h_comp_A0
      rw [hfval 0, haAval] at h
      exact_mod_cast h
    have : f N ≤ aA + alpha := le_trans hfN_le_f0 hc0
    exact_mod_cast this

/-- Frozen public endpoint for VS40 Lemma `lch`. -/
theorem lemma_lch
    (V T : Map) (hV : isOptimalConditional V)
    (hT : IsOptimalTotalConditional T) :
    LemmaLchStatement V T := by
  obtain ⟨c, hc⟩ := lemma_lch_with_mem V T hV hT
  refine ⟨c, ?_⟩
  intro x n A hA epsilon alpha q hq hxlen hxA hepsilon halpha hnormal
  obtain ⟨H, hH, hxH, hstrong, htwoPart, homega, hplain⟩ :=
    hc x n A hA epsilon alpha q hq hxlen hxA hepsilon halpha hnormal
  exact ⟨H, hH, hxH, hstrong, htwoPart, homega, hplain⟩

end Kolmogorov
