import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.InformationLogic.Formulas
import KolmogorovMathlib.Complexity.IncompressibleStrings.SplitDecompressors
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.CommonInformation.OverlapExtraction
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.NormalPair
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.Prefix.OptimalExistence

/-!
# Problem complexity and intuitionistic logic (SUV §13.2)

The "modus ponens" inequality `C(X ∧ Y) ≤ C(X) + C(X → Y) + O(log C(X))` and its failure in
the reverse direction (Problem 338), the invariance of formula problems under the choice of the
calculus (Problem 339) and Kleene's realizability of provable formulas (Problem 340), with the
corollaries used in the proof of Theorem 238.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus PFormula

/-- SUV Section 13.2, unnumbered claim (printed p. 403): `C(X ∧ Y) ≤ C(X) + C(X → Y)` with
precision `O(log C(X))` ("Moreover, we can add `Y` in the left-hand side"), the constant
depending on `D` and `P` only.
Proof: for minimal solutions `x ∈ X`, `p ∈ X → Y` the pair `[x, [p](x)]` solves `X ∧ Y` and is
computed from `⟨x, p⟩`, whose complexity is at most `C(x) + C(p) + O(log C(x))`
(`plainK_pair_le_add_two_log`).  For `C(X) = ⊤` the bound is trivial (`toNat ⊤ = 0` but the
right-hand side is `⊤`). -/
theorem problemK_conj_le_add_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString,
      problemK D (P.conj X Y) ≤
        problemK D X + problemK D (P.imp X Y) + (logSlack c (problemK D X).toNat : ℕ∞) := by
  obtain ⟨k, hk⟩ := plainK_pair_le_add_two_log D hD
  have hf : Partrec (fun z : BitString =>
      (P.lang (decodeSecond z, decodeFirst z)).map (P.pair (decodeFirst z))) := by
    have h1 : Partrec (fun z : BitString => P.lang (decodeSecond z, decodeFirst z)) :=
      hP.2.2.2.2.2.1.comp (decodeSecond_computable.pair decodeFirst_computable)
    refine Partrec.map h1 ?_
    exact hP.1.comp (decodeFirst_computable.comp Computable.fst) Computable.snd
  obtain ⟨cf, hcf⟩ := plainK_le_of_mem_partrec D hD _ hf
  refine ⟨cf + k + 2, fun X Y => ?_⟩
  by_cases hXt : problemK D X = ⊤
  · rw [hXt]; simp
  by_cases hIt : problemK D (P.imp X Y) = ⊤
  · rw [hIt]; simp
  have hXne : X.Nonempty := by
    rcases X.eq_empty_or_nonempty with rfl | h
    · exact absurd (problemK_empty D) hXt
    · exact h
  have hIne : (P.imp X Y).Nonempty := by
    rcases (P.imp X Y).eq_empty_or_nonempty with h | h
    · rw [h] at hIt; exact absurd (problemK_empty D) hIt
    · exact h
  obtain ⟨x, hx, hxeq⟩ := exists_mem_plainK_eq_problemK D hXne
  obtain ⟨p, hp, hpeq⟩ := exists_mem_plainK_eq_problemK D hIne
  obtain ⟨y, hy, hy'⟩ := hp x hx
  have hmem : P.pair x y ∈ P.conj X Y := Set.mem_image2_of_mem hx hy
  have hyf : P.pair x y ∈
      (P.lang (decodeSecond (pairCode x p), decodeFirst (pairCode x p))).map
        (P.pair (decodeFirst (pairCode x p))) := by
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_map _ hy'
  have h1 := hcf _ _ hyf
  have h2 := hk x p
  set m := (problemK D X).toNat with hm
  have hmx : (cVal D x : ℕ) = m := by
    simp [cVal, hxeq, hm]
  have hlog : Nat.log 2 m ≤ (Nat.bits m).length := by
    rw [Nat.size_eq_bits_len]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact (Nat.log_lt_of_lt_pow h0.ne' (Nat.lt_size_self m)).le
  have hkk : 2 * Nat.log 2 m + (cf + k) ≤ logSlack (cf + k + 2) m := by
    unfold logSlack; nlinarith
  calc problemK D (P.conj X Y) ≤ plainK D (P.pair x y) := problemK_le_of_mem D hmem
    _ ≤ plainK D (pairCode x p) + (cf : ℕ∞) := h1
    _ ≤ (plainK D x + plainK D p + ((2 * Nat.log 2 (cVal D x) + k : ℕ) : ℕ∞)) + (cf : ℕ∞) := by
        gcongr; exact h2
    _ = problemK D X + problemK D (P.imp X Y) +
          ((2 * Nat.log 2 m + (cf + k) : ℕ) : ℕ∞) := by
        rw [hmx, hxeq, hpeq]; push_cast; ring
    _ ≤ problemK D X + problemK D (P.imp X Y) + (logSlack (cf + k + 2) m : ℕ∞) := by
        gcongr

/-- SUV Section 13.2, unnumbered claim (printed p. 403): the same inequality
`C(X ∧ Y) ≤ C(X) + C(X → Y)` with the alternative precision `O(log C(X → Y))` mentioned by the
book ("or `O(log C(X → Y))`").  Proof: as for `problemK_conj_le_add_imp`, but code a shortest
description of the program `p` self-delimitingly instead of the one of the solution `x`. -/
theorem problemK_conj_le_add_imp_log_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString,
      problemK D (P.conj X Y) ≤
        problemK D X + problemK D (P.imp X Y) +
          (logSlack c (problemK D (P.imp X Y)).toNat : ℕ∞) := by
  obtain ⟨k, hk⟩ := plainK_pair_le_add_two_log D hD
  have hf : Partrec (fun z : BitString =>
      (P.lang (decodeFirst z, decodeSecond z)).map (fun y => P.pair (decodeSecond z) y)) := by
    have h1 : Partrec (fun z : BitString => P.lang (decodeFirst z, decodeSecond z)) :=
      hP.2.2.2.2.2.1.comp (decodeFirst_computable.pair decodeSecond_computable)
    exact Partrec.map h1 (hP.1.comp (decodeSecond_computable.comp Computable.fst) Computable.snd)
  obtain ⟨c0, hc0⟩ := plainK_le_of_mem_partrec D hD _ hf
  refine ⟨2 + k + c0, fun X Y => ?_⟩
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp
  rcases (P.imp X Y).eq_empty_or_nonempty with hI | hI
  · rw [hI]; simp
  obtain ⟨x, hx, hxeq⟩ := exists_mem_plainK_eq_problemK D hX
  obtain ⟨p, hp, hpeq⟩ := exists_mem_plainK_eq_problemK D hI
  obtain ⟨y, hy, hy'⟩ := hp x hx
  have hmem : P.pair x y ∈ P.conj X Y := Set.mem_image2_of_mem hx hy
  have h1 : plainK D (P.pair x y) ≤ plainK D (pairCode p x) + (c0 : ℕ∞) := by
    apply hc0
    simp only [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_map_iff _ |>.2 ⟨y, hy', rfl⟩
  have h2 : plainK D (pairCode p x) ≤ plainK D p + plainK D x +
      ((2 * Nat.log 2 (cVal D p) + k : ℕ) : ℕ∞) := hk p x
  have hcv : cVal D p = (problemK D (P.imp X Y)).toNat := by
    unfold cVal; rw [hpeq]
  set m := (problemK D (P.imp X Y)).toNat with hm
  have hlog : 2 * Nat.log 2 (cVal D p) + k ≤ logSlack (2 + k) m := by
    rw [hcv]
    have : Nat.log 2 m ≤ (Nat.bits m).length := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · simp [h0]
      · rw [Nat.size_eq_bits_len]
        exact (Nat.log_lt_of_lt_pow h0.ne' (Nat.lt_size_self m)).le
    unfold logSlack
    nlinarith
  have hlog' : ((2 * Nat.log 2 (cVal D p) + k : ℕ) : ℕ∞) ≤ (logSlack (2 + k) m : ℕ∞) := by
    exact_mod_cast hlog
  have hsl : (logSlack (2 + k) m : ℕ∞) + (c0 : ℕ∞) ≤ (logSlack (2 + k + c0) m : ℕ∞) := by
    have : logSlack (2 + k) m + c0 ≤ logSlack (2 + k + c0) m := by
      rw [logSlack_add_constants]
      unfold logSlack
      nlinarith [Nat.zero_le (c0 * (Nat.bits m).length)]
    exact_mod_cast this
  calc problemK D (P.conj X Y) ≤ plainK D (P.pair x y) := problemK_le_of_mem D hmem
    _ ≤ plainK D (pairCode p x) + (c0 : ℕ∞) := h1
    _ ≤ plainK D p + plainK D x + (logSlack (2 + k) m : ℕ∞) + (c0 : ℕ∞) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = problemK D X + problemK D (P.imp X Y) + ((logSlack (2 + k) m : ℕ∞) + (c0 : ℕ∞)) := by
        rw [hxeq, hpeq]; ring
    _ ≤ problemK D X + problemK D (P.imp X Y) + (logSlack (2 + k + c0) m : ℕ∞) := by gcongr

/-- SUV Section 13.2, unnumbered claim (printed p. 403): `C(Y) ≤ C(X) + C(X → Y) + O(log C(X))`
("if both problems `X` and `X → Y` are simple, then `Y` is simple, too"), generalizing
`C(y) ≤ C(x) + C(y|x)`.  Book's idea: a solution `x` of `X` and a solution `p` of `X → Y` give
the solution `[p](x)` of `Y`.  Here derived from `problemK_conj_le_add_imp` and
`problemK_right_le_conj`. -/
theorem problemK_le_add_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString,
      problemK D Y ≤
        problemK D X + problemK D (P.imp X Y) + (logSlack c (problemK D X).toNat : ℕ∞) := by
  obtain ⟨c, hc⟩ := problemK_conj_le_add_imp D hD P hP
  obtain ⟨c1, hc1⟩ := problemK_right_le_conj D hD P hP
  refine ⟨c + c1, fun X Y => ?_⟩
  set m := (problemK D X).toNat
  have hL : ((logSlack c m : ℕ) : ℕ∞) + c1 ≤ (logSlack (c + c1) m : ℕ) := by
    rw [logSlack_add_constants]
    push_cast
    gcongr
    exact_mod_cast (show c1 ≤ c1 * (Nat.bits m).length + c1 from Nat.le_add_left _ _)
  calc problemK D Y ≤ problemK D (P.conj X Y) + c1 := hc1 X Y
    _ ≤ problemK D X + problemK D (P.imp X Y) + (logSlack c m : ℕ∞) + c1 := by
        gcongr; exact hc X Y
    _ = problemK D X + problemK D (P.imp X Y) + ((logSlack c m : ℕ∞) + c1) := by ring
    _ ≤ problemK D X + problemK D (P.imp X Y) + (logSlack (c + c1) m : ℕ∞) := by gcongr

/-- Step 1 of the proof of `exists_problemK_conj_add_le_add_imp`: the lower bound for
the programs of `X → Y` of complexity at least `n` ("prefix case").  Here
`X = {x | |x| = n, n ≤ C(x) + logSlack a n}` (the strings of length `n` of deficiency
`O(log n)`) and `Y = {y | |y| = 2n, 2n ≤ C(y)}` (the incompressible strings of length `2n`).
For `a` at least a constant `a0` (depending on `D` only), every `p ∈ X → Y` with `C(p) ≥ n`
satisfies `2n ≤ C(p) + O(log n)`.
Proof: if `C(p) ≥ 2n` there is nothing to prove.  Otherwise let `q` be a shortest program of `p`,
`n ≤ |q| < 2n`, so `C(q) ≥ |q| - O(1)`.  The first `n` bits `x` of `q` form a string of `X`
(`C(q) ≤ C(x) + (|q| - n) + O(log n)`, so `C(x) ≥ n - O(log n)`), and `y ∈ [p](x) ∩ Y` is
computed from `q` and `n`, so `2n ≤ C(y) ≤ |q| + O(log n) = C(p) + O(log n)`. -/
private theorem exists_problemK_conj_add_le_add_imp_prefix_case (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ a0 c : ℕ, ∀ a : ℕ, a0 ≤ a → ∀ (n : ℕ) (p : BitString),
      p ∈ P.imp {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞)}
          {y : BitString | y.length = 2 * n ∧ ((2 * n : ℕ) : ℕ∞) ≤ plainK D y} →
        (n : ℕ∞) ≤ plainK D p →
          ((2 * n : ℕ) : ℕ∞) ≤ plainK D p + (logSlack c n : ℕ∞) := by
  obtain ⟨c0, hc0⟩ := plainK_le_of_mem_partrec D hD (fun q => D (q, []))
    (hD.1.comp (Computable.pair Computable.id (Computable.const [])))
  obtain ⟨cLen, hLen⟩ := plainK_le_length D hD
  obtain ⟨cThree, hThree⟩ := plainK_threeBlock_le D hD
  obtain ⟨cAbs, hAbs⟩ := logSlack_absorb_of_le_linear cThree 2 1
  have hf : Partrec (fun z : BitString × (ℕ × Bool) =>
      (D (z.1, [])).bind (fun p => P.lang (p, z.1.take z.2.1))) := by
    have hg : Computable (fun x : (BitString × (ℕ × Bool)) × BitString =>
        (x.2, x.1.1.take x.1.2.1)) :=
      Computable.pair Computable.snd
        (Primrec.list_take.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.fst)).to_comp
    exact Partrec.bind (hD.1.comp (Computable.pair Computable.fst (Computable.const [])))
      (Partrec.comp hP.2.2.2.2.2.1 hg).to₂
  obtain ⟨c1, hc1⟩ := problemK_le_of_partrec_advice D hD _ hf
  refine ⟨c0 + cAbs, c1 + cLen, fun a ha n p hp hpn => ?_⟩
  by_cases h2n : ((2 * n : ℕ) : ℕ∞) ≤ plainK D p
  · exact h2n.trans le_self_add
  have hlt : plainK D p < ((2 * n : ℕ) : ℕ∞) := not_le.1 h2n
  obtain ⟨kp, hkp⟩ := exists_plainComplexityValue D hD p
  obtain ⟨q, hq, hqlen⟩ := hkp.exists_program
  have hkp' : plainK D p = (kp : ℕ∞) := hkp
  rw [hkp'] at hlt hpn
  have hkp2 : kp < 2 * n := by exact_mod_cast hlt
  have hnkp : n ≤ kp := by exact_mod_cast hpn
  obtain ⟨kq, hkq⟩ := exists_plainComplexityValue D hD q
  obtain ⟨kx, hkx⟩ := exists_plainComplexityValue D hD (q.take n)
  have hkq' : plainK D q = (kq : ℕ∞) := hkq
  have hkx' : plainK D (q.take n) = (kx : ℕ∞) := hkx
  have h1 : kp ≤ kq + c0 := by
    have := hc0 q p hq
    rw [hkp', hkq'] at this
    exact_mod_cast this
  have h3 : kq ≤ kx + (0 + (kp - n) + logSlack cThree (kp + 1)) := by
    have := hThree [] (q.take n) (q.drop n)
    simp only [List.nil_append, List.take_append_drop, List.length_nil, List.length_drop,
      hqlen] at this
    rw [hkq', hkx'] at this
    exact_mod_cast this
  have h4 : logSlack cThree (kp + 1) ≤ logSlack cAbs n := hAbs n (kp + 1) (by omega)
  have h5 : logSlack cAbs n + c0 ≤ logSlack a n := by
    unfold logSlack
    nlinarith
  have hxn : n ≤ kx + logSlack a n := by omega
  have hxX : q.take n ∈ {x : BitString | x.length = n ∧
      (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞)} := by
    refine ⟨by rw [List.length_take]; omega, ?_⟩
    rw [hkx']
    exact_mod_cast hxn
  obtain ⟨y, hyY, hy⟩ := hp _ hxX
  have hy2 := hc1 {q} {y} n (fun q' hq' => ⟨false, y, rfl, by
    rw [Set.mem_singleton_iff] at hq'
    subst hq'
    exact Part.mem_bind_iff.2 ⟨p, hq, hy⟩⟩)
  simp only [problemK_singleton] at hy2
  have hqK : plainK D q ≤ (kp : ℕ∞) + (cLen : ℕ∞) := by
    have := hLen q
    simpa [programLength, hqlen] using this
  have h6 : kp + cLen + logSlack c1 n ≤ kp + logSlack (c1 + cLen) n := by
    unfold logSlack
    nlinarith
  calc ((2 * n : ℕ) : ℕ∞) ≤ plainK D y := hyY.2
    _ ≤ plainK D q + (logSlack c1 n : ℕ∞) := hy2
    _ ≤ ((kp : ℕ∞) + (cLen : ℕ∞)) + (logSlack c1 n : ℕ∞) := by gcongr
    _ ≤ plainK D p + (logSlack (c1 + cLen) n : ℕ∞) := by
        rw [hkp']
        exact_mod_cast h6

/-- Step 1 of the proof of `exists_problemK_conj_add_le_add_imp_padding_case`:
a shortest program of a string is incompressible.  For every `p` with `C(p) = m` there is a
program `q` of length `m` with `p ∈ D (q, [])` and `m ≤ C(q) + c` (`p` is computable from `q`,
so `C(p) ≤ C(q) + O(1)`), the constant `c` depending on `D` only. -/
private theorem exists_problemK_conj_add_le_add_imp_shortest_program
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (p : BitString) (m : ℕ), plainK D p = (m : ℕ∞) →
      ∃ q : BitString, q.length = m ∧ p ∈ D (q, []) ∧ (m : ℕ∞) ≤ plainK D q + (c : ℕ∞) := by
  have hf : Partrec (fun q : BitString => D (q, [])) :=
    hD.1.comp (Computable.id.pair (Computable.const []))
  obtain ⟨c, hc⟩ := plainK_le_of_mem_partrec D hD _ hf
  refine ⟨c, fun p m hm => ?_⟩
  obtain ⟨q, hq, hqlen⟩ := exists_program_le_cVal D hD p
  have hcv : cVal D p = m := by unfold cVal; rw [hm]; rfl
  have hle : plainK D p ≤ (q.length : ℕ∞) := sInf_le ⟨q, hq, rfl⟩
  rw [hm] at hle
  have : q.length = m := by
    have h1 : m ≤ q.length := by exact_mod_cast hle
    omega
  refine ⟨q, this, hq, ?_⟩
  have := hc q p hq
  rwa [hm] at this

/-- Step 2 of the proof of `exists_problemK_conj_add_le_add_imp_padding_case`:
symmetry of information for a conditionally random tail.  If `|q| + |r| = n` and
`C(r | q) ≥ |r|`, then `C(q) + |r| ≤ C(⟨q, r⟩) + O(log n)`
(`plainK_pair_ge_plainK_add_length_of_random_budget` with `epsilon = 0`), the constant
depending on `D` only. -/
private theorem exists_problemK_conj_add_le_add_imp_symmetry
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (q r : BitString) (n : ℕ), q.length + r.length = n →
      (r.length : ℕ∞) ≤ condK D r q →
        plainK D q + (r.length : ℕ∞) ≤ plainK D (pairCode q r) + (logSlack c n : ℕ∞) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := plainK_pair_ge_plainK_add_length_of_random D U hD hU
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  refine ⟨c, fun q r n hn hr => ?_⟩
  obtain ⟨kx, hkx⟩ : ∃ k : ℕ, plainK D q = (k : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_natCast_add (hcl q))).symm⟩
  obtain ⟨kxy, hkxy⟩ : ∃ k : ℕ, plainK D (pairCode q r) = (k : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_natCast_add (hcl (pairCode q r)))).symm⟩
  have h := hc q r 0 kx kxy hkx hkxy (by simpa using hr)
  rw [hn] at h
  rw [hkx, hkxy]
  exact_mod_cast h

/-- Step 5 of the proof of `exists_problemK_conj_add_le_add_imp_padding_case`:
the pair `⟨x, bits m⟩` costs `O(log n)` bits more than `x`: for `|x| ≤ n` and `m ≤ n`,
`C(⟨x, bits m⟩) ≤ C(x) + O(log n)`, the constant depending on `D` only
(`plainK_pair_le_plainK_add_length` and `|bits m| ≤ |bits n|`). -/
private theorem exists_problemK_conj_add_le_add_imp_pair_advice
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (x : BitString) (m n : ℕ), x.length ≤ n → m ≤ n →
      plainK D (pairCode x (Nat.bits m)) ≤ plainK D x + (logSlack c n : ℕ∞) := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := plainK_pair_le_plainK_add_length D U hD hU
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  refine ⟨1 + 2 * c, fun x m n hx hm => ?_⟩
  obtain ⟨kx, hkx⟩ : ∃ k : ℕ, plainK D x = (k : ℕ∞) :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_natCast_add (hcl x))).symm⟩
  have h := hc x (Nat.bits m) kx hkx
  have hy1 : (Nat.bits m).length ≤ (Nat.bits n).length := length_natBits_mono hm
  have hy2 : (Nat.bits m).length ≤ n := (length_natBits_le m).trans hm
  have hs : logSlack c (x.length + (Nat.bits m).length) ≤ logSlack (2 * c) n := by
    calc logSlack c (x.length + (Nat.bits m).length) ≤ logSlack c (n + n) :=
          logSlack_mono_right c (by omega)
      _ ≤ logSlack c n + logSlack c n := logSlack_add_le c n n
      _ = logSlack (2 * c) n := by unfold logSlack; ring
  have hk : (Nat.bits m).length + logSlack (2 * c) n ≤ logSlack (1 + 2 * c) n := by
    rw [logSlack_add_constants]
    unfold logSlack
    omega
  calc plainK D (pairCode x (Nat.bits m))
      ≤ ((kx + (Nat.bits m).length + logSlack c (x.length + (Nat.bits m).length) : ℕ) : ℕ∞) := h
    _ ≤ ((kx + logSlack (1 + 2 * c) n : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
    _ = plainK D x + (logSlack (1 + 2 * c) n : ℕ∞) := by rw [hkx]; push_cast; rfl

/-- Step 3 of the proof of `exists_problemK_conj_add_le_add_imp_padding_case`:
the pair `⟨q, r⟩` is computable from the concatenation `q r` and the length `|q|`:
for `|q| + |r| ≤ n`, `C(⟨q, r⟩) ≤ C(q r) + O(log n)`, the constant depending on `D` only
(code `|q|` self-delimitingly, apply the computable map
`⟨x, bits m⟩ ↦ ⟨x.take m, x.drop m⟩`, and use Step 5). -/
private theorem exists_problemK_conj_add_le_add_imp_concat_advice
    (D : Map) (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ (q r : BitString) (n : ℕ), q.length + r.length ≤ n →
      plainK D (pairCode q r) ≤ plainK D (q ++ r) + (logSlack c n : ℕ∞) := by
  obtain ⟨c5, h5⟩ :=
    exists_problemK_conj_add_le_add_imp_pair_advice D hD
  have hf : Computable (fun z : BitString =>
      pairCode ((decodeFirst z).take (decodeBits (decodeSecond z)))
        ((decodeFirst z).drop (decodeBits (decodeSecond z)))) := by
    have hm : Computable (fun z : BitString => decodeBits (decodeSecond z)) :=
      decodeBits_computable.comp decodeSecond_computable
    have h1 : Computable (fun z : BitString =>
        (decodeFirst z).take (decodeBits (decodeSecond z))) :=
      Primrec.list_take.to_comp.comp hm decodeFirst_computable
    have h2 : Computable (fun z : BitString =>
        (decodeFirst z).drop (decodeBits (decodeSecond z))) :=
      Primrec.list_drop.to_comp.comp hm decodeFirst_computable
    exact (pairCode_computable.comp (h1.pair h2)).of_eq (fun z => rfl)
  obtain ⟨c0, h0⟩ := plainK_map_le D hD _ hf
  refine ⟨c5 + c0, fun q r n hn => ?_⟩
  have hx := h0 (pairCode (q ++ r) (Nat.bits q.length))
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
    List.take_left', List.drop_left'] at hx
  have h5' := h5 (q ++ r) q.length n (by rw [List.length_append]; exact hn) (by omega)
  calc plainK D (pairCode q r)
      ≤ plainK D (pairCode (q ++ r) (Nat.bits q.length)) + (c0 : ℕ∞) := hx
    _ ≤ plainK D (q ++ r) + (logSlack c5 n : ℕ∞) + (c0 : ℕ∞) := by gcongr
    _ = plainK D (q ++ r) + ((logSlack c5 n + c0 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ plainK D (q ++ r) + (logSlack (c5 + c0) n : ℕ∞) := by
        gcongr; exact_mod_cast logSlack_add_nat_le c5 c0 n

/-- Step 4 of the proof of `exists_problemK_conj_add_le_add_imp_padding_case`:
evaluating the program coded in the prefix of `x`.  If `p ∈ D (x.take m, [])` and
`y ∈ [p](x)` then `C(y) ≤ C(⟨x, bits m⟩) + O(1)` (a fixed partial computable map takes the
prefix of `x` of length `m`, decodes `p` with `D` and applies it to `x`, using `P.lang`), the
constant depending on `D` and `P` only. -/
private theorem exists_problemK_conj_add_le_add_imp_eval
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ (x p y : BitString) (m : ℕ),
      p ∈ D (x.take m, []) → y ∈ P.lang (p, x) →
        plainK D y ≤ plainK D (pairCode x (Nat.bits m)) + (c : ℕ∞) := by
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  have hf : Partrec (fun z : BitString =>
      (D ((decodeFirst z).take (decodeBits (decodeSecond z)), [])).bind
        (fun p => P.lang (p, decodeFirst z))) := by
    have hm : Computable (fun z : BitString => decodeBits (decodeSecond z)) :=
      decodeBits_computable.comp decodeSecond_computable
    have h1 : Computable (fun z : BitString =>
        (decodeFirst z).take (decodeBits (decodeSecond z))) :=
      Primrec.list_take.to_comp.comp hm decodeFirst_computable
    refine Partrec.bind (hD.1.comp (h1.pair (Computable.const []))) ?_
    exact (hL.comp (Computable.snd.pair (decodeFirst_computable.comp Computable.fst))).to₂
  obtain ⟨c, hc⟩ := plainK_le_of_mem_partrec D hD _ hf
  refine ⟨c, fun x p y m hp hy => hc _ _ ?_⟩
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits]
  exact Part.mem_bind_iff.2 ⟨p, hp, hy⟩

/-- Step 2 of the proof of `exists_problemK_conj_add_le_add_imp`: no program of `X → Y`
(same `X`, `Y` as in Step 1) has complexity below `n` ("padding case").
For `a` at least a constant `a0` (depending on `D` only), if `p ∈ X → Y` and `C(p) < n` then
`n ≤ logSlack c n`, that is, `n = O(log n)` (so only boundedly many `n` can occur).
Proof: let `q` be a shortest program of `p`, `|q| = C(p) < n`, `C(q) ≥ |q| - O(1)`.  Pad it with
`r`, `|r| = n - |q|`, `C(r | q) ≥ |r|` (counting, `exists_incompressible_string`).  Then
`C(⟨q, r⟩) ≥ C(q) + C(r | q) - O(log n) ≥ n - O(log n)`, hence `x = q r` has `C(x) ≥ n - O(log n)`
and lies in `X`.  A string `y ∈ [p](x) ∩ Y` is computed from `x` and `|q|` (take the prefix
`q` of `x`, decode `p`, apply it to `x`), so `2n ≤ C(y) ≤ C(x) + O(log n) ≤ n + O(log n)`. -/
private theorem exists_problemK_conj_add_le_add_imp_padding_case (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ a0 c : ℕ, ∀ a : ℕ, a0 ≤ a → ∀ (n : ℕ) (p : BitString),
      p ∈ P.imp {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞)}
          {y : BitString | y.length = 2 * n ∧ ((2 * n : ℕ) : ℕ∞) ≤ plainK D y} →
        plainK D p < (n : ℕ∞) → n ≤ logSlack c n := by
  obtain ⟨c1, h1⟩ :=
    exists_problemK_conj_add_le_add_imp_shortest_program D hD
  obtain ⟨c2, h2⟩ := exists_problemK_conj_add_le_add_imp_symmetry D hD
  obtain ⟨c3, h3⟩ :=
    exists_problemK_conj_add_le_add_imp_concat_advice D hD
  obtain ⟨c4, h4⟩ := exists_problemK_conj_add_le_add_imp_eval D hD P hP
  obtain ⟨c5, h5⟩ :=
    exists_problemK_conj_add_le_add_imp_pair_advice D hD
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  refine ⟨c1 + c2 + c3, cl + c4 + c5, fun a ha n p hp hlt => ?_⟩
  -- the complexity of `p` is a natural number `m < n`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, plainK D p = (m : ℕ∞) :=
    ⟨(plainK D p).toNat, (ENat.natCast_toNat (ne_top_of_lt hlt)).symm⟩
  have hmn : m < n := by rw [hm] at hlt; exact_mod_cast hlt
  obtain ⟨q, hqlen, hpq, hqK⟩ := h1 p m hm
  obtain ⟨r, hrlen, hrK⟩ := exists_incompressible_string D q (n - m)
  set x : BitString := q ++ r with hx
  have hxlen : x.length = n := by
    rw [hx, List.length_append, hqlen, hrlen]; omega
  -- `x` lies in `X`
  have hs2 := h2 q r n (by rw [hqlen, hrlen]; omega) (by rw [hrlen]; exact hrK)
  have hs3 := h3 q r n (by rw [hqlen, hrlen]; omega)
  have hxX : (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞) := by
    have hsl : c1 + logSlack c2 n + logSlack c3 n ≤ logSlack a n := by
      have : logSlack (c1 + c2 + c3) n ≤ logSlack a n := logSlack_mono_left ha n
      rw [logSlack_add_constants, logSlack_add_constants] at this
      unfold logSlack at this ⊢
      nlinarith [Nat.zero_le ((Nat.bits n).length)]
    have hsl' : (c1 : ℕ∞) + (logSlack c2 n : ℕ∞) + (logSlack c3 n : ℕ∞) ≤
        (logSlack a n : ℕ∞) := by exact_mod_cast hsl
    have hnm : (n : ℕ∞) = (m : ℕ∞) + ((n - m : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]; congr 1; omega
    calc (n : ℕ∞) = (m : ℕ∞) + ((n - m : ℕ) : ℕ∞) := hnm
      _ ≤ (plainK D q + (c1 : ℕ∞)) + (r.length : ℕ∞) := by rw [hrlen]; gcongr
      _ = (plainK D q + (r.length : ℕ∞)) + (c1 : ℕ∞) := by ring
      _ ≤ (plainK D (pairCode q r) + (logSlack c2 n : ℕ∞)) + (c1 : ℕ∞) := by gcongr
      _ ≤ ((plainK D x + (logSlack c3 n : ℕ∞)) + (logSlack c2 n : ℕ∞)) + (c1 : ℕ∞) := by
          gcongr
      _ = plainK D x + ((c1 : ℕ∞) + (logSlack c2 n : ℕ∞) + (logSlack c3 n : ℕ∞)) := by ring
      _ ≤ plainK D x + (logSlack a n : ℕ∞) := by gcongr
  have hxmem : x ∈ {x : BitString | x.length = n ∧
      (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞)} := ⟨hxlen, hxX⟩
  obtain ⟨y, hyY, hyp⟩ := hp x hxmem
  have hq : x.take m = q := by
    rw [hx, ← hqlen]; exact List.take_left
  have hy := h4 x p y m (by rw [hq]; exact hpq) hyp
  have hpair := h5 x m n hxlen.le hmn.le
  have hxC : plainK D x ≤ (n : ℕ∞) + (cl : ℕ∞) := by
    have := hcl x
    simpa [programLength, hxlen] using this
  have h2n : ((2 * n : ℕ) : ℕ∞) ≤ plainK D y := hyY.2
  have hnat : 2 * n ≤ n + cl + c4 + logSlack c5 n := by
    have : ((2 * n : ℕ) : ℕ∞) ≤ ((n + cl + c4 + logSlack c5 n : ℕ) : ℕ∞) := by
      calc ((2 * n : ℕ) : ℕ∞) ≤ plainK D y := h2n
        _ ≤ plainK D (pairCode x (Nat.bits m)) + (c4 : ℕ∞) := hy
        _ ≤ (plainK D x + (logSlack c5 n : ℕ∞)) + (c4 : ℕ∞) := by gcongr
        _ ≤ ((n : ℕ∞) + (cl : ℕ∞) + (logSlack c5 n : ℕ∞)) + (c4 : ℕ∞) := by gcongr
        _ = ((n + cl + c4 + logSlack c5 n : ℕ) : ℕ∞) := by push_cast; ring
    exact_mod_cast this
  have : logSlack c5 n ≤ logSlack (cl + c4 + c5) n := logSlack_mono_left (by omega) n
  have hk : logSlack (cl + c4 + c5) n = logSlack (cl + c4) n + logSlack c5 n := by
    rw [logSlack_add_constants]
  have hk2 : cl + c4 ≤ logSlack (cl + c4) n := by
    unfold logSlack; nlinarith [Nat.zero_le ((cl + c4) * (Nat.bits n).length)]
  omega

/-- SUV Problem 338 (Section 13.2, printed p. 403): there are problems `X`, `Y` such that
`C(X ∧ Y)` is significantly less than `C(X) + C(X → Y)`.  Reading: a linear gap at the scale
of the solutions — for every `n` there are nonempty `X`, `Y` whose solutions have length
`O(n)` with `C(X ∧ Y) + n ≤ C(X) + C(X → Y) + O(log n)`.  The length bound is essential: for
strings of length `O(n)` the reverse inequality holds for singletons up to `O(log n)`
(symmetry of information), while without it singletons of huge complexity would satisfy the
inequality trivially.  (Nonempty `X`, `Y` make both sides finite.)
Hint (book): `X` = the incompressible strings of length `n`, `Y` = the incompressible strings of
length `2n` ("incompressible" with deficiency `O(log n)`); then `C(X) ≈ n`, `C(X ∧ Y) ≈ 2n`
(take `x` a half of a random `y`), and `C(X → Y) ≈ 2n` (feed a solution `p` the first `n` bits of
a shortest program of `p`, a string of `X` whose image has complexity at most `C(p) + O(1)`; if
`C(p) < n`, pad that shortest program with bits random relative to it, and the image has
complexity `n + O(log n) < 2n`, a contradiction). -/
theorem exists_problemK_conj_add_le_add_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c k : ℕ, ∀ n : ℕ, ∃ X Y : Set BitString,
      X.Nonempty ∧ Y.Nonempty ∧ (∀ s ∈ X, s.length ≤ c * (n + 1)) ∧
        (∀ s ∈ Y, s.length ≤ c * (n + 1)) ∧
        problemK D (P.conj X Y) + (n : ℕ∞) ≤
          problemK D X + problemK D (P.imp X Y) + (logSlack k n : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := plainK_halves_of_incompressible D hD
  obtain ⟨a1, e1, h1⟩ := exists_problemK_conj_add_le_add_imp_prefix_case D hD P hP
  obtain ⟨a2, e2, h2⟩ := exists_problemK_conj_add_le_add_imp_padding_case D hD P hP
  obtain ⟨cl, hcl⟩ := plainK_le_length D hD
  have hf : Computable (fun y : BitString => P.pair (y.take (y.length / 2)) y) :=
    hP.1.comp ((Primrec.list_take.comp (Primrec.nat_div.comp Primrec.list_length
      (Primrec.const 2)) Primrec.id).to_comp) Computable.id
  obtain ⟨cm, hcm⟩ := plainK_map_le D hD _ hf
  set a := max (max c1 a1) a2 with ha
  have ha1 : a1 ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
  have ha2 : a2 ≤ a := le_max_right _ _
  have hac1 : c1 ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  refine ⟨2, a + (e1 + 2 * e2) + (cl + cm), fun n => ?_⟩
  -- the problems
  set X : Set BitString :=
    {x : BitString | x.length = n ∧ (n : ℕ∞) ≤ plainK D x + (logSlack a n : ℕ∞)} with hX
  set Y : Set BitString :=
    {y : BitString | y.length = 2 * n ∧ ((2 * n : ℕ) : ℕ∞) ≤ plainK D y} with hY
  obtain ⟨y, hylen, hyK⟩ := exists_incompressible_string D [] (2 * n)
  have hyK' : ((2 * n : ℕ) : ℕ∞) ≤ plainK D y := hyK
  have hyY : y ∈ Y := ⟨hylen, hyK'⟩
  have hxlen : (y.take n).length = n := by
    rw [List.length_take, hylen]; omega
  have hac : (c1 : ℕ∞) ≤ (logSlack a n : ℕ∞) := by
    have : c1 ≤ logSlack a n := le_trans hac1 (Nat.le_add_left _ _)
    exact_mod_cast this
  have hxX : y.take n ∈ X := by
    refine ⟨hxlen, ?_⟩
    exact (hc1 n y hylen hyK').1.trans (by gcongr)
  -- a general lower bound principle
  have key : ∀ (S : Set BitString) (m : ℕ∞) (t : ℕ∞),
      (∀ s ∈ S, m ≤ plainK D s + t) → m ≤ problemK D S + t := by
    intro S m t hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨s, hs, hseq⟩ := exists_mem_plainK_eq_problemK D hne
    rw [← hseq]; exact hS s hs
  -- lower bound for `X`
  have hXlow : (n : ℕ∞) ≤ problemK D X + (logSlack a n : ℕ∞) :=
    key X _ _ (fun s hs => hs.2)
  -- lower bound for `X → Y`
  have hIlow : ((2 * n : ℕ) : ℕ∞) ≤ problemK D (P.imp X Y) + (logSlack (e1 + 2 * e2) n : ℕ∞) := by
    refine key _ _ _ (fun p hp => ?_)
    by_cases hpn : (n : ℕ∞) ≤ plainK D p
    · have := h1 a ha1 n p hp hpn
      exact this.trans (by gcongr; exact_mod_cast logSlack_mono_left (Nat.le_add_right _ _) n)
    · have hlt : plainK D p < (n : ℕ∞) := not_le.1 hpn
      have h3 := h2 a ha2 n p hp hlt
      have h4 : 2 * n ≤ logSlack (e1 + 2 * e2) n := by
        calc 2 * n ≤ 2 * logSlack e2 n := by omega
          _ = logSlack (2 * e2) n := by unfold logSlack; ring
          _ ≤ logSlack (e1 + 2 * e2) n := logSlack_mono_left (Nat.le_add_left _ _) n
      calc ((2 * n : ℕ) : ℕ∞) ≤ (logSlack (e1 + 2 * e2) n : ℕ∞) := by exact_mod_cast h4
        _ ≤ plainK D p + (logSlack (e1 + 2 * e2) n : ℕ∞) := le_add_self
  -- upper bound for `X ∧ Y`
  have hconj : problemK D (P.conj X Y) ≤ ((2 * n + (cl + cm) : ℕ) : ℕ∞) := by
    have hmem : P.pair (y.take n) y ∈ P.conj X Y := Set.mem_image2_of_mem hxX hyY
    have hdiv : y.length / 2 = n := by rw [hylen]; omega
    have h5 := hcm y
    simp only [hdiv] at h5
    have h6 : plainK D y ≤ ((2 * n : ℕ) : ℕ∞) + (cl : ℕ∞) := by
      have := hcl y
      simpa [programLength, hylen] using this
    calc problemK D (P.conj X Y) ≤ plainK D (P.pair (y.take n) y) := problemK_le_of_mem D hmem
      _ ≤ plainK D y + (cm : ℕ∞) := h5
      _ ≤ ((2 * n : ℕ) : ℕ∞) + (cl : ℕ∞) + (cm : ℕ∞) := by gcongr
      _ = ((2 * n + (cl + cm) : ℕ) : ℕ∞) := by push_cast; ring
  refine ⟨X, Y, ⟨_, hxX⟩, ⟨_, hyY⟩, ?_, ?_, ?_⟩
  · intro s hs; rw [hs.1]; omega
  · intro s hs; rw [hs.1]; omega
  · have hk : logSlack a n + logSlack (e1 + 2 * e2) n + (cl + cm) ≤
        logSlack (a + (e1 + 2 * e2) + (cl + cm)) n := by
      unfold logSlack; nlinarith
    have hk' : (logSlack a n : ℕ∞) + (logSlack (e1 + 2 * e2) n : ℕ∞) + ((cl + cm : ℕ) : ℕ∞) ≤
        (logSlack (a + (e1 + 2 * e2) + (cl + cm)) n : ℕ∞) := by exact_mod_cast hk
    calc problemK D (P.conj X Y) + (n : ℕ∞)
        ≤ ((2 * n + (cl + cm) : ℕ) : ℕ∞) + (n : ℕ∞) := by gcongr
      _ = (n : ℕ∞) + ((2 * n : ℕ) : ℕ∞) + ((cl + cm : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ (problemK D X + (logSlack a n : ℕ∞)) +
            (problemK D (P.imp X Y) + (logSlack (e1 + 2 * e2) n : ℕ∞)) +
            ((cl + cm : ℕ) : ℕ∞) := by gcongr
      _ = problemK D X + problemK D (P.imp X Y) +
            ((logSlack a n : ℕ∞) + (logSlack (e1 + 2 * e2) n : ℕ∞) + ((cl + cm : ℕ) : ℕ∞)) := by
          ring
      _ ≤ problemK D X + problemK D (P.imp X Y) +
            (logSlack (a + (e1 + 2 * e2) + (cl + cm)) n : ℕ∞) := by gcongr

private lemma exists_partrec_eval_calculus_reduction_conj (P Q : ProblemCalculus)
    (hP : P.Admissible) (hQ : Q.Admissible) {f g : BitString →. BitString}
    (hf : Partrec f) (hg : Partrec g) :
    ∃ h : BitString →. BitString, Partrec h ∧ ∀ A A' B B' : Set BitString,
      (∀ s ∈ A, ∃ t ∈ A', t ∈ f s) → (∀ s ∈ B, ∃ t ∈ B', t ∈ g s) →
      ∀ s ∈ P.conj A B, ∃ t ∈ Q.conj A' B', t ∈ h s := by
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  refine ⟨fun s => (f ((P.unpair s).getD ([], [])).1).bind fun u =>
    (g ((P.unpair s).getD ([], [])).2).map fun w => Q.pair u w, ?_, ?_⟩
  · refine Partrec.bind (hf.comp (Computable.fst.comp hab)) ?_
    refine Partrec.map (hg.comp (Computable.snd.comp (hab.comp Computable.fst))) ?_
    exact hQ.1.comp (Computable.snd.comp Computable.fst) Computable.snd
  · intro A A' B B' hA hB s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := hs
    obtain ⟨u, hu, hu'⟩ := hA x hx
    obtain ⟨w, hw, hw'⟩ := hB y hy
    refine ⟨Q.pair u w, ⟨u, hu, w, hw, rfl⟩, ?_⟩
    simp only [hP.2.2.1 x y, Option.getD_some]
    exact Part.mem_bind_iff.2 ⟨u, hu', Part.mem_map_iff _ |>.2 ⟨w, hw', rfl⟩⟩

private lemma exists_partrec_eval_calculus_reduction_disj (P Q : ProblemCalculus)
    (hP : P.Admissible) (hQ : Q.Admissible) {f g : BitString →. BitString}
    (hf : Partrec f) (hg : Partrec g) :
    ∃ h : BitString →. BitString, Partrec h ∧ ∀ A A' B B' : Set BitString,
      (∀ s ∈ A, ∃ t ∈ A', t ∈ f s) → (∀ s ∈ B, ∃ t ∈ B', t ∈ g s) →
      ∀ s ∈ P.disj A B, ∃ t ∈ Q.disj A' B', t ∈ h s := by
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  have hc : Computable fun s : BitString => decide (((P.unpair s).getD ([], [])).1 = P.tag0) :=
    (Primrec.eq.decide.to_comp).comp (Computable.fst.comp hab) (Computable.const _) |>.of_eq
      fun _ => rfl
  refine ⟨fun s => cond (decide (((P.unpair s).getD ([], [])).1 = P.tag0))
    ((f ((P.unpair s).getD ([], [])).2).map fun w => Q.pair Q.tag0 w)
    ((g ((P.unpair s).getD ([], [])).2).map fun w => Q.pair Q.tag1 w), ?_, ?_⟩
  · refine Partrec.cond hc ?_ ?_
    · exact Partrec.map (hf.comp (Computable.snd.comp hab))
        (hQ.1.comp (Computable.const _) Computable.snd)
    · exact Partrec.map (hg.comp (Computable.snd.comp hab))
        (hQ.1.comp (Computable.const _) Computable.snd)
  · intro A A' B B' hA hB s hs
    rcases hs with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := hA x hx
      refine ⟨Q.pair Q.tag0 w, Or.inl ⟨w, hw, rfl⟩, ?_⟩
      simp only [hP.2.2.1 _ x, Option.getD_some, decide_true, Bool.cond_true]
      exact Part.mem_map_iff _ |>.2 ⟨w, hw', rfl⟩
    · obtain ⟨w, hw, hw'⟩ := hB y hy
      refine ⟨Q.pair Q.tag1 w, Or.inr ⟨w, hw, rfl⟩, ?_⟩
      have hne : ¬ P.tag1 = P.tag0 := fun h => hP.2.2.2.2.1 h.symm
      simp only [hP.2.2.1 _ y, Option.getD_some, hne, decide_false, Bool.cond_false]
      exact Part.mem_map_iff _ |>.2 ⟨w, hw', rfl⟩

private lemma exists_partrec_eval_calculus_reduction_imp (P Q : ProblemCalculus)
    (hP : P.Admissible) (hQ : Q.Admissible) {f g : BitString →. BitString}
    (hf : Partrec f) (hg : Partrec g) :
    ∃ h : BitString →. BitString, Partrec h ∧ ∀ A A' B B' : Set BitString,
      (∀ s ∈ A', ∃ t ∈ A, t ∈ f s) → (∀ s ∈ B, ∃ t ∈ B', t ∈ g s) →
      ∀ s ∈ P.imp A B, ∃ t ∈ Q.imp A' B', t ∈ h s := by
  obtain ⟨hQl, hQg⟩ := hQ.2.2.2.2.2
  obtain ⟨tr, htr, hV⟩ := hQg (fun p => (f p.2).bind fun a => (P.lang (p.1, a)).bind g) (by
    refine Partrec.bind (hf.comp Computable.snd) ?_
    refine Partrec.bind (hP.2.2.2.2.2.1.comp ?_) ?_
    · exact (Computable.fst.comp Computable.fst).pair Computable.snd
    · exact hg.comp Computable.snd)
  refine ⟨fun s => Part.some (tr s), htr.partrec, ?_⟩
  intro A A' B B' hA hB s hs
  refine ⟨tr s, ?_, Part.mem_some _⟩
  intro b hb
  obtain ⟨a, ha, ha'⟩ := hA b hb
  obtain ⟨y, hy, hy'⟩ := hs a ha
  obtain ⟨z, hz, hz'⟩ := hB y hy
  refine ⟨z, hz, ?_⟩
  rw [hV]
  exact Part.mem_bind_iff.2 ⟨a, ha', Part.mem_bind_iff.2 ⟨y, hy', hz'⟩⟩

private lemma exists_partrec_eval_calculus_reduction_both {ι : Type} (P Q : ProblemCalculus)
    (hP : P.Admissible) (hQ : Q.Admissible) (Φ : PFormula ι) :
    (∃ f : BitString →. BitString, Partrec f ∧
      ∀ v : ι → Set BitString, ∀ s ∈ Φ.eval P v, ∃ t ∈ Φ.eval Q v, t ∈ f s) ∧
    (∃ f : BitString →. BitString, Partrec f ∧
      ∀ v : ι → Set BitString, ∀ s ∈ Φ.eval Q v, ∃ t ∈ Φ.eval P v, t ∈ f s) := by
  induction Φ with
  | var i =>
    refine ⟨⟨fun s => Part.some s, Computable.id.partrec, fun v s hs => ⟨s, hs, Part.mem_some _⟩⟩,
      ⟨fun s => Part.some s, Computable.id.partrec, fun v s hs => ⟨s, hs, Part.mem_some _⟩⟩⟩
  | conj A B ihA ihB =>
    obtain ⟨⟨fA, hfA, hA⟩, ⟨gA, hgA, hA'⟩⟩ := ihA
    obtain ⟨⟨fB, hfB, hB⟩, ⟨gB, hgB, hB'⟩⟩ := ihB
    obtain ⟨h1, hh1, h1'⟩ := exists_partrec_eval_calculus_reduction_conj P Q hP hQ hfA hfB
    obtain ⟨h2, hh2, h2'⟩ := exists_partrec_eval_calculus_reduction_conj Q P hQ hP hgA hgB
    exact ⟨⟨h1, hh1, fun v => h1' _ _ _ _ (hA v) (hB v)⟩,
      ⟨h2, hh2, fun v => h2' _ _ _ _ (hA' v) (hB' v)⟩⟩
  | disj A B ihA ihB =>
    obtain ⟨⟨fA, hfA, hA⟩, ⟨gA, hgA, hA'⟩⟩ := ihA
    obtain ⟨⟨fB, hfB, hB⟩, ⟨gB, hgB, hB'⟩⟩ := ihB
    obtain ⟨h1, hh1, h1'⟩ := exists_partrec_eval_calculus_reduction_disj P Q hP hQ hfA hfB
    obtain ⟨h2, hh2, h2'⟩ := exists_partrec_eval_calculus_reduction_disj Q P hQ hP hgA hgB
    exact ⟨⟨h1, hh1, fun v => h1' _ _ _ _ (hA v) (hB v)⟩,
      ⟨h2, hh2, fun v => h2' _ _ _ _ (hA' v) (hB' v)⟩⟩
  | imp A B ihA ihB =>
    obtain ⟨⟨fA, hfA, hA⟩, ⟨gA, hgA, hA'⟩⟩ := ihA
    obtain ⟨⟨fB, hfB, hB⟩, ⟨gB, hgB, hB'⟩⟩ := ihB
    obtain ⟨h1, hh1, h1'⟩ := exists_partrec_eval_calculus_reduction_imp P Q hP hQ hgA hfB
    obtain ⟨h2, hh2, h2'⟩ := exists_partrec_eval_calculus_reduction_imp Q P hQ hP hfA hgB
    exact ⟨⟨h1, hh1, fun v => h1' _ _ _ _ (hA' v) (hB v)⟩,
      ⟨h2, hh2, fun v => h2' _ _ _ _ (hA v) (hB' v)⟩⟩

/-- SUV Problem 339 (Section 13.2, printed p. 404), the argument: for two admissible calculi
`P`, `Q` (different pairing functions, tags and languages) and every formula `Φ` there is one
partial computable map sending every solution of `Φ_P(X, Y, …)` to a solution of
`Φ_Q(X, Y, …)`, for all problems `X, Y, …` at once.  Book's proof: induction on `Φ`; identity
for variables; componentwise for `∧`, `∨` (re-pair, re-tag); for `Ψ → Θ` the map
`s ↦ t(s)` where `[t(s)]_Q(b) = f^Θ_PQ([s]_P(f^Ψ_QP(b)))`, `t` given by the Gödel property of
`Q.lang`.  (The induction needs both directions simultaneously.) -/
theorem exists_partrec_eval_calculus_reduction {ι : Type} (P Q : ProblemCalculus)
    (hP : P.Admissible) (hQ : Q.Admissible) (Φ : PFormula ι) :
    ∃ f : BitString →. BitString, Partrec f ∧
      ∀ v : ι → Set BitString, ∀ s ∈ Φ.eval P v, ∃ t ∈ Φ.eval Q v, t ∈ f s := by
  exact (exists_partrec_eval_calculus_reduction_both P Q hP hQ Φ).1

/-- SUV Problem 339 (Section 13.2, printed p. 404), the claim: the complexities of
`Φ_P(X, Y, …)` and `Φ_Q(X, Y, …)` differ by `O(1)`, the constant depending on `Φ`, `P`, `Q`
but not on the problems.  Follows from `exists_partrec_eval_calculus_reduction` and
`problemK_le_of_partrec` (exchange `P` and `Q` for the other inequality). -/
theorem problemK_eval_calculus_le (D : Map) (hD : isOptimalConditional D) {ι : Type}
    (P Q : ProblemCalculus) (hP : P.Admissible) (hQ : Q.Admissible) (Φ : PFormula ι) :
    ∃ c : ℕ, ∀ v : ι → Set BitString,
      problemK D (Φ.eval Q v) ≤ problemK D (Φ.eval P v) + (c : ℕ∞) := by
  obtain ⟨f, hf, hred⟩ := exists_partrec_eval_calculus_reduction P Q hP hQ Φ
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD f hf
  exact ⟨c, fun v => hc _ _ (hred v)⟩

private lemma exists_uniform_solution_of_provable_curry1 (P : ProblemCalculus)
    (hP : P.Admissible) (g : BitString → BitString →. BitString)
    (hg : Partrec fun q : BitString × BitString => g q.1 q.2) :
    ∃ t : BitString → BitString, Computable t ∧ ∀ s x, P.lang (t s, x) = g s x := by
  obtain ⟨_, hQg⟩ := hP.2.2.2.2.2
  obtain ⟨t, ht, h⟩ := hQg (fun q => g q.1 q.2) hg
  exact ⟨t, ht, h⟩

private lemma exists_uniform_solution_of_provable_curry2 (P : ProblemCalculus)
    (hP : P.Admissible) (g : BitString → BitString → BitString →. BitString)
    (hg : Partrec fun q : (BitString × BitString) × BitString => g q.1.1 q.1.2 q.2) :
    ∃ t : BitString → BitString → BitString, Computable₂ t ∧
      ∀ s r x, P.lang (t s r, x) = g s r x := by
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  obtain ⟨t, ht, h⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun s x => g ((P.unpair s).getD ([], [])).1 ((P.unpair s).getD ([], [])).2 x)
    (hg.comp ((hab.comp Computable.fst).pair Computable.snd))
  refine ⟨fun s r => t (P.pair s r), ht.comp hP.1, ?_⟩
  intro s r x
  rw [h]
  simp only [hP.2.2.1 s r, Option.getD_some]

private lemma exists_uniform_solution_of_provable_ax_k (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp A (P.imp B A) := by
  obtain ⟨t1, ht1, h1⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun s _ => Part.some s)
    (Computable.fst : Computable fun q : BitString × BitString => q.1).partrec
  obtain ⟨t2, ht2, h2⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ x => Part.some (t1 x)) (ht1.comp Computable.snd).partrec
  refine ⟨t2 [], fun A B x hx => ⟨t1 x, ?_, ?_⟩⟩
  · intro b _
    refine ⟨x, hx, ?_⟩
    rw [h1]; exact Part.mem_some _
  · rw [h2]; exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_s (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B C : Set BitString,
      s ∈ P.imp (P.imp A (P.imp B C)) (P.imp (P.imp A B) (P.imp A C)) := by
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  obtain ⟨w, hw, h1⟩ := exists_uniform_solution_of_provable_curry2 P hP
    (fun p r a => (P.lang (p, a)).bind fun u => (P.lang (r, a)).bind fun c => P.lang (u, c)) (by
      refine Partrec.bind (hL.comp ?_) ?_
      · exact (Computable.fst.comp Computable.fst).pair Computable.snd
      · refine Partrec.bind (hL.comp ?_) ?_
        · exact (Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
            (Computable.snd.comp Computable.fst)
        · exact hL.comp ((Computable.snd.comp Computable.fst).pair Computable.snd))
  obtain ⟨q, hq, h2⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun p r => Part.some (w p r)) hw.partrec
  obtain ⟨p0, hp0, h3⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ p => Part.some (q p)) (hq.comp Computable.snd).partrec
  refine ⟨p0 [], fun A B C p hp => ⟨q p, ?_, ?_⟩⟩
  · intro r hr
    refine ⟨w p r, ?_, ?_⟩
    · intro a ha
      obtain ⟨u, hu, hu'⟩ := hp a ha
      obtain ⟨b, hb, hb'⟩ := hr a ha
      obtain ⟨c, hc, hc'⟩ := hu b hb
      refine ⟨c, hc, ?_⟩
      rw [h1]
      exact Part.mem_bind_iff.2 ⟨u, hu', Part.mem_bind_iff.2 ⟨b, hb', hc'⟩⟩
    · rw [h2]; exact Part.mem_some _
  · rw [h3]; exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_conj_left (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp (P.conj A B) A := by
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  obtain ⟨t, ht, h⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ z => Part.some ((P.unpair z).getD ([], [])).1)
    (Computable.fst.comp (hab.comp Computable.snd)).partrec
  refine ⟨t [], fun A B z hz => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  refine ⟨x, hx, ?_⟩
  rw [h]
  simp only [hP.2.2.1 x y, Option.getD_some]
  exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_conj_right (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp (P.conj A B) B := by
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  obtain ⟨t, ht, h⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ z => Part.some ((P.unpair z).getD ([], [])).2)
    (Computable.snd.comp (hab.comp Computable.snd)).partrec
  refine ⟨t [], fun A B z hz => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  refine ⟨y, hy, ?_⟩
  rw [h]
  simp only [hP.2.2.1 x y, Option.getD_some]
  exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_conj_intro (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp A (P.imp B (P.conj A B)) := by
  obtain ⟨t1, ht1, h1⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun a b => Part.some (P.pair a b)) (hP.1.partrec)
  obtain ⟨t2, ht2, h2⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ x => Part.some (t1 x)) (ht1.comp Computable.snd).partrec
  refine ⟨t2 [], fun A B x hx => ⟨t1 x, ?_, ?_⟩⟩
  · intro y hy
    refine ⟨P.pair x y, ⟨x, hx, y, hy, rfl⟩, ?_⟩
    rw [h1]; exact Part.mem_some _
  · rw [h2]; exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_disj_left (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp A (P.disj A B) := by
  obtain ⟨t, ht, h⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ x => Part.some (P.pair P.tag0 x))
    (hP.1.comp (Computable.const _) Computable.snd).partrec
  refine ⟨t [], fun A B x hx => ⟨P.pair P.tag0 x, Or.inl ⟨x, hx, rfl⟩, ?_⟩⟩
  rw [h]; exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_disj_right (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B : Set BitString, s ∈ P.imp B (P.disj A B) := by
  obtain ⟨t, ht, h⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ x => Part.some (P.pair P.tag1 x))
    (hP.1.comp (Computable.const _) Computable.snd).partrec
  refine ⟨t [], fun A B x hx => ⟨P.pair P.tag1 x, Or.inr ⟨x, hx, rfl⟩, ?_⟩⟩
  rw [h]; exact Part.mem_some _

private lemma exists_uniform_solution_of_provable_ax_disj_elim (P : ProblemCalculus)
    (hP : P.Admissible) : ∃ s, ∀ A B C : Set BitString,
      s ∈ P.imp (P.imp A C) (P.imp (P.imp B C) (P.imp (P.disj A B) C)) := by
  have hL : Partrec P.lang := hP.2.2.2.2.2.1
  have hab : Computable fun s : BitString => (P.unpair s).getD ([], []) :=
    Computable.option_getD hP.2.1 (Computable.const _)
  obtain ⟨w, hw, h1⟩ := exists_uniform_solution_of_provable_curry2 P hP
    (fun p r z => cond (decide (((P.unpair z).getD ([], [])).1 = P.tag0))
      (P.lang (p, ((P.unpair z).getD ([], [])).2))
      (P.lang (r, ((P.unpair z).getD ([], [])).2))) (by
      have hz : Computable fun q : (BitString × BitString) × BitString =>
          (P.unpair q.2).getD ([], []) := hab.comp Computable.snd
      have hc : Computable fun q : (BitString × BitString) × BitString =>
          decide (((P.unpair q.2).getD ([], [])).1 = P.tag0) :=
        (Primrec.eq.decide.to_comp).comp (Computable.fst.comp hz) (Computable.const _) |>.of_eq
          fun _ => rfl
      refine Partrec.cond hc ?_ ?_
      · exact hL.comp ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp hz))
      · exact hL.comp ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp hz)))
  obtain ⟨q, hq, h2⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun p r => Part.some (w p r)) hw.partrec
  obtain ⟨p0, hp0, h3⟩ := exists_uniform_solution_of_provable_curry1 P hP
    (fun _ p => Part.some (q p)) (hq.comp Computable.snd).partrec
  refine ⟨p0 [], fun A B C p hp => ⟨q p, ?_, ?_⟩⟩
  · intro r hr
    refine ⟨w p r, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
      · obtain ⟨c, hc, hc'⟩ := hp x hx
        refine ⟨c, hc, ?_⟩
        rw [h1]
        simp only [hP.2.2.1 _ x, Option.getD_some, decide_true, Bool.cond_true]
        exact hc'
      · obtain ⟨c, hc, hc'⟩ := hr y hy
        refine ⟨c, hc, ?_⟩
        rw [h1]
        have hne : ¬ P.tag1 = P.tag0 := fun h => hP.2.2.2.2.1 h.symm
        simp only [hP.2.2.1 _ y, Option.getD_some, hne, decide_false, Bool.cond_false]
        exact hc'
    · rw [h2]; exact Part.mem_some _
  · rw [h3]; exact Part.mem_some _

/-- SUV Problem 340 (Section 13.2, printed p. 405), Kleene: for every formula `Φ` provable in
IPC there is one string `s` that solves `Φ(X, Y, …)` for all problems `X, Y, …`.  Hint (book):
induction on the derivation; e.g. for the axiom `p → (q → p)` the solution is the program
"transform `x` into a program that outputs `x` on every input"; modus ponens applies the
solution of `A → B` to the solution of `A`.  All programs are obtained from the Gödel property
of `P.lang`; pairs and tags are handled with `P.pair`, `P.unpair`. -/
theorem exists_uniform_solution_of_provable {ι : Type} (P : ProblemCalculus)
    (hP : P.Admissible) {Φ : PFormula ι} (h : Φ.Provable) :
    ∃ s : BitString, ∀ v : ι → Set BitString, s ∈ Φ.eval P v := by
  induction h with
  | ax_k A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_k P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_s A B C =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_s P hP
    exact ⟨s, fun v => hs _ _ _⟩
  | ax_conj_left A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_conj_left P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_conj_right A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_conj_right P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_conj_intro A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_conj_intro P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_disj_left A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_disj_left P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_disj_right A B =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_disj_right P hP
    exact ⟨s, fun v => hs _ _⟩
  | ax_disj_elim A B C =>
    obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable_ax_disj_elim P hP
    exact ⟨s, fun v => hs _ _ _⟩
  | mp _ _ ih1 ih2 =>
    obtain ⟨s1, hs1⟩ := ih1
    obtain ⟨s2, hs2⟩ := ih2
    obtain ⟨y, -, hy⟩ := hs1 (fun _ => ∅) s2 (hs2 _)
    refine ⟨y, fun v => ?_⟩
    obtain ⟨y', hy'B, hy'⟩ := hs1 v s2 (hs2 v)
    rwa [← Part.mem_unique hy' hy]

/-- SUV Section 13.2, unnumbered claim (printed p. 404): if `Φ` is provable in IPC, the
complexity of `Φ(X, Y, …)` is bounded by a constant depending on `Φ` (and `D`, `P`) but not on
the problems `X, Y, …`.  Book's proof (Kleene): one string solves all the instances
(Problem 340, `exists_uniform_solution_of_provable`); its complexity is the constant. -/
theorem problemK_eval_le_of_provable (D : Map) (hD : isOptimalConditional D) {ι : Type}
    (P : ProblemCalculus) (hP : P.Admissible) {Φ : PFormula ι} (h : Φ.Provable) :
    ∃ c : ℕ, ∀ v : ι → Set BitString, problemK D (Φ.eval P v) ≤ (c : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable P hP h
  obtain ⟨c, hc⟩ := exists_problemK_le_of_mem D hD s
  exact ⟨c, fun v => hc _ (hs v)⟩

/-- SUV Section 13.4, step of the proof of Theorem 238 (printed p. 413): if `Φ → Ψ` is provable
in IPC then `C(Ψ(X, …)) ≤ C(Φ(X, …)) + O(1)` uniformly in the problems ("As the implication
`Φ(T₁, …, T_m) → J` is provable in IPC, the complexity of the problem
`Φ(X₁, …, X_m) → J(u₁, …, u_k)` is `O(1)`").  Proof: apply the uniform solution of `Φ → Ψ`
(Problem 340) to solutions of `Φ`. -/
theorem problemK_eval_le_of_provable_imp (D : Map) (hD : isOptimalConditional D) {ι : Type}
    (P : ProblemCalculus) (hP : P.Admissible) {Φ Ψ : PFormula ι}
    (h : (PFormula.imp Φ Ψ).Provable) :
    ∃ c : ℕ, ∀ v : ι → Set BitString,
      problemK D (Ψ.eval P v) ≤ problemK D (Φ.eval P v) + (c : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_uniform_solution_of_provable P hP h
  have hf : Partrec (fun x : BitString => P.lang (s, x)) :=
    hP.2.2.2.2.2.1.comp ((Computable.const s).pair Computable.id)
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD _ hf
  exact ⟨c, fun v => hc _ _ (fun x hx => hs v x hx)⟩

end InformationLogic
end Kolmogorov
