import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.PlainPairSymmetry
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.BudgetedCornerBallModels

/-!
# Problems 333-337 (SUV §13.1)

Exercises on conjunction, disjunction, pseudo-disjunction and implication of singletons
(SUV printed pp. 402-403).  "Strings of length at most `n`" with precision `O(log n)` is
`∃ k, ∀ n x y, x.length ≤ n → y.length ≤ n → … + logSlack k n`, the library's convention
(`logSlack k n = k * |bits n| + k`).
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- SUV Problem 333 (Section 13.1, printed p. 402).  "Prove that `C(X ∨~ Y) = C(X ∨ Y) + O(1)`",
first half: `C(X ∨~ Y) ≤ C(X ∨ Y) + O(1)`, the constant independent of the problems `X`, `Y`.
Proof idea: the computable map `[0, x] ↦ [x, Λ]`, `[1, y] ↦ [Λ, y]` (or simply
`[t, w] ↦ [w, w]`) sends solutions of `X ∨ Y` to solutions of `X ∨~ Y`. -/
theorem problemK_pdisj_le_disj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ X Y : Set BitString,
      problemK D (P.pdisj X Y) ≤ problemK D (P.disj X Y) + (k : ℕ∞) := by
  obtain ⟨hpair, hunpair, hinv, -, -, -⟩ := hP
  have hsnd : Computable (fun z : BitString => ((P.unpair z).map Prod.snd).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
      (Computable.const [])
  obtain ⟨c0, hc0⟩ := plainK_map_le D hD _ (hpair.comp hsnd (Computable.const []))
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD _ (hpair.comp (Computable.const []) hsnd)
  refine ⟨max c0 c1, fun X Y => ?_⟩
  rcases (P.disj X Y).eq_empty_or_nonempty with h | h
  · rw [h, problemK_empty, top_add]; exact le_top
  obtain ⟨z, hz, hzeq⟩ := exists_mem_plainK_eq_problemK D h
  rw [← hzeq]
  rcases hz with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · have hmem : P.pair x [] ∈ P.pdisj X Y := ⟨x, [], rfl, Or.inl hx⟩
    have h0 := hc0 (P.pair P.tag0 x)
    simp only [hinv, Option.map_some, Option.getD_some] at h0
    exact (problemK_le_of_mem D hmem).trans
      (h0.trans (by gcongr; exact_mod_cast le_max_left c0 c1))
  · have hmem : P.pair [] y ∈ P.pdisj X Y := ⟨[], y, rfl, Or.inr hy⟩
    have h1 := hc1 (P.pair P.tag1 y)
    simp only [hinv, Option.map_some, Option.getD_some] at h1
    exact (problemK_le_of_mem D hmem).trans
      (h1.trans (by gcongr; exact_mod_cast le_max_right c0 c1))

/-- SUV Problem 333 (Section 13.1, printed p. 402).  `C(X ∨~ Y) = C(X ∨ Y) + O(1)`, second
half: `C(X ∨ Y) ≤ C(X ∨~ Y) + O(1)`, the constant independent of `X`, `Y`.
Proof idea: from a solution `[x, y]` of `X ∨~ Y` both `[0, x]` and `[1, y]` are computable with
`O(1)` overhead and one of them solves `X ∨ Y` (there is no uniform reduction, which is the
point of Problems 336-337, but none is needed: two computable maps suffice). -/
theorem problemK_disj_le_pdisj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ X Y : Set BitString,
      problemK D (P.disj X Y) ≤ problemK D (P.pdisj X Y) + (k : ℕ∞) := by
  obtain ⟨hpair, hunpair, hinv, -, -, -⟩ := hP
  have hfst : Computable (fun z : BitString => ((P.unpair z).map Prod.fst).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.fst.comp Computable.snd).to₂)
      (Computable.const [])
  have hsnd : Computable (fun z : BitString => ((P.unpair z).map Prod.snd).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
      (Computable.const [])
  obtain ⟨c0, hc0⟩ := plainK_map_le D hD _ (hpair.comp (Computable.const P.tag0) hfst)
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD _ (hpair.comp (Computable.const P.tag1) hsnd)
  refine ⟨max c0 c1, fun X Y => ?_⟩
  rcases (P.pdisj X Y).eq_empty_or_nonempty with h | h
  · rw [h, problemK_empty, top_add]; exact le_top
  obtain ⟨z, hz, hzeq⟩ := exists_mem_plainK_eq_problemK D h
  rw [← hzeq]
  obtain ⟨x, y, rfl, hxy⟩ := hz
  rcases hxy with hx | hy
  · have hmem : P.pair P.tag0 x ∈ P.disj X Y := Or.inl ⟨x, hx, rfl⟩
    have h0 := hc0 (P.pair x y)
    simp only [hinv, Option.map_some, Option.getD_some] at h0
    exact (problemK_le_of_mem D hmem).trans
      (h0.trans (by gcongr; exact_mod_cast le_max_left c0 c1))
  · have hmem : P.pair P.tag1 y ∈ P.disj X Y := Or.inr ⟨y, hy, rfl⟩
    have h1 := hc1 (P.pair x y)
    simp only [hinv, Option.map_some, Option.getD_some] at h1
    exact (problemK_le_of_mem D hmem).trans
      (h1.trans (by gcongr; exact_mod_cast le_max_right c0 c1))

/-- SUV Problem 334 (Section 13.1, printed p. 402).  "Find the complexity of the problem
`a → (b → c)`" for strings `a`, `b`, `c`; answer `C(c | a, b) + O(1)`, upper bound:
`C(a → (b → c)) ≤ C(c | a, b) + O(1)`.
Proof idea (book's hint): the problem is equivalent to `(a ∧ b) → c` (currying and uncurrying
are computable translations of programs, by the Gödel property), whose complexity is
`C(c | [a, b]) + O(1)` (`problemK_imp_singleton_le_condK`).  The answer with precision `O(1)` is
our reading of "find", the pair `⟨a, b⟩` coded by `pairCode a b`. -/
theorem problemK_imp_imp_singleton_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ a b c : BitString,
      problemK D (P.imp {a} (P.imp {b} {c})) ≤ condK D c (pairCode a b) + (k : ℕ∞) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  -- `t2 (pairCode q a')` on input `b'` runs `D (q, pairCode a' b')`
  obtain ⟨t2, ht2, hts2⟩ := hG (fun r => D (decodeFirst r.1, pairCode (decodeSecond r.1) r.2))
    (hD.1.comp ((hdf.comp Computable.fst).pair (hpc.comp (hds.comp Computable.fst) Computable.snd)))
  -- `t1 q` on input `a'` prints the program `t2 (pairCode q a')`
  obtain ⟨t1, ht1, hts1⟩ := hG (fun r => Part.some (t2 (pairCode r.1 r.2)))
    (ht2.comp (hpc.comp Computable.fst Computable.snd)).partrec
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t1 ht1
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  refine ⟨c1 + c2, fun a b c => ?_⟩
  rcases eq_top_or_lt_top (condK D c (pairCode a b)) with h | h
  · rw [h, top_add]; exact le_top
  have hne : (candidateLengths D c (pairCode a b)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [condK, hemp] at h
  obtain ⟨q, hq, hqlen⟩ := csInf_mem hne
  have hmem : t1 q ∈ P.imp {a} (P.imp {b} {c}) := by
    intro a' ha'
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨t2 (pairCode q a'), ?_, by rw [hts1]; exact Part.mem_some _⟩
    intro b' hb'
    rw [Set.mem_singleton_iff] at hb'
    subst hb'
    refine ⟨c, Set.mem_singleton c, ?_⟩
    rw [hts2]
    simp only [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hq
  calc problemK D (P.imp {a} (P.imp {b} {c})) ≤ plainK D (t1 q) := problemK_le_of_mem D hmem
    _ ≤ plainK D q + c1 := hc1 q
    _ ≤ ((q.length : ℕ∞) + c2) + c1 := by gcongr; exact hc2 q
    _ = condK D c (pairCode a b) + ((c1 + c2 : ℕ) : ℕ∞) := by
        rw [show condK D c (pairCode a b) = (q.length : ℕ∞) from hqlen.symm]; push_cast; ring

/-- SUV Problem 334 (Section 13.1, printed p. 402).  The complexity of `a → (b → c)` is
`C(c | a, b) + O(1)`, lower bound: `C(c | a, b) ≤ C(a → (b → c)) + O(1)`.
Proof idea: given `[a, b]` and a solution `p`, run `p` on `a` and the resulting program on `b`;
this is a decompressor for `c` given `[a, b]`, so optimality of `D` applies. -/
theorem condK_le_problemK_imp_imp_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ a b c : BitString,
      condK D c (pairCode a b) ≤ problemK D (P.imp {a} (P.imp {b} {c})) + (k : ℕ∞) := by
  obtain ⟨-, -, -, -, -, hL, -⟩ := hP
  let E : Map := fun pr => (D (pr.1, [])).bind
    (fun p => (P.lang (p, decodeFirst pr.2)).bind (fun p' => P.lang (p', decodeSecond pr.2)))
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hinner : Partrec₂ (fun (q : (BitString × BitString) × BitString) (p' : BitString) =>
      P.lang (p', decodeSecond q.1.2)) :=
    (hL.comp (Computable.snd.pair
      (hds.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))))).to₂
  have hmid : Partrec₂ (fun (pr : BitString × BitString) (p : BitString) =>
      (P.lang (p, decodeFirst pr.2)).bind (fun p' => P.lang (p', decodeSecond pr.2))) :=
    (Partrec.bind (hL.comp (Computable.snd.pair
      (hdf.comp (Computable.snd.comp Computable.fst)))) hinner).to₂
  have hE : isDecompressor E :=
    Partrec.bind (hD.1.comp (Computable.fst.pair (Computable.const []))) hmid
  obtain ⟨k, hk⟩ := hD.2 E hE
  refine ⟨k, fun a b c => ?_⟩
  rcases (P.imp {a} (P.imp {b} {c})).eq_empty_or_nonempty with h | h
  · rw [h, problemK_empty, top_add]; exact le_top
  obtain ⟨p, hp, hpeq⟩ := exists_mem_plainK_eq_problemK D h
  rw [← hpeq]
  refine (hk c (pairCode a b)).trans ?_
  gcongr
  change sInf (candidateLengths E c (pairCode a b)) ≤ sInf (candidateLengths D p [])
  apply sInf_le_sInf
  rintro m ⟨r, hr, rfl⟩
  obtain ⟨p', hp', hpp'⟩ := hp a (Set.mem_singleton a)
  obtain ⟨c', hc', hp'c⟩ := hp' b (Set.mem_singleton b)
  rw [Set.mem_singleton_iff] at hc'
  subst hc'
  refine ⟨r, Part.mem_bind_iff.2 ⟨p, hr, ?_⟩, rfl⟩
  simp only [decodeFirst_pairCode, decodeSecond_pairCode]
  exact Part.mem_bind_iff.2 ⟨p', hpp', hp'c⟩

/-- SUV Problem 335 (Section 13.1, printed p. 403).  "Find the complexity of `a ∧ (b → c)` (with
logarithmic precision)"; answer `C(a) + C(c | a, b)`, upper bound:
`C(a ∧ (b → c)) ≤ C(a) + C(c | a, b) + O(log n)` for strings of length at most `n`.
Proof idea (book's hint): given `a` and a program mapping `[a, b]` to `c` one gets a program
converting `b` to `c` (Gödel property, `a` hardwired); the solution `[a, that program]` is
computable from a self-delimiting pair (shortest description of `a`, shortest description of
`c` given `[a, b]`), `plainK_pair_le_add_two_log`.  "Logarithmic precision" is read as `O(log n)`
for strings of length at most `n`. -/
theorem problemK_conj_imp_singleton_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b c : BitString), a.length ≤ n → b.length ≤ n → c.length ≤ n →
      problemK D (P.conj {a} (P.imp {b} {c})) ≤
        plainK D a + condK D c (pairCode a b) + (logSlack k n : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -, hG⟩ := hP
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  -- `t2 (pairCode q a')` on input `b'` runs `D (q, pairCode a' b')`
  obtain ⟨t2, ht2, hts2⟩ := hG (fun r => D (decodeFirst r.1, pairCode (decodeSecond r.1) r.2))
    (hD.1.comp ((hdf.comp Computable.fst).pair (hpc.comp (hds.comp Computable.fst) Computable.snd)))
  -- from `pairCode qa qc` compute `[a, t2 (pairCode qc a)]`, `a = D (qa, [])`
  let g : BitString →. BitString := fun w => (D (decodeFirst w, [])).map
    (fun a' => P.pair a' (t2 (pairCode (decodeSecond w) a')))
  have hg : Partrec g :=
    Partrec.map (hD.1.comp (hdf.pair (Computable.const [])))
      (hpair.comp Computable.snd
        (ht2.comp (hpc.comp (hds.comp Computable.fst) Computable.snd))).to₂
  obtain ⟨c1, hc1⟩ := plainK_le_of_mem_partrec D hD g hg
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 1 (2 * c2)
  -- finiteness of `plainK` and the natural-number value
  have hfin : ∀ x : BitString, plainK D x = (cVal D x : ℕ∞) ∧ cVal D x ≤ x.length + c2 := by
    intro x
    have hne : plainK D x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (x.length + c2))
      (by simpa using hc2 x)
    have heq : plainK D x = (cVal D x : ℕ∞) := by
      dsimp [cVal]; rw [ENat.natCast_toNat hne]
    refine ⟨heq, ?_⟩
    have h := hc2 x
    rw [heq] at h
    exact_mod_cast (by simpa using h : (cVal D x : ℕ∞) ≤ ((x.length + c2 : ℕ) : ℕ∞))
  refine ⟨C + (c2 + c2 + k0 + c1), fun n a b c ha hb hcl => ?_⟩
  rcases eq_or_ne (condK D c (pairCode a b)) ⊤ with h | h
  · rw [h]; simp
  obtain ⟨qa, hqa, hqalen⟩ := exists_program_le_cVal D hD a
  have hcK : condK D c (pairCode a b) = ((condK D c (pairCode a b)).toNat : ℕ∞) :=
    (ENat.natCast_toNat h).symm
  obtain ⟨qc, hqclen, hqc⟩ :=
    (condK_le_iff D c (pairCode a b) (condK D c (pairCode a b)).toNat).mp hcK.le
  -- the solution
  have himp : t2 (pairCode qc a) ∈ P.imp {b} {c} := by
    intro b' hb'
    rw [Set.mem_singleton_iff] at hb'
    refine ⟨c, Set.mem_singleton c, ?_⟩
    rw [hts2, hb']
    simp only [decodeFirst_pairCode, decodeSecond_pairCode]
    exact hqc
  have hz : P.pair a (t2 (pairCode qc a)) ∈ P.conj {a} (P.imp {b} {c}) :=
    Set.mem_image2_of_mem (Set.mem_singleton a) himp
  have hzg : P.pair a (t2 (pairCode qc a)) ∈ g (pairCode qa qc) := by
    simp only [g, decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_map _ hqa
  -- the numbers
  obtain ⟨hqa_eq, hqa_le⟩ := hfin qa
  obtain ⟨ha_eq, ha_le⟩ := hfin a
  obtain ⟨hqc_eq, hqc_le⟩ := hfin qc
  set m := cVal D qa with hm
  have hmn : m ≤ 1 * n + 2 * c2 := by omega
  have hlog : Nat.log 2 m ≤ (Nat.bits (1 * n + 2 * c2)).length := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; simp
    have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
    have h2 : m < 2 ^ (Nat.bits (1 * n + 2 * c2)).length := by
      rw [Nat.size_eq_bits_len]
      exact lt_of_le_of_lt hmn (Nat.lt_size_self _)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h1 h2)
    omega
  have hslack : 2 * Nat.log 2 m ≤ logSlack C n := by
    have h1 := hC n
    have h2 : logSlack 2 (1 * n + 2 * c2) = 2 * (Nat.bits (1 * n + 2 * c2)).length + 2 := rfl
    omega
  have hconst : c2 + c2 + k0 + c1 ≤ logSlack (c2 + c2 + k0 + c1) n := Nat.le_add_left _ _
  have hnat : qa.length + c2 + (qc.length + c2) + (2 * Nat.log 2 m + k0) + c1 ≤
      cVal D a + (condK D c (pairCode a b)).toNat +
        logSlack (C + (c2 + c2 + k0 + c1)) n := by
    have hqclen' : qc.length ≤ (condK D c (pairCode a b)).toNat := hqclen
    rw [logSlack_add_constants]
    omega
  calc problemK D (P.conj {a} (P.imp {b} {c}))
      ≤ plainK D (P.pair a (t2 (pairCode qc a))) := problemK_le_of_mem D hz
    _ ≤ plainK D (pairCode qa qc) + (c1 : ℕ∞) := hc1 _ _ hzg
    _ ≤ plainK D qa + plainK D qc + ((2 * Nat.log 2 m + k0 : ℕ) : ℕ∞) + (c1 : ℕ∞) := by
        gcongr
        exact hk0 qa qc
    _ ≤ ((qa.length : ℕ∞) + c2) + ((qc.length : ℕ∞) + c2) + ((2 * Nat.log 2 m + k0 : ℕ) : ℕ∞)
          + (c1 : ℕ∞) := by
        gcongr
        · exact hc2 qa
        · exact hc2 qc
    _ = ((qa.length + c2 + (qc.length + c2) + (2 * Nat.log 2 m + k0) + c1 : ℕ) : ℕ∞) := by
        push_cast; rfl
    _ ≤ ((cVal D a + (condK D c (pairCode a b)).toNat +
        logSlack (C + (c2 + c2 + k0 + c1)) n : ℕ) : ℕ∞) := by exact_mod_cast hnat
    _ = plainK D a + condK D c (pairCode a b) +
        (logSlack (C + (c2 + c2 + k0 + c1)) n : ℕ∞) := by
        push_cast
        rw [ha_eq, ← hcK]

/-- Step 1 of the proof of `plainK_add_condK_le_problemK_conj_imp_singleton`: the
triple `⟨⟨a, b⟩, c⟩` is computable from `[z, q]` where `z = [a, p]` is a solution of
`a ∧ (b → c)` and `q` is a program producing `b` from `a`: unpair `z`, run `D (q, a)` and `[p]`. -/
private theorem plainK_add_condK_le_problemK_conj_imp_singleton_decode (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ (z q a p b c' : BitString), P.unpair z = some (a, p) → b ∈ D (q, a) →
      c' ∈ P.lang (p, b) →
      cPair D (pairCode a b) c' ≤ plainK D (pairCode z q) + (c : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, hL, -⟩ := hP
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  have hpc : Computable₂ pairCode := CodedFiniteDistribution.pairCode_primrec.to_comp
  let f : BitString →. BitString := fun w =>
    (Part.ofOption (P.unpair (decodeFirst w))).bind fun ap =>
      (D (decodeSecond w, ap.1)).bind fun b =>
        (P.lang (ap.2, b)).map fun c' => pairCode (pairCode ap.1 b) c'
  have hf : Partrec f := by
    refine Partrec.bind (Computable.ofOption (hunpair.comp hdf)) ?_
    refine Partrec.bind ?_ ?_
    · exact hD.1.comp ((hds.comp Computable.fst).pair (Computable.fst.comp Computable.snd))
    · refine Partrec.map ?_ ?_
      · exact hL.comp ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          Computable.snd)
      · exact hpc.comp (hpc.comp (Computable.fst.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst))) (Computable.snd.comp Computable.fst))
          Computable.snd
  obtain ⟨c, hc⟩ := plainK_le_of_mem_partrec D hD f hf
  refine ⟨c, fun z q a p b c' hz hb hc' => hc (pairCode z q) _ ?_⟩
  simp only [f, decodeFirst_pairCode, decodeSecond_pairCode, hz]
  exact Part.mem_bind_iff.2 ⟨(a, p), by simp [Part.ofOption],
    Part.mem_bind_iff.2 ⟨b, hb, (Part.mem_map_iff _).2 ⟨c', hc', rfl⟩⟩⟩

/-- Step 2 of the proof of `plainK_add_condK_le_problemK_conj_imp_singleton`: the
budgeted form of `C(z, q) ≤ C(z) + C(q) + O(log N)` when `C(z) ≤ N`, with `C(q) ≤ |q| + O(1)`
(`plainK_pair_le_add_two_log`, `plainK_le_length`). -/
private theorem plainK_add_condK_le_problemK_conj_imp_singleton_pair (D : Map)
    (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (z q : BitString) (N : ℕ), plainK D z ≤ (N : ℕ∞) →
      cPair D z q ≤ plainK D z + (q.length : ℕ∞) + (logSlack k N : ℕ∞) := by
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨cL, hcL⟩ := plainK_le_length D hD
  refine ⟨2 + k0 + cL, fun z q N hz => ?_⟩
  have hval : cVal D z ≤ N := by
    unfold cVal
    have := ENat.toNat_le_toNat hz (ENat.natCast_ne_top N)
    simpa using this
  have hlog : Nat.log 2 (cVal D z) ≤ (Nat.bits N).length := by
    have h1 : Nat.log 2 (cVal D z) ≤ Nat.log 2 N := Nat.log_mono_right hval
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp only [Nat.log_zero_right, Nat.le_zero] at h1
      omega
    · have h2 : Nat.log 2 N < Nat.size N := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
      have h3 : (Nat.bits N).length = Nat.size N := by rw [Nat.size_eq_bits_len]
      omega
  have h1 := hk0 z q
  have h2 := hcL q
  calc cPair D z q ≤ plainK D z + plainK D q + ((2 * Nat.log 2 (cVal D z) + k0 : ℕ) : ℕ∞) := h1
    _ ≤ plainK D z + ((q.length : ℕ∞) + (cL : ℕ∞)) + ((2 * (Nat.bits N).length + k0 : ℕ) : ℕ∞) := by
        refine add_le_add (add_le_add le_rfl h2) ?_
        exact_mod_cast (by omega : 2 * Nat.log 2 (cVal D z) + k0 ≤ 2 * (Nat.bits N).length + k0)
    _ = plainK D z + (q.length : ℕ∞) + (((cL + (2 * (Nat.bits N).length + k0) : ℕ)) : ℕ∞) := by
        push_cast
        ring
    _ ≤ plainK D z + (q.length : ℕ∞) + (logSlack (2 + k0 + cL) N : ℕ∞) := by
        refine add_le_add le_rfl ?_
        have : cL + (2 * (Nat.bits N).length + k0) ≤ logSlack (2 + k0 + cL) N := by
          unfold logSlack; nlinarith
        exact_mod_cast this

/-- SUV Problem 335 (Section 13.1, printed p. 403).  The complexity of `a ∧ (b → c)` is
`C(a) + C(c | a, b)` with logarithmic precision, lower bound:
`C(a) + C(c | a, b) ≤ C(a ∧ (b → c)) + O(log n)` for strings of length at most `n`.
Proof idea (book's hint): add `C(b | a)` to both sides;
the triple `a, b, c` is reconstructed from `a`, a program converting `a` to `b` and a program
converting `b` to `c`, so `C(a, b, c) ≤ C(a ∧ (b → c)) + C(b|a) + O(log n)`; conclude by the
symmetry of information `C(a, b, c) = C(a) + C(b|a) + C(c|a, b) + O(log n)` (Chapter 2,
`plainK_add_condK_le_plainK_pair_add_three_log`). -/
theorem plainK_add_condK_le_problemK_conj_imp_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b c : BitString), a.length ≤ n → b.length ≤ n → c.length ≤ n →
      plainK D a + condK D c (pairCode a b) ≤
        problemK D (P.conj {a} (P.imp {b} {c})) + (logSlack k n : ℕ∞) := by
  have hinv := hP.2.2.1
  obtain ⟨cDec, hDec⟩ := plainK_add_condK_le_problemK_conj_imp_singleton_decode D hD P hP
  obtain ⟨kB, hB⟩ := plainK_add_condK_le_problemK_conj_imp_singleton_pair D hD
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨cS, hS⟩ := plainK_add_condK_le_plainK_pair D U hD hU
  obtain ⟨cL, hcL⟩ := plainK_le_length D hD
  obtain ⟨cC, hcC⟩ := condK_le_plainK D hD
  obtain ⟨K3, hK3⟩ := logSlack_linear_bound (kB + cDec + 2 * cS) 7 (2 * cL + cC + 3)
  refine ⟨K3, fun n a b c ha hb hc => ?_⟩
  rcases (P.conj {a} (P.imp {b} {c})).eq_empty_or_nonempty with h | h
  · rw [h, problemK_empty, top_add]; exact le_top
  obtain ⟨z, hz, hzeq⟩ := exists_mem_plainK_eq_problemK D h
  rw [← hzeq]
  obtain ⟨a', ha', p, hp, hzdef⟩ := hz
  have haa : a' = a := ha'
  rw [haa] at hzdef
  obtain ⟨c', hc', hcp⟩ := hp b (Set.mem_singleton b)
  have hcc : c' = c := hc'
  rw [hcc] at hcp
  have hunp : P.unpair z = some (a, p) := by rw [← hzdef, hinv]
  -- a shortest program `q` for `b` given `a`
  have hYne : (candidateLengths D b a).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact condK_ne_top_of_optimal D hD b a (by simp [condK, hemp])
  obtain ⟨q, hq, hqlen⟩ := csInf_mem hYne
  have hY : condK D b a = (q.length : ℕ∞) := hqlen.symm
  by_cases hcase : plainK D a + condK D c (pairCode a b) ≤ plainK D z
  · exact hcase.trans le_self_add
  have hcase := lt_of_not_ge hcase
  have hlen : ∀ w : BitString, plainK D w ≤ ((w.length + cL : ℕ) : ℕ∞) := fun w =>
    (hcL w).trans (by push_cast; exact le_rfl)
  have hXle : plainK D a ≤ ((n + cL : ℕ) : ℕ∞) :=
    (hlen a).trans (by exact_mod_cast Nat.add_le_add_right ha cL)
  have hZle : condK D c (pairCode a b) ≤ ((n + cL + cC : ℕ) : ℕ∞) :=
    (hcC c (pairCode a b)).trans (by
      have h1 := hlen c
      calc plainK D c + (cC : ℕ∞) ≤ ((c.length + cL : ℕ) : ℕ∞) + (cC : ℕ∞) := by gcongr
        _ ≤ ((n + cL + cC : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega : c.length + cL + cC ≤ n + cL + cC))
  obtain ⟨N, hN⟩ : ∃ N, N = 7 * n + (2 * cL + cC + 3) := ⟨_, rfl⟩
  have hTN : plainK D z ≤ (N : ℕ∞) :=
    hcase.le.trans ((add_le_add hXle hZle).trans (by
      rw [← Nat.cast_add]; exact_mod_cast (by omega : n + cL + (n + cL + cC) ≤ N)))
  have hbud : ∀ w : BitString, w.length + cL ≤ N → plainK D w ≤ (N : ℕ∞) := fun w hw =>
    (hlen w).trans (by exact_mod_cast hw)
  have hXN : plainK D a ≤ (N : ℕ∞) := hbud a (by omega)
  have hx' : plainK D (pairCode a b) ≤ (N : ℕ∞) := hbud _ (by simp only [length_pairCode]; omega)
  have hpz : plainK D (pairCode (pairCode a b) c) ≤ (N : ℕ∞) :=
    hbud _ (by simp only [length_pairCode]; omega)
  have hsym1 := hS a b N hXN hx'
  have hsym2 := hS (pairCode a b) c N hx' hpz
  rw [hY] at hsym1
  have hdec := hDec z q a p b c hunp hq hcp
  have hpair := hB z q N hTN
  have hcP : cPair D (pairCode a b) c = plainK D (pairCode (pairCode a b) c) := rfl
  have hcP2 : cPair D z q = plainK D (pairCode z q) := rfl
  rw [hcP2] at hpair
  rw [hcP] at hdec
  have hS1 : plainK D (pairCode (pairCode a b) c) ≤
      plainK D z + (q.length : ℕ∞) + (logSlack kB N : ℕ∞) + (cDec : ℕ∞) :=
    hdec.trans (add_le_add_left hpair _)
  have key : (plainK D a + condK D c (pairCode a b)) + (q.length : ℕ∞) ≤
      (plainK D z + ((logSlack kB N + cDec + 2 * logSlack cS N : ℕ) : ℕ∞)) + (q.length : ℕ∞) := by
    calc (plainK D a + condK D c (pairCode a b)) + (q.length : ℕ∞)
        = (plainK D a + (q.length : ℕ∞)) + condK D c (pairCode a b) := by ring
      _ ≤ (plainK D (pairCode a b) + (logSlack cS N : ℕ∞)) + condK D c (pairCode a b) := by
          gcongr
      _ = (plainK D (pairCode a b) + condK D c (pairCode a b)) + (logSlack cS N : ℕ∞) := by ring
      _ ≤ (plainK D (pairCode (pairCode a b) c) + (logSlack cS N : ℕ∞)) +
            (logSlack cS N : ℕ∞) := by gcongr
      _ ≤ ((plainK D z + (q.length : ℕ∞) + (logSlack kB N : ℕ∞) + (cDec : ℕ∞)) +
            (logSlack cS N : ℕ∞)) + (logSlack cS N : ℕ∞) := by gcongr
      _ = (plainK D z + ((logSlack kB N + cDec + 2 * logSlack cS N : ℕ) : ℕ∞)) +
            (q.length : ℕ∞) := by push_cast; ring
  have hcancel := (ENat.add_le_add_iff_right (ENat.natCast_ne_top q.length)).1 key
  have hSle : logSlack kB N + cDec + 2 * logSlack cS N ≤ logSlack K3 n := by
    have h1 := hK3 n
    rw [← hN] at h1
    refine le_trans ?_ h1
    unfold logSlack
    nlinarith [Nat.zero_le (cDec * (Nat.bits N).length)]
  refine hcancel.trans ?_
  exact add_le_add le_rfl (by exact_mod_cast hSle)

/-- SUV Problem 336 (Section 13.1, printed p. 403).  "Prove that the complexity of
`(x ∨ y) → (x ∨~ y)` is `O(1)`", first claim: a constant bounds `C((x ∨ y) → (x ∨~ y))` for all
strings `x`, `y`.
Proof idea: one program solves it for all `x`, `y`: `[t, w] ↦ [w, w]` (written in `P.lang` by
the Gödel property); `w` solves the disjunct selected by the tag, so `[w, w]` solves
`x ∨~ y`. -/
theorem problemK_imp_disj_pdisj_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ x y : BitString,
      problemK D (P.imp (P.disj {x} {y}) (P.pdisj {x} {y})) ≤ (k : ℕ∞) := by
  obtain ⟨hpair, hunpair, hinv, -, -, -, hG⟩ := hP
  have hsnd : Computable (fun z : BitString => ((P.unpair z).map Prod.snd).getD []) :=
    Computable.option_getD
      (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
      (Computable.const [])
  -- the program `[t, w] ↦ [w, w]` needs no case distinction: `w` solves one of the disjuncts
  have hV : Partrec (fun q : BitString × BitString =>
      Part.some (P.pair (((P.unpair q.2).map Prod.snd).getD [])
        (((P.unpair q.2).map Prod.snd).getD []))) :=
    (hpair.comp (hsnd.comp Computable.snd) (hsnd.comp Computable.snd)).partrec
  obtain ⟨t, -, hts⟩ := hG _ hV
  obtain ⟨c, hc⟩ := exists_problemK_le_of_mem D hD (t [])
  refine ⟨c, fun x y => hc _ ?_⟩
  intro z hz
  rcases hz with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
  · refine ⟨P.pair x' x', ⟨x', x', rfl, Or.inl hx'⟩, ?_⟩
    rw [hts]
    simp [hinv]
  · refine ⟨P.pair y' y', ⟨y', y', rfl, Or.inr hy'⟩, ?_⟩
    rw [hts]
    simp [hinv]

/-- SUV Problem 336 (Section 13.1, printed p. 403).  "The reverse implication
`(x ∨~ y) → (x ∨ y)` has the same complexity as `x ∨ y`, up to `O(log n)` additive term, if `x`
and `y` are strings of length at most `n`", upper bound:
`C((x ∨~ y) → (x ∨ y)) ≤ C(x ∨ y) + O(log n)`.
Proof idea (in fact `O(1)`): the program that ignores its input and prints a fixed solution `s`
of `x ∨ y` is computable from `s` (Gödel property). -/
theorem problemK_imp_pdisj_disj_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.pdisj {x} {y}) (P.disj {x} {y})) ≤
        problemK D (P.disj {x} {y}) + (logSlack k n : ℕ∞) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  -- `t s` ignores its input and prints `s`
  obtain ⟨t, ht, hts⟩ := hG (fun r => Part.some r.1) Computable.fst.partrec
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD (fun s => Part.some (t s)) ht.partrec
  refine ⟨c, fun n x y _ _ => ?_⟩
  refine (hc (P.disj {x} {y}) _ fun s hs => ⟨t s, ?_, Part.mem_some _⟩).trans ?_
  · intro w _
    exact ⟨s, hs, by rw [hts]; exact Part.mem_some s⟩
  · gcongr
    exact Nat.le_add_left _ _

/-- Dovetailed search for a witness: if `chk (a, b) s` is a computable test, there is a partial
computable `f` returning, on `a`, some `b` for which the test succeeds at some stage, and
defined whenever such a `b` exists. -/
private lemma problemK_disj_le_imp_pdisj_disj_search {α β : Type*} [Primcodable α]
    [Primcodable β] (chk : α × β → ℕ → Bool) (hchk : Computable₂ chk) :
    ∃ f : α →. β, Partrec f ∧ (∀ a b, b ∈ f a → ∃ s, chk (a, b) s = true) ∧
      ∀ a b s, chk (a, b) s = true → (f a).Dom := by
  let g : α → ℕ → Option β := fun a k =>
    (Encodable.decode (α := β) k.unpair.1).bind fun b =>
      bif chk (a, b) k.unpair.2 then some b else none
  have hk1 : Computable fun p : α × ℕ => p.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hk2 : Computable fun p : α × ℕ => p.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hg : Computable₂ g := by
    refine Computable.option_bind (Computable.decode.comp hk1) ?_
    have hc : Computable fun q : (α × ℕ) × β => chk (q.1.1, q.2) q.1.2.unpair.2 :=
      hchk.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
        (hk2.comp Computable.fst)
    have hs : Computable fun q : (α × ℕ) × β => (some q.2 : Option β) :=
      (Computable.option_some (α := β)).comp Computable.snd
    exact (Computable.cond hc hs (Computable.const (none : Option β))).to₂
  refine ⟨fun a => Nat.rfindOpt (g a), Partrec.rfindOpt hg, ?_, ?_⟩
  · intro a b hb
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hb
    simp only [g, Option.mem_def] at hk
    cases hd : Encodable.decode (α := β) k.unpair.1 with
    | none => simp [hd] at hk
    | some b0 =>
      simp only [hd, Option.bind_some] at hk
      cases hc : chk (a, b0) k.unpair.2 with
      | false => simp [hc] at hk
      | true =>
        simp only [hc, Bool.cond_true, Option.some.injEq] at hk
        subst hk
        exact ⟨_, hc⟩
  · intro a b s hs
    change (Nat.rfindOpt (g a)).Dom
    rw [Nat.rfindOpt_dom]
    refine ⟨Nat.pair (Encodable.encode b) s, b, ?_⟩
    simp [g, hs]

/-- `z` is a valid answer of `p` for the disjunction `u ∨ v`: `[p](z)` is `[0, u]` or `[1, v]`. -/
private def problemK_disj_le_imp_pdisj_disj_valid (P : ProblemCalculus) (p u v z : BitString) :
    Prop :=
  P.pair P.tag0 u ∈ P.lang (p, z) ∨ P.pair P.tag1 v ∈ P.lang (p, z)

/-- The pair `(u, v)` of strings of length at most `n` is compatible with `p`: for all `w` of
length at most `n` both `[p]([u, w])` and `[p]([w, v])` solve `u ∨ v`. -/
private def problemK_disj_le_imp_pdisj_disj_compat (P : ProblemCalculus) (p : BitString)
    (n : ℕ) (u v : BitString) : Prop :=
  u.length ≤ n ∧ v.length ≤ n ∧ ∀ w : BitString, w.length ≤ n →
    problemK_disj_le_imp_pdisj_disj_valid P p u v (P.pair u w) ∧
      problemK_disj_le_imp_pdisj_disj_valid P p u v (P.pair w v)

private lemma problemK_disj_le_imp_pdisj_disj_valid_re (P : ProblemCalculus)
    (hP : P.Admissible) :
    IsRE (fun a : BitString × BitString × BitString × BitString =>
      problemK_disj_le_imp_pdisj_disj_valid P a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  obtain ⟨hpair, -, -, -, -, hL, -⟩ := hP
  have h0 := (Partrec.graphIsRe P.lang hL).comp_computable
    (g := fun a : BitString × BitString × BitString × BitString =>
      ((a.1, a.2.2.2), P.pair P.tag0 a.2.1))
    (Computable.pair (Computable.pair Computable.fst
      (Computable.snd.comp (Computable.snd.comp Computable.snd)))
      (hpair.comp (Computable.const P.tag0) (Computable.fst.comp Computable.snd)))
  have h1 := (Partrec.graphIsRe P.lang hL).comp_computable
    (g := fun a : BitString × BitString × BitString × BitString =>
      ((a.1, a.2.2.2), P.pair P.tag1 a.2.2.1))
    (Computable.pair (Computable.pair Computable.fst
      (Computable.snd.comp (Computable.snd.comp Computable.snd)))
      (hpair.comp (Computable.const P.tag1)
        (Computable.fst.comp (Computable.snd.comp Computable.snd))))
  exact h0.or h1

/-- Compatibility is enumerable: a partial computable function finding, given `(p, n)`, some
compatible pair, defined whenever a compatible pair exists. -/
private lemma problemK_disj_le_imp_pdisj_disj_compat_search (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ f : BitString × ℕ →. BitString × BitString, Partrec f ∧
      (∀ a r, r ∈ f a → problemK_disj_le_imp_pdisj_disj_compat P a.1 a.2 r.1 r.2) ∧
      ∀ (a : BitString × ℕ) (r : BitString × BitString),
        problemK_disj_le_imp_pdisj_disj_compat P a.1 a.2 r.1 r.2 → (f a).Dom := by
  obtain ⟨chkV, hchkV, hmono, hiff⟩ :=
    (problemK_disj_le_imp_pdisj_disj_valid_re P hP).exists_stageApprox
  obtain ⟨hpair, -, -, -, -, -, -⟩ := hP
  let chk : (BitString × ℕ) × (BitString × BitString) → ℕ → Bool := fun a s =>
    decide (a.2.1.length ≤ a.1.2) && decide (a.2.2.length ≤ a.1.2) &&
      ((List.range (a.1.2 + 1)).flatMap allStrings).all (fun w =>
        chkV (a.1.1, a.2.1, a.2.2, P.pair a.2.1 w) s &&
          chkV (a.1.1, a.2.1, a.2.2, P.pair w a.2.2) s)
  have hchk : Computable₂ chk := by
    have hq1 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ => q.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hq2 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ => q.1.1.2 :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hq3 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ => q.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hq4 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ => q.1.2.2 :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hq5 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ => q.2 :=
      Computable.snd
    have hle1 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ =>
        decide (q.1.2.1.length ≤ q.1.1.2) :=
      (Primrec.nat_le.decide.to_comp).comp (Computable.list_length.comp hq3) hq2
    have hle2 : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ =>
        decide (q.1.2.2.length ≤ q.1.1.2) :=
      (Primrec.nat_le.decide.to_comp).comp (Computable.list_length.comp hq4) hq2
    have hlist : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ =>
        (List.range (q.1.1.2 + 1)).flatMap allStrings :=
      (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (CodedFiniteDistribution.allStrings_primrec.comp Primrec.snd).to₂).to_comp
    have hp : Computable₂ fun (q : ((BitString × ℕ) × (BitString × BitString)) × ℕ)
        (w : BitString) =>
        !(chkV (q.1.1.1, q.1.2.1, q.1.2.2, P.pair q.1.2.1 w) q.2 &&
          chkV (q.1.1.1, q.1.2.1, q.1.2.2, P.pair w q.1.2.2) q.2) := by
      have e1 : Computable fun r : (((BitString × ℕ) × (BitString × BitString)) × ℕ) ×
          BitString =>
          chkV (r.1.1.1.1, r.1.1.2.1, r.1.1.2.2, P.pair r.1.1.2.1 r.2) r.1.2 :=
        hchkV.comp (Computable.pair (hq1.comp Computable.fst)
          (Computable.pair (hq3.comp Computable.fst) (Computable.pair (hq4.comp Computable.fst)
            (hpair.comp (hq3.comp Computable.fst) Computable.snd)))) (hq5.comp Computable.fst)
      have e2 : Computable fun r : (((BitString × ℕ) × (BitString × BitString)) × ℕ) ×
          BitString =>
          chkV (r.1.1.1.1, r.1.1.2.1, r.1.1.2.2, P.pair r.2 r.1.1.2.2) r.1.2 :=
        hchkV.comp (Computable.pair (hq1.comp Computable.fst)
          (Computable.pair (hq3.comp Computable.fst) (Computable.pair (hq4.comp Computable.fst)
            (hpair.comp Computable.snd (hq4.comp Computable.fst))))) (hq5.comp Computable.fst)
      exact (Primrec.not.to_comp.comp (Primrec.and.to_comp.comp e1 e2)).to₂
    have hall : Computable fun q : ((BitString × ℕ) × (BitString × BitString)) × ℕ =>
        ((List.range (q.1.1.2 + 1)).flatMap allStrings).all (fun w =>
          chkV (q.1.1.1, q.1.2.1, q.1.2.2, P.pair q.1.2.1 w) q.2 &&
            chkV (q.1.1.1, q.1.2.1, q.1.2.2, P.pair w q.1.2.2) q.2) :=
      (Primrec.not.to_comp.comp (computable_list_any hlist hp)).of_eq fun q => by
        rw [List.all_eq_not_any_not]
    have := Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hle1 hle2) hall
    exact this
  obtain ⟨f, hf, hsound, hdom⟩ := problemK_disj_le_imp_pdisj_disj_search chk hchk
  refine ⟨f, hf, ?_, ?_⟩
  · intro a r hr
    obtain ⟨s, hs⟩ := hsound a r hr
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_flatMap, List.mem_range, mem_allStrings] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    refine ⟨h1, h2, fun w hw => ?_⟩
    have := h3 w ⟨w.length, by omega, rfl⟩
    exact ⟨(hiff _).2 ⟨s, this.1⟩, (hiff _).2 ⟨s, this.2⟩⟩
  · intro a r hr
    obtain ⟨h1, h2, h3⟩ := hr
    have hex : ∀ w ∈ (List.range (a.2 + 1)).flatMap allStrings, ∃ s,
        chkV (a.1, r.1, r.2, P.pair r.1 w) s = true ∧
          chkV (a.1, r.1, r.2, P.pair w r.2) s = true := by
      intro w hw
      simp only [List.mem_flatMap, List.mem_range, mem_allStrings] at hw
      obtain ⟨m, hm, hwm⟩ := hw
      obtain ⟨hv1, hv2⟩ := h3 w (by omega)
      obtain ⟨s1, hs1⟩ := (hiff (a.1, r.1, r.2, P.pair r.1 w)).1 hv1
      obtain ⟨s2, hs2⟩ := (hiff (a.1, r.1, r.2, P.pair w r.2)).1 hv2
      exact ⟨max s1 s2, hmono _ _ _ (le_max_left _ _) hs1, hmono _ _ _ (le_max_right _ _) hs2⟩
    choose! sw hsw using hex
    refine hdom a r (((List.range (a.2 + 1)).flatMap allStrings).toFinset.sup sw) ?_
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨h1, h2⟩, fun w hw => ?_⟩
    have hle : sw w ≤ ((List.range (a.2 + 1)).flatMap allStrings).toFinset.sup sw :=
      Finset.le_sup (f := sw) (List.mem_toFinset.2 hw)
    exact ⟨hmono _ _ _ hle (hsw w hw).1, hmono _ _ _ hle (hsw w hw).2⟩

/-- SUV Problem 336 (Section 13.1, printed p. 403).  `(x ∨~ y) → (x ∨ y)` has the same
complexity as `x ∨ y` up to `O(log n)` for strings of length at most `n`, lower bound:
`C(x ∨ y) ≤ C((x ∨~ y) → (x ∨ y)) + O(log n)`.
Proof idea (book's hint): a pair `(u, v)` of strings of
length at most `n` is compatible with a solution `p` if for all `w` of length at most `n` both
`[p]([u, w])` and `[p]([w, v])` solve `u ∨ v`; `(x, y)` is compatible, compatibility is
enumerable given `p` and `n`, and every compatible pair has `u = x` or `v = y`.  For the first
compatible pair output `[0, u]` or `[1, v]` according to one advice bit
(`problemK_le_of_partrec_advice`). -/
theorem problemK_disj_le_imp_pdisj_disj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.disj {x} {y}) ≤
        problemK D (P.imp (P.pdisj {x} {y}) (P.disj {x} {y})) + (logSlack k n : ℕ∞) := by
  obtain ⟨f0, hf0, hf0s, hf0d⟩ := problemK_disj_le_imp_pdisj_disj_compat_search P hP
  obtain ⟨hpair, -, hinv, -, htag, -, -⟩ := hP
  let f : BitString × (ℕ × Bool) →. BitString := fun q =>
    (f0 (q.1, q.2.1)).map (fun r => bif q.2.2 then P.pair P.tag1 r.2 else P.pair P.tag0 r.1)
  have hf : Partrec f := by
    have h1 : Partrec fun q : BitString × (ℕ × Bool) => f0 (q.1, q.2.1) :=
      hf0.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))
    refine Partrec.map h1 ?_
    exact (Computable.cond (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (hpair.comp (Computable.const P.tag1) (Computable.snd.comp Computable.snd))
      (hpair.comp (Computable.const P.tag0) (Computable.fst.comp Computable.snd))).to₂
  obtain ⟨c, hc⟩ := problemK_le_of_partrec_advice D hD f hf
  have hinj : ∀ a b c d, P.pair a b = P.pair c d → a = c ∧ b = d := by
    intro a b c d h
    have := congrArg P.unpair h
    rw [hinv, hinv] at this
    simpa using this
  refine ⟨c, fun n x y hx hy => hc _ _ n ?_⟩
  intro p hp
  have hcompat : problemK_disj_le_imp_pdisj_disj_compat P p n x y := by
    refine ⟨hx, hy, fun w hw => ⟨?_, ?_⟩⟩
    · obtain ⟨r, hr, hrl⟩ := hp (P.pair x w) ⟨x, w, rfl, Or.inl rfl⟩
      rcases hr with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
      · rw [Set.mem_singleton_iff] at hx'; subst hx'; exact Or.inl hrl
      · rw [Set.mem_singleton_iff] at hy'; subst hy'; exact Or.inr hrl
    · obtain ⟨r, hr, hrl⟩ := hp (P.pair w y) ⟨w, y, rfl, Or.inr rfl⟩
      rcases hr with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩
      · rw [Set.mem_singleton_iff] at hx'; subst hx'; exact Or.inl hrl
      · rw [Set.mem_singleton_iff] at hy'; subst hy'; exact Or.inr hrl
  have hdom := hf0d (p, n) (x, y) hcompat
  set r := (f0 (p, n)).get hdom with hr
  have hrmem : r ∈ f0 (p, n) := Part.get_mem hdom
  obtain ⟨hu, hv, hw⟩ := hf0s (p, n) r hrmem
  have key : r.1 = x ∨ r.2 = y := by
    obtain ⟨r', hr', hrl⟩ := hp (P.pair r.1 y) ⟨r.1, y, rfl, Or.inr rfl⟩
    have hval := (hw y hy).1
    have hr'' : r' = P.pair P.tag0 r.1 ∨ r' = P.pair P.tag1 r.2 := by
      rcases hval with h | h
      · exact Or.inl (Part.mem_unique hrl h)
      · exact Or.inr (Part.mem_unique hrl h)
    rcases hr' with ⟨x', hx', rfl⟩ | ⟨y', hy', rfl⟩ <;>
    rcases hr'' with h | h
    · rw [Set.mem_singleton_iff] at hx'; subst hx'
      exact Or.inl (hinj _ _ _ _ h).2.symm
    · rw [Set.mem_singleton_iff] at hx'; subst hx'
      exact absurd (hinj _ _ _ _ h).1 htag
    · rw [Set.mem_singleton_iff] at hy'; subst hy'
      exact absurd (hinj _ _ _ _ h).1.symm htag
    · rw [Set.mem_singleton_iff] at hy'; subst hy'
      exact Or.inr (hinj _ _ _ _ h).2.symm
  rcases key with h | h
  · refine ⟨false, P.pair P.tag0 r.1, Or.inl ⟨x, rfl, by rw [h]⟩, ?_⟩
    exact Part.mem_map_iff _ |>.2 ⟨r, hrmem, rfl⟩
  · refine ⟨true, P.pair P.tag1 r.2, Or.inr ⟨y, rfl, by rw [h]⟩, ?_⟩
    exact Part.mem_map_iff _ |>.2 ⟨r, hrmem, rfl⟩

/-- Compatibility of the pair `(u, v)` with a program `p` at scale `m` (SUV Problem 336, printed
p. 403, used in Problem 337): `u`, `v` have length at most `m` and for every `w` of length at
most `m` the value `[p]([u, w])` is defined and solves `u ∨ v`. -/
private def problemK_imp_imp_pdisj_disj_pdisj_le_log_compat (P : ProblemCalculus) (m : ℕ)
    (p u v : BitString) : Prop :=
  u.length ≤ m ∧ v.length ≤ m ∧
    ∀ w : BitString, w.length ≤ m → ∃ z ∈ P.disj {u} {v}, z ∈ P.lang (p, P.pair u w)

/-- Soundness of the code of a partial computable function: a halting `evaln` run gives a value
of the function. -/
private lemma problemK_imp_imp_pdisj_disj_pdisj_le_log_search_aux_sound
    {α β : Type*} [Primcodable α] [Primcodable β] (f : α →. β)
    (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind
        (fun a => Part.map Encodable.encode (f a)))
    (k : ℕ) (a : α) (r : ℕ) (h : Nat.Partrec.Code.evaln k c (Encodable.encode a) = some r) :
    ∃ z ∈ f a, Encodable.encode z = r := by
  have h1 := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr h)
  rw [hc] at h1
  simpa using h1

/-- Completeness of the code of a partial computable function: every value is reached by some
`evaln` run. -/
private lemma problemK_imp_imp_pdisj_disj_pdisj_le_log_search_aux_complete
    {α β : Type*} [Primcodable α] [Primcodable β] (f : α →. β)
    (c : Nat.Partrec.Code)
    (hc : c.eval = fun n => (Part.ofOption (Encodable.decode (α := α) n)).bind
        (fun a => Part.map Encodable.encode (f a)))
    (a : α) (z : β) (hz : z ∈ f a) :
    ∃ k, Nat.Partrec.Code.evaln k c (Encodable.encode a) = some (Encodable.encode z) := by
  have h1 : Encodable.encode z ∈ c.eval (Encodable.encode a) := by
    rw [hc]
    exact Part.mem_bind_iff.2 ⟨a, by simp, Part.mem_map_iff _ |>.2 ⟨z, hz, rfl⟩⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 h1
  exact ⟨k, Option.mem_def.mp hk⟩

/-- The stage-`k` compatibility test for the pair `(u, v)` with the program `p` at scale `m`,
for input `((m, p), (u, v), k)`: `u`, `v` have length at most `m` and, for every `w` of length at
most `m`, the `k`-step run of the code `c` of `P.lang` on `(p, [u, w])` halts with `[0, u]` or
`[1, v]` (all compared through `Encodable.encode`). -/
private def problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk
    (P : ProblemCalculus) (c : Nat.Partrec.Code)
    (a : (ℕ × BitString) × (BitString × BitString) × ℕ) : Bool :=
  decide (a.2.1.1.length ≤ a.1.1) && decide (a.2.1.2.length ≤ a.1.1) &&
    !((allStringsUpTo a.1.1).any fun w =>
      !((Nat.Partrec.Code.evaln a.2.2 c (Encodable.encode (a.1.2, P.pair a.2.1.1 w))).map
        (fun r => decide (r = Encodable.encode (P.pair P.tag0 a.2.1.1)) ||
          decide (r = Encodable.encode (P.pair P.tag1 a.2.1.2)))).getD false)

/-- The stage-`k` compatibility test is computable. -/
private lemma problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_computable
    (P : ProblemCalculus) (hpair : Computable₂ P.pair)
    (c : Nat.Partrec.Code) :
    Computable (problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c) := by
  have hm : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ => a.1.1 :=
    Computable.fst.comp Computable.fst
  have hp : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ => a.1.2 :=
    Computable.snd.comp Computable.fst
  have hu : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ => a.2.1.1 :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hv : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ => a.2.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hk : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ => a.2.2 :=
    Computable.snd.comp Computable.snd
  have hlen : Computable (List.length : BitString → ℕ) := Primrec.list_length.to_comp
  have hle := Primrec.nat_le.decide.to_comp
  have h1 := hle.comp (hlen.comp hu) hm
  have h2 := hle.comp (hlen.comp hv) hm
  have h3 : Computable fun a : (ℕ × BitString) × (BitString × BitString) × ℕ =>
      (allStringsUpTo a.1.1).any fun w =>
      !((Nat.Partrec.Code.evaln a.2.2 c (Encodable.encode (a.1.2, P.pair a.2.1.1 w))).map
        (fun r => decide (r = Encodable.encode (P.pair P.tag0 a.2.1.1)) ||
          decide (r = Encodable.encode (P.pair P.tag1 a.2.1.2)))).getD false := by
    have hev : Computable fun q : ((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString =>
          (Nat.Partrec.Code.evaln q.1.2.2 c
            (Encodable.encode (q.1.1.2, P.pair q.1.2.1.1 q.2))) :=
        (evalnCoreComputable c).comp (Computable.pair (hk.comp Computable.fst)
          (Computable.encode.comp (Computable.pair (hp.comp Computable.fst)
            (hpair.comp (hu.comp Computable.fst) Computable.snd))))
    have hu' : Computable fun q :
        (((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString) × ℕ =>
          q.1.1.2.1.1 := hu.comp (Computable.fst.comp Computable.fst)
    have hv' : Computable fun q :
        (((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString) × ℕ =>
          q.1.1.2.1.2 := hv.comp (Computable.fst.comp Computable.fst)
    have he1 : Computable fun q :
        (((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString) × ℕ =>
        Encodable.encode (P.pair P.tag0 q.1.1.2.1.1) :=
      Computable.encode.comp (hpair.comp (Computable.const P.tag0) hu')
    have he2 : Computable fun q :
        (((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString) × ℕ =>
        Encodable.encode (P.pair P.tag1 q.1.1.2.1.2) :=
      Computable.encode.comp (hpair.comp (Computable.const P.tag1) hv')
    have hdec := Primrec.eq.decide.to_comp (α := ℕ)
    have hg : Computable₂ fun (x : ((ℕ × BitString) × (BitString × BitString) × ℕ) × BitString)
        (r : ℕ) => decide (r = Encodable.encode (P.pair P.tag0 x.1.2.1.1)) ||
          decide (r = Encodable.encode (P.pair P.tag1 x.1.2.1.2)) :=
      (Primrec.or.to_comp.comp (hdec.comp Computable.snd he1) (hdec.comp Computable.snd he2))
    have htest : Computable₂ fun (a : (ℕ × BitString) × (BitString × BitString) × ℕ)
        (w : BitString) => !((Nat.Partrec.Code.evaln a.2.2 c
          (Encodable.encode (a.1.2, P.pair a.2.1.1 w))).map
        (fun r => decide (r = Encodable.encode (P.pair P.tag0 a.2.1.1)) ||
          decide (r = Encodable.encode (P.pair P.tag1 a.2.1.2)))).getD false :=
      Primrec.not.to_comp.comp
        (Computable.option_getD (Computable.option_map hev hg) (Computable.const false))
    exact computable_list_any (allStringsUpTo_primrec.to_comp.comp hm) htest
  exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp h1 h2) (Primrec.not.to_comp.comp h3))

/-- A passed stage test implies compatibility. -/
private lemma problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_sound
    (P : ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (P.lang a)))
    (m : ℕ) (p u v : BitString) (k : ℕ)
    (h : problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c ((m, p), (u, v), k) = true) :
    problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p u v := by
  unfold problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_false] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun w hw => ?_⟩
  have h4 := h3 w ((mem_allStringsUpTo m w).2 hw)
  cases hev : Nat.Partrec.Code.evaln k c (Encodable.encode (p, P.pair u w)) with
  | none =>
    simp only [hev, Option.map_none, Option.getD_none] at h4
    exact absurd trivial h4
  | some r =>
    simp only [hev, Option.map_some, Option.getD_some] at h4
    obtain ⟨z, hz, hzr⟩ :=
      problemK_imp_imp_pdisj_disj_pdisj_le_log_search_aux_sound P.lang c hc k
        (p, P.pair u w) r hev
    refine ⟨z, ?_, hz⟩
    have h5 : r = Encodable.encode (P.pair P.tag0 u) ∨
        r = Encodable.encode (P.pair P.tag1 v) := by
      have h6 := by simpa using h4
      exact Classical.or_iff_not_imp_left.2 h6
    rcases h5 with h | h
    · rw [h] at hzr
      exact Or.inl ⟨u, rfl, (Encodable.encode_injective hzr).symm⟩
    · rw [h] at hzr
      exact Or.inr ⟨v, rfl, (Encodable.encode_injective hzr).symm⟩

/-- A compatible pair passes the stage test at some stage. -/
private lemma problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_complete
    (P : ProblemCalculus) (c : Nat.Partrec.Code)
    (hc : c.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (P.lang a)))
    (m : ℕ) (p u v : BitString)
    (h : problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p u v) :
    ∃ k, problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c ((m, p), (u, v), k) =
      true := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ w : BitString, w.length ≤ m → ∃ k r,
      Nat.Partrec.Code.evaln k c (Encodable.encode (p, P.pair u w)) = some r ∧
        (r = Encodable.encode (P.pair P.tag0 u) ∨ r = Encodable.encode (P.pair P.tag1 v)) := by
    intro w hw
    obtain ⟨z, hz, hzl⟩ := h3 w hw
    obtain ⟨k, hk⟩ :=
      problemK_imp_imp_pdisj_disj_pdisj_le_log_search_aux_complete P.lang c hc
        (p, P.pair u w) z hzl
    refine ⟨k, _, hk, ?_⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · rw [Set.mem_singleton_iff] at ha; subst ha; exact Or.inl rfl
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact Or.inr rfl
  choose! K R hK using key
  refine ⟨(allStringsUpTo m).toFinset.sup K, ?_⟩
  unfold problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_false]
  refine ⟨⟨h1, h2⟩, fun w hw => ?_⟩
  have hwm : w.length ≤ m := (mem_allStringsUpTo m w).1 hw
  obtain ⟨he, hor⟩ := hK w hwm
  have hle : K w ≤ (allStringsUpTo m).toFinset.sup K :=
    Finset.le_sup (f := K) (List.mem_toFinset.2 hw)
  have he' := Nat.Partrec.Code.evaln_mono hle (Option.mem_def.mpr he)
  rw [Option.mem_def] at he'
  simp only [he', Option.map_some, Option.getD_some]
  simpa using Classical.or_iff_not_imp_left.1 hor

/-- Step 1 of the proof of `problemK_imp_imp_pdisj_disj_pdisj_le_log`: the search
algorithm.  There is a partial computable `F` such that for all `m` and `p`, if some pair is
compatible with `p` at scale `m` (`problemK_imp_imp_pdisj_disj_pdisj_le_log_compat`), then
`F (m, p)` is defined and equals `[u, v]` for some compatible pair `(u, v)`.
Proof idea: compatibility of `(u, v)` is semi-decidable (finitely many `w`, each requiring that the
partial computable `P.lang` converges on `(p, [u, w])` to `[0, u]` or `[1, v]`), the candidate pairs
are the strings of length at most `m`; dovetail over pairs and computation steps
(`IsRE`, `Partrec.rfindOpt` / `Code.evaln`, cf. `Kolmogorov.IsRE.exists_encodable`) and output
`[u, v]` for the first pair whose check succeeds. -/
private theorem problemK_imp_imp_pdisj_disj_pdisj_le_log_search
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ F : ℕ × BitString →. BitString, Partrec F ∧ ∀ (m : ℕ) (p : BitString),
      (∃ u v, problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p u v) →
        ∃ u v, problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p u v ∧
          P.pair u v ∈ F (m, p) := by
  classical
  have hpair : Computable₂ P.pair := hP.1
  have hlang : Partrec P.lang := hP.2.2.2.2.2.1
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hlang
  let probe : ℕ × BitString → ℕ → Option BitString := fun a s =>
    (Encodable.decode (α := BitString × BitString) s.unpair.1).bind fun uv =>
      bif problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c (a, uv, s.unpair.2)
      then some (P.pair uv.1 uv.2) else none
  have hprobe : Computable₂ probe := by
    refine Computable.option_bind
      (Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd)))
      ?_
    have hchk : Computable fun q : ((ℕ × BitString) × ℕ) × (BitString × BitString) =>
        problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c
          (q.1.1, q.2, q.1.2.unpair.2) :=
      (problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_computable P hpair c).comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair Computable.snd
            (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))))
    exact (Computable.cond hchk
      (Computable.option_some.comp (hpair.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)))
      (Computable.const none)).to₂
  refine ⟨fun a => Nat.rfindOpt (probe a), Partrec.rfindOpt hprobe, fun m p hex => ?_⟩
  obtain ⟨u, v, hcmp⟩ := hex
  obtain ⟨k, hk⟩ :=
    problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_complete P c hc m p u v hcmp
  have hs : P.pair u v ∈ probe (m, p) (Nat.pair (Encodable.encode (u, v)) k) := by
    simp [probe, hk]
  have hdom : (Nat.rfindOpt (probe (m, p))).Dom := Nat.rfindOpt_dom.2 ⟨_, _, hs⟩
  have hmem := Part.get_mem hdom
  obtain ⟨s, hs'⟩ := Nat.rfindOpt_spec hmem
  simp only [probe] at hs'
  cases hd : Encodable.decode (α := BitString × BitString) s.unpair.1 with
  | none => simp [hd] at hs'
  | some uv =>
    rw [hd] at hs'
    simp only [Option.bind_some] at hs'
    cases hch : problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk P c
        ((m, p), uv, s.unpair.2) with
    | false => simp [hch] at hs'
    | true =>
      simp only [hch, Bool.cond_true, Option.mem_def, Option.some.injEq] at hs'
      refine ⟨uv.1, uv.2,
        problemK_imp_imp_pdisj_disj_pdisj_le_log_search_chk_sound P c hc m p uv.1 uv.2
          s.unpair.2 hch, ?_⟩
      rw [hs']; exact hmem

/-- Step 2 of the proof of `problemK_imp_imp_pdisj_disj_pdisj_le_log`: for strings
`x`, `y` of length at most `m` and every solution `p` of `(x ∨~ y) → (x ∨ y)`, the pair `(x, y)` is
compatible with `p`, and every compatible pair `(u, v)` has `u = x` or `v = y`, i.e. `[u, v]` solves
`x ∨~ y`.  (Take `w = y`: `[p]([u, y])` solves both `x ∨ y` and `u ∨ v`, and the pairing is
injective with distinct tags.) -/
private theorem problemK_imp_imp_pdisj_disj_pdisj_le_log_step2_compat
    (P : ProblemCalculus) (hP : P.Admissible) (m : ℕ) (x y : BitString)
    (hx : x.length ≤ m) (hy : y.length ≤ m) (p : BitString)
    (hp : p ∈ P.imp (P.pdisj {x} {y}) (P.disj {x} {y})) :
    problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p x y ∧
      ∀ u v, problemK_imp_imp_pdisj_disj_pdisj_le_log_compat P m p u v →
        P.pair u v ∈ P.pdisj {x} {y} := by
  obtain ⟨-, -, hinv, -, htag, -⟩ := hP
  have hinj : ∀ a b c d, P.pair a b = P.pair c d → a = c ∧ b = d := by
    intro a b c d h
    have := congrArg P.unpair h
    rw [hinv, hinv] at this
    simpa using this
  refine ⟨⟨hx, hy, fun w _ => hp _ ⟨x, w, rfl, Or.inl rfl⟩⟩, fun u v huv => ?_⟩
  obtain ⟨-, -, h⟩ := huv
  obtain ⟨z, hz, hzl⟩ := h y hy
  obtain ⟨z', hz', hzl'⟩ := hp _ ⟨u, y, rfl, Or.inr rfl⟩
  have hzz : z = z' := Part.mem_unique hzl hzl'
  subst hzz
  refine ⟨u, v, rfl, ?_⟩
  rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;>
    rcases hz' with ⟨a', ha', h'⟩ | ⟨b', hb', h'⟩
  · rw [Set.mem_singleton_iff] at ha ha'
    subst ha ha'
    exact Or.inl (Set.mem_singleton_iff.2 (hinj _ _ _ _ h').2.symm)
  · exact absurd (hinj _ _ _ _ h').1.symm htag
  · exact absurd (hinj _ _ _ _ h').1 htag
  · rw [Set.mem_singleton_iff] at hb hb'
    subst hb hb'
    exact Or.inr (Set.mem_singleton_iff.2 (hinj _ _ _ _ h').2.symm)

/-- SUV Problem 337 (Section 13.1, printed p. 403).  "Show that the problem
`((x ∨~ y) → (x ∨ y)) → (x ∨~ y)` has complexity `O(log n)` if `x` and `y` are strings of length
at most `n`."
Proof idea: with the compatibility notion of Problem 336 (`(x, y)` is compatible with every
solution `p` of `(x ∨~ y) → (x ∨ y)`, compatibility is enumerable given `p` and `n`, and every
compatible pair `(u, v)` has `u = x` or `v = y`), the program that, given `p`, outputs `[u, v]`
for the first compatible pair solves the problem; it depends on `n` only (Gödel property, `n`
hardwired). -/
theorem problemK_imp_imp_pdisj_disj_pdisj_le_log (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n → y.length ≤ n →
      problemK D (P.imp (P.imp (P.pdisj {x} {y}) (P.disj {x} {y})) (P.pdisj {x} {y})) ≤
        (logSlack k n : ℕ∞) := by
  obtain ⟨F, hF, hFspec⟩ := problemK_imp_imp_pdisj_disj_pdisj_le_log_search P hP
  have hG := hP.2.2.2.2.2.2
  have hpow : Computable (fun s : BitString => 2 ^ s.length) := by
    have h : Primrec (fun s : BitString => s.foldr (fun _ a => 2 * a) 1) :=
      Primrec.list_foldr Primrec.id (Primrec.const 1)
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)).to₂
    refine h.to_comp.of_eq fun s => ?_
    induction s with
    | nil => rfl
    | cons b s ih =>
      change 2 * List.foldr (fun _ a => 2 * a) 1 s = 2 ^ (s.length + 1)
      rw [ih, pow_succ, mul_comm]
  obtain ⟨t, ht, hts⟩ := hG (fun r => F (2 ^ r.1.length, r.2))
    (hF.comp ((hpow.comp Computable.fst).pair Computable.snd))
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t ht
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  refine ⟨c1 + c2 + 1, fun n x y hx hy => ?_⟩
  set s : BitString := List.replicate (Nat.size n) false with hs
  have hm : n ≤ 2 ^ s.length := by
    rw [hs, List.length_replicate]; exact (Nat.lt_size_self n).le
  have hmem : t s ∈ P.imp (P.imp (P.pdisj {x} {y}) (P.disj {x} {y})) (P.pdisj {x} {y}) := by
    intro p hp
    obtain ⟨hc, hall⟩ := problemK_imp_imp_pdisj_disj_pdisj_le_log_step2_compat P hP
      (2 ^ s.length) x y (hx.trans hm) (hy.trans hm) p hp
    obtain ⟨u, v, huv, hF'⟩ := hFspec (2 ^ s.length) p ⟨x, y, hc⟩
    exact ⟨P.pair u v, hall u v huv, by rw [hts]; exact hF'⟩
  calc problemK D _ ≤ plainK D (t s) := problemK_le_of_mem D hmem
    _ ≤ plainK D s + c1 := hc1 s
    _ ≤ ((programLength s : ℕ∞) + c2) + c1 := by gcongr; exact hc2 s
    _ ≤ (logSlack (c1 + c2 + 1) n : ℕ∞) := by
        have hl : programLength s = Nat.size n := by simp [programLength, hs]
        have hb : (Nat.bits n).length = Nat.size n := Nat.size_eq_bits_len n
        rw [hl]
        have : Nat.size n + c2 + c1 ≤ logSlack (c1 + c2 + 1) n := by
          unfold logSlack
          rw [hb]
          nlinarith [Nat.zero_le (Nat.size n * c1), Nat.zero_le (Nat.size n * c2)]
        exact_mod_cast this

end InformationLogic
end Kolmogorov
