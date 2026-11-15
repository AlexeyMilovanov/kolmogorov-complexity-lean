import KolmogorovMathlib.InformationLogic.OperationsComplexity

/-!
# A problem whose complexity is not expressible through complexities of tuples (SUV §13.6)

The problem `(a → c) ∧ (b → d)`: three upper and two lower bounds (Problem 342) and a gap
between them (Problem 343), with the definitions used by Theorem 247 (two quadruples with the
same complexity profile, all strings, pairs, triples and the quadruple up to `O(log n)`, but
problem complexities differing by a linear amount) and Problem 344 (the same for
`(p ∨ q) → (r ∨ s)`).  Theorem 247 and Problem 344 themselves are stated in
`InformationLogic.NonTupleLemmas`, after the two lemmas of the book's proofs, so that their
proofs can use those lemmas.

A quadruple is a map `Fin 4 → BitString`, `(a, b, c, d) = (q 0, q 1, q 2, q 3)`; a sub-tuple is
coded with `listCode` in increasing index order.  "Logarithmic accuracy" is `O(log n)` for
strings of length at most `n`.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- The code of the sub-tuple of `u` indexed by `S` (increasing index order). -/
def subtupleCode {k : ℕ} (u : Fin k → BitString) (S : Finset (Fin k)) : BitString :=
  listCode (((List.finRange k).filter (fun i => decide (i ∈ S))).map u)

/-- The complexities of all sub-tuples (single strings, pairs, triples, …, the whole tuple) of
`u` and `v` agree up to `slack`. -/
def TupleProfileClose (D : Map) {k : ℕ} (slack : ℕ) (u v : Fin k → BitString) : Prop :=
  ∀ S : Finset (Fin k), S.Nonempty →
    plainK D (subtupleCode u S) ≤ plainK D (subtupleCode v S) + (slack : ℕ∞) ∧
      plainK D (subtupleCode v S) ≤ plainK D (subtupleCode u S) + (slack : ℕ∞)

/-- The problem `(a → c) ∧ (b → d)` for the quadruple `q = (a, b, c, d)`. -/
def quadProblem (P : ProblemCalculus) (q : Fin 4 → BitString) : Set BitString :=
  P.conj (P.imp {q 0} {q 2}) (P.imp {q 1} {q 3})

/-- The problem `(p ∨ q) → (r ∨ s)` for the quadruple `(p, q, r, s)` (Problem 344). -/
def disjImpProblem (P : ProblemCalculus) (q : Fin 4 → BitString) : Set BitString :=
  P.imp (P.disj {q 0} {q 1}) (P.disj {q 2} {q 3})

/-- The three upper bounds of Problem 342 for `(a → c) ∧ (b → d)`:
`C(c|a) + C(d|b)`, `C(d|b, c) + C(c)`, `C(c|a, d) + C(d)`. -/
noncomputable def upperBound342 (D : Map) (a b c d : BitString) : Fin 3 → ℕ∞ :=
  ![condK D c a + condK D d b, condK D d (pairCode b c) + plainK D c,
    condK D c (pairCode a d) + plainK D d]

/-- The two lower bounds of Problem 342, `C(b, c, d | a) − C(b | a, c)` and
`C(a, c, d | b) − C(a | b, d)`, as pairs (minuend, subtrahend), avoiding truncated
subtraction. -/
noncomputable def lowerBound342 (D : Map) (a b c d : BitString) : Fin 2 → ℕ∞ × ℕ∞ :=
  ![(condK D (listCode [b, c, d]) a, condK D b (pairCode a c)),
    (condK D (listCode [a, c, d]) b, condK D a (pairCode b d))]

/-- A shortest program for `x` given `y` exists and has length `≤ n + c` when `|x| ≤ n`. -/
private lemma problemK_quad_le_condK_add_condK_prog (D : Map) (hD : isOptimalConditional D) :
    ∃ c0 : ℕ, ∀ (n : ℕ) (x y : BitString), x.length ≤ n →
      ∃ p : BitString, produces D p y x ∧ p.length ≤ n + c0 ∧
        (p.length : ℕ∞) ≤ condK D x y := by
  obtain ⟨c1, hc1⟩ := plainK_le_length D hD
  obtain ⟨c2, hc2⟩ := condK_le_plainK D hD
  refine ⟨c1 + c2, fun n x y hx => ?_⟩
  have hfin : condK D x y ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := by
    calc condK D x y ≤ plainK D x + (c2 : ℕ∞) := hc2 _ _
      _ ≤ (x.length : ℕ∞) + c1 + c2 := by gcongr; exact hc1 _
      _ ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := by
        push_cast
        rw [add_assoc]
        gcongr
  have hne : condK D x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hfin
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  obtain ⟨p, hp, hpr⟩ := (condK_le_iff D x y m).mp (le_of_eq hm.symm)
  refine ⟨p, hpr, ?_, ?_⟩
  · have : (m : ℕ∞) ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := hm ▸ hfin
    have h2 : m ≤ n + (c1 + c2) := by exact_mod_cast this
    exact le_trans hp h2
  · rw [← hm]
    exact_mod_cast hp

/-- SUV Problem 342 (Section 13.6, printed p. 417).  First upper bound: for all strings
`a, b, c, d` of length at most `n`, `C((a → c) ∧ (b → d)) ≤ C(c|a) + C(d|b) + O(log n)`
("with logarithmic accuracy"), the constant independent of the strings.
Proof idea (an exercise, no proof in the book): if `p` maps `a` to `c` and `q` maps `b` to `d`
(shortest conditional programs, lengths `≤ n + O(1)`), the Gödel translations of `p`, `q` form a
solution `[α, β]`; it is computable from the pair `(p, q)` coded self-delimitingly, which costs
`|p| + |q| + O(log n)` (`problemK_imp_singleton_le_condK`, `plainK_pair_le_add_two_log`). -/
theorem problemK_quad_le_condK_add_condK (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      problemK D (quadProblem P q) ≤
        condK D (q 2) (q 0) + condK D (q 3) (q 1) + (logSlack k n : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG D hD.1
  have hdf : Computable decodeFirst := CodedFiniteDistribution.decodeFirst_primrec.to_comp
  have hds : Computable decodeSecond := CodedFiniteDistribution.decodeSecond_primrec.to_comp
  let f : BitString → BitString := fun w => P.pair (t (decodeFirst w)) (t (decodeSecond w))
  have hf : Computable f := hpair.comp (ht.comp hdf) (ht.comp hds)
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD f hf
  obtain ⟨c0, hprog⟩ := problemK_quad_le_condK_add_condK_prog D hD
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 1 (c0 + c2)
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
  refine ⟨C + (c1 + k0 + c2 + c2), fun n q hq => ?_⟩
  obtain ⟨p, hpr, hplen, hpc⟩ := hprog n (q 2) (q 0) (hq 2)
  obtain ⟨p', hpr', hplen', hpc'⟩ := hprog n (q 3) (q 1) (hq 3)
  have h1 : t p ∈ P.imp {q 0} {q 2} := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨q 2, Set.mem_singleton _, by rw [hts]; exact hpr⟩
  have h2 : t p' ∈ P.imp {q 1} {q 3} := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨q 3, Set.mem_singleton _, by rw [hts]; exact hpr'⟩
  have hz : P.pair (t p) (t p') ∈ quadProblem P q := Set.mem_image2_of_mem h1 h2
  have hzf : P.pair (t p) (t p') = f (pairCode p p') := by
    simp only [f, decodeFirst_pairCode, decodeSecond_pairCode]
  obtain ⟨hp_eq, hp_le⟩ := hfin p
  obtain ⟨hp'_eq, hp'_le⟩ := hfin p'
  set m := cVal D p with hm
  have hmn : m ≤ 1 * n + (c0 + c2) := by omega
  have hlog : Nat.log 2 m ≤ (Nat.bits (1 * n + (c0 + c2))).length := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; simp
    have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
    have h2 : m < 2 ^ (Nat.bits (1 * n + (c0 + c2))).length := by
      rw [Nat.size_eq_bits_len]
      exact lt_of_le_of_lt hmn (Nat.lt_size_self _)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h1 h2)
    omega
  have hslack : 2 * Nat.log 2 m ≤ logSlack C n := by
    have h1 := hC n
    have h2 : logSlack 2 (1 * n + (c0 + c2)) = 2 * (Nat.bits (1 * n + (c0 + c2))).length + 2 :=
      rfl
    omega
  have hconst : c1 + k0 + c2 + c2 ≤ logSlack (c1 + k0 + c2 + c2) n := Nat.le_add_left _ _
  have hslack' : 2 * Nat.log 2 m + (c1 + k0 + c2 + c2) ≤
      logSlack (C + (c1 + k0 + c2 + c2)) n := by
    rw [logSlack_add_constants]
    omega
  calc problemK D (quadProblem P q)
      ≤ plainK D (P.pair (t p) (t p')) := problemK_le_of_mem D hz
    _ = plainK D (f (pairCode p p')) := by rw [hzf]
    _ ≤ plainK D (pairCode p p') + (c1 : ℕ∞) := hc1 _
    _ ≤ plainK D p + plainK D p' + ((2 * Nat.log 2 m + k0 : ℕ) : ℕ∞) + (c1 : ℕ∞) := by
        gcongr
        exact hk0 p p'
    _ ≤ ((p.length : ℕ∞) + c2) + ((p'.length : ℕ∞) + c2) +
          ((2 * Nat.log 2 m + k0 : ℕ) : ℕ∞) + (c1 : ℕ∞) := by
        gcongr
        · exact hc2 p
        · exact hc2 p'
    _ ≤ condK D (q 2) (q 0) + condK D (q 3) (q 1) +
          ((2 * Nat.log 2 m + (c1 + k0 + c2 + c2) : ℕ) : ℕ∞) := by
        have e : ((p.length : ℕ∞) + c2) + ((p'.length : ℕ∞) + c2) +
            ((2 * Nat.log 2 m + k0 : ℕ) : ℕ∞) + (c1 : ℕ∞) =
            (p.length : ℕ∞) + (p'.length : ℕ∞) +
              ((2 * Nat.log 2 m + (c1 + k0 + c2 + c2) : ℕ) : ℕ∞) := by
          push_cast; ring
        rw [e]
        gcongr
    _ ≤ condK D (q 2) (q 0) + condK D (q 3) (q 1) +
          (logSlack (C + (c1 + k0 + c2 + c2)) n : ℕ∞) := by
        gcongr

/-- Step 1 of the proof of `problemK_quad_le_condK_add_plainK_left`: a partial computable map `G`
of two programs `s`, `r` yields plain complexity at most `|s| + |r| + 2 |bits |s|| + O(1)`
(layout `pairCode (bits |s|) (s ++ r)`). -/
private theorem problemK_quad_le_condK_add_plainK_left_combine (D : Map)
    (hD : isOptimalConditional D) (G : BitString × BitString →. BitString)
    (hG : Partrec G) :
    ∃ c : ℕ, ∀ (s r v : BitString), v ∈ G (s, r) →
      plainK D v ≤ (s.length : ℕ∞) + (r.length : ℕ∞) +
        ((2 * (Nat.bits s.length).length + c : ℕ) : ℕ∞) := by
  let sp : BitString → BitString := fun w => (decodeSecond w).take (decodeBits (decodeFirst w))
  let pp : BitString → BitString := fun w => (decodeSecond w).drop (decodeBits (decodeFirst w))
  have hlen : Computable fun w : BitString => decodeBits (decodeFirst w) :=
    decodeBits_computable.comp decodeFirst_computable
  have hsp : Computable sp := Primrec.list_take.to_comp.comp hlen decodeSecond_computable
  have hpp : Computable pp := Primrec.list_drop.to_comp.comp hlen decodeSecond_computable
  let E : Map := fun pr => G (sp pr.1, pp pr.1)
  have hE : isDecompressor E :=
    Partrec.comp hG ((hsp.comp Computable.fst).pair (hpp.comp Computable.fst))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C + 1, fun s r v hv => ?_⟩
  set w : BitString := pairCode (Nat.bits s.length) (s ++ r) with hw
  have h1 : sp w = s := by
    simp only [sp, hw, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.take_left]
  have h2 : pp w = r := by
    simp only [pp, hw, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.drop_left]
  have hprod : produces E w [] v := by
    change v ∈ G (sp w, pp w)
    rw [h1, h2]; exact hv
  calc plainK D v ≤ plainK E v + (C : ℕ∞) := hC v []
    _ ≤ (w.length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨w, hprod, rfl⟩
    _ ≤ _ := by
      rw [hw, length_pairCode, List.length_append]
      have h : (((Nat.bits s.length).length + 1 + (Nat.bits s.length).length +
          (s.length + r.length) + C : ℕ) : ℕ∞) ≤ (s.length : ℕ∞) + (r.length : ℕ∞) +
          ((2 * (Nat.bits s.length).length + (C + 1) : ℕ) : ℕ∞) := by
        rw [← Nat.cast_add, ← Nat.cast_add]
        exact_mod_cast (by omega)
      exact h

/-- Step 2 of the proof of `problemK_quad_le_condK_add_plainK_left`: the partial computable map
`(s, r) ↦ [α, β]` where `c = D(s, [])`, `α` is the Gödel translation of "print `c`" and `β` is
the Gödel translation of "on input `x` run `D` with program `r` on the condition `[x, c]`"; it is
correct whenever `s` is a program for `c` and `r` a program for `d` given `[b, c]`. -/
private theorem problemK_quad_le_condK_add_plainK_left_map (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ G : BitString × BitString →. BitString, Partrec G ∧
      ∀ (s r a b c d : BitString), c ∈ D (s, []) → d ∈ D (r, pairCode b c) →
        ∃ σ ∈ G (s, r), σ ∈ P.conj (P.imp {a} {c}) (P.imp {b} {d}) := by
  obtain ⟨hpair, -, -, -, -, hL⟩ := hP
  obtain ⟨t1, ht1, ht1e⟩ := hL.2 (fun pr => Part.some pr.1)
    (Computable.fst.partrec)
  obtain ⟨t2, ht2, ht2e⟩ := hL.2
    (fun pr => D (decodeFirst pr.1, pairCode pr.2 (decodeSecond pr.1)))
    (hD.1.comp ((decodeFirst_computable.comp Computable.fst).pair
      (Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
        (g := fun pr : BitString × BitString => (pr.2, decodeSecond pr.1)) pairCode_computable
        (Computable.snd.pair (decodeSecond_computable.comp Computable.fst)))))
  let G : BitString × BitString →. BitString := fun x =>
    (D (x.1, [])).bind fun c => Part.some (P.pair (t1 c) (t2 (pairCode x.2 c)))
  refine ⟨G, ?_, ?_⟩
  · refine Partrec.bind (hD.1.comp (Computable.fst.pair (Computable.const []))) ?_
    refine Computable.partrec ?_
    have h1 : Computable fun y : (BitString × BitString) × BitString => t1 y.2 :=
      ht1.comp Computable.snd
    have h2 : Computable fun y : (BitString × BitString) × BitString =>
        t2 (pairCode y.1.2 y.2) :=
      ht2.comp (Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
        (g := fun y : (BitString × BitString) × BitString => (y.1.2, y.2)) pairCode_computable
        ((Computable.snd.comp Computable.fst).pair Computable.snd))
    exact Computable.comp (f := fun p : BitString × BitString => P.pair p.1 p.2)
      (g := fun y : (BitString × BitString) × BitString => (t1 y.2, t2 (pairCode y.1.2 y.2)))
      hpair (h1.pair h2)
  · intro s r a b c d hc hd
    refine ⟨P.pair (t1 c) (t2 (pairCode r c)), ?_, ?_⟩
    · exact Part.mem_bind_iff.2 ⟨c, hc, Part.mem_some _⟩
    · refine ⟨t1 c, ?_, t2 (pairCode r c), ?_, rfl⟩
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨c, Set.mem_singleton _, ?_⟩
        rw [ht1e]
        exact Part.mem_some _
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨d, Set.mem_singleton _, ?_⟩
        rw [ht2e]
        simp only [decodeFirst_pairCode, decodeSecond_pairCode]
        exact hd

/-- SUV Problem 342 (Section 13.6, printed p. 417).  Second upper bound: for strings of length at
most `n`, `C((a → c) ∧ (b → d)) ≤ C(d | b, c) + C(c) + O(log n)`.
Proof idea (exercise): from a shortest program for `c` and a shortest program `r` for `d` given
`[b, c]` (coded self-delimitingly, `O(log n)` extra bits) compute `α` = "print `c`" and `β` =
"on input `x` run `r` on the condition `[x, c]`" (Gödel translations), and output `[α, β]`. -/
theorem problemK_quad_le_condK_add_plainK_left (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      problemK D (quadProblem P q) ≤
        condK D (q 3) (pairCode (q 1) (q 2)) + plainK D (q 2) + (logSlack k n : ℕ∞) := by
  obtain ⟨G, hG, hGs⟩ := problemK_quad_le_condK_add_plainK_left_map D hD P hP
  obtain ⟨c1, hc1⟩ := problemK_quad_le_condK_add_plainK_left_combine D hD G hG
  obtain ⟨ca, hca⟩ := condK_le_plainK D hD
  obtain ⟨cb, hcb⟩ := plainK_le_length D hD
  refine ⟨2 + 2 * (ca + cb) + c1, fun n q hq => ?_⟩
  have hmfin : plainK D (q 2) ≤ ((n + (ca + cb) : ℕ) : ℕ∞) := by
    calc plainK D (q 2) ≤ ((q 2).length : ℕ∞) + (cb : ℕ∞) := hcb _
      _ ≤ _ := by
        have := hq 2
        exact_mod_cast (by omega)
  have hefin : condK D (q 3) (pairCode (q 1) (q 2)) ≤ ((n + (ca + cb) : ℕ) : ℕ∞) := by
    calc condK D (q 3) (pairCode (q 1) (q 2)) ≤ plainK D (q 3) + (ca : ℕ∞) := hca _ _
      _ ≤ ((q 3).length : ℕ∞) + (cb : ℕ∞) + (ca : ℕ∞) := by gcongr; exact hcb _
      _ ≤ _ := by
        have := hq 3
        exact_mod_cast (by omega)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hmfin)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hefin)
  have hmN : m ≤ n + (ca + cb) := by
    rw [← hm] at hmfin; exact_mod_cast hmfin
  have heN : e ≤ n + (ca + cb) := by
    rw [← he] at hefin; exact_mod_cast hefin
  obtain ⟨s, hslen, hsprod⟩ := (condK_le_iff D (q 2) [] m).mp (le_of_eq hm.symm)
  obtain ⟨r, hrlen, hrprod⟩ := (condK_le_iff D (q 3) (pairCode (q 1) (q 2)) e).mp
    (le_of_eq he.symm)
  obtain ⟨σ, hσG, hσ⟩ := hGs s r (q 0) (q 1) (q 2) (q 3) hsprod hrprod
  have h1 := hc1 s r σ hσG
  have hsN : s.length ≤ n + (ca + cb) := le_trans hslen hmN
  have hL1 := length_natBits_mono hsN
  have hL2 : (Nat.bits (n + (ca + cb))).length ≤ (Nat.bits n).length + (ca + cb) := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    apply Nat.size_le.2
    rw [pow_add]
    have h1 := Nat.lt_size_self n
    have h2 : ca + cb < 2 ^ (ca + cb) := Nat.lt_two_pow_self
    nlinarith
  have hnum : s.length + r.length + (2 * (Nat.bits s.length).length + c1) ≤
      m + e + logSlack (2 + 2 * (ca + cb) + c1) n := by
    unfold logSlack
    have h3 : programLength s ≤ m := hslen
    have h4 : programLength r ≤ e := hrlen
    simp only [programLength] at h3 h4
    nlinarith [Nat.zero_le ((2 * (ca + cb) + c1) * (Nat.bits n).length)]
  calc problemK D (quadProblem P q) ≤ plainK D σ := problemK_le_of_mem D hσ
    _ ≤ (s.length : ℕ∞) + (r.length : ℕ∞) + ((2 * (Nat.bits s.length).length + c1 : ℕ) : ℕ∞) :=
      h1
    _ ≤ (m : ℕ∞) + (e : ℕ∞) + ((logSlack (2 + 2 * (ca + cb) + c1) n : ℕ) : ℕ∞) := by
      exact_mod_cast hnum
    _ = _ := by rw [he, hm]; ring

private lemma problemK_quad_le_condK_add_plainK_right_bits_add_le (n m : ℕ) :
    (Nat.bits (n + m)).length ≤ (Nat.bits n).length + m := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  apply Nat.size_le.2
  rw [pow_add]
  have h1 := Nat.lt_size_self n
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  nlinarith

/-- Step 1 of the proof of `problemK_quad_le_condK_add_plainK_right`: Gödel property
with the string `X` hardwired: if `r` produces `y` from `pairCode x X`, then `t (pairCode X r)`
solves `{x} → {y}`. -/
private theorem problemK_quad_le_condK_add_plainK_right_hardwire (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ t : BitString → BitString, Computable t ∧ ∀ r X x y : BitString,
      y ∈ D (r, pairCode x X) → t (pairCode X r) ∈ P.imp {x} {y} := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
  let V : Map := fun sx => D (decodeSecond sx.1, pairCode sx.2 (decodeFirst sx.1))
  have hV : Partrec V :=
    hD.1.comp ((decodeSecond_computable.comp Computable.fst).pair
      (hpc.comp Computable.snd (decodeFirst_computable.comp Computable.fst)))
  obtain ⟨t, ht, hts⟩ := hG V hV
  refine ⟨t, ht, fun r X x y h => ?_⟩
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  refine ⟨y, Set.mem_singleton y, ?_⟩
  rw [hts]
  simpa [V, decodeFirst_pairCode, decodeSecond_pairCode] using h

/-- Step 2 of the proof of `problemK_quad_le_condK_add_plainK_right`: a total computable
`t` such that `t d` is a program that prints `d` on every input. -/
private theorem problemK_quad_le_condK_add_plainK_right_const (P : ProblemCalculus)
    (hP : P.Admissible) :
    ∃ t : BitString → BitString, Computable t ∧ ∀ d x : BitString, d ∈ P.lang (t d, x) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  let V : Map := fun sx => Part.some sx.1
  have hV : Partrec V := Computable.partrec (Computable.fst : Computable
    (fun sx : BitString × BitString => sx.1))
  obtain ⟨t, ht, hts⟩ := hG V hV
  exact ⟨t, ht, fun d x => by rw [hts]; exact Part.mem_some d⟩

/-- Step 3 of the proof of `problemK_quad_le_condK_add_plainK_right`: a partial computable
map `F (r, p)` that runs `p` to get `d`, and outputs the solution `[α, β]` of
`(a → c) ∧ (b → d)` with `α` = "run `r` on `[x, d]`" and `β` = "print `d`".  It is correct
whenever `r` produces `c` from `[a, d]` and `p` produces `d`. -/
private theorem problemK_quad_le_condK_add_plainK_right_map (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ F : BitString × BitString →. BitString, Partrec F ∧
      ∀ (r p a b c d : BitString), c ∈ D (r, pairCode a d) → d ∈ D (p, []) →
        ∃ σ ∈ F (r, p), σ ∈ P.conj (P.imp {a} {c}) (P.imp {b} {d}) := by
  obtain ⟨t1, ht1, ht1s⟩ := problemK_quad_le_condK_add_plainK_right_hardwire D hD P hP
  obtain ⟨t2, ht2, ht2s⟩ := problemK_quad_le_condK_add_plainK_right_const P hP
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  let F : BitString × BitString →. BitString := fun x =>
    (D (x.2, [])).map fun d => P.pair (t1 (pairCode d x.1)) (t2 d)
  refine ⟨F, ?_, fun r p a b c d hc hd => ?_⟩
  · have h1 : Partrec fun x : BitString × BitString => D (x.2, []) :=
      hD.1.comp (Computable.snd.pair (Computable.const []))
    have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
    have h2 : Computable fun y : (BitString × BitString) × BitString =>
        P.pair (t1 (pairCode y.2 y.1.1)) (t2 y.2) :=
      hpair.comp (ht1.comp (hpc.comp Computable.snd (Computable.fst.comp Computable.fst)))
        (ht2.comp Computable.snd)
    exact Partrec.map h1 h2
  · refine ⟨_, Part.mem_map _ hd, ?_⟩
    exact Set.mem_image2_of_mem (ht1s r d a c hc) (fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨d, Set.mem_singleton d, ht2s d w⟩)

/-- Step 4 of the proof of `problemK_quad_le_condK_add_plainK_right`: a partial
computable map `F` of two programs `r`, `p` gives plain complexity at most
`|r| + |p| + 2 |bits |r|| + O(1)` (layout `pairCode (bits |r|) (r ++ p)`). -/
private theorem problemK_quad_le_condK_add_plainK_right_combine (D : Map)
    (hD : isOptimalConditional D) (F : BitString × BitString →. BitString) (hF : Partrec F) :
    ∃ c : ℕ, ∀ (r p v : BitString), v ∈ F (r, p) →
      plainK D v ≤ (r.length : ℕ∞) + (p.length : ℕ∞) +
        ((2 * (Nat.bits r.length).length + c : ℕ) : ℕ∞) := by
  let sp : BitString → BitString := fun r => (decodeSecond r).take (decodeBits (decodeFirst r))
  let pp : BitString → BitString := fun r => (decodeSecond r).drop (decodeBits (decodeFirst r))
  have hlen : Computable fun r : BitString => decodeBits (decodeFirst r) :=
    decodeBits_computable.comp decodeFirst_computable
  have hsp : Computable sp := Primrec.list_take.to_comp.comp hlen decodeSecond_computable
  have hpp : Computable pp := Primrec.list_drop.to_comp.comp hlen decodeSecond_computable
  let E : Map := fun pr => F (sp pr.1, pp pr.1)
  have hE : isDecompressor E :=
    Partrec.comp hF ((hsp.comp Computable.fst).pair (hpp.comp Computable.fst))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C + 1, fun r p v hv => ?_⟩
  set w : BitString := pairCode (Nat.bits r.length) (r ++ p) with hw
  have h1 : sp w = r := by
    simp only [sp, hw, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.take_left]
  have h2 : pp w = p := by
    simp only [pp, hw, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.drop_left]
  have hprod : produces E w [] v := by
    change v ∈ F (sp w, pp w)
    rw [h1, h2]; exact hv
  calc plainK D v ≤ condK E v [] + (C : ℕ∞) := hC v []
    _ ≤ (w.length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨w, hprod, rfl⟩
    _ ≤ _ := by
      rw [hw, length_pairCode, List.length_append]
      have h : (((Nat.bits r.length).length + 1 + (Nat.bits r.length).length +
          (r.length + p.length) + C : ℕ) : ℕ∞) ≤ (r.length : ℕ∞) + (p.length : ℕ∞) +
          ((2 * (Nat.bits r.length).length + (C + 1) : ℕ) : ℕ∞) := by
        rw [← Nat.cast_add, ← Nat.cast_add]
        exact_mod_cast (by omega)
      exact h

/-- SUV Problem 342 (Section 13.6, printed p. 417).  Third upper bound: for strings of length at
most `n`, `C((a → c) ∧ (b → d)) ≤ C(c | a, d) + C(d) + O(log n)`.
Proof idea (exercise; symmetric to the second bound): `β` = "print `d`", `α` = "on input `x` run
a shortest program for `c` given `[a, d]` on the condition `[x, d]`", both computed from the two
descriptions coded self-delimitingly. -/
theorem problemK_quad_le_condK_add_plainK_right (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      problemK D (quadProblem P q) ≤
        condK D (q 2) (pairCode (q 0) (q 3)) + plainK D (q 3) + (logSlack k n : ℕ∞) := by
  obtain ⟨F, hF, hFs⟩ := problemK_quad_le_condK_add_plainK_right_map D hD P hP
  obtain ⟨c1, hc1⟩ := problemK_quad_le_condK_add_plainK_right_combine D hD F hF
  obtain ⟨ca, hca⟩ := condK_le_plainK D hD
  obtain ⟨cb, hcb⟩ := plainK_le_length D hD
  refine ⟨2 * (ca + cb) + c1 + 2, fun n q hq => ?_⟩
  -- the program for `d`
  have hdfin : plainK D (q 3) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENat.natCast_ne_top ((q 3).length + cb)) ?_
    calc plainK D (q 3) ≤ ((q 3).length : ℕ∞) + (cb : ℕ∞) := hcb _
      _ = _ := by push_cast; rfl
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hdfin
  obtain ⟨p, hplen, hpprod⟩ := (condK_le_iff D (q 3) [] m).mp (le_of_eq hm.symm)
  -- the program for `c` given `[a, d]`
  have hcle : condK D (q 2) (pairCode (q 0) (q 3)) ≤ ((n + (ca + cb) : ℕ) : ℕ∞) := by
    calc condK D (q 2) (pairCode (q 0) (q 3)) ≤ plainK D (q 2) + (ca : ℕ∞) := hca _ _
      _ ≤ ((q 2).length : ℕ∞) + cb + ca := by gcongr; exact hcb _
      _ ≤ ((n + (ca + cb) : ℕ) : ℕ∞) := by
        have := hq 2
        push_cast
        rw [add_assoc, add_comm (cb : ℕ∞) (ca : ℕ∞)]
        gcongr
  have hcfin : condK D (q 2) (pairCode (q 0) (q 3)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcle
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hcfin
  obtain ⟨r, hrlen, hrprod⟩ := (condK_le_iff D _ _ e).mp (le_of_eq he.symm)
  have hrn : r.length ≤ n + (ca + cb) := by
    have h0 : (e : ℕ∞) ≤ ((n + (ca + cb) : ℕ) : ℕ∞) := by rw [he]; exact hcle
    have : programLength r ≤ n + (ca + cb) := hrlen.trans (by exact_mod_cast h0)
    simpa [programLength] using this
  obtain ⟨σ, hσF, hσ⟩ := hFs r p (q 0) (q 1) (q 2) (q 3) hrprod hpprod
  have h1 := hc1 r p σ hσF
  have hL1 := length_natBits_mono hrn
  have hL2 := problemK_quad_le_condK_add_plainK_right_bits_add_le n (ca + cb)
  have hnum : r.length + p.length + (2 * (Nat.bits r.length).length + c1) ≤
      e + m + logSlack (2 * (ca + cb) + c1 + 2) n := by
    unfold logSlack
    have : programLength p ≤ m := hplen
    have h4 : programLength r ≤ e := hrlen
    simp only [programLength] at this h4
    nlinarith [Nat.zero_le ((2 * (ca + cb) + c1) * (Nat.bits n).length)]
  calc problemK D (quadProblem P q) ≤ plainK D σ := problemK_le_of_mem D hσ
    _ ≤ (r.length : ℕ∞) + (p.length : ℕ∞) + ((2 * (Nat.bits r.length).length + c1 : ℕ) : ℕ∞) := h1
    _ ≤ (e : ℕ∞) + (m : ℕ∞) + ((logSlack (2 * (ca + cb) + c1 + 2) n : ℕ) : ℕ∞) := by
      exact_mod_cast hnum
    _ = condK D (q 2) (pairCode (q 0) (q 3)) + plainK D (q 3) +
        (logSlack (2 * (ca + cb) + c1 + 2) n : ℕ∞) := by rw [← he, ← hm]

private lemma condK_triple_le_problemK_quad_add_left_S1_comp : Computable t16_first_S1 := by
  have hA : Computable decodeFirst := decodeFirst_computable
  have hlen_p : Computable (fun w => decodeBits (decodeFirst w)) :=
    decodeBits_computable.comp hA
  have hrest : Computable decodeSecond := decodeSecond_computable
  exact Primrec.list_take.to_comp.comp hlen_p hrest

private lemma condK_triple_le_problemK_quad_add_left_S2_comp : Computable t16_first_S2 := by
  have hA : Computable decodeFirst := decodeFirst_computable
  have hlen_p : Computable (fun w => decodeBits (decodeFirst w)) :=
    decodeBits_computable.comp hA
  have hrest : Computable decodeSecond := decodeSecond_computable
  exact Primrec.list_drop.to_comp.comp hlen_p hrest

private lemma condK_triple_le_problemK_quad_add_left_pc {γ : Type} [Primcodable γ]
    {f g : γ → BitString} (hf : Computable f) (hg : Computable g) :
    Computable (fun x => pairCode (f x) (g x)) :=
  Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
    (g := fun x => (f x, g x)) pairCode_computable (hf.pair hg)

/-- The decompressor of the proof: from `w = [|r|, r ++ p]` and the condition `a` it runs `D` on
`p` to get a solution `s = [α, β]`, computes `c = [α](a)`, `b = D(r, [a, c])`, `d = [β](b)`
and outputs `[b, c, d]`. -/
private noncomputable def condK_triple_le_problemK_quad_add_left_E (P : ProblemCalculus)
    (D : Map) : Map := fun pr =>
  (D (t16_first_S2 pr.1, [])).bind fun s =>
    ((P.unpair s : Option (BitString × BitString)) : Part (BitString × BitString)).bind
      fun ab => (P.lang (ab.1, pr.2)).bind fun c =>
        (D (t16_first_S1 pr.1, pairCode pr.2 c)).bind fun b =>
          (P.lang (ab.2, b)).map fun d => listCode [b, c, d]

private lemma condK_triple_le_problemK_quad_add_left_E_isDecompressor (P : ProblemCalculus)
    (hP : P.Admissible) (D : Map) (hD : isDecompressor D) :
    isDecompressor (condK_triple_le_problemK_quad_add_left_E P D) := by
  obtain ⟨-, hunpair, -, -, -, hG⟩ := hP
  have hL : Partrec P.lang := hG.1
  have hS1 := condK_triple_le_problemK_quad_add_left_S1_comp
  have hS2 := condK_triple_le_problemK_quad_add_left_S2_comp
  unfold isDecompressor condK_triple_le_problemK_quad_add_left_E
  refine Partrec.bind (hD.comp ((hS2.comp Computable.fst).pair (Computable.const []))) ?_
  refine Partrec.bind (Computable.ofOption (hunpair.comp Computable.snd)) ?_
  refine Partrec.bind (hL.comp (((Computable.fst.comp Computable.snd).comp Computable.id).pair
    (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.id))))) ?_
  have hpr : Computable (fun y : ((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) => y.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hpair : Computable (fun y : ((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) => (y.1.1.1.2, y.2)) :=
    (Computable.snd.comp hpr).pair Computable.snd
  have hpc : Computable (fun y : ((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) => pairCode y.1.1.1.2 y.2) :=
    Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
      (g := fun y : ((((BitString × BitString) × BitString) ×
        (BitString × BitString)) × BitString) => (y.1.1.1.2, y.2)) pairCode_computable hpair
  have hs1 : Computable (fun y : ((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) => t16_first_S1 y.1.1.1.1) :=
    Computable.comp (f := t16_first_S1)
      (g := fun y : ((((BitString × BitString) × BitString) ×
        (BitString × BitString)) × BitString) => y.1.1.1.1) hS1
      (Computable.fst.comp hpr)
  have h4 : Partrec (fun y : ((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) =>
      D (t16_first_S1 y.1.1.1.1, pairCode y.1.1.1.2 y.2)) :=
    hD.comp (hs1.pair hpc)
  refine Partrec.bind h4 ?_
  have h5 : Partrec (fun y : (((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) × BitString) =>
      P.lang (y.1.1.2.2, y.2)) :=
    hL.comp ((Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst))).pair Computable.snd)
  refine Partrec.map h5 ?_
  have hz : Computable (fun z : ((((((BitString × BitString) × BitString) ×
      (BitString × BitString)) × BitString) × BitString) × BitString) =>
      pairCode z.1.2 (pairCode z.1.1.2 (pairCode z.2 []))) :=
    condK_triple_le_problemK_quad_add_left_pc (Computable.snd.comp Computable.fst)
      (condK_triple_le_problemK_quad_add_left_pc
        (Computable.snd.comp (Computable.fst.comp Computable.fst))
        (condK_triple_le_problemK_quad_add_left_pc Computable.snd (Computable.const [])))
  exact hz

private lemma condK_triple_le_problemK_quad_add_left_bits_add_le (n m : ℕ) :
    (Nat.bits (n + m)).length ≤ (Nat.bits n).length + m := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  apply Nat.size_le.2
  rw [pow_add]
  have h1 := Nat.lt_size_self n
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  nlinarith

/-- SUV Problem 342 (Section 13.6, printed p. 417).  First lower bound:
`C((a → c) ∧ (b → d)) ≥ C(b, c, d | a) − C(b | a, c)` with logarithmic accuracy, written without
subtraction: for strings of length at most `n`,
`C(b, c, d | a) ≤ C((a → c) ∧ (b → d)) + C(b | a, c) + O(log n)`.
Proof idea (exercise): given `a`, a shortest solution `[α, β]` and a shortest program for `b`
given `[a, c]` (separated by the self-delimiting length of the latter, `O(log n)` bits), compute
`c = [α](a)`, then `b`, then `d = [β](b)`. -/
theorem condK_triple_le_problemK_quad_add_left (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      condK D (listCode [q 1, q 2, q 3]) (q 0) ≤
        problemK D (quadProblem P q) + condK D (q 1) (pairCode (q 0) (q 2)) +
          (logSlack k n : ℕ∞) := by
  have hP' := hP
  obtain ⟨-, -, hinv, -, -, -⟩ := hP'
  obtain ⟨c_opt, hc_opt⟩ := hD.2 _ (condK_triple_le_problemK_quad_add_left_E_isDecompressor
    P hP D hD.1)
  obtain ⟨c1, hc1⟩ := plainK_le_length D hD
  obtain ⟨c2, hc2⟩ := condK_le_plainK D hD
  refine ⟨2 * (c1 + c2) + 3 + c_opt, fun n q hq => ?_⟩
  rcases (quadProblem P q).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, problemK_empty]; simp
  obtain ⟨s, hs, hseq⟩ := exists_mem_plainK_eq_problemK D hne
  -- a shortest program for `b` given `[a, c]` is short
  have hbfin : condK D (q 1) (pairCode (q 0) (q 2)) ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := by
    calc condK D (q 1) (pairCode (q 0) (q 2)) ≤ plainK D (q 1) + (c2 : ℕ∞) := hc2 _ _
      _ ≤ ((q 1).length : ℕ∞) + c1 + c2 := by gcongr; exact hc1 _
      _ ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := by
        have := hq 1
        push_cast
        rw [add_assoc]
        gcongr
  have hbne : (candidateLengths D (q 1) (pairCode (q 0) (q 2))).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : condK D (q 1) (pairCode (q 0) (q 2)) = ⊤ := by simp [condK, hemp]
    rw [this] at hbfin
    exact absurd hbfin (by simp)
  obtain ⟨r, hr, hrlen⟩ := csInf_mem hbne
  have hrlen' : (r.length : ℕ∞) = condK D (q 1) (pairCode (q 0) (q 2)) := hrlen
  have hrle : r.length ≤ n + (c1 + c2) := by
    have : (r.length : ℕ∞) ≤ ((n + (c1 + c2) : ℕ) : ℕ∞) := hrlen'.le.trans hbfin
    exact_mod_cast this
  -- a shortest program for the solution `s`
  have hsfin : plainK D s ≤ (s.length : ℕ∞) + c1 := hc1 s
  have hsne : (candidateLengths D s []).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : plainK D s = ⊤ := by simp [plainK, condK, hemp]
    rw [this] at hsfin
    exact absurd hsfin (by simp)
  obtain ⟨p, hp, hplen⟩ := csInf_mem hsne
  have hplen' : (p.length : ℕ∞) = problemK D (quadProblem P q) := by
    rw [← hseq]; exact hplen
  -- the components of the solution
  obtain ⟨α, hα, β, hβ, rfl⟩ := Set.mem_image2.1 hs
  obtain ⟨c', hc', hcmem⟩ := hα (q 0) (Set.mem_singleton _)
  obtain ⟨d', hd', hdmem⟩ := hβ (q 1) (Set.mem_singleton _)
  rw [Set.mem_singleton_iff] at hc' hd'
  subst hc' hd'
  -- the program for the decompressor
  set w : BitString := pairCode (Nat.bits r.length) (r ++ p) with hw
  have hw_eq : w = pairCode (Nat.bits r.length) (r ++ p) := rfl
  have hS1 : t16_first_S1 w = r := by
    dsimp [t16_first_S1]
    rw [hw_eq, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.take_left]
  have hS2 : t16_first_S2 w = p := by
    dsimp [t16_first_S2]
    rw [hw_eq, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.drop_left]
  have hprod : produces (condK_triple_le_problemK_quad_add_left_E P D) w (q 0)
      (listCode [q 1, q 2, q 3]) := by
    dsimp only [produces, condK_triple_le_problemK_quad_add_left_E]
    rw [hS1, hS2]
    have hcmem' : q 2 ∈ P.lang ((α, β).1, q 0) := hcmem
    have hdmem' : q 3 ∈ P.lang ((α, β).2, q 1) := hdmem
    refine Part.mem_bind hp (Part.mem_bind ?_ (Part.mem_bind hcmem'
      (Part.mem_bind hr (Part.mem_map _ hdmem'))))
    rw [hinv]
    exact Part.mem_some _
  have hw_len : w.length = r.length + p.length + (2 * (Nat.bits r.length).length + 1) := by
    rw [hw_eq, length_pairCode, List.length_append]
    omega
  have hcondE : condK (condK_triple_le_problemK_quad_add_left_E P D)
      (listCode [q 1, q 2, q 3]) (q 0) ≤ (w.length : ℕ∞) :=
    (condK_le_iff _ _ _ _).2 ⟨w, le_rfl, hprod⟩
  have hbits : (Nat.bits r.length).length ≤ (Nat.bits n).length + (c1 + c2) :=
    (length_natBits_mono hrle).trans (condK_triple_le_problemK_quad_add_left_bits_add_le n _)
  have hslack : 2 * (Nat.bits r.length).length + 1 + c_opt ≤
      logSlack (2 * (c1 + c2) + 3 + c_opt) n := by
    unfold logSlack
    nlinarith
  calc condK D (listCode [q 1, q 2, q 3]) (q 0)
      ≤ condK (condK_triple_le_problemK_quad_add_left_E P D)
          (listCode [q 1, q 2, q 3]) (q 0) + (c_opt : ℕ∞) := hc_opt _ _
    _ ≤ (w.length : ℕ∞) + (c_opt : ℕ∞) := by gcongr
    _ = (p.length : ℕ∞) + (r.length : ℕ∞) +
          ((2 * (Nat.bits r.length).length + 1 + c_opt : ℕ) : ℕ∞) := by
        rw [hw_len]; push_cast; ring
    _ ≤ problemK D (quadProblem P q) + condK D (q 1) (pairCode (q 0) (q 2)) +
          (logSlack (2 * (c1 + c2) + 3 + c_opt) n : ℕ∞) := by
        rw [hplen', hrlen']
        gcongr

/-- Step 1 of the proof of `condK_triple_le_problemK_quad_add_right`: a partial computable map `G`
of two programs `s`, `p` and the condition `b` yields conditional complexity at most
`|s| + |p| + 2 |bits |s|| + O(1)` (layout `pairCode (bits |s|) (s ++ p)`). -/
private theorem condK_triple_le_problemK_quad_add_right_combine (D : Map)
    (hD : isOptimalConditional D) (G : BitString × BitString × BitString →. BitString)
    (hG : Partrec G) :
    ∃ c : ℕ, ∀ (s p b v : BitString), v ∈ G (s, p, b) →
      condK D v b ≤ (s.length : ℕ∞) + (p.length : ℕ∞) +
        ((2 * (Nat.bits s.length).length + c : ℕ) : ℕ∞) := by
  let sp : BitString → BitString := fun r => (decodeSecond r).take (decodeBits (decodeFirst r))
  let pp : BitString → BitString := fun r => (decodeSecond r).drop (decodeBits (decodeFirst r))
  have hlen : Computable fun r : BitString => decodeBits (decodeFirst r) :=
    decodeBits_computable.comp decodeFirst_computable
  have hsp : Computable sp := Primrec.list_take.to_comp.comp hlen decodeSecond_computable
  have hpp : Computable pp := Primrec.list_drop.to_comp.comp hlen decodeSecond_computable
  let E : Map := fun pr => G (sp pr.1, pp pr.1, pr.2)
  have hE : isDecompressor E :=
    Partrec.comp hG (((hsp.comp Computable.fst).pair
      ((hpp.comp Computable.fst).pair Computable.snd)))
  obtain ⟨C, hC⟩ := hD.2 E hE
  refine ⟨C + 1, fun s p b v hv => ?_⟩
  set r : BitString := pairCode (Nat.bits s.length) (s ++ p) with hr
  have h1 : sp r = s := by
    simp only [sp, hr, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.take_left]
  have h2 : pp r = p := by
    simp only [pp, hr, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits,
      List.drop_left]
  have hprod : produces E r b v := by
    change v ∈ G (sp r, pp r, b)
    rw [h1, h2]; exact hv
  calc condK D v b ≤ condK E v b + (C : ℕ∞) := hC v b
    _ ≤ (r.length : ℕ∞) + (C : ℕ∞) := by
      gcongr
      exact sInf_le ⟨r, hprod, rfl⟩
    _ ≤ _ := by
      rw [hr, length_pairCode, List.length_append]
      have h : (((Nat.bits s.length).length + 1 + (Nat.bits s.length).length +
          (s.length + p.length) + C : ℕ) : ℕ∞) ≤ (s.length : ℕ∞) + (p.length : ℕ∞) +
          ((2 * (Nat.bits s.length).length + (C + 1) : ℕ) : ℕ∞) := by
        rw [← Nat.cast_add, ← Nat.cast_add]
        exact_mod_cast (by omega)
      exact h

/-- Step 2 of the proof of `condK_triple_le_problemK_quad_add_right`: the partial computable map
`(s, p, b) ↦ [a, c, d]` that runs `s` to get a solution `[α, β]`, computes `d = [β](b)`, runs `p`
on `[b, d]` to get `a`, and computes `c = [α](a)`; it is correct on every solution. -/
private theorem condK_triple_le_problemK_quad_add_right_map (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ G : BitString × BitString × BitString →. BitString, Partrec G ∧
      ∀ (s p a b c d σ : BitString), σ ∈ P.conj (P.imp {a} {c}) (P.imp {b} {d}) →
        σ ∈ D (s, []) → a ∈ D (p, pairCode b d) → listCode [a, c, d] ∈ G (s, p, b) := by
  obtain ⟨-, hunpair, hinv, -, -, hL, -⟩ := hP
  let fα : BitString → BitString := fun σ => ((P.unpair σ).map Prod.fst).getD []
  let fβ : BitString → BitString := fun σ => ((P.unpair σ).map Prod.snd).getD []
  have hfα : Computable fα :=
    Computable.option_getD (Computable.option_map hunpair
      (Computable.fst.comp Computable.snd).to₂) (Computable.const [])
  have hfβ : Computable fβ :=
    Computable.option_getD (Computable.option_map hunpair
      (Computable.snd.comp Computable.snd).to₂) (Computable.const [])
  let G : BitString × BitString × BitString →. BitString := fun x =>
    (D (x.1, [])).bind fun σ => (P.lang (fβ σ, x.2.2)).bind fun d =>
      (D (x.2.1, pairCode x.2.2 d)).bind fun a =>
        (P.lang (fα σ, a)).map fun c => listCode [a, c, d]
  refine ⟨G, ?_, ?_⟩
  · have h1 : Partrec fun x : BitString × BitString × BitString => D (x.1, []) :=
      hD.1.comp (Computable.fst.pair (Computable.const []))
    have h2 : Partrec fun y : (BitString × BitString × BitString) × BitString =>
        P.lang (fβ y.2, y.1.2.2) :=
      hL.comp ((hfβ.comp Computable.snd).pair (Computable.snd.comp (Computable.snd.comp
        Computable.fst)))
    have h3p : Computable fun y : ((BitString × BitString × BitString) × BitString) × BitString =>
        y.1.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have h3b : Computable fun y : ((BitString × BitString × BitString) × BitString) × BitString =>
        y.1.1.2.2 :=
      Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have h3d : Computable fun y : ((BitString × BitString × BitString) × BitString) × BitString =>
        y.2 := Computable.snd
    have h3pc : Computable fun y : ((BitString × BitString × BitString) × BitString) ×
        BitString => pairCode y.1.1.2.2 y.2 :=
      CodedFiniteDistribution.pairCode_primrec.to_comp.comp h3b h3d
    have h3 : Partrec fun y : ((BitString × BitString × BitString) × BitString) × BitString =>
        D (y.1.1.2.1, pairCode y.1.1.2.2 y.2) :=
      hD.1.comp (h3p.pair h3pc)
    have h4 : Partrec fun y : (((BitString × BitString × BitString) × BitString) × BitString) ×
        BitString => P.lang (fα y.1.1.2, y.2) :=
      hL.comp ((hfα.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        Computable.snd)
    have h5 : Computable fun y : ((((BitString × BitString × BitString) × BitString) × BitString) ×
        BitString) × BitString => listCode [y.1.2, y.2, y.1.1.2] := by
      exact listCode_computable.comp (Computable.list_cons.comp (Computable.snd.comp
        Computable.fst) (Computable.list_cons.comp Computable.snd (Computable.list_cons.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Computable.const []))))
    exact Partrec.bind h1 (Partrec.bind h2 (Partrec.bind h3 (Partrec.map h4 h5)))
  · intro s p a b c d σ hσ hs hp
    obtain ⟨α, hα, β, hβ, rfl⟩ := hσ
    have hu := hinv α β
    have hfa : fα (P.pair α β) = α := by simp [fα, hu]
    have hfb : fβ (P.pair α β) = β := by simp [fβ, hu]
    obtain ⟨c', hc', hc'm⟩ := hα a (Set.mem_singleton a)
    obtain ⟨d', hd', hd'm⟩ := hβ b (Set.mem_singleton b)
    rw [Set.mem_singleton_iff] at hc' hd'
    subst hc' hd'
    simp only [G, Part.mem_bind_iff, Part.mem_map_iff]
    refine ⟨_, hs, ?_⟩
    rw [hfb]
    refine ⟨d', hd'm, a, hp, ?_⟩
    rw [hfa]
    exact ⟨c', hc'm, rfl⟩

/-- SUV Problem 342 (Section 13.6, printed p. 417).  Second lower bound:
`C((a → c) ∧ (b → d)) ≥ C(a, c, d | b) − C(a | b, d)` with logarithmic accuracy, written as
`C(a, c, d | b) ≤ C((a → c) ∧ (b → d)) + C(a | b, d) + O(log n)` for strings of length at most
`n`.
Proof idea (exercise; symmetric to the first lower bound): given `b`, a solution `[α, β]` and a
program for `a` given `[b, d]`, compute `d = [β](b)`, then `a`, then `c = [α](a)`. -/
theorem condK_triple_le_problemK_quad_add_right (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      condK D (listCode [q 0, q 2, q 3]) (q 1) ≤
        problemK D (quadProblem P q) + condK D (q 0) (pairCode (q 1) (q 3)) +
          (logSlack k n : ℕ∞) := by
  obtain ⟨G, hG, hGs⟩ :=
    condK_triple_le_problemK_quad_add_right_map D hD P hP
  obtain ⟨c1, hc1⟩ := condK_triple_le_problemK_quad_add_right_combine D hD G hG
  obtain ⟨ca, hca⟩ := condK_le_plainK D hD
  obtain ⟨cb, hcb⟩ := plainK_le_length D hD
  refine ⟨2 + 2 * (9 + (ca + cb)) + c1, fun n q hq => ?_⟩
  have hXlen : (listCode [q 0, q 2, q 3]).length ≤ 6 * n + 3 := by
    have h0 := hq 0
    have h2 := hq 2
    have h3 := hq 3
    simp only [length_listCode_cons, listCode_nil, List.length_nil]
    omega
  have hLHS : condK D (listCode [q 0, q 2, q 3]) (q 1) ≤ ((6 * n + 3 + (ca + cb) : ℕ) : ℕ∞) := by
    calc condK D (listCode [q 0, q 2, q 3]) (q 1)
        ≤ plainK D (listCode [q 0, q 2, q 3]) + (ca : ℕ∞) := hca _ _
      _ ≤ ((listCode [q 0, q 2, q 3]).length : ℕ∞) + (cb : ℕ∞) + (ca : ℕ∞) := by
        gcongr; exact hcb _
      _ ≤ _ := by exact_mod_cast (by omega)
  rcases (quadProblem P q).eq_empty_or_nonempty with hE | hne
  · rw [hE, problemK_empty, top_add, top_add]; exact le_top
  obtain ⟨σ, hσ, hσeq⟩ := exists_mem_plainK_eq_problemK D hne
  have hσfin : plainK D σ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENat.natCast_ne_top (σ.length + cb)) ?_
    calc plainK D σ ≤ (σ.length : ℕ∞) + (cb : ℕ∞) := hcb σ
      _ = _ := by push_cast; rfl
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hσfin
  have hpk : problemK D (quadProblem P q) = (m : ℕ∞) := by rw [← hσeq, ← hm]
  by_cases hmN : 6 * n + 3 + (ca + cb) < m
  · refine hLHS.trans ?_
    rw [hpk]
    refine le_trans ?_ (le_self_add.trans le_self_add)
    exact_mod_cast hmN.le
  obtain ⟨s, hslen, hsprod⟩ := (condK_le_iff D σ [] m).mp (le_of_eq hm.symm)
  rw [hpk]
  rcases eq_or_ne (condK D (q 0) (pairCode (q 1) (q 3))) ⊤ with htop | hfin
  · rw [htop, add_top, top_add]; exact le_top
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨p, hplen, hpprod⟩ := (condK_le_iff D _ _ e).mp (le_of_eq he.symm)
  have hmem := hGs s p (q 0) (q 1) (q 2) (q 3) σ hσ hsprod hpprod
  have h1 := hc1 s p (q 1) _ hmem
  have hsN : s.length ≤ 6 * n + 3 + (ca + cb) := le_trans hslen (not_lt.mp hmN)
  have hL1 := length_natBits_mono hsN
  have hL2 : (Nat.bits (6 * n + 3 + (ca + cb))).length ≤ (Nat.bits n).length + (9 + (ca + cb)) := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_add]
    have hA : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have hB : 9 + (ca + cb) < 2 ^ (9 + (ca + cb)) := Nat.lt_two_pow_self
    have hC : 6 * n + 3 + (ca + cb) ≤ (9 + (ca + cb)) * 2 ^ Nat.size n := by nlinarith
    calc 6 * n + 3 + (ca + cb) ≤ (9 + (ca + cb)) * 2 ^ Nat.size n := hC
      _ < 2 ^ (9 + (ca + cb)) * 2 ^ Nat.size n :=
        Nat.mul_lt_mul_of_pos_right hB (by positivity)
      _ = _ := mul_comm _ _
  have hnum : s.length + p.length + (2 * (Nat.bits s.length).length + c1) ≤
      m + e + logSlack (2 + 2 * (9 + (ca + cb)) + c1) n := by
    unfold logSlack
    have : programLength p ≤ e := hplen
    have h4 : programLength s ≤ m := hslen
    simp only [programLength] at this h4
    nlinarith [Nat.zero_le ((2 * (9 + (ca + cb)) + c1) * (Nat.bits n).length)]
  calc condK D (listCode [q 0, q 2, q 3]) (q 1)
      ≤ (s.length : ℕ∞) + (p.length : ℕ∞) + ((2 * (Nat.bits s.length).length + c1 : ℕ) : ℕ∞) := h1
    _ ≤ (m : ℕ∞) + condK D (q 0) (pairCode (q 1) (q 3)) +
        ((logSlack (2 + 2 * (9 + (ca + cb)) + c1) n : ℕ) : ℕ∞) := by
      rw [← he]
      exact_mod_cast hnum

/-- A word of conditional complexity `≤ k` belongs to `compressibleWords`. -/
private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_mem (D : Map)
    (x y : BitString) (k : ℕ) (h : condK D x y ≤ (k : ℕ∞)) :
    x ∈ compressibleWords D y k := by
  classical
  obtain ⟨p, hp, hprod⟩ := (condK_le_iff D x y k).1 h
  rw [compressibleWords, Finset.mem_filter]
  refine ⟨?_, h⟩
  rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
  exact ⟨p, mem_programsLe k p hp, progToOut_eq_some.mpr hprod⟩

private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_lt (D : Map)
    (x y : BitString) (k : ℕ) (h : ¬ ((k + 3 : ℕ) : ℕ∞) ≤ condK D x y + 2) :
    condK D x y ≤ (k : ℕ∞) := by
  induction hc : condK D x y using ENat.recTopCoe with
  | top => exact absurd (by rw [hc]; simp) h
  | coe m =>
    rw [hc] at h
    have : ¬ k + 3 ≤ m + 2 := by exact_mod_cast h
    exact_mod_cast (by omega : m ≤ k)

/-- Counting step: there are strings `a`, `b` of length `≤ n` with both conditional complexities
`≥ n - 2`. -/
private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_count (D : Map)
    (n : ℕ) :
    ∃ a b : BitString, a.length ≤ n ∧ b.length ≤ n ∧
      (n : ℕ∞) ≤ condK D a b + 2 ∧ (n : ℕ∞) ≤ condK D b a + 2 := by
  classical
  by_cases hn : n ≤ 2
  · refine ⟨[], [], by simp, by simp, ?_, ?_⟩ <;>
    · calc (n : ℕ∞) ≤ 2 := by exact_mod_cast hn
        _ ≤ _ := le_add_self
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hSc : (stringsOfLength (k + 3)).card = 2 ^ (k + 3) := card_stringsOfLength _
    set S := stringsOfLength (k + 3) with hS
    have hbound : ∀ (f : BitString → BitString → BitString × BitString),
        ((S.biUnion (fun y => (compressibleWords D y k).image (fun x => f x y))).card ≤
          2 ^ (k + 3) * 2 ^ (k + 1)) := by
      intro f
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ y ∈ S, ((compressibleWords D y k).image (fun x => f x y)).card
          ≤ ∑ y ∈ S, 2 ^ (k + 1) := by
            refine Finset.sum_le_sum (fun y _ => ?_)
            refine (Finset.card_image_le).trans ?_
            exact (card_compressibleWordsLt D y k).le
        _ = 2 ^ (k + 3) * 2 ^ (k + 1) := by rw [Finset.sum_const, hSc]; simp
    set B1 := S.biUnion (fun y => (compressibleWords D y k).image (fun x => (x, y))) with hB1
    set B2 := S.biUnion (fun y => (compressibleWords D y k).image (fun x => (y, x))) with hB2
    have hB : (B1 ∪ B2).card < (S ×ˢ S).card := by
      refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
      have h1 := hbound (fun x y => (x, y))
      have h2 := hbound (fun x y => (y, x))
      rw [Finset.card_product, hSc]
      have h3 : 2 ^ (k + 3) * 2 ^ (k + 1) + 2 ^ (k + 3) * 2 ^ (k + 1) <
          2 ^ (k + 3) * 2 ^ (k + 3) := by
        have : (0 : ℕ) < 2 ^ (k + 1) := by positivity
        have h4 : 2 ^ (k + 3) = 2 ^ (k + 1) * 4 := by ring
        rw [h4]
        nlinarith
      exact lt_of_le_of_lt (add_le_add h1 h2) h3
    obtain ⟨⟨a, b⟩, hab, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
    rw [Finset.mem_product, hS, mem_stringsOfLength, mem_stringsOfLength] at hab
    have hbS : b ∈ S := by rw [hS, mem_stringsOfLength]; exact hab.2
    have haS : a ∈ S := by rw [hS, mem_stringsOfLength]; exact hab.1
    refine ⟨a, b, hab.1.le, hab.2.le, ?_, ?_⟩
    · by_contra hc
      apply hnot
      refine Finset.mem_union_left _ ?_
      rw [hB1, Finset.mem_biUnion]
      refine ⟨b, hbS, ?_⟩
      rw [Finset.mem_image]
      exact ⟨a, exists_quadruples_lowerBound342_add_le_upperBound342_aux_mem D a b k
        (exists_quadruples_lowerBound342_add_le_upperBound342_aux_lt D a b k hc), rfl⟩
    · by_contra hc
      apply hnot
      refine Finset.mem_union_right _ ?_
      rw [hB2, Finset.mem_biUnion]
      refine ⟨a, haS, ?_⟩
      rw [Finset.mem_image]
      exact ⟨b, exists_quadruples_lowerBound342_add_le_upperBound342_aux_mem D b a k
        (exists_quadruples_lowerBound342_add_le_upperBound342_aux_lt D b a k hc), rfl⟩

/-- Mapping the decoded string together with the condition by a computable function costs `O(1)`. -/
private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_map (D : Map)
    (hD : isOptimalConditional D) (g : BitString → BitString → BitString)
    (hg : Computable₂ g) :
    ∃ c : ℕ, ∀ x y : BitString, condK D (g y x) y ≤ condK D x y + (c : ℕ∞) := by
  let D' : Map := fun pr => (D pr).map (g pr.2)
  have hD' : isDecompressor D' :=
    Partrec.map hD.1 (hg.comp (Computable.snd.comp Computable.fst) Computable.snd)
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c, fun x y => ?_⟩
  refine le_trans (hc (g y x) y) ?_
  gcongr
  apply sInf_le_sInf
  rintro m ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_map _ hp, rfl⟩

/-- Replacing the condition by something computable from it costs `O(1)`. -/
private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_cond (D : Map)
    (hD : isOptimalConditional D) (s : BitString → BitString) (hs : Computable s) :
    ∃ c : ℕ, ∀ x y : BitString, condK D x y ≤ condK D x (s y) + (c : ℕ∞) := by
  let D' : Map := fun pr => D (pr.1, s pr.2)
  have hD' : isDecompressor D' :=
    hD.1.comp (Computable.pair Computable.fst (hs.comp Computable.snd))
  obtain ⟨c, hc⟩ := hD.2 D' hD'
  refine ⟨c, fun x y => ?_⟩
  refine le_trans (hc x y) ?_
  gcongr
  apply sInf_le_sInf
  rintro m ⟨p, hp, rfl⟩
  exact ⟨p, hp, rfl⟩

/-- Arithmetic step. -/
private lemma exists_quadruples_lowerBound342_add_le_upperBound342_aux_arith
    (L P Q U L2 : ℕ∞) (n c3 e c : ℕ) (hc : c3 + e + 2 ≤ c)
    (h1 : L ≤ P + c3) (h2 : (n : ℕ∞) ≤ Q + 2) (h3 : P + Q ≤ U + e) :
    L + n ≤ U + L2 + c := by
  calc L + n ≤ (P + c3) + (Q + 2) := add_le_add h1 h2
    _ = (P + Q) + (c3 + 2) := by ring
    _ ≤ (U + e) + (c3 + 2) := by gcongr
    _ = U + ((c3 + e + 2 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ U + L2 + c := by
        calc U + ((c3 + e + 2 : ℕ) : ℕ∞) ≤ U + (c : ℕ∞) :=
          add_le_add_right (by exact_mod_cast hc) U
          _ ≤ U + L2 + c := by rw [add_assoc]; gcongr; exact le_add_self

/-- SUV Problem 343 (Section 13.6, printed p. 417).  There is a sequence of quadruples
`(aₙ, bₙ, cₙ, dₙ)` of lengths `O(n)` such that for all `n` each of the three upper bounds of
Problem 342 exceeds each of the two lower bounds by `n − O(1)`; written without subtraction as
`L₁ + n ≤ U + L₂ + c` for a lower bound `L₁ − L₂` and an upper bound `U` (the exact expressions
of `upperBound342`, `lowerBound342`, not "up to `O(log n)`").
Proof idea (book's hint): `a = d`, `b = c` for independent random `a`, `b` of length `n`; then
every upper bound is `≈ 2n` and every lower bound is `≈ n`.  For the `O(1)` precision choose
`a`, `b` with `C(a|b) ≥ n − 1` and `C(b|a) ≥ n − 1` simultaneously (fewer than
`2 · 2ⁿ · 2ⁿ⁻¹` pairs violate one of them); then `L₁ ≤ C(b|a) + O(1)`, `L₂ ≤ C(a|b) + O(1)`, the
subtrahends are `≥ 0`, and every upper bound is `≥ C(a|b) + C(b|a) − O(1)` (conditions computable
from one another change conditional complexity by `O(1)`, `condK_map_le`). -/
theorem exists_quadruples_lowerBound342_add_le_upperBound342 (D : Map)
    (hD : isOptimalConditional D) :
    ∃ (c : ℕ) (q : ℕ → Fin 4 → BitString), (∀ n i, (q n i).length ≤ c * (n + 1)) ∧
      ∀ (n : ℕ) (i : Fin 3) (j : Fin 2),
        (lowerBound342 D (q n 0) (q n 1) (q n 2) (q n 3) j).1 + (n : ℕ∞) ≤
          upperBound342 D (q n 0) (q n 1) (q n 2) (q n 3) i +
            (lowerBound342 D (q n 0) (q n 1) (q n 2) (q n 3) j).2 + (c : ℕ∞) := by
  choose a b ha hb hab hba using
    fun n => exists_quadruples_lowerBound342_add_le_upperBound342_aux_count D n
  obtain ⟨cp, hcp⟩ := condK_le_plainK D hD
  obtain ⟨c1, hc1⟩ := exists_quadruples_lowerBound342_add_le_upperBound342_aux_cond D hD
    (fun z => pairCode z z)
    (Computable₂.comp (pairCode_computable : Computable₂ pairCode) Computable.id Computable.id)
  obtain ⟨c2, hc2⟩ := exists_quadruples_lowerBound342_add_le_upperBound342_aux_map D hD
    (fun y x => listCode [x, x, y])
    (listCode_computable.comp (Computable.list_cons.comp Computable.snd
      (Computable.list_cons.comp Computable.snd
        (Computable.list_cons.comp Computable.fst (Computable.const [])))))
  obtain ⟨c3, hc3⟩ := exists_quadruples_lowerBound342_add_le_upperBound342_aux_map D hD
    (fun y x => listCode [x, y, x])
    (listCode_computable.comp (Computable.list_cons.comp Computable.snd
      (Computable.list_cons.comp Computable.fst
        (Computable.list_cons.comp Computable.snd (Computable.const [])))))
  refine ⟨cp + c1 + c2 + c3 + 3, fun n => ![a n, b n, b n, a n], ?_, ?_⟩
  · intro n i
    have h1 := ha n
    have h2 := hb n
    fin_cases i <;> simp <;> nlinarith
  · intro n i j
    have hX := hab n
    have hY := hba n
    have hU : condK D (a n) (b n) + condK D (b n) (a n) ≤
        upperBound342 D (a n) (b n) (b n) (a n) i + ((c1 + cp : ℕ) : ℕ∞) := by
      push_cast
      have e1 := hc1 (a n) (b n)
      have e2 := hc1 (b n) (a n)
      have e3 := hcp (b n) (a n)
      have e4 := hcp (a n) (b n)
      fin_cases i
      · change _ ≤ condK D (b n) (a n) + condK D (a n) (b n) + _
        rw [add_comm (condK D (b n) (a n))]
        exact le_self_add
      · change _ ≤ condK D (a n) (pairCode (b n) (b n)) + plainK D (b n) + _
        calc condK D (a n) (b n) + condK D (b n) (a n)
            ≤ (condK D (a n) (pairCode (b n) (b n)) + c1) + (plainK D (b n) + cp) :=
              add_le_add e1 e3
          _ = _ := by ring
      · change _ ≤ condK D (b n) (pairCode (a n) (a n)) + plainK D (a n) + _
        calc condK D (a n) (b n) + condK D (b n) (a n)
            ≤ (plainK D (a n) + cp) + (condK D (b n) (pairCode (a n) (a n)) + c1) :=
              add_le_add e4 e2
          _ = _ := by ring
    change (lowerBound342 D (a n) (b n) (b n) (a n) j).1 + (n : ℕ∞) ≤
      upperBound342 D (a n) (b n) (b n) (a n) i +
        (lowerBound342 D (a n) (b n) (b n) (a n) j).2 + _
    fin_cases j
    · exact exists_quadruples_lowerBound342_add_le_upperBound342_aux_arith _ (condK D (b n) (a n))
        (condK D (a n) (b n)) _ _ n c2 (c1 + cp) _ (by omega) (hc2 (b n) (a n)) (hab n)
        (by rw [add_comm]; exact hU)
    · exact exists_quadruples_lowerBound342_add_le_upperBound342_aux_arith _ (condK D (a n) (b n))
        (condK D (b n) (a n)) _ _ n c3 (c1 + cp) _ (by omega) (hc3 (a n) (b n)) (hba n) hU

end InformationLogic
end Kolmogorov
