import KolmogorovMathlib.InformationLogic.Bridges
import KolmogorovMathlib.Multisource.InformationDistance.Part02
import KolmogorovMathlib.Multisource.TwoConditions

/-!
# Complexity of the basic operations (SUV §13.1, unnumbered claims)

The claims of SUV §13.1 (printed pp. 401-402) that relate the operations on problems to the
complexities of strings, pairs and conditional complexity, including the restatements of two
results of Chapter 12 (information distance, Theorem 232; two conditions, Theorem 234).

Conventions: `D` is an arbitrary optimal decompressor (the complexity `C`), `P` an arbitrary
admissible calculus; every `O(1)` is `∃ c, ∀ …, … + c` with `c` depending on `D` and `P` only.
-/

namespace Kolmogorov
namespace InformationLogic

open ProblemCalculus

/-- SUV Section 13.1, in-text claim (printed p. 401).  "The complexity of `{x} ∧ {y}` is just
the complexity of the pair `⟨x, y⟩`", upper bound: `C({x} ∧ {y}) ≤ C(x, y) + O(1)`.
Proof idea: `{x} ∧ {y} = {[x, y]}`; for the standard calculus `[x, y] = pairCode x y` and the two
sides are equal; for an arbitrary admissible calculus the pairings differ by a computable
translation (`P.pair` applied to `decodeFirst`, `decodeSecond`), which costs `O(1)`. -/
theorem problemK_conj_singleton_le_cPair (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString, problemK D (P.conj {x} {y}) ≤ cPair D x y + (c : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  have hh : Computable (fun z : BitString => P.pair (decodeFirst z) (decodeSecond z)) :=
    hpair.comp CodedFiniteDistribution.decodeFirst_primrec.to_comp
      CodedFiniteDistribution.decodeSecond_primrec.to_comp
  obtain ⟨c, hc⟩ := plainK_map_le D hD _ hh
  refine ⟨c, fun x y => ?_⟩
  have hmem : P.pair x y ∈ P.conj {x} {y} :=
    Set.mem_image2_of_mem (Set.mem_singleton x) (Set.mem_singleton y)
  have h := hc (pairCode x y)
  rw [decodeFirst_pairCode, decodeSecond_pairCode] at h
  exact (problemK_le_of_mem D hmem).trans h

/-- SUV Section 13.1, in-text claim (printed p. 401).  The complexity of `{x} ∧ {y}` is the
complexity of the pair, lower bound: `C(x, y) ≤ C({x} ∧ {y}) + O(1)`.
Proof idea: the only solution is `[x, y]`; translate it back with `P.unpair` and `pairCode`, a
computable map, which costs `O(1)`. -/
theorem cPair_le_problemK_conj_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString, cPair D x y ≤ problemK D (P.conj {x} {y}) + (c : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, -⟩ := hP
  have hh : Computable (fun z : BitString =>
      ((P.unpair z).map (fun ab => pairCode ab.1 ab.2)).getD []) :=
    Computable.option_getD (Computable.option_map hunpair
      (CodedFiniteDistribution.pairCode_primrec.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂) (Computable.const [])
  obtain ⟨c, hc⟩ := plainK_map_le D hD _ hh
  refine ⟨c, fun x y => ?_⟩
  have hconj : P.conj {x} {y} = {P.pair x y} := Set.image2_singleton
  rw [hconj, problemK_singleton]
  have h := hc (P.pair x y)
  simp only [hinv, Option.map_some, Option.getD_some] at h
  exact h

/-- SUV Section 13.1, in-text claim (printed p. 401).  "The complexity `C(X ∨ Y)` is equal to
`min(C(X), C(Y)) + O(1)` for every two problems", upper bound:
`C(X ∨ Y) ≤ min (C(X), C(Y)) + O(1)`, the constant independent of `X`, `Y`.
Proof idea: the maps `x ↦ [0, x]` and `y ↦ [1, y]` are computable and send solutions of `X`
(resp. `Y`) to solutions of `X ∨ Y` (`problemK_le_of_partrec`). -/
theorem problemK_disj_le_min (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString,
      problemK D (P.disj X Y) ≤ min (problemK D X) (problemK D Y) + (c : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  have h0 : Partrec (fun x : BitString => (P.pair P.tag0 x : Part BitString)) :=
    (hpair.comp (Computable.const _) Computable.id).partrec
  have h1 : Partrec (fun y : BitString => (P.pair P.tag1 y : Part BitString)) :=
    (hpair.comp (Computable.const _) Computable.id).partrec
  obtain ⟨c0, hc0⟩ := problemK_le_of_partrec D hD _ h0
  obtain ⟨c1, hc1⟩ := problemK_le_of_partrec D hD _ h1
  refine ⟨max c0 c1, fun X Y => ?_⟩
  have hX : problemK D (P.disj X Y) ≤ problemK D X + c0 :=
    hc0 X _ (fun x hx => ⟨_, Or.inl ⟨x, hx, rfl⟩, Part.mem_some _⟩)
  have hY : problemK D (P.disj X Y) ≤ problemK D Y + c1 :=
    hc1 Y _ (fun y hy => ⟨_, Or.inr ⟨y, hy, rfl⟩, Part.mem_some _⟩)
  rcases le_total (problemK D X) (problemK D Y) with h | h
  · rw [min_eq_left h]
    exact hX.trans (by gcongr; exact_mod_cast le_max_left c0 c1)
  · rw [min_eq_right h]
    exact hY.trans (by gcongr; exact_mod_cast le_max_right c0 c1)

/-- SUV Section 13.1, in-text claim (printed p. 401).  `C(X ∨ Y) = min(C(X), C(Y)) + O(1)`,
lower bound: `min (C(X), C(Y)) ≤ C(X ∨ Y) + O(1)`, the constant independent of `X`, `Y`.
Proof idea: dropping the tag of a solution `[0, x]` or `[1, y]` (via `P.unpair`) is computable
and gives a solution of `X ∪ Y`, whose complexity is `min (C(X), C(Y))`. -/
theorem min_le_problemK_disj (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ X Y : Set BitString,
      min (problemK D X) (problemK D Y) ≤ problemK D (P.disj X Y) + (c : ℕ∞) := by
  obtain ⟨-, hunpair, hinv, -, -, -⟩ := hP
  have hf : Partrec (fun z : BitString => ((P.unpair z).map Prod.snd : Part BitString)) :=
    Computable.ofOption (Computable.option_map hunpair (Computable.snd.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := problemK_le_of_partrec D hD _ hf
  refine ⟨c, fun X Y => ?_⟩
  have hU : problemK D (X ∪ Y) = min (problemK D X) (problemK D Y) := by
    simp only [problemK]
    exact iInf_union
  rw [← hU]
  refine hc (P.disj X Y) (X ∪ Y) ?_
  rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact ⟨x, Or.inl hx, by simp [hinv]⟩
  · exact ⟨y, Or.inr hy, by simp [hinv]⟩

/-- SUV Section 13.1, in-text claim (printed p. 402).  "The complexity of `{x} → {y}` is equal
to the conditional complexity `C(y|x) + O(1)`", upper bound: `C({x} → {y}) ≤ C(y|x) + O(1)`.
Proof idea: by the Gödel property of `P.lang` there is a total computable `t` with
`[t(q)](x) = D(q, x)`; apply it to a shortest `D`-program for `y` given `x` and use
`plainK_le_length`, `plainK_map_le`. -/
theorem problemK_imp_singleton_le_condK (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString, problemK D (P.imp {x} {y}) ≤ condK D y x + (c : ℕ∞) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ := hP
  obtain ⟨t, ht, hts⟩ := hG D hD.1
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t ht
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  refine ⟨c1 + c2, fun x y => ?_⟩
  rcases eq_top_or_lt_top (condK D y x) with h | h
  · rw [h, top_add]; exact le_top
  have hne : (candidateLengths D y x).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [condK, hemp] at h
  obtain ⟨q, hq, hqlen⟩ := csInf_mem hne
  have hmem : t q ∈ P.imp {x} {y} := by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨y, Set.mem_singleton y, by rw [hts]; exact hq⟩
  calc problemK D (P.imp {x} {y}) ≤ plainK D (t q) := problemK_le_of_mem D hmem
    _ ≤ plainK D q + c1 := hc1 q
    _ ≤ ((q.length : ℕ∞) + c2) + c1 := by gcongr; exact hc2 q
    _ = condK D y x + ((c1 + c2 : ℕ) : ℕ∞) := by
        rw [show condK D y x = (q.length : ℕ∞) from hqlen.symm]; push_cast; ring

/-- SUV Section 13.1, in-text claim (printed p. 402).  `C({x} → {y}) = C(y|x) + O(1)`, lower
bound: `C(y|x) ≤ C({x} → {y}) + O(1)`.
Proof idea: the decompressor `(r, x) ↦ [D(r, Λ)](x)` is partial computable; a description of a
solution `p` is a description of `y` given `x`; apply the optimality of `D`. -/
theorem condK_le_problemK_imp_singleton (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString, condK D y x ≤ problemK D (P.imp {x} {y}) + (c : ℕ∞) := by
  obtain ⟨-, -, -, -, -, hL, -⟩ := hP
  let E : Map := fun pr => (D (pr.1, [])).bind (fun p => P.lang (p, pr.2))
  have hE : isDecompressor E :=
    Partrec.bind (hD.1.comp (Computable.fst.pair (Computable.const [])))
      (hL.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂
  obtain ⟨c, hc⟩ := hD.2 E hE
  refine ⟨c, fun x y => ?_⟩
  rcases (P.imp {x} {y}).eq_empty_or_nonempty with h | h
  · rw [h, problemK_empty, top_add]; exact le_top
  obtain ⟨p, hp, hpeq⟩ := exists_mem_plainK_eq_problemK D h
  rw [← hpeq]
  refine (hc y x).trans ?_
  gcongr
  change sInf (candidateLengths E y x) ≤ sInf (candidateLengths D p [])
  apply sInf_le_sInf
  rintro n ⟨r, hr, rfl⟩
  obtain ⟨y', hy', hy'mem⟩ := hp x (Set.mem_singleton x)
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  exact ⟨r, Part.mem_bind_iff.2 ⟨p, hr, hy'mem⟩, rfl⟩

/-- Step 1 of the proof of `problemK_imp_conj_imp_le`: Gödel property with the string
`X` hardwired.  There is a total computable `t` such that whenever `r` is a `D`-program
producing `y` from the condition `pairCode x X`, the string `t (pairCode X r)` solves
`{x} → {y}`. -/
private theorem problemK_imp_conj_imp_le_hardwire (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
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

/-- Step 2 of the proof of `problemK_imp_conj_imp_le`: one string codes a solution of
`(x → y) ∧ (y → x)`.  If `r1` produces `y` from `pairCode x X` and `r2` produces `x` from
`pairCode y X`, then `C((x → y) ∧ (y → x)) ≤ C(pairCode r1 (pairCode r2 X)) + O(1)`, the
constant independent of `x, y, X, r1, r2`. -/
private theorem problemK_imp_conj_imp_le_solution (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y X r1 r2 : BitString,
      y ∈ D (r1, pairCode x X) → x ∈ D (r2, pairCode y X) →
      problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x})) ≤
        plainK D (pairCode r1 (pairCode r2 X)) + (c : ℕ∞) := by
  obtain ⟨t, ht, ht1⟩ := problemK_imp_conj_imp_le_hardwire D hD P hP
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  let f : BitString → BitString := fun w =>
    P.pair (t (pairCode (decodeSecond (decodeSecond w)) (decodeFirst w)))
      (t (pairCode (decodeSecond (decodeSecond w)) (decodeFirst (decodeSecond w))))
  have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
  have hf : Computable f :=
    hpair.comp
      (ht.comp (hpc.comp (decodeSecond_computable.comp decodeSecond_computable)
        decodeFirst_computable))
      (ht.comp (hpc.comp (decodeSecond_computable.comp decodeSecond_computable)
        (decodeFirst_computable.comp decodeSecond_computable)))
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  refine ⟨c, fun x y X r1 r2 h1 h2 => ?_⟩
  have hmem : f (pairCode r1 (pairCode r2 X)) ∈ P.conj (P.imp {x} {y}) (P.imp {y} {x}) := by
    simp only [f, decodeFirst_pairCode, decodeSecond_pairCode]
    exact Set.mem_image2_of_mem (ht1 r1 X x y h1) (ht1 r2 X y x h2)
  exact (problemK_le_of_mem D hmem).trans (hc _)

/-- Step 3 of the proof of `problemK_imp_conj_imp_le`: the code string is cheap,
`C(pairCode r1 (pairCode r2 X)) ≤ |X| + 2 |r1| + 2 |r2| + 2 + O(1)`, the constant independent
of `r1, r2, X`. -/
private theorem problemK_imp_conj_imp_le_code_length (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ r1 r2 X : BitString,
      plainK D (pairCode r1 (pairCode r2 X)) ≤
        ((X.length + 2 * r1.length + 2 * r2.length + 2 : ℕ) : ℕ∞) + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := plainK_le_length D hD
  refine ⟨c, fun r1 r2 X => ?_⟩
  refine (hc _).trans (add_le_add (le_of_eq ?_) le_rfl)
  simp only [programLength, length_pairCode]
  norm_cast
  omega

/-- Step 4 of the proof of `problemK_imp_conj_imp_le`: both conditional complexities
are bounded by the complexity of the pair, `C(x|y), C(y|x) ≤ C(x, y) + O(1)`. -/
private theorem problemK_imp_conj_imp_le_condK_le_cPair (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y : BitString,
      condK D x y ≤ cPair D x y + (c : ℕ∞) ∧ condK D y x ≤ cPair D x y + (c : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD (fun w => decodeFirst w) decodeFirst_computable
  obtain ⟨c2, hc2⟩ := plainK_map_le D hD (fun w => decodeSecond w) decodeSecond_computable
  obtain ⟨c3, hc3⟩ := condK_le_plainK D hD
  refine ⟨c1 + c2 + c3, fun x y => ⟨?_, ?_⟩⟩
  · have h1 := hc1 (pairCode x y)
    simp only [decodeFirst_pairCode] at h1
    change plainK D x ≤ plainK D (pairCode x y) + (c1 : ℕ∞) at h1
    calc condK D x y ≤ plainK D x + (c3 : ℕ∞) := hc3 x y
      _ ≤ (cPair D x y + (c1 : ℕ∞)) + (c3 : ℕ∞) := by gcongr; exact h1
      _ ≤ cPair D x y + ((c1 + c2 + c3 : ℕ) : ℕ∞) := by
          rw [add_assoc]; gcongr; exact_mod_cast (by omega : c1 + c3 ≤ c1 + c2 + c3)
  · have h2 := hc2 (pairCode x y)
    simp only [decodeSecond_pairCode] at h2
    change plainK D y ≤ plainK D (pairCode x y) + (c2 : ℕ∞) at h2
    calc condK D y x ≤ plainK D y + (c3 : ℕ∞) := hc3 y x
      _ ≤ (cPair D x y + (c2 : ℕ∞)) + (c3 : ℕ∞) := by gcongr; exact h2
      _ ≤ cPair D x y + ((c1 + c2 + c3 : ℕ) : ℕ∞) := by
          rw [add_assoc]; gcongr; exact_mod_cast (by omega : c2 + c3 ≤ c1 + c2 + c3)

/-- Step 5 of the proof of `problemK_imp_conj_imp_le`: a finite conditional complexity
is attained by a program: if `condK D y z ≠ ⊤` there is `r` with `y ∈ D (r, z)` and
`|r| = C(y | z)`. -/
private theorem problemK_imp_conj_imp_le_program (D : Map) (y z : BitString)
    (h : condK D y z ≠ ⊤) :
    ∃ r : BitString, y ∈ D (r, z) ∧ (r.length : ℕ∞) = condK D y z := by
  have hne : (candidateLengths D y z).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [condK, hemp] at h
  obtain ⟨q, hq, hqlen⟩ := csInf_mem hne
  exact ⟨q, hq, hqlen⟩

/-- SUV Section 13.1, in-text claim restating Chapter 12 (printed p. 402).  The complexity of
`(x → y) ∧ (y → x)` is `max (C(x|y), C(y|x)) + O(log C(x, y))`, upper bound.
Proof idea: SUV Theorem 232 (`exists_informationDistanceCode` with
`k = max (C(x|y), C(y|x)) + 1 ≤ C(x, y) + O(1)`) gives a string `X` of length `k + 1` with
`C(x | y, X)`, `C(y | x, X) = O(log k)`; the two programs (`X` and an `O(log k)`-bit
conditional description hardwired, built with the Gödel property) form a solution of complexity
`k + O(log k)`.  The precision is the book's `O(log C(x, y))`, with `C(x, y) = cPair D x y`. -/
theorem problemK_imp_conj_imp_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString,
      problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x})) ≤
        max (condK D x y) (condK D y x) + (logSlack c (cPairVal D x y) : ℕ∞) := by
  obtain ⟨cA, hA⟩ := problemK_imp_conj_imp_le_solution D hD P hP
  obtain ⟨cL, hL⟩ := problemK_imp_conj_imp_le_code_length D hD
  obtain ⟨c4, h4⟩ := problemK_imp_conj_imp_le_condK_le_cPair D hD
  obtain ⟨cI, hI⟩ := exists_informationDistanceCode D hD
  set L : ℕ := (Nat.bits (c4 + 1)).length + 1 with hLdef
  refine ⟨4 * cI * (L + 2) + 4 + cL + cA, fun x y => ?_⟩
  set n : ℕ := cPairVal D x y with hn
  have hcP : cPair D x y = (n : ℕ∞) := (ENat.natCast_toNat (plainK_ne_top D hD _)).symm
  obtain ⟨h4a, h4b⟩ := h4 x y
  rw [hcP] at h4a h4b
  have hxy_top : condK D x y ≠ ⊤ := ne_top_of_le_natCast (n := n + c4) (by exact_mod_cast h4a)
  have hyx_top : condK D y x ≠ ⊤ := ne_top_of_le_natCast (n := n + c4) (by exact_mod_cast h4b)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hxy_top
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hyx_top
  have han : a ≤ n + c4 := by
    rw [← ha] at h4a; exact_mod_cast h4a
  have hbn : b ≤ n + c4 := by
    rw [← hb] at h4b; exact_mod_cast h4b
  obtain ⟨X, hXlen, hX1, hX2, -⟩ := hI (max a b + 1) x y
    (by rw [← ha]; exact_mod_cast Nat.lt_succ_of_le (le_max_left a b))
    (by rw [← hb]; exact_mod_cast Nat.lt_succ_of_le (le_max_right a b))
  set k : ℕ := max a b + 1 with hk
  set s : ℕ := logSlack cI k with hs
  -- programs
  obtain ⟨r2, hr2, hr2len⟩ := problemK_imp_conj_imp_le_program D x (pairCode y X)
    (ne_top_of_le_natCast hX1)
  obtain ⟨r1, hr1, hr1len⟩ := problemK_imp_conj_imp_le_program D y (pairCode x X)
    (ne_top_of_le_natCast hX2)
  have hr1s : r1.length ≤ s := by
    have h := hX2
    rw [← hr1len] at h; exact_mod_cast h
  have hr2s : r2.length ≤ s := by
    have h := hX1
    rw [← hr2len] at h; exact_mod_cast h
  have hmain : problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x})) ≤
      ((max a b + 4 * s + 4 + cL + cA : ℕ) : ℕ∞) := by
    calc problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x}))
        ≤ plainK D (pairCode r1 (pairCode r2 X)) + (cA : ℕ∞) := hA x y X r1 r2 hr1 hr2
      _ ≤ (((X.length + 2 * r1.length + 2 * r2.length + 2 : ℕ) : ℕ∞) + (cL : ℕ∞)) + (cA : ℕ∞) := by
          gcongr; exact hL r1 r2 X
      _ = ((X.length + 2 * r1.length + 2 * r2.length + 2 + cL + cA : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ _ := by
          exact_mod_cast (by rw [hXlen]; omega)
  -- the logarithmic slack
  have hkn : k ≤ n + (c4 + 1) := by
    simp only [hk]; omega
  have hbits : (Nat.bits k).length ≤ (Nat.bits n).length + L := by
    have h1 := length_natBits_mono hkn
    have h2 := length_natBits_add_le n (c4 + 1)
    omega
  have hslack : 4 * s + 4 + cL + cA ≤ logSlack (4 * cI * (L + 2) + 4 + cL + cA) n := by
    simp only [hs, logSlack]
    nlinarith [Nat.zero_le (cI * (Nat.bits n).length), Nat.zero_le (cI * L),
      Nat.zero_le (cI * (Nat.bits n).length * L), Nat.zero_le (cL * (Nat.bits n).length),
      Nat.zero_le (cA * (Nat.bits n).length), Nat.zero_le ((Nat.bits n).length),
      Nat.mul_le_mul_left cI hbits]
  rw [← ha, ← hb, (Monotone.map_max (f := fun m : ℕ => (m : ℕ∞))
    (fun m m' h => by dsimp only; exact_mod_cast h)).symm]
  refine hmain.trans ?_
  rw [← Nat.cast_add]
  exact_mod_cast (by omega : max a b + 4 * s + 4 + cL + cA ≤
    max a b + logSlack (4 * cI * (L + 2) + 4 + cL + cA) n)

/-- SUV Section 13.1, in-text claim restating Chapter 12 (printed p. 402).  The complexity of
`(x → y) ∧ (y → x)` is at least `max (C(x|y), C(y|x))` up to the book's `O(log C(x, y))`.
Proof idea (in fact `O(1)` suffices): each component of a solution is a program converting one
string into the other and is computable from the solution (`problemK_left_le_conj`,
`problemK_right_le_conj`, `condK_le_problemK_imp_singleton`). -/
theorem max_condK_le_problemK_imp_conj_imp (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y : BitString,
      max (condK D x y) (condK D y x) ≤
        problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x})) +
          (logSlack c (cPairVal D x y) : ℕ∞) := by
  obtain ⟨a1, ha1⟩ := problemK_left_le_conj D hD P hP
  obtain ⟨a2, ha2⟩ := problemK_right_le_conj D hD P hP
  obtain ⟨b, hb⟩ := condK_le_problemK_imp_singleton D hD P hP
  refine ⟨a1 + a2 + b, fun x y => ?_⟩
  set S := problemK D (P.conj (P.imp {x} {y}) (P.imp {y} {x})) with hS
  have hs : ((a1 + a2 + b : ℕ) : ℕ∞) ≤ (logSlack (a1 + a2 + b) (cPairVal D x y) : ℕ) := by
    exact_mod_cast Nat.le_add_left _ _
  have hk : ∀ a : ℕ, a ≤ a1 + a2 → S + a + b ≤ S + (logSlack (a1 + a2 + b) (cPairVal D x y) : ℕ∞) :=
      by
    intro a ha
    calc S + a + b = S + ((a + b : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ S + ((a1 + a2 + b : ℕ) : ℕ∞) := by
          gcongr
      _ ≤ _ := by gcongr
  have h1 : condK D y x ≤ S + (logSlack (a1 + a2 + b) (cPairVal D x y) : ℕ∞) :=
    (hb x y).trans <| (add_le_add_left (ha1 _ _) _ |>.trans (hk a1 (by omega)))
  have h2 : condK D x y ≤ S + (logSlack (a1 + a2 + b) (cPairVal D x y) : ℕ∞) :=
    (hb y x).trans <| (add_le_add_left (ha2 _ _) _ |>.trans (hk a2 (by omega)))
  exact max_le h2 h1

/-- Step 1 of the proof of `problemK_two_conditions_le`: the three strings of the
triple are computable from its code, so `C(x), C(y), C(z) ≤ C(x, y, z) + O(1)`. -/
private theorem problemK_two_conditions_le_projections (D : Map)
    (hD : isOptimalConditional D) :
    ∃ c : ℕ, ∀ x y z : BitString,
      plainK D x ≤ plainK D (listCode [x, y, z]) + (c : ℕ∞) ∧
      plainK D y ≤ plainK D (listCode [x, y, z]) + (c : ℕ∞) ∧
      plainK D z ≤ plainK D (listCode [x, y, z]) + (c : ℕ∞) := by
  obtain ⟨c1, h1⟩ := plainK_map_le D hD (fun w => decodeFirst w) decodeFirst_computable
  obtain ⟨c2, h2⟩ := plainK_map_le D hD (fun w => decodeFirst (decodeSecond w))
    (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨c3, h3⟩ := plainK_map_le D hD (fun w => decodeFirst (decodeSecond (decodeSecond w)))
    (decodeFirst_computable.comp (decodeSecond_computable.comp decodeSecond_computable))
  refine ⟨c1 + c2 + c3, fun x y z => ⟨?_, ?_, ?_⟩⟩
  · have h := h1 (listCode [x, y, z])
    simp only [listCode, List.foldr_cons, List.foldr_nil, decodeFirst_pairCode] at h
    change plainK D x ≤ plainK D (listCode [x, y, z]) + _ at h
    refine h.trans ?_
    gcongr
    exact_mod_cast (by omega : c1 ≤ c1 + c2 + c3)
  · have h := h2 (listCode [x, y, z])
    simp only [listCode, List.foldr_cons, List.foldr_nil, decodeFirst_pairCode,
      decodeSecond_pairCode] at h
    change plainK D y ≤ plainK D (listCode [x, y, z]) + _ at h
    refine h.trans ?_
    gcongr
    exact_mod_cast (by omega : c2 ≤ c1 + c2 + c3)
  · have h := h3 (listCode [x, y, z])
    simp only [listCode, List.foldr_cons, List.foldr_nil, decodeFirst_pairCode,
      decodeSecond_pairCode] at h
    change plainK D z ≤ plainK D (listCode [x, y, z]) + _ at h
    refine h.trans ?_
    gcongr
    exact_mod_cast (by omega : c3 ≤ c1 + c2 + c3)

/-- Step 2 of the proof of `problemK_two_conditions_le`: one string codes a solution of
`(x → z) ∧ (y → z)`.  If `r1` produces `z` from `pairCode x X` and `r2` produces `z` from
`pairCode y X`, then `C((x → z) ∧ (y → z)) ≤ C(pairCode r1 (pairCode r2 X)) + O(1)`, the
constant independent of `x, y, z, X, r1, r2`. -/
private theorem problemK_two_conditions_le_solution (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y z X r1 r2 : BitString,
      z ∈ D (r1, pairCode x X) → z ∈ D (r2, pairCode y X) →
      problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) ≤
        plainK D (pairCode r1 (pairCode r2 X)) + (c : ℕ∞) := by
  obtain ⟨t, ht, ht1⟩ := problemK_imp_conj_imp_le_hardwire D hD P hP
  obtain ⟨hpair, -, -, -, -, -⟩ := hP
  let f : BitString → BitString := fun w =>
    P.pair (t (pairCode (decodeSecond (decodeSecond w)) (decodeFirst w)))
      (t (pairCode (decodeSecond (decodeSecond w)) (decodeFirst (decodeSecond w))))
  have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
  have hf : Computable f :=
    hpair.comp
      (ht.comp (hpc.comp (decodeSecond_computable.comp decodeSecond_computable)
        decodeFirst_computable))
      (ht.comp (hpc.comp (decodeSecond_computable.comp decodeSecond_computable)
        (decodeFirst_computable.comp decodeSecond_computable)))
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  refine ⟨c, fun x y z X r1 r2 h1 h2 => ?_⟩
  have hmem : f (pairCode r1 (pairCode r2 X)) ∈ P.conj (P.imp {x} {z}) (P.imp {y} {z}) := by
    simp only [f, decodeFirst_pairCode, decodeSecond_pairCode]
    exact Set.mem_image2_of_mem (ht1 r1 X x z h1) (ht1 r2 X y z h2)
  exact (problemK_le_of_mem D hmem).trans (hc _)

/-- SUV Section 13.1, in-text claim restating Chapter 12 (printed p. 402).  The minimal
complexity of a solution of `(x → z) ∧ (y → z)` is `max (C(z|x), C(z|y)) + O(log C(x, y, z))`,
upper bound.
Proof idea: SUV Theorem 234 (`exists_twoConditionCode`, with `n = C(x, y, z) + O(1)`, which
bounds `C(x)`, `C(y)`, `C(z)`, and `k = max (C(z|x), C(z|y), 1)`) gives a string `X` of length
`k + O(log n)` from which `z` is restored given either `x` or `y` with `O(log n)` more bits; the
two programs with `X` hardwired form the solution.  The triple is coded by `listCode [x, y, z]`
(the library's `cTriple`). -/
theorem problemK_two_conditions_le (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y z : BitString,
      problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) ≤
        max (condK D z x) (condK D z y) +
          (logSlack c (plainK D (listCode [x, y, z])).toNat : ℕ∞) := by
  obtain ⟨cP, hP1⟩ := problemK_two_conditions_le_projections D hD
  obtain ⟨cA, hA⟩ := problemK_two_conditions_le_solution D hD P hP
  obtain ⟨cL, hL⟩ := problemK_imp_conj_imp_le_code_length D hD
  obtain ⟨c4, h4⟩ := condK_le_plainK D hD
  obtain ⟨cT, hT⟩ := exists_twoConditionCode D hD
  set L : ℕ := (Nat.bits cP).length + 1 with hLdef
  refine ⟨5 * cT * (L + 2) + 3 + cL + cA, fun x y z => ?_⟩
  set N : ℕ := (plainK D (listCode [x, y, z])).toNat with hN
  have hw : plainK D (listCode [x, y, z]) = (N : ℕ∞) :=
    (ENat.natCast_toNat (plainK_ne_top D hD _)).symm
  obtain ⟨hx, hy, hz⟩ := hP1 x y z
  rw [hw] at hx hy hz
  have hxn : plainK D x ≤ ((N + cP : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact hx
  have hyn : plainK D y ≤ ((N + cP : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact hy
  have hzn : plainK D z ≤ ((N + cP : ℕ) : ℕ∞) := by rw [Nat.cast_add]; exact hz
  have hzx : condK D z x ≤ ((N + cP + c4 : ℕ) : ℕ∞) := by
    refine (h4 z x).trans ?_
    rw [Nat.cast_add (N + cP) c4]
    exact add_le_add_left hzn _ |>.trans le_rfl
  have hzy : condK D z y ≤ ((N + cP + c4 : ℕ) : ℕ∞) := by
    refine (h4 z y).trans ?_
    rw [Nat.cast_add (N + cP) c4]
    exact add_le_add_left hzn _ |>.trans le_rfl
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_natCast hzx)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_natCast hzy)
  set k : ℕ := max (max a b) 1 with hk
  have hkpos : 0 < k := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hCA : condK D z x ≤ (k : ℕ∞) := by
    rw [← ha]; exact_mod_cast (le_max_left a b).trans (le_max_left _ _)
  have hCB : condK D z y ≤ (k : ℕ∞) := by
    rw [← hb]; exact_mod_cast (le_max_right a b).trans (le_max_left _ _)
  obtain ⟨X, hXlen, -, hX1, hX2⟩ := hT (N + cP) k x y z hxn hyn hzn hkpos hCA hCB
  set s : ℕ := logSlack cT (N + cP) with hs
  obtain ⟨r1, hr1, hr1len⟩ := problemK_imp_conj_imp_le_program D z (pairCode x X)
    (ne_top_of_le_natCast hX1)
  obtain ⟨r2, hr2, hr2len⟩ := problemK_imp_conj_imp_le_program D z (pairCode y X)
    (ne_top_of_le_natCast hX2)
  have hr1s : r1.length ≤ s := by
    have h := hX1
    rw [← hr1len] at h; exact_mod_cast h
  have hr2s : r2.length ≤ s := by
    have h := hX2
    rw [← hr2len] at h; exact_mod_cast h
  have hmain : problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) ≤
      ((max a b + 5 * s + 3 + cL + cA : ℕ) : ℕ∞) := by
    calc problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z}))
        ≤ plainK D (pairCode r1 (pairCode r2 X)) + (cA : ℕ∞) := hA x y z X r1 r2 hr1 hr2
      _ ≤ (((X.length + 2 * r1.length + 2 * r2.length + 2 : ℕ) : ℕ∞) + (cL : ℕ∞)) +
            (cA : ℕ∞) := by
          gcongr; exact hL r1 r2 X
      _ = ((X.length + 2 * r1.length + 2 * r2.length + 2 + cL + cA : ℕ) : ℕ∞) := by
          push_cast; ring
      _ ≤ _ := by
          exact_mod_cast (by omega)
  have hbits : (Nat.bits (N + cP)).length ≤ (Nat.bits N).length + L := by
    have h := length_natBits_add_le N cP
    omega
  have hslack : 5 * s + 3 + cL + cA ≤ logSlack (5 * cT * (L + 2) + 3 + cL + cA) N := by
    simp only [hs, logSlack]
    nlinarith [Nat.zero_le (cT * (Nat.bits N).length), Nat.zero_le (cT * L),
      Nat.zero_le (cT * (Nat.bits N).length * L), Nat.zero_le (cL * (Nat.bits N).length),
      Nat.zero_le (cA * (Nat.bits N).length), Nat.zero_le ((Nat.bits N).length),
      Nat.mul_le_mul_left cT hbits]
  rw [← ha, ← hb, (Monotone.map_max (f := fun m : ℕ => (m : ℕ∞))
    (fun m m' h => by dsimp only; exact_mod_cast h)).symm]
  refine hmain.trans ?_
  rw [← Nat.cast_add]
  exact_mod_cast (by omega : max a b + 5 * s + 3 + cL + cA ≤
    max a b + logSlack (5 * cT * (L + 2) + 3 + cL + cA) N)

/-- SUV Section 13.1, in-text claim restating Chapter 12 (printed p. 402).  The lower bound
matching `problemK_two_conditions_le`: `max (C(z|x), C(z|y)) ≤ C((x → z) ∧ (y → z))` up to the
book's precision `O(log C(x, y, z))`.
Proof idea (in fact `O(1)` suffices): the two components of a solution are programs mapping `x`
to `z` and `y` to `z`, computable from the solution (`problemK_left_le_conj`,
`problemK_right_le_conj`, `condK_le_problemK_imp_singleton`). -/
theorem max_condK_le_problemK_two_conditions (D : Map) (hD : isOptimalConditional D)
    (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ x y z : BitString,
      max (condK D z x) (condK D z y) ≤
        problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) +
          (logSlack c (plainK D (listCode [x, y, z])).toNat : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := condK_le_problemK_imp_singleton D hD P hP
  obtain ⟨c2, hc2⟩ := problemK_left_le_conj D hD P hP
  obtain ⟨c3, hc3⟩ := problemK_right_le_conj D hD P hP
  refine ⟨c1 + c2 + c3, fun x y z => ?_⟩
  have hs : ((c1 + c2 + c3 : ℕ) : ℕ∞) ≤
      (logSlack (c1 + c2 + c3) (plainK D (listCode [x, y, z])).toNat : ℕ∞) := by
    have h : c1 + c2 + c3 ≤ logSlack (c1 + c2 + c3) (plainK D (listCode [x, y, z])).toNat :=
      Nat.le_add_left _ _
    exact_mod_cast h
  refine max_le ?_ ?_
  · calc condK D z x ≤ problemK D (P.imp {x} {z}) + c1 := hc1 x z
      _ ≤ (problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) + (c2 : ℕ∞)) + c1 := by
          gcongr; exact hc2 _ _
      _ ≤ problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) + ((c1 + c2 + c3 : ℕ) : ℕ∞) := by
          rw [add_assoc]; gcongr
          exact_mod_cast (by omega : c2 + c1 ≤ c1 + c2 + c3)
      _ ≤ _ := by gcongr
  · calc condK D z y ≤ problemK D (P.imp {y} {z}) + c1 := hc1 y z
      _ ≤ (problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) + (c3 : ℕ∞)) + c1 := by
          gcongr; exact hc3 _ _
      _ ≤ problemK D (P.conj (P.imp {x} {z}) (P.imp {y} {z})) + ((c1 + c2 + c3 : ℕ) : ℕ∞) := by
          rw [add_assoc]; gcongr
          exact_mod_cast (by omega : c3 + c1 ≤ c1 + c2 + c3)
      _ ≤ _ := by gcongr

end InformationLogic
end Kolmogorov
