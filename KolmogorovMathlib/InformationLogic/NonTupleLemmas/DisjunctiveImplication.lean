import KolmogorovMathlib.InformationLogic.NonTupleLemmas.QuadrupleGap

/-!
# Disjunctive Implication

This module formalizes Problem 344 of Section 13.6 of Shen, Uspensky and Vereshchagin,
"Kolmogorov complexity and algorithmic randomness": the complexity of the problem
`(p ∨ q) → (r ∨ s)` is not determined by the complexity profile of the quadruple `(p, q, r, s)`.

The main declaration is `exists_quadruples_profileClose_problemK_disjImp_gap`, which gives two
sequences of quadruples of lengths `O(n)` with the same complexity profile up to `O(log n)`
whose disjunctive-implication problems differ in complexity by at least `n / m`.  The quadruples
are derived from the base quadruples of the proof of Theorem 247 as `(a, b, ⟨a, c⟩, ⟨b, d⟩)`.
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- The quadruple `(p, q, r, s) = (a, b, ⟨a, c⟩, ⟨b, d⟩)` built from `(a, b, c, d)` for Problem 344
(the book's concatenations `ac`, `bd`, written with the self-delimiting `pairCode` so that the
sub-tuples stay computably equivalent without knowing `n`). -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_derived
    (q : Fin 4 → BitString) : Fin 4 → BitString :=
  ![q 0, q 1, pairCode (q 0) (q 2), pairCode (q 1) (q 3)]

/-- Auxiliary for `exists_quadruples_profileClose_problemK_disjImp_gap_upper`:
xor is associative and commutative on words of equal length. -/
private lemma exists_quadruples_profileClose_problemK_disjImp_gap_upper_xor
    (a b e : BitString) (hab : a.length = b.length) :
    xorStr (xorStr a b) e = xorStr b (xorStr a e) := by
  refine List.ext_getElem (by simp [hab]) (fun i h1 h2 => ?_)
  have hi : i < a.length := by simpa using h1
  have hib : i < b.length := hab ▸ hi
  have hia : i < (xorStr a b).length := by simpa using hi
  have hie : i < (xorStr a e).length := by simpa using hi
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2,
    getD_xorStr _ _ _ hia, getD_xorStr _ _ _ hib, getD_xorStr _ _ _ hi, getD_xorStr _ _ _ hi]
  cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> simp

/-- Step 1 of the proof of
`exists_quadruples_profileClose_problemK_disjImp_gap_base`: the upper bound for the xor
quadruple.  For `n`-bit words `a, b, e` and `d = (a ⊕ b) ⊕ e`, the problem `(p ∨ q) → (r ∨ s)` of
the derived quadruple `(a, b, ⟨a, e⟩, ⟨b, d⟩)` has complexity `≤ n + c`, `c` independent of
`n, a, b, e`.  Proof: put `w = a ⊕ e` (an `n`-bit word, `C(w) ≤ n + O(1)`).  Let `V (s, x)`
unpair `x` into `(τ, z)` and output `P.pair τ ⟨z, z ⊕ s⟩`; by the Gödel property there is a
computable `t` with `[t s](x) = V (s, x)`.  Then `t w` maps `[0, a] ↦ [0, ⟨a, a ⊕ w⟩] = [0, ⟨a, e⟩]`
and `[1, b] ↦ [1, ⟨b, b ⊕ w⟩] = [1, ⟨b, d⟩]` (xor is involutive on words of equal length), so
`t w` solves the problem and `C(t w) ≤ C(w) + O(1) ≤ n + O(1)`. -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_upper
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ (n : ℕ) (a b e : BitString), a.length = n → b.length = n → e.length = n →
      problemK D (disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived
          ![a, b, e, xorStr (xorStr a b) e])) ≤ (n : ℕ∞) + (c : ℕ∞) := by
  classical
  obtain ⟨hpair, hunpair, hinv, -, -, -, hG⟩ := hP
  let f : BitString × BitString → BitString := fun r =>
    ((P.unpair r.2).map (fun tz => P.pair tz.1 (pairCode tz.2 (xorStr tz.2 r.1)))).getD []
  have hf : Computable f := by
    refine Computable.option_getD (Computable.option_map (hunpair.comp Computable.snd) ?_)
      (Computable.const [])
    have hx : Computable fun p : (BitString × BitString) × (BitString × BitString) =>
        xorStr p.2.2 p.1.1 :=
      xorStr_primrec.to_comp.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.fst)
    have hpc : Computable fun p : (BitString × BitString) × (BitString × BitString) =>
        pairCode p.2.2 (xorStr p.2.2 p.1.1) :=
      Computable₂.comp (pairCode_computable : Computable₂ pairCode)
        (Computable.snd.comp Computable.snd) hx
    exact (hpair.comp (Computable.fst.comp Computable.snd) hpc).to₂
  obtain ⟨t, ht, hts⟩ := hG (fun r => Part.some (f r)) (Computable.partrec hf)
  obtain ⟨c0, hc0⟩ := plainK_le_length D hD
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD t ht
  refine ⟨c0 + c1, fun n a b e ha hb he => ?_⟩
  have hw : (xorStr a e).length = n := by simp [ha]
  have hmem : t (xorStr a e) ∈ disjImpProblem P
      (exists_quadruples_profileClose_problemK_disjImp_gap_derived
        ![a, b, e, xorStr (xorStr a b) e]) := by
    intro x hx
    simp only [exists_quadruples_profileClose_problemK_disjImp_gap_derived,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hx ⊢
    have hlang : ∀ x, P.lang (t (xorStr a e), x) = Part.some (f (xorStr a e, x)) := by
      intro x
      rw [hts]
    rcases hx with ⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩
    · simp only [Set.mem_singleton_iff] at hx'
      subst hx'
      refine ⟨P.pair P.tag0 (pairCode x' e), Or.inl ⟨_, rfl, rfl⟩, ?_⟩
      rw [hlang]
      simp [f, hinv, xorStr_xorStr_left x' e (ha.trans he.symm)]
    · simp only [Set.mem_singleton_iff] at hx'
      subst hx'
      refine ⟨P.pair P.tag1 (pairCode x' (xorStr (xorStr a x') e)), Or.inr ⟨_, rfl, rfl⟩, ?_⟩
      rw [hlang]
      simp only [f, hinv, Option.map_some, Option.getD_some, Part.mem_some_iff]
      rw [exists_quadruples_profileClose_problemK_disjImp_gap_upper_xor a x' e
        (ha.trans hb.symm)]
  calc _ ≤ plainK D (t (xorStr a e)) := problemK_le_of_mem D hmem
    _ ≤ plainK D (xorStr a e) + (c1 : ℕ∞) := hc1 _
    _ ≤ ((xorStr a e).length : ℕ∞) + (c0 : ℕ∞) + (c1 : ℕ∞) := by
        gcongr; simpa using hc0 (xorStr a e)
    _ = _ := by rw [hw]; push_cast; ring

/-- Step 1 of the proof of `exists_quadruples_profileClose_problemK_disjImp_gap`: the
two base quadruples of the proof of Theorem 247 (probabilistic version: the triple
`(ã, b̃, c̃)` of complexity `≥ 3n − 1` among the good triples of
`exists_computable_family_problemK_quad_ge`, `d̃ = Q(ã, b̃, c̃)`; `(ā, b̄, c̄)` a random `3n`-bit
string cut in three, `d̄ = ā ⊕ b̄ ⊕ c̄`), together with the facts about them that Problem 344
uses: lengths `O(n)`, the same complexity profile up to `O(log n)`, the profile of `ũ`
(`C(ã), C(b̃) ≤ n`, `C(ã, b̃, c̃), C(ã, b̃, d̃) ≥ 3n`, all up to `O(log n)`), the bound
`C((a → c) ∧ (b → d)) ≥ 2n − O(log n)` for `ũ`, and the upper bound `n + O(1)` for the problem
`(p ∨ q) → (r ∨ s)` of the derived `ū` (one program with the hardwired `e = ā ⊕ c̄` maps
`[0, x] ↦ [0, ⟨x, x ⊕ e⟩]` and `[1, y] ↦ [1, ⟨y, y ⊕ e⟩]`). -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_base
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ (c N : ℕ) (u v : ℕ → Fin 4 → BitString),
      (∀ n i, (u n i).length ≤ c * (n + 1) ∧ (v n i).length ≤ c * (n + 1)) ∧
      (∀ n, TupleProfileClose D (logSlack c n) (u n) (v n)) ∧
      ∀ n ≥ N,
        ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P (u n)) + (logSlack c n : ℕ∞) ∧
        ((3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode (u n) {0, 1, 2}) + (logSlack c n : ℕ∞) ∧
        ((3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode (u n) {0, 1, 3}) + (logSlack c n : ℕ∞) ∧
        plainK D (subtupleCode (u n) {0}) ≤ (n : ℕ∞) + (logSlack c n : ℕ∞) ∧
        plainK D (subtupleCode (u n) {1}) ≤ (n : ℕ∞) + (logSlack c n : ℕ∞) ∧
        problemK D (disjImpProblem P
          (exists_quadruples_profileClose_problemK_disjImp_gap_derived (v n))) ≤
          ((n + c : ℕ) : ℕ∞) := by
  classical
  obtain ⟨Q, cQ, N, hQ, hN⟩ := exists_computable_family_problemK_quad_ge D hD P hP
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_u D hD P hP Q hQ cQ
  obtain ⟨k3, h3⟩ := exists_quadruples_profileClose_problemK_quad_gap_profile_v D hD
  obtain ⟨c4, h4⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_upper D hD P hP
  have key : ∀ n : ℕ, ∃ uv : (Fin 4 → BitString) × (Fin 4 → BitString),
      (∀ i, (uv.1 i).length ≤ (k2 + k3 + cQ + c4 + 1) * (n + 1) ∧
        (uv.2 i).length ≤ (k2 + k3 + cQ + c4 + 1) * (n + 1)) ∧
      TupleProfileClose D (logSlack (k2 + k3 + cQ + c4 + 1) n) uv.1 uv.2 ∧
      (N ≤ n →
        ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P uv.1) +
          (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) ∧
        ((3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode uv.1 {0, 1, 2}) +
            (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) ∧
        ((3 * n : ℕ) : ℕ∞) ≤
          plainK D (subtupleCode uv.1 {0, 1, 3}) +
            (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) ∧
        plainK D (subtupleCode uv.1 {0}) ≤ (n : ℕ∞) +
          (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) ∧
        plainK D (subtupleCode uv.1 {1}) ≤ (n : ℕ∞) +
          (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) ∧
        problemK D (disjImpProblem P
          (exists_quadruples_profileClose_problemK_disjImp_gap_derived uv.2)) ≤
          ((n + (k2 + k3 + cQ + c4 + 1) : ℕ) : ℕ∞)) := by
    intro n
    by_cases hn : N ≤ n
    · obtain ⟨hlen, hcard⟩ := hN n hn
      obtain ⟨⟨a, b, e⟩, ht, hrand⟩ :=
        exists_quadruples_profileClose_problemK_quad_gap_count D n
          {t : BitString × BitString × BitString |
            t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.1, t.2.1, t.2.2,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞) ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.2, t.1, t.2.1,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞) ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.1, t.2.2, t.1,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞)}
          (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩) hcard
      obtain ⟨ha, hb, he, hl1, hl2, hl3⟩ := ht
      have hQlen := hlen a b e ha hb he
      have hxlen : (xorStr (xorStr a b) e).length = n := by simp [ha]
      have hs : (logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞) ≤
          (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) := by
        have h1 := logSlack_add_constants k2 k3 n
        have h2 := logSlack_mono_left (c := k2 + k3) (c' := k2 + k3 + cQ + c4 + 1)
          (by omega) n
        exact_mod_cast (by omega : logSlack k2 n + logSlack k3 n ≤
          logSlack (k2 + k3 + cQ + c4 + 1) n)
      have hs2 : (logSlack k2 n : ℕ∞) ≤ (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) := by
        exact_mod_cast logSlack_mono_left (c := k2) (c' := k2 + k3 + cQ + c4 + 1) (by omega) n
      have hsQ : (logSlack cQ n : ℕ∞) ≤ (logSlack (k2 + k3 + cQ + c4 + 1) n : ℕ∞) := by
        exact_mod_cast logSlack_mono_left (c := cQ) (c' := k2 + k3 + cQ + c4 + 1) (by omega) n
      have hprof := h2 n a b e ha hb he hQlen hrand hl1 hl2 hl3
      refine ⟨(![a, b, e, Q n a b e], ![a, b, e, xorStr (xorStr a b) e]), ?_, ?_, ?_⟩
      · intro i
        have hnc : n ≤ (k2 + k3 + cQ + c4 + 1) * (n + 1) := by nlinarith
        fin_cases i <;> simp [ha, hb, he, hQlen, hxlen, hnc]
      · intro S hS
        obtain ⟨u1, u2⟩ := hprof S hS
        obtain ⟨v1, v2⟩ := h3 n a b e ha hb he hrand S hS
        constructor
        · calc _ ≤ _ := u1
            _ ≤ (plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) +
                (logSlack k3 n : ℕ∞)) + (logSlack k2 n : ℕ∞) := by gcongr
            _ = plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) +
                ((logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞)) := by ring
            _ ≤ _ := by gcongr
        · calc _ ≤ _ := v1
            _ ≤ (plainK D (subtupleCode ![a, b, e, Q n a b e] S) +
                (logSlack k2 n : ℕ∞)) + (logSlack k3 n : ℕ∞) := by gcongr
            _ = plainK D (subtupleCode ![a, b, e, Q n a b e] S) +
                ((logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞)) := by ring
            _ ≤ _ := by gcongr
      · intro _
        have hup := h4 n a b e ha hb he
        have c012 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
        have c013 : ({0, 1, 3} : Finset (Fin 4)).card = 3 := by decide
        have c0 : ({0} : Finset (Fin 4)).card = 1 := by decide
        have c1 : ({1} : Finset (Fin 4)).card = 1 := by decide
        have p012 := (hprof {0, 1, 2} ⟨0, by decide⟩).2
        have p013 := (hprof {0, 1, 3} ⟨0, by decide⟩).2
        have p0 := (hprof {0} ⟨0, by decide⟩).1
        have p1 := (hprof {1} ⟨1, by decide⟩).1
        rw [c012] at p012
        rw [c013] at p013
        rw [c0] at p0
        rw [c1] at p1
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hl1.trans (by gcongr)
        · exact (by simpa using p012 : ((3 * n : ℕ) : ℕ∞) ≤ _).trans (by gcongr)
        · exact (by simpa using p013 : ((3 * n : ℕ) : ℕ∞) ≤ _).trans (by gcongr)
        · exact (by simpa using p0 : plainK D (subtupleCode ![a, b, e, Q n a b e] {0}) ≤
            (n : ℕ∞) + (logSlack k2 n : ℕ∞)).trans (by gcongr)
        · exact (by simpa using p1 : plainK D (subtupleCode ![a, b, e, Q n a b e] {1}) ≤
            (n : ℕ∞) + (logSlack k2 n : ℕ∞)).trans (by gcongr)
        · exact hup.trans (by exact_mod_cast (by omega))
    · refine ⟨(fun _ => [], fun _ => []), ?_, ?_, fun h => absurd h hn⟩
      · intro i; simp
      · intro S _
        exact ⟨le_self_add, le_self_add⟩
  choose uv huv using key
  exact ⟨k2 + k3 + cQ + c4 + 1, N, fun n => (uv n).1, fun n => (uv n).2,
    fun n => (huv n).1, fun n => (huv n).2.1, fun n hn => (huv n).2.2 hn⟩

/-- Auxiliary for `exists_quadruples_profileClose_problemK_disjImp_gap_profile`: the index
set `S ∪ {0 | 2 ∈ S} ∪ {1 | 3 ∈ S}`. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup
    (S : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => j ∈ S ∨ (j = 0 ∧ 2 ∈ S) ∨ (j = 1 ∧ 3 ∈ S))

/-- Auxiliary: the entry of the decoded list of `w` at the position of the index `i` in `S`. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk
    (S : Finset (Fin 4)) (w : BitString) (i : Fin 4) : BitString :=
  (decodeListCode w).getD (((List.finRange 4).filter (fun j => decide (j ∈ S))).idxOf i) []

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_computable
    (S : Finset (Fin 4)) (i : Fin 4) :
    Computable (fun w => exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk
      S w i) :=
  (Primrec.list_getD ([] : BitString)).to_comp.comp decodeListCode_computable
    (Computable.const _)

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_subtupleCode
    (q : Fin 4 → BitString) (S : Finset (Fin 4)) (i : Fin 4) (hi : i ∈ S) :
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S
      (subtupleCode q S) i = q i := by
  unfold exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk subtupleCode
  rw [decodeListCode_listCode]
  have hiL : i ∈ (List.finRange 4).filter (fun j => decide (j ∈ S)) := by simp [hi]
  have hlt := List.idxOf_lt_length_iff.mpr hiL
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp [List.getElem_idxOf]

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_listCode_map_computable
    {ι : Type} (L : List ι) (b : ι → BitString → BitString)
    (hb : ∀ j, Computable (b j)) :
    Computable (fun w => listCode (L.map (fun j => b j w))) := by
  induction L with
  | nil => simpa using Computable.const ([] : BitString)
  | cons j L ih =>
    have := Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
      (g := fun w => (b j w, listCode (L.map (fun j => b j w)))) pairCode_computable
      ((hb j).pair ih)
    simpa [listCode_cons] using this

/-- Auxiliary: the entries of the base quadruple recovered from a code of the sub-tuple `S` of the
derived quadruple. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB
    (S : Finset (Fin 4)) (w : BitString) : Fin 4 → BitString
  | 0 => if (0 : Fin 4) ∈ S then
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 0
    else decodeFirst (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 2)
  | 1 => if (1 : Fin 4) ∈ S then
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 1
    else decodeFirst (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 3)
  | 2 => decodeSecond (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 2)
  | 3 => decodeSecond (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk S w 3)

/-- Auxiliary: forward map, sub-tuple `S` of the derived quadruple to sub-tuple `sup S` of the
base quadruple. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd
    (S : Finset (Fin 4)) (w : BitString) : BitString :=
  listCode (((List.finRange 4).filter (fun j => decide (j ∈
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S))).map
    (fun j => exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB S w j))

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd_computable
    (S : Finset (Fin 4)) :
    Computable (exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd S) := by
  have hlk := exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_computable S
  apply exists_quadruples_profileClose_problemK_disjImp_gap_profile_listCode_map_computable
    (b := fun j w =>
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB S w j)
  intro j
  fin_cases j
  · by_cases h : (0 : Fin 4) ∈ S
    · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h] using
        hlk 0
    · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h] using
        decodeFirst_computable.comp (hlk 2)
  · by_cases h : (1 : Fin 4) ∈ S
    · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h] using
        hlk 1
    · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h] using
        decodeFirst_computable.comp (hlk 3)
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB] using
      decodeSecond_computable.comp (hlk 2)
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB] using
      decodeSecond_computable.comp (hlk 3)

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd_eq
    (u : Fin 4 → BitString) (S : Finset (Fin 4)) :
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd S
      (subtupleCode (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S) =
    subtupleCode u (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S) := by
  unfold exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd
  conv_rhs => unfold subtupleCode
  congr 1
  apply List.map_congr_left
  intro j hj
  have hlk := fun i (hi : i ∈ S) =>
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_subtupleCode
      (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S i hi
  simp only [List.mem_filter, decide_eq_true_eq,
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup, Finset.mem_filter,
    Finset.mem_univ, true_and] at hj
  have hj := hj.2
  generalize subtupleCode (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S = w
    at hlk ⊢
  have hall : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hall j with rfl | rfl | rfl | rfl
  · by_cases h : (0 : Fin 4) ∈ S
    · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h,
        hlk 0 h, exists_quadruples_profileClose_problemK_disjImp_gap_derived]
    · have h2 : (2 : Fin 4) ∈ S := by simpa [h] using hj
      simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h,
        hlk 2 h2, exists_quadruples_profileClose_problemK_disjImp_gap_derived,
        decodeFirst_pairCode]
  · by_cases h : (1 : Fin 4) ∈ S
    · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h,
        hlk 1 h, exists_quadruples_profileClose_problemK_disjImp_gap_derived]
    · have h2 : (3 : Fin 4) ∈ S := by simpa [h] using hj
      simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB, h,
        hlk 3 h2, exists_quadruples_profileClose_problemK_disjImp_gap_derived,
        decodeFirst_pairCode]
  · have h2 : (2 : Fin 4) ∈ S := by simpa using hj
    simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB,
      hlk 2 h2, exists_quadruples_profileClose_problemK_disjImp_gap_derived,
      decodeSecond_pairCode]
  · have h2 : (3 : Fin 4) ∈ S := by simpa using hj
    simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwdB,
      hlk 3 h2, exists_quadruples_profileClose_problemK_disjImp_gap_derived,
      decodeSecond_pairCode]

/-- Auxiliary: the entries of the derived quadruple recovered from a code of a sub-tuple of the
base quadruple. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB
    (T : Finset (Fin 4)) (w : BitString) : Fin 4 → BitString
  | 0 => exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 0
  | 1 => exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 1
  | 2 => pairCode (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 0)
      (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 2)
  | 3 => pairCode (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 1)
      (exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk T w 3)

/-- Auxiliary: backward map, sub-tuple `sup S` of the base quadruple to sub-tuple `S` of the
derived quadruple. -/
private def exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd
    (S : Finset (Fin 4)) (w : BitString) : BitString :=
  listCode (((List.finRange 4).filter (fun j => decide (j ∈ S))).map
    (fun j => exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB
      (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S) w j))

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd_computable
    (S : Finset (Fin 4)) :
    Computable (exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd S) := by
  have hlk := exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_computable
    (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S)
  have hpc : ∀ {f g : BitString → BitString}, Computable f → Computable g →
      Computable (fun x => pairCode (f x) (g x)) := fun hf hg =>
    Computable.comp (f := fun p : BitString × BitString => pairCode p.1 p.2)
      pairCode_computable (hf.pair hg)
  apply exists_quadruples_profileClose_problemK_disjImp_gap_profile_listCode_map_computable
    (b := fun j w =>
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB
        (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S) w j)
  intro j
  fin_cases j
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB] using hlk 0
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB] using hlk 1
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB] using
      hpc (hlk 0) (hlk 2)
  · simpa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB] using
      hpc (hlk 1) (hlk 3)

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd_eq
    (u : Fin 4 → BitString) (S : Finset (Fin 4)) :
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd S
      (subtupleCode u
        (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S)) =
    subtupleCode (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S := by
  unfold exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd
  conv_rhs => unfold subtupleCode
  congr 1
  apply List.map_congr_left
  intro j hj
  have hlk := fun i (hi : i ∈
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S) =>
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_lk_subtupleCode u _ i hi
  simp only [List.mem_filter, decide_eq_true_eq] at hj
  have hj := hj.2
  have hS : ∀ i, i ∈ S → i ∈
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S := by
    intro i hi
    simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup, hi]
  have h0 : (2 : Fin 4) ∈ S → (0 : Fin 4) ∈
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S := by
    intro h
    simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup, h]
  have h1 : (3 : Fin 4) ∈ S → (1 : Fin 4) ∈
      exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S := by
    intro h
    simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup, h]
  have hall : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hall j with rfl | rfl | rfl | rfl
  · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB,
      hlk 0 (hS 0 hj), exists_quadruples_profileClose_problemK_disjImp_gap_derived]
  · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB,
      hlk 1 (hS 1 hj), exists_quadruples_profileClose_problemK_disjImp_gap_derived]
  · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB,
      hlk 0 (h0 hj), hlk 2 (hS 2 hj),
      exists_quadruples_profileClose_problemK_disjImp_gap_derived]
  · simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwdB,
      hlk 1 (h1 hj), hlk 3 (hS 3 hj),
      exists_quadruples_profileClose_problemK_disjImp_gap_derived]

/-- Auxiliary: for each `S` there are constants for both directions between the sub-tuple `S` of
the derived quadruple and the sub-tuple `sup S` of the base quadruple. -/
private lemma exists_quadruples_profileClose_problemK_disjImp_gap_profile_const
    (D : Map) (hD : isOptimalConditional D) (S : Finset (Fin 4)) :
    ∃ c1 c2 : ℕ, ∀ u : Fin 4 → BitString,
      plainK D (subtupleCode
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S) ≤
        plainK D (subtupleCode u
          (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S)) +
          (c1 : ℕ∞) ∧
      plainK D (subtupleCode u
          (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S)) ≤
        plainK D (subtupleCode
          (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S) + (c2 : ℕ∞) := by
  obtain ⟨c1, h1⟩ := plainK_partrec_map_le D hD _
    (exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd_computable S).partrec
  obtain ⟨c2, h2⟩ := plainK_partrec_map_le D hD _
    (exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd_computable S).partrec
  refine ⟨c1, c2, fun u => ⟨?_, ?_⟩⟩
  · have := h1 (subtupleCode u
      (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S)) _
      (Part.mem_some _)
    rwa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_bwd_eq] at this
  · have := h2 (subtupleCode
      (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S) _ (Part.mem_some _)
    rwa [exists_quadruples_profileClose_problemK_disjImp_gap_profile_fwd_eq] at this

/-- Step 2 of the proof of `exists_quadruples_profileClose_problemK_disjImp_gap`:
every sub-tuple of the derived quadruple `(a, b, ⟨a, c⟩, ⟨b, d⟩)` is computably equivalent (by
fixed computable maps in both directions, independent of the quadruple) to a sub-tuple of
`(a, b, c, d)`, so a profile bound for two quadruples transfers to the derived ones with an
additional `O(1)` slack. -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_profile
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (s : ℕ) (u v : Fin 4 → BitString), TupleProfileClose D s u v →
      TupleProfileClose D (s + k)
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived u)
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived v) := by
  classical
  choose c1 c2 hc using fun S =>
    exists_quadruples_profileClose_problemK_disjImp_gap_profile_const D hD S
  refine ⟨∑ S : Finset (Fin 4), (c1 S + c2 S), fun s u v huv S hS => ?_⟩
  have hSne : (exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S).Nonempty :=
      by
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, by simp [exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup, hi]⟩
  obtain ⟨h1, h2⟩ := huv _ hSne
  have hle : c1 S + c2 S ≤ ∑ S : Finset (Fin 4), (c1 S + c2 S) :=
    Finset.single_le_sum (f := fun S => c1 S + c2 S) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ S)
  have hk : ((c1 S : ℕ∞) + (c2 S : ℕ∞)) ≤ ((∑ S : Finset (Fin 4), (c1 S + c2 S) : ℕ) : ℕ∞) := by
    exact_mod_cast hle
  obtain ⟨a1, a2⟩ := hc S u
  obtain ⟨b1, b2⟩ := hc S v
  generalize exists_quadruples_profileClose_problemK_disjImp_gap_profile_sup S = T at *
  generalize (∑ S : Finset (Fin 4), (c1 S + c2 S) : ℕ) = k at *
  generalize plainK D (subtupleCode u T) = xu at *
  generalize plainK D (subtupleCode v T) = xv at *
  generalize plainK D (subtupleCode
    (exists_quadruples_profileClose_problemK_disjImp_gap_derived u) S) = yu at *
  generalize plainK D (subtupleCode
    (exists_quadruples_profileClose_problemK_disjImp_gap_derived v) S) = yv at *
  rw [Nat.cast_add]
  constructor
  · calc yu ≤ xu + c1 S := a1
      _ ≤ (xv + s) + c1 S := by gcongr
      _ ≤ ((yv + c2 S) + s) + c1 S := by gcongr
      _ = yv + (s + (c1 S + c2 S)) := by ring
      _ ≤ yv + (s + k) := by gcongr
  · calc yv ≤ xv + c1 S := b1
      _ ≤ (xu + s) + c1 S := by gcongr
      _ ≤ ((yu + c2 S) + s) + c1 S := by gcongr
      _ = yu + (s + (c1 S + c2 S)) := by ring
      _ ≤ yu + (s + k) := by gcongr

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub013
    (q : Fin 4 → BitString) : subtupleCode q {0, 1, 3} = listCode [q 0, q 1, q 3] := by
  simp [subtupleCode, List.finRange]

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub012
    (q : Fin 4 → BitString) : subtupleCode q {0, 1, 2} = listCode [q 0, q 1, q 2] := by
  simp [subtupleCode, List.finRange]

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub0
    (q : Fin 4 → BitString) : subtupleCode q {0} = listCode [q 0] := by
  simp [subtupleCode, List.finRange]

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub1
    (q : Fin 4 → BitString) : subtupleCode q {1} = listCode [q 1] := by
  simp [subtupleCode, List.finRange]

private lemma exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_pair
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (a π : BitString), a.length ≤ n →
      plainK D (pairCode (listCode [a]) π) ≤
        plainK D π + plainK D (listCode [a]) + (logSlack k n : ℕ∞) := by
  obtain ⟨k0, h0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨c1, hc1⟩ := plainK_le_length D hD
  refine ⟨2 + 2 * (Nat.bits (c1 + 3)).length + k0, fun n a π ha => ?_⟩
  have hX : plainK D (listCode [a]) ≤ ((2 * n + 1 + c1 : ℕ) : ℕ∞) := by
    refine (hc1 _).trans ?_
    have : programLength (listCode [a]) = 2 * a.length + 1 := by
      simp [programLength, listCode]; omega
    rw [this]
    exact_mod_cast (by omega : 2 * a.length + 1 + c1 ≤ 2 * n + 1 + c1)
  have hcv : cVal D (listCode [a]) ≤ 2 * n + 1 + c1 := by
    unfold cVal
    exact ENat.toNat_le_of_le_natCast hX
  have hlog : Nat.log 2 (cVal D (listCode [a])) ≤ (Nat.bits (c1 + 3)).length +
      (Nat.bits n).length := by
    have hm : cVal D (listCode [a]) < 2 ^ ((Nat.bits (c1 + 3)).length + (Nat.bits n).length) := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, pow_add]
      calc cVal D (listCode [a]) ≤ 2 * n + 1 + c1 := hcv
        _ ≤ (c1 + 3) * (n + 1) := by nlinarith
        _ ≤ (c1 + 3) * 2 ^ n.size := Nat.mul_le_mul_left _ (Nat.lt_size_self n)
        _ < 2 ^ (c1 + 3).size * 2 ^ n.size :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
    by_cases h0' : cVal D (listCode [a]) = 0
    · rw [h0']; simp
    · exact (Nat.log_lt_of_lt_pow h0' hm).le
  have hk := h0 (listCode [a]) π
  unfold cPair at hk
  have hslack : 2 * Nat.log 2 (cVal D (listCode [a])) + k0 ≤
      logSlack (2 + 2 * (Nat.bits (c1 + 3)).length + k0) n := by
    unfold logSlack
    generalize (Nat.bits (c1 + 3)).length = S1 at *
    generalize (Nat.bits n).length = S2 at *
    nlinarith [Nat.zero_le (S1 * S2), Nat.zero_le (k0 * S2)]
  calc plainK D (pairCode (listCode [a]) π)
      ≤ plainK D (listCode [a]) + plainK D π +
        ((2 * Nat.log 2 (cVal D (listCode [a])) + k0 : ℕ) : ℕ∞) := hk
    _ ≤ plainK D (listCode [a]) + plainK D π +
        (logSlack (2 + 2 * (Nat.bits (c1 + 3)).length + k0) n : ℕ∞) := by
      gcongr
    _ = _ := by ring

/-- Step 1 of the proof of
`exists_quadruples_profileClose_problemK_disjImp_gap_cases`:
if the solution `π` maps `[0, a]` to `[1, ⟨b, d⟩]` (where `q = (a, b, c, d)`, strings of length at
most `n`), then `(a, b, d)` is computed from `(a, π)`: a fixed partial computable map runs the
language on `π` and `[0, a]`, unpairs the result and splits the pair code; so
`C(a, b, d) ≤ C(⟨a-code, π⟩) + O(1) ≤ C(π) + C(a-code) + O(log n)` (using `C(a-code) ≤ 2n + O(1)`).
-/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_first
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      ∀ π : BitString,
        P.pair P.tag1 (pairCode (q 1) (q 3)) ∈ P.lang (π, P.pair P.tag0 (q 0)) →
        plainK D (subtupleCode q {0, 1, 3}) ≤
          plainK D π + plainK D (subtupleCode q {0}) + (logSlack k n : ℕ∞) := by
  obtain ⟨hpair, hunp, hinv, -, -, hG⟩ := hP
  have hL : Partrec P.lang := hG.1
  obtain ⟨k, hk⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_pair D hD
  let ex : BitString → BitString := fun y => (P.unpair y).casesOn [] (fun p => p.2)
  have hex : Computable ex :=
    Computable.option_casesOn hunp (Computable.const [])
      ((Computable.snd.comp Computable.snd).to₂)
  let mf : BitString → BitString → BitString := fun w y =>
    pairCode (decodeFirst (decodeFirst w))
      (pairCode (decodeFirst (ex y)) (pairCode (decodeSecond (ex y)) []))
  have hmf : Computable₂ mf := by
    have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
    have hw : Computable (fun p : BitString × BitString => decodeFirst (decodeFirst p.1)) :=
      decodeFirst_computable.comp (decodeFirst_computable.comp Computable.fst)
    have hy : Computable (fun p : BitString × BitString => ex p.2) := hex.comp Computable.snd
    exact hpc.comp hw
      (hpc.comp (decodeFirst_computable.comp hy)
        (hpc.comp (decodeSecond_computable.comp hy) (Computable.const [])))
  let F : BitString →. BitString := fun w =>
    (P.lang (decodeSecond w, P.pair P.tag0 (decodeFirst (decodeFirst w)))).map (mf w)
  have hF : Partrec F :=
    Partrec.map
      (hL.comp ((decodeSecond_computable).pair
        (hpair.comp (Computable.const P.tag0)
          (decodeFirst_computable.comp decodeFirst_computable))))
      hmf
  obtain ⟨c0, hc0⟩ := plainK_le_of_mem_partrec D hD F hF
  refine ⟨k + c0, fun n q hq π hπ => ?_⟩
  rw [exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub013,
    exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub0]
  have hmem : listCode [q 0, q 1, q 3] ∈ F (pairCode (listCode [q 0]) π) := by
    have hm := Part.mem_map (mf (pairCode (listCode [q 0]) π)) hπ
    have e : mf (pairCode (listCode [q 0]) π) (P.pair P.tag1 (pairCode (q 1) (q 3))) =
        listCode [q 0, q 1, q 3] := by
      simp [mf, ex, hinv, decodeFirst_pairCode, decodeSecond_pairCode, listCode]
    rw [e] at hm
    simpa [F, decodeFirst_pairCode, decodeSecond_pairCode, listCode] using hm
  have h1 := hc0 _ _ hmem
  have h2 := hk n (q 0) π (hq 0)
  have hs : (logSlack k n : ℕ∞) + (c0 : ℕ∞) ≤ (logSlack (k + c0) n : ℕ∞) := by
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr (by unfold logSlack; nlinarith [Nat.zero_le (c0 * (Nat.bits n).length)])
  calc plainK D (listCode [q 0, q 1, q 3])
      ≤ plainK D (pairCode (listCode [q 0]) π) + (c0 : ℕ∞) := h1
    _ ≤ (plainK D π + plainK D (listCode [q 0]) + (logSlack k n : ℕ∞)) + (c0 : ℕ∞) := by
      gcongr
    _ = plainK D π + plainK D (listCode [q 0]) + ((logSlack k n : ℕ∞) + (c0 : ℕ∞)) := by ring
    _ ≤ _ := by gcongr

/-- Step 2 of the proof of
`exists_quadruples_profileClose_problemK_disjImp_gap_cases`:
symmetric to step 1: if `π` maps `[1, b]` to `[0, ⟨a, c⟩]`, then `(a, b, c)` is computed from
`(b, π)`, so `C(a, b, c) ≤ C(π) + C(b-code) + O(log n)`. -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_second
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      ∀ π : BitString,
        P.pair P.tag0 (pairCode (q 0) (q 2)) ∈ P.lang (π, P.pair P.tag1 (q 1)) →
        plainK D (subtupleCode q {0, 1, 2}) ≤
          plainK D π + plainK D (subtupleCode q {1}) + (logSlack k n : ℕ∞) := by
  obtain ⟨hpair, hunp, hinv, -, -, hG⟩ := hP
  have hL : Partrec P.lang := hG.1
  obtain ⟨k, hk⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_pair D hD
  let ex : BitString → BitString := fun y => (P.unpair y).casesOn [] (fun p => p.2)
  have hex : Computable ex :=
    Computable.option_casesOn hunp (Computable.const [])
      ((Computable.snd.comp Computable.snd).to₂)
  let mf : BitString → BitString → BitString := fun w y =>
    pairCode (decodeFirst (ex y))
      (pairCode (decodeFirst (decodeFirst w)) (pairCode (decodeSecond (ex y)) []))
  have hmf : Computable₂ mf := by
    have hpc : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
    have hw : Computable (fun p : BitString × BitString => decodeFirst (decodeFirst p.1)) :=
      decodeFirst_computable.comp (decodeFirst_computable.comp Computable.fst)
    have hy : Computable (fun p : BitString × BitString => ex p.2) := hex.comp Computable.snd
    exact hpc.comp (decodeFirst_computable.comp hy)
      (hpc.comp hw
        (hpc.comp (decodeSecond_computable.comp hy) (Computable.const [])))
  let F : BitString →. BitString := fun w =>
    (P.lang (decodeSecond w, P.pair P.tag1 (decodeFirst (decodeFirst w)))).map (mf w)
  have hF : Partrec F :=
    Partrec.map
      (hL.comp ((decodeSecond_computable).pair
        (hpair.comp (Computable.const P.tag1)
          (decodeFirst_computable.comp decodeFirst_computable))))
      hmf
  obtain ⟨c0, hc0⟩ := plainK_le_of_mem_partrec D hD F hF
  refine ⟨k + c0, fun n q hq π hπ => ?_⟩
  rw [exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub012,
    exists_quadruples_profileClose_problemK_disjImp_gap_cases_aux_sub1]
  have hmem : listCode [q 0, q 1, q 2] ∈ F (pairCode (listCode [q 1]) π) := by
    have hm := Part.mem_map (mf (pairCode (listCode [q 1]) π)) hπ
    have e : mf (pairCode (listCode [q 1]) π) (P.pair P.tag0 (pairCode (q 0) (q 2))) =
        listCode [q 0, q 1, q 2] := by
      simp [mf, ex, hinv, decodeFirst_pairCode, decodeSecond_pairCode, listCode]
    rw [e] at hm
    simpa [F, decodeFirst_pairCode, decodeSecond_pairCode, listCode] using hm
  have h1 := hc0 _ _ hmem
  have h2 := hk n (q 1) π (hq 1)
  have hs : (logSlack k n : ℕ∞) + (c0 : ℕ∞) ≤ (logSlack (k + c0) n : ℕ∞) := by
    rw [← Nat.cast_add]
    exact Nat.cast_le.mpr (by unfold logSlack; nlinarith [Nat.zero_le (c0 * (Nat.bits n).length)])
  calc plainK D (listCode [q 0, q 1, q 2])
      ≤ plainK D (pairCode (listCode [q 1]) π) + (c0 : ℕ∞) := h1
    _ ≤ (plainK D π + plainK D (listCode [q 1]) + (logSlack k n : ℕ∞)) + (c0 : ℕ∞) := by
      gcongr
    _ = plainK D π + plainK D (listCode [q 1]) + ((logSlack k n : ℕ∞) + (c0 : ℕ∞)) := by ring
    _ ≤ _ := by gcongr

/-- Step 3 of the proof of
`exists_quadruples_profileClose_problemK_disjImp_gap_cases`:
if `π` maps `[0, a]` to `[0, ⟨a, c⟩]` and `[1, b]` to `[1, ⟨b, d⟩]`, then the Gödel translations
`t₀(π)`, `t₁(π)` of the partial computable maps `V₀(s, x) = c` (read off from `[s]([0, x])`) and
`V₁(s, y) = d` (read off from `[s]([1, y])`) give the solution `[t₀(π), t₁(π)]` of
`(a → c) ∧ (b → d)`, a computable function of `π`; hence `C((a → c) ∧ (b → d)) ≤ C(π) + O(1)`,
the constant independent of `q` and `π`. -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_solution
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ (q : Fin 4 → BitString) (π : BitString),
      P.pair P.tag0 (pairCode (q 0) (q 2)) ∈ P.lang (π, P.pair P.tag0 (q 0)) →
      P.pair P.tag1 (pairCode (q 1) (q 3)) ∈ P.lang (π, P.pair P.tag1 (q 1)) →
      problemK D (quadProblem P q) ≤ plainK D π + (c : ℕ∞) := by
  obtain ⟨hpair, hunp, hinv, -, -, hG⟩ := hP
  have hL : Partrec P.lang := hG.1
  let g : BitString → BitString := fun y =>
    (P.unpair y).casesOn [] (fun p => decodeSecond p.2)
  have hg : Computable g :=
    Computable.option_casesOn hunp (Computable.const [])
      ((decodeSecond_computable.comp (Computable.snd.comp Computable.snd)).to₂)
  let V0 : Map := fun sx => (P.lang (sx.1, P.pair P.tag0 sx.2)).map g
  let V1 : Map := fun sx => (P.lang (sx.1, P.pair P.tag1 sx.2)).map g
  have hV0 : Partrec V0 :=
    Partrec.map
      (hL.comp (Computable.fst.pair (hpair.comp (Computable.const P.tag0) Computable.snd)))
      (hg.comp Computable.snd).to₂
  have hV1 : Partrec V1 :=
    Partrec.map
      (hL.comp (Computable.fst.pair (hpair.comp (Computable.const P.tag1) Computable.snd)))
      (hg.comp Computable.snd).to₂
  obtain ⟨t0, ht0, hts0⟩ := hG.2 V0 hV0
  obtain ⟨t1, ht1, hts1⟩ := hG.2 V1 hV1
  let f : BitString → BitString := fun s => P.pair (t0 s) (t1 s)
  have hf : Computable f := hpair.comp ht0 ht1
  obtain ⟨c, hc⟩ := plainK_map_le D hD f hf
  refine ⟨c, fun q π h0 h1 => ?_⟩
  have hmem : f π ∈ quadProblem P q := by
    refine Set.mem_image2_of_mem ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨q 2, rfl, ?_⟩
      rw [hts0]
      have e : g (P.pair P.tag0 (pairCode (q 0) (q 2))) = q 2 := by
        simp [g, hinv, decodeSecond_pairCode]
      have hm := Part.mem_map g h0
      rw [e] at hm
      exact hm
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨q 3, rfl, ?_⟩
      rw [hts1]
      have e : g (P.pair P.tag1 (pairCode (q 1) (q 3))) = q 3 := by
        simp [g, hinv, decodeSecond_pairCode]
      have hm := Part.mem_map g h1
      rw [e] at hm
      exact hm
  exact (problemK_le_of_mem D hmem).trans (hc π)

/-- Step 3 of the proof of `exists_quadruples_profileClose_problemK_disjImp_gap`: a
solution `π` of `(p ∨ q) → (r ∨ s)` for the derived quadruple `(a, b, ⟨a, c⟩, ⟨b, d⟩)` (strings
of length at most `n`) maps `[0, a]` and `[1, b]` into `{[0, ⟨a, c⟩], [1, ⟨b, d⟩]}`.  If `[0, a]`
goes to `[1, ⟨b, d⟩]`, then `(a, b, d)` is computed from `(a, π)`; if `[1, b]` goes to
`[0, ⟨a, c⟩]`, then `(a, b, c)` is computed from `(b, π)`; otherwise a Gödel translation of `π`
(`α(x) = c` from `π([0, x])`, `β(y) = d` from `π([1, y])`) is a solution of
`(a → c) ∧ (b → d)` of complexity `≤ C(π) + O(1)`.  Hence one of the three alternatives holds
(the first and the last two pay `O(log n)` for coding a pair). -/
private theorem exists_quadruples_profileClose_problemK_disjImp_gap_cases
    (D : Map) (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ k : ℕ, ∀ (n : ℕ) (q : Fin 4 → BitString), (∀ i, (q i).length ≤ n) →
      ∀ π ∈ disjImpProblem P
          (exists_quadruples_profileClose_problemK_disjImp_gap_derived q),
        problemK D (quadProblem P q) ≤ plainK D π + (logSlack k n : ℕ∞) ∨
        plainK D (subtupleCode q {0, 1, 3}) ≤
          plainK D π + plainK D (subtupleCode q {0}) + (logSlack k n : ℕ∞) ∨
        plainK D (subtupleCode q {0, 1, 2}) ≤
          plainK D π + plainK D (subtupleCode q {1}) + (logSlack k n : ℕ∞) := by
  obtain ⟨k1, h1⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_first D hD P hP
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_second D hD P hP
  obtain ⟨k3, h3⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_solution D hD P hP
  have hmono : ∀ (a b n : ℕ), a ≤ b → logSlack a n ≤ logSlack b n := by
    intro a b n hab
    unfold logSlack
    exact add_le_add (Nat.mul_le_mul_right _ hab) hab
  refine ⟨k1 + k2 + k3, fun n q hq π hπ => ?_⟩
  have hs1 : (logSlack k1 n : ℕ∞) ≤ (logSlack (k1 + k2 + k3) n : ℕ∞) :=
    Nat.cast_le.mpr (hmono _ _ _ (by omega))
  have hs2 : (logSlack k2 n : ℕ∞) ≤ (logSlack (k1 + k2 + k3) n : ℕ∞) :=
    Nat.cast_le.mpr (hmono _ _ _ (by omega))
  have hs3 : (k3 : ℕ∞) ≤ (logSlack (k1 + k2 + k3) n : ℕ∞) :=
    Nat.cast_le.mpr (by unfold logSlack; omega)
  obtain ⟨y, hy, hyπ⟩ := hπ (P.pair P.tag0 (q 0)) (Or.inl ⟨q 0, rfl, rfl⟩)
  obtain ⟨y', hy', hyπ'⟩ := hπ (P.pair P.tag1 (q 1)) (Or.inr ⟨q 1, rfl, rfl⟩)
  simp only [exists_quadruples_profileClose_problemK_disjImp_gap_derived,
    ProblemCalculus.disj, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hy hy'
  rcases hy with ⟨z, hz, hzy⟩ | ⟨z, hz, hzy⟩
  · rcases hy' with ⟨z', hz', hzy'⟩ | ⟨z', hz', hzy'⟩
    · right; right
      have hz'' : z' = pairCode (q 0) (q 2) := by simpa using hz'
      subst hz''
      subst hzy'
      exact (h2 n q hq π hyπ').trans (by gcongr)
    · left
      have hz1 : z = pairCode (q 0) (q 2) := by simpa using hz
      have hz2 : z' = pairCode (q 1) (q 3) := by simpa using hz'
      subst hz1 hz2 hzy hzy'
      exact (h3 q π hyπ hyπ').trans (by gcongr)
  · right; left
    have hz1 : z = pairCode (q 1) (q 3) := by simpa using hz
    subst hz1
    subst hzy
    exact (h1 n q hq π hyπ).trans (by gcongr)

/-- SUV Problem 344 (Section 13.6, printed p. 423).  The complexity of `(p ∨ q) → (r ∨ s)` is
not expressible through the complexities of `p, q, r, s`, their pairs, triples and the
quadruple: stated in the precise shape of Theorem 247 (two sequences of quadruples of lengths
`O(n)` with the same complexity profile up to `O(log n)` whose problems differ in complexity by
at least `n/m`).
Proof idea (book's hint): `p = a`, `q = b`, `r = ac`, `s = bd` (concatenations) for the two
quadruples of the proof of Theorem 247.  Every sub-tuple of `(p, q, r, s)` is computably
equivalent, given `n`, to a sub-tuple of `(a, b, c, d)`, so the profiles agree up to
`O(log n)`.  For `ū`: one program with the hardwired `e = a ⊕ c` maps `[0, x] ↦ [0, x(x ⊕ e)]`
and `[1, y] ↦ [1, y(y ⊕ e)]`, complexity `≤ n + O(1)`.  For `ũ` a solution maps `a` to `c` and
`b` to `d` (a solution of `(a → c) ∧ (b → d)`), or maps `a` to `(b, d)`, or `b` to `(a, c)`;
each costs `≥ 2n − O(log n)` for the probabilistic quadruples.  The statement of Theorem 247
alone does not imply this one: the proof needs the specific quadruples (from
`exists_computable_family_problemK_quad_ge`). -/
theorem exists_quadruples_profileClose_problemK_disjImp_gap (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ (m c N : ℕ) (u v : ℕ → Fin 4 → BitString), 0 < m ∧
      (∀ n i, (u n i).length ≤ c * (n + 1) ∧ (v n i).length ≤ c * (n + 1)) ∧
      (∀ n, TupleProfileClose D (logSlack c n) (u n) (v n)) ∧
      ∀ n ≥ N, (m : ℕ∞) * problemK D (disjImpProblem P (v n)) + (n : ℕ∞) ≤
        (m : ℕ∞) * problemK D (disjImpProblem P (u n)) := by
  classical
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_profile D hD
  obtain ⟨k3, h3⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_cases D hD P hP
  obtain ⟨c, N, u, v, hlen, hprof, hdata⟩ :=
    exists_quadruples_profileClose_problemK_disjImp_gap_base D hD P hP
  have hbits : ∀ n : ℕ, (Nat.bits (c * (n + 1))).length ≤
      (Nat.bits c).length + (Nat.bits n).length := by
    intro n
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le, pow_add]
    calc c * (n + 1) ≤ c * 2 ^ n.size := Nat.mul_le_mul_left _ (Nat.lt_size_self n)
      _ < 2 ^ c.size * 2 ^ n.size :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self c) (by positivity)
  obtain ⟨M, hM⟩ := exists_bits_linear_domination 1 (4 * c + 2 * k3)
    (6 * c + 2 * k3 * ((Nat.bits c).length + 2))
  refine ⟨2, 3 * c + 1 + k2, max N M,
    fun n => exists_quadruples_profileClose_problemK_disjImp_gap_derived (u n),
    fun n => exists_quadruples_profileClose_problemK_disjImp_gap_derived (v n),
    by norm_num, ?_, ?_, ?_⟩
  · intro n i
    have hu := hlen n
    unfold exists_quadruples_profileClose_problemK_disjImp_gap_derived
    constructor <;> fin_cases i <;>
      simp only [length_pairCode, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      nlinarith [(hu 0).1, (hu 1).1, (hu 2).1, (hu 3).1, (hu 0).2, (hu 1).2, (hu 2).2,
        (hu 3).2]
  · intro n S hS
    have e1 : logSlack c n + k2 ≤ logSlack (3 * c + 1 + k2) n := by
      unfold logSlack
      nlinarith [Nat.zero_le (c * (Nat.bits n).length), Nat.zero_le (k2 * (Nat.bits n).length),
        Nat.zero_le (Nat.bits n).length]
    obtain ⟨h1, h1'⟩ := h2 (logSlack c n) (u n) (v n) (hprof n) S hS
    have e1' : ((logSlack c n + k2 : ℕ) : ℕ∞) ≤ (logSlack (3 * c + 1 + k2) n : ℕ∞) :=
      by exact_mod_cast e1
    exact ⟨h1.trans (by gcongr), h1'.trans (by gcongr)⟩
  · intro n hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hnM : M ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨hq, h012, h013, ha, hb, hup⟩ := hdata n hnN
    have hMn := hM n hnM
    have hTb := Nat.mul_le_mul_left k3 (hbits n)
    have key : ∀ π ∈ disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived (u n)),
        ((2 * n : ℕ) : ℕ∞) ≤ plainK D π +
          ((2 * logSlack c n + logSlack k3 (c * (n + 1)) : ℕ) : ℕ∞) := by
      intro π hπ
      by_cases hpt : plainK D π = ⊤
      · simp [hpt]
      obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hpt
      rcases h3 (c * (n + 1)) (u n) (fun i => (hlen n i).1) π hπ with h | h | h
      · have : ((2 * n : ℕ) : ℕ∞) ≤ ((p + logSlack k3 (c * (n + 1)) + logSlack c n : ℕ) : ℕ∞) :=
          calc ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P (u n)) + (logSlack c n : ℕ∞) := hq
            _ ≤ (plainK D π + (logSlack k3 (c * (n + 1)) : ℕ∞)) + (logSlack c n : ℕ∞) := by
                gcongr
            _ = _ := by rw [← hp]; push_cast; rfl
        have := Nat.cast_le.mp this
        have : ((2 * n : ℕ) : ℕ∞) ≤ ((p + (2 * logSlack c n + logSlack k3 (c * (n + 1))) : ℕ) :
            ℕ∞) := by exact_mod_cast (by omega)
        rw [← hp]; exact this
      · have : ((3 * n : ℕ) : ℕ∞) ≤
            ((p + (n + logSlack c n) + logSlack k3 (c * (n + 1)) + logSlack c n : ℕ) : ℕ∞) :=
          calc ((3 * n : ℕ) : ℕ∞) ≤ plainK D (subtupleCode (u n) {0, 1, 3}) +
                (logSlack c n : ℕ∞) := h013
            _ ≤ (plainK D π + plainK D (subtupleCode (u n) {0}) +
                (logSlack k3 (c * (n + 1)) : ℕ∞)) + (logSlack c n : ℕ∞) := by gcongr
            _ ≤ (plainK D π + ((n : ℕ∞) + (logSlack c n : ℕ∞)) +
                (logSlack k3 (c * (n + 1)) : ℕ∞)) + (logSlack c n : ℕ∞) := by gcongr
            _ = _ := by rw [← hp]; push_cast; rfl
        have h' := Nat.cast_le.mp this
        have : ((2 * n : ℕ) : ℕ∞) ≤ ((p + (2 * logSlack c n + logSlack k3 (c * (n + 1))) : ℕ) :
            ℕ∞) := by exact_mod_cast (by omega)
        rw [← hp]; exact this
      · have : ((3 * n : ℕ) : ℕ∞) ≤
            ((p + (n + logSlack c n) + logSlack k3 (c * (n + 1)) + logSlack c n : ℕ) : ℕ∞) :=
          calc ((3 * n : ℕ) : ℕ∞) ≤ plainK D (subtupleCode (u n) {0, 1, 2}) +
                (logSlack c n : ℕ∞) := h012
            _ ≤ (plainK D π + plainK D (subtupleCode (u n) {1}) +
                (logSlack k3 (c * (n + 1)) : ℕ∞)) + (logSlack c n : ℕ∞) := by gcongr
            _ ≤ (plainK D π + ((n : ℕ∞) + (logSlack c n : ℕ∞)) +
                (logSlack k3 (c * (n + 1)) : ℕ∞)) + (logSlack c n : ℕ∞) := by gcongr
            _ = _ := by rw [← hp]; push_cast; rfl
        have h' := Nat.cast_le.mp this
        have : ((2 * n : ℕ) : ℕ∞) ≤ ((p + (2 * logSlack c n + logSlack k3 (c * (n + 1))) : ℕ) :
            ℕ∞) := by exact_mod_cast (by omega)
        rw [← hp]; exact this
    change ((2 : ℕ) : ℕ∞) * problemK D (disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived (v n))) + (n : ℕ∞) ≤
      ((2 : ℕ) : ℕ∞) * problemK D (disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived (u n)))
    by_cases hX : disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived (u n)) = ∅
    · rw [hX]; simp
    obtain ⟨π, hπX, hπeq⟩ := exists_mem_plainK_eq_problemK D (Set.nonempty_iff_ne_empty.mpr hX)
    by_cases hpt : plainK D π = ⊤
    · rw [← hπeq, hpt]; simp
    obtain ⟨p, hp⟩ := ENat.ne_top_iff_exists.mp hpt
    have hvt : problemK D (disjImpProblem P
        (exists_quadruples_profileClose_problemK_disjImp_gap_derived (v n))) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) hup
    obtain ⟨q, hqq⟩ := ENat.ne_top_iff_exists.mp hvt
    rw [← hqq] at hup ⊢
    have hup' : q ≤ n + c := by exact_mod_cast hup
    have hk := key π hπX
    rw [← hp] at hk
    have hk' : 2 * n ≤ p + (2 * logSlack c n + logSlack k3 (c * (n + 1))) := by
      exact_mod_cast hk
    rw [← hπeq, ← hp]
    have hSd : logSlack c n = c * (Nat.bits n).length + c := rfl
    have hTd : logSlack k3 (c * (n + 1)) = k3 * (Nat.bits (c * (n + 1))).length + k3 := rfl
    have : 2 * q + n ≤ 2 * p := by nlinarith
    exact_mod_cast this

end InformationLogic
end Kolmogorov
