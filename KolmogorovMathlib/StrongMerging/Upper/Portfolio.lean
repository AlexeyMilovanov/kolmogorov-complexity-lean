import KolmogorovMathlib.StrongMerging.Upper.Trial
import KolmogorovMathlib.StrongMerging.Upper.PortfolioFilter

/-!
# The universal portfolio (blueprint T04, `UpperPortfolio`)

`sublinear-merging.tex`, subsection "A uniform portfolio and exact partition normalization"
(tex ~904–918) and the blueprint paragraph "Portfolio and exact normalization"
(tex ~4011–4024).

* `outTrial cs e r oA oB z` is the `r`-th finite trial (T01) at the input `z`, with the witness
  outputs read by the functions `oA`, `oB` (`progOut` for the semantic selector, `tableOut` of
  complete-run tables inside the program); `outCost` is its observable cost
  `T_r = (j_r + 1) L_r`.
* `outPortfolio cs e oA oB z` runs the `n + 1` trials `r = 0, …, n` (`n = |z|`) and returns the
  candidate of least observable cost, ties to the least `r` (`argminUpTo`); it returns `{z}` when
  `|z| ≤ 1` or a witness output does not contain `z`.  It computes no profile, no mutual
  information and no complexity value.  `portfolioModel` is the semantic selector `q₀`.
* `upperPortfolio` (T04): for the fixed step constant `c_*` there is `c₀` such that for total
  witnesses of length `≤ e` one total program `q₀` of length `≤ 7 (e + 1) + c₀`, carrying only
  `p_A, p_B, e`, outputs the code of `portfolioModel` on every input.
* `portfolioModel_spec`: at a qualifying instance the selector returns the candidate of a trial
  `r* ≤ n` whose cost is least among all `r ≤ n`; `mem_portfolioModel_self`: the selector
  contains its input everywhere.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### The portfolio as a function of the witness outputs -/

/-- The shape graph at the input `z` read from the output functions `oA`, `oB`: data length
`|z|` and the floor buckets of the parsed outputs at `z`. -/
noncomputable def outShape (oA oB : BitString → BitString) (z : BitString) : ShapeParams :=
  ⟨oA, oB, z.length, Nat.log 2 (parseModel (oA z)).card, Nat.log 2 (parseModel (oB z)).card⟩

/-- The `r`-th trial at the input `z`, with step `L_r = c_* (H + r)`, `H = e + ⌈log₂ (|z| + 2)⌉`,
and the larger-bucket parsed output as fallback. -/
noncomputable def outTrial (cs e r : ℕ) (oA oB : BitString → BitString) (z : BitString) :
    Finset BitString × ℕ :=
  trialRun (outShape oA oB z) (trialStep cs z.length e r)
    (largerModel (parseModel (oA z)) (parseModel (oB z))) z

/-- The observable cost `T_r = (j_r + 1) L_r` of the `r`-th trial at `z`. -/
noncomputable def outCost (cs e r : ℕ) (oA oB : BitString → BitString) (z : BitString) : ℕ :=
  ((outTrial cs e r oA oB z).2 + 1) * trialStep cs z.length e r

/-- The least index `r ≤ m` minimizing `f` (a left fold keeping the first strict improvement). -/
def argminUpTo (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range (m + 1)).foldl (fun best r => if f r < f best then r else best) 0

/-- **The fold computes a minimizer**: `argminUpTo f m ≤ m` and `f (argminUpTo f m) ≤ f r` for
every `r ≤ m` (induction on `m`, `List.range_succ`, `List.foldl_append`). -/
theorem argminUpTo_spec (f : ℕ → ℕ) (m : ℕ) :
    argminUpTo f m ≤ m ∧ ∀ r ≤ m, f (argminUpTo f m) ≤ f r := by
  induction m with
  | zero =>
    have h0 : argminUpTo f 0 = 0 := by
      change List.foldl _ 0 (List.range 1) = 0
      simp
    rw [h0]
    exact ⟨le_rfl, fun r hr => by rw [Nat.le_zero.mp hr]⟩
  | succ m ih =>
    have hstep : argminUpTo f (m + 1) =
        if f (m + 1) < f (argminUpTo f m) then m + 1 else argminUpTo f m := by
      change List.foldl _ 0 (List.range (m + 1 + 1)) = _
      rw [List.range_succ (n := m + 1), List.foldl_append]
      rfl
    obtain ⟨h1, h2⟩ := ih
    rw [hstep]
    split_ifs with hlt
    · refine ⟨le_rfl, fun r hr => ?_⟩
      rcases Nat.lt_or_ge r (m + 1) with hr' | hr'
      · exact (le_of_lt hlt).trans (h2 r (by omega))
      · obtain rfl : r = m + 1 := by omega
        exact le_rfl
    · refine ⟨by omega, fun r hr => ?_⟩
      rcases Nat.lt_or_ge r (m + 1) with hr' | hr'
      · exact h2 r (by omega)
      · obtain rfl : r = m + 1 := by omega
        omega

/-- **The portfolio** (tex ~906): `{z}` on short or invalid inputs, otherwise the candidate of the
trial of least observable cost among `r = 0, …, |z|`. -/
noncomputable def outPortfolio (cs e : ℕ) (oA oB : BitString → BitString) (z : BitString) :
    Finset BitString :=
  if z.length ≤ 1 ∨ z ∉ parseModel (oA z) ∨ z ∉ parseModel (oB z) then {z}
  else (outTrial cs e (argminUpTo (fun r => outCost cs e r oA oB z) z.length) oA oB z).1

/-- **The semantic portfolio selector** `q₀(z)`, with the witness outputs read by the canonical
total interpreter. -/
noncomputable def portfolioModel (cs e : ℕ) (pA pB z : BitString) : Finset BitString :=
  outPortfolio cs e (progOut pA) (progOut pB) z

/-- **The portfolio contains its input** on every binary string. -/
theorem mem_outPortfolio_self (cs e : ℕ) (oA oB : BitString → BitString) (z : BitString) :
    z ∈ outPortfolio cs e oA oB z := by
  unfold outPortfolio
  split_ifs with h
  · exact Finset.mem_singleton_self z
  · simp only [not_or, not_le, not_not] at h
    exact mem_trialRun _ _ (mem_largerModel h.2.1 h.2.2)

/-- The semantic selector contains its input. -/
theorem mem_portfolioModel_self (cs e : ℕ) (pA pB z : BitString) :
    z ∈ portfolioModel cs e pA pB z :=
  mem_outPortfolio_self cs e _ _ z

/-- **Congruence of the portfolio**: output functions that agree on the strings of length `|z|`
give the same portfolio at `z` (`trialRun_congr` for every trial). -/
theorem outPortfolio_congr (cs e : ℕ) (z : BitString) {oA oB oA' oB' : BitString → BitString}
    (h : ∀ y : BitString, y.length = z.length → oA y = oA' y ∧ oB y = oB' y) :
    outPortfolio cs e oA oB z = outPortfolio cs e oA' oB' z := by
  obtain ⟨hA, hB⟩ := h z rfl
  have hag : (outShape oA oB z).AgreeOn (outShape oA' oB' z) := by
    refine ⟨rfl, ?_, ?_, fun y hy => h y hy⟩
    · simp only [outShape, hA]
    · simp only [outShape, hB]
  have htrial : ∀ r, outTrial cs e r oA oB z = outTrial cs e r oA' oB' z := by
    intro r
    unfold outTrial
    rw [trialRun_congr hag _ _ rfl, hA, hB]
  unfold outPortfolio outCost
  simp only [htrial, hA, hB]

/-! ### The literal portfolio program -/

/-- The code of the selected core `coreOf` on the table shape `tableShape TA TB n a b` at the
budget `s` (an optional code). -/
noncomputable def pfF_coreCode (TA TB : List (BitString × BitString)) (n a b s : ℕ)
    (z : BitString) : Option BitString :=
  (coreOf (tableShape TA TB n a b) s z).map canonicalFiniteSetCode

/-- **The code of the selected core is primitive recursive** in the tables, `(n, a, b)`, the
budget and the input: `List.find?` of the membership test over the family codes
(`vertexCores_codes_primrec`), related by `List.find?_map`. -/
theorem pfF_coreCode_primrec :
    Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × ℕ × BitString =>
      pfF_coreCode q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2 := by
  have hz : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString => q.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec fun q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString => (Sum.inl (tableOut q.1.1 q.2.2.2) : BitString ⊕ BitString) :=
    Primrec.sumInl.comp (tableOut_primrec.comp (Primrec.fst.comp Primrec.fst) hz)
  have hpar := Primrec.pair (Primrec.fst (α := List (BitString × BitString) ×
    List (BitString × BitString)) (β := (ℕ × ℕ × ℕ) × ℕ × BitString))
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hv))
  have hcodes := vertexCores_codes_primrec.comp hpar
  have htest : Primrec₂ fun (q : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString) (w : BitString) =>
      decide (q.2.2.2 ∈ canonicalPointListOfCode w) :=
    bitString_mem_primrec.comp (hz.comp Primrec.fst)
      (canonicalPointListOfCode_primrec.comp Primrec.snd)
  have hfind := list_find?_primrec hcodes htest
  refine hfind.of_eq fun q => ?_
  simp only [pfF_coreCode, coreOf, List.find?_map, Function.comp_def,
    canonicalPointListOfCode_canonicalFiniteSetCode, mem_canonicalFinsetList]
  rfl

/-- **One round of the trial loop on codes.**  A state `(done, j, w)` is either finished with the
result `(w, j)` (`done = true`) or running at the index `j` with the current core code `w`.  A
running state stops with the fallback code `w0` on the degree test or a missing look-ahead core,
stops with `w` on a successful size comparison, and otherwise advances to `(j + 1, w')`. -/
noncomputable def pfF_step (TA TB : List (BitString × BitString)) (n a b L : ℕ) (w0 z : BitString)
    (st : Bool × ℕ × BitString) : Bool × ℕ × BitString :=
  bif st.1 then st
  else if min a b ≤ (st.2.1 + 1) * L then (true, st.2.1, w0)
  else (pfF_coreCode TA TB n a b ((st.2.1 + 1) * L) z).elim (true, st.2.1, w0) fun w' =>
    if (canonicalPointListOfCode st.2.2).length ≤
        2 ^ (st.2.1 * L) * (canonicalPointListOfCode w').length then (true, st.2.1, st.2.2)
    else (false, st.2.1 + 1, w')

/-- The result read off a state of the code-level loop: the stored result of a finished state, the
fallback code `w0` with the current index of a running one (the loop ran out of fuel). -/
def pfF_finish (w0 : BitString) (st : Bool × ℕ × BitString) : BitString × ℕ :=
  bif st.1 then (st.2.2, st.2.1) else (w0, st.2.1)

/-- **The code-level round is primitive recursive** (`Primrec.cond`, `Primrec.ite`,
`Primrec.option_casesOn` over `pfF_coreCode_primrec`). -/
theorem pfF_step_primrec :
    Primrec₂ fun (p : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) (st : Bool × ℕ × BitString) =>
      pfF_step p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2 st := by
  have hj : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) => x.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) => x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hab : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) =>
      min x.1.2.1.2.1 x.1.2.1.2.2 :=
    Primrec.nat_min.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst)))) (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp
      (Primrec.snd.comp Primrec.fst))))
  have hL : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) => x.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hw0 : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) => x.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hz : Primrec fun x : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × (Bool × ℕ × BitString) => x.1.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hj1 := Primrec.nat_add.comp hj (Primrec.const 1)
  have hs := Primrec.nat_mul.comp hj1 hL
  have hcc := pfF_coreCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (hs.pair hz)))
  have hlen : Primrec fun w : BitString => (canonicalPointListOfCode w).length :=
    Primrec.list_length.comp canonicalPointListOfCode_primrec
  have hstop := (Primrec.const true).pair (hj.pair hw0)
  have hinner : Primrec₂ fun (x : ((List (BitString × BitString) ×
      List (BitString × BitString)) × (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) ×
      (Bool × ℕ × BitString)) (w' : BitString) =>
      if (canonicalPointListOfCode x.2.2.2).length ≤
          2 ^ (x.2.2.1 * x.1.2.2.1) * (canonicalPointListOfCode w').length then
        (true, x.2.2.1, x.2.2.2)
      else (false, x.2.2.1 + 1, w') :=
    Primrec.ite (Primrec.nat_le.comp (hlen.comp (hw.comp Primrec.fst))
      (Primrec.nat_mul.comp (shapePR_pow_primrec.comp (Primrec.const 2)
        (Primrec.nat_mul.comp (hj.comp Primrec.fst) (hL.comp Primrec.fst)))
        (hlen.comp Primrec.snd)))
      ((Primrec.const true).pair ((hj.comp Primrec.fst).pair (hw.comp Primrec.fst)))
      ((Primrec.const false).pair ((hj1.comp Primrec.fst).pair Primrec.snd))
  have hopt := Primrec.option_casesOn hcc hstop hinner
  have hif := Primrec.ite (Primrec.nat_le.comp hab hs) hstop hopt
  have hall := Primrec.cond (Primrec.fst.comp Primrec.snd) Primrec.snd hif
  refine hall.of_eq fun x => ?_
  rcases x with ⟨⟨⟨TA, TB⟩, ⟨n, a, b⟩, L, w0, z⟩, ⟨d, j, w⟩⟩
  cases d
  · simp only [pfF_step, Bool.cond_false]
    split_ifs
    · rfl
    · cases pfF_coreCode TA TB n a b ((j + 1) * L) z <;> rfl
  · rfl

/-- **The result read-off is primitive recursive** (`Primrec.cond`). -/
theorem pfF_finish_primrec : Primrec₂ pfF_finish := by
  have h := Primrec.cond (Primrec.fst.comp (Primrec.snd (α := BitString)
    (β := Bool × ℕ × BitString)))
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun _ => rfl

/-- A finished state is a fixed point of the code-level iteration. -/
theorem pfF_iterate_done (TA TB : List (BitString × BitString)) (n a b L : ℕ) (w0 z : BitString)
    (k j : ℕ) (w : BitString) :
    (pfF_step TA TB n a b L w0 z)^[k] (true, j, w) = (true, j, w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih

/-- **The code-level iteration computes the trial loop** (induction on the fuel): from the running
state `(j, code F)` with fallback code `code big`, `fuel` rounds followed by `pfF_finish` give the
code of the candidate and the stopping index of `trialLoop`. -/
theorem pfF_loop_eq (TA TB : List (BitString × BitString)) (n a b L : ℕ)
    (big : Finset BitString) (z : BitString) (fuel j : ℕ) (F : Finset BitString) :
    pfF_finish (canonicalFiniteSetCode big)
        ((pfF_step TA TB n a b L (canonicalFiniteSetCode big) z)^[fuel]
          (false, j, canonicalFiniteSetCode F)) =
      (canonicalFiniteSetCode (trialLoop (tableShape TA TB n a b) L big z fuel j F).1,
        (trialLoop (tableShape TA TB n a b) L big z fuel j F).2) := by
  induction fuel generalizing j F with
  | zero => rfl
  | succ fuel ih =>
    have ha : (tableShape TA TB n a b).a = a := rfl
    have hb : (tableShape TA TB n a b).b = b := rfl
    have hlen : ∀ G : Finset BitString,
        (canonicalPointListOfCode (canonicalFiniteSetCode G)).length = G.card := fun G => by
      rw [canonicalPointListOfCode_canonicalFiniteSetCode, length_canonicalFinsetList]
    rw [Function.iterate_succ_apply]
    simp only [trialLoop, ha, hb]
    by_cases h1 : min a b ≤ (j + 1) * L
    · have hs : pfF_step TA TB n a b L (canonicalFiniteSetCode big) z
          (false, j, canonicalFiniteSetCode F) = (true, j, canonicalFiniteSetCode big) := by
        simp only [pfF_step, Bool.cond_false, h1, ↓reduceIte]
      rw [hs, pfF_iterate_done]
      simp only [h1, ↓reduceIte, pfF_finish, Bool.cond_true]
    · simp only [h1, ↓reduceIte]
      cases hc : coreOf (tableShape TA TB n a b) ((j + 1) * L) z with
      | none =>
        have hs : pfF_step TA TB n a b L (canonicalFiniteSetCode big) z
            (false, j, canonicalFiniteSetCode F) = (true, j, canonicalFiniteSetCode big) := by
          simp only [pfF_step, Bool.cond_false, h1, ↓reduceIte, pfF_coreCode, hc, Option.map_none,
            Option.elim_none]
        rw [hs, pfF_iterate_done]
        rfl
      | some F' =>
        by_cases h2 : F.card ≤ 2 ^ (j * L) * F'.card
        · have hs : pfF_step TA TB n a b L (canonicalFiniteSetCode big) z
              (false, j, canonicalFiniteSetCode F) = (true, j, canonicalFiniteSetCode F) := by
            simp only [pfF_step, Bool.cond_false, h1, ↓reduceIte, pfF_coreCode, hc, Option.map_some,
              Option.elim_some, hlen, h2]
          rw [hs, pfF_iterate_done]
          simp only [h2, ↓reduceIte]
          rfl
        · have hs : pfF_step TA TB n a b L (canonicalFiniteSetCode big) z
              (false, j, canonicalFiniteSetCode F) = (false, j + 1, canonicalFiniteSetCode F') := by
            simp only [pfF_step, Bool.cond_false, h1, ↓reduceIte, pfF_coreCode, hc, Option.map_some,
              Option.elim_some, hlen, h2]
          rw [hs, ih]
          simp only [h2, ↓reduceIte]

/-- The code-level trial: the immediate degree stop, the option case on the initial core, and the
code-level loop from the running state `(1, code F_L)` with fuel `min a b + 1`. -/
noncomputable def pfF_runCode (TA TB : List (BitString × BitString)) (n a b L : ℕ)
    (w0 z : BitString) : BitString × ℕ :=
  if min a b ≤ L then (w0, 0)
  else (pfF_coreCode TA TB n a b L z).elim (w0, 1) fun w =>
    pfF_finish w0 ((pfF_step TA TB n a b L w0 z)^[min a b + 1] (false, 1, w))

/-- **The code-level trial is primitive recursive** (`Primrec.nat_iterate` on `pfF_step_primrec`,
`Primrec.option_casesOn`, `Primrec.ite`). -/
theorem pfF_runCode_primrec :
    Primrec fun p : (List (BitString × BitString) × List (BitString × BitString)) ×
        (ℕ × ℕ × ℕ) × ℕ × BitString × BitString =>
      pfF_runCode p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hmin : Primrec fun p : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString => min p.2.1.2.1 p.2.1.2.2 :=
    Primrec.nat_min.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hL : Primrec fun p : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw0 : Primrec fun p : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hz : Primrec fun p : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hcc := pfF_coreCode_primrec.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (hL.pair hz)))
  have hh : Primrec₂ fun (y : ((List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) × BitString) (st : Bool × ℕ × BitString) =>
      pfF_step y.1.1.1 y.1.1.2 y.1.2.1.1 y.1.2.1.2.1 y.1.2.1.2.2 y.1.2.2.1 y.1.2.2.2.1
        y.1.2.2.2.2 st :=
    pfF_step_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hit := Primrec.nat_iterate (Primrec.nat_add.comp (hmin.comp Primrec.fst) (Primrec.const 1))
    ((Primrec.const false).pair ((Primrec.const 1).pair Primrec.snd)) hh
  have hfin : Primrec₂ fun (p : (List (BitString × BitString) × List (BitString × BitString)) ×
      (ℕ × ℕ × ℕ) × ℕ × BitString × BitString) (w : BitString) =>
      pfF_finish p.2.2.2.1 ((pfF_step p.1.1 p.1.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2 p.2.2.1 p.2.2.2.1
        p.2.2.2.2)^[min p.2.1.2.1 p.2.1.2.2 + 1] (false, 1, w)) :=
    pfF_finish_primrec.comp (hw0.comp Primrec.fst) hit
  have hopt := Primrec.option_casesOn hcc (hw0.pair (Primrec.const 1)) hfin
  have hall := Primrec.ite (Primrec.nat_le.comp hmin hL) (hw0.pair (Primrec.const 0)) hopt
  refine hall.of_eq fun p => ?_
  rcases p with ⟨⟨TA, TB⟩, ⟨n, a, b⟩, L, w0, z⟩
  simp only [pfF_runCode]
  split_ifs
  · rfl
  · cases pfF_coreCode TA TB n a b L z <;> rfl

/-- **The trial on the table shape is the code-level trial** (`pfF_loop_eq` for the loop, an
option case on the initial core). -/
theorem pfF_trialRun_code (TA TB : List (BitString × BitString)) (n a b L : ℕ)
    (big : Finset BitString) (z : BitString) :
    (canonicalFiniteSetCode (trialRun (tableShape TA TB n a b) L big z).1,
      (trialRun (tableShape TA TB n a b) L big z).2) =
      pfF_runCode TA TB n a b L (canonicalFiniteSetCode big) z := by
  have ha : (tableShape TA TB n a b).a = a := rfl
  have hb : (tableShape TA TB n a b).b = b := rfl
  unfold trialRun pfF_runCode
  rw [ha, hb]
  by_cases h : min a b ≤ L
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    cases hc : coreOf (tableShape TA TB n a b) L z with
    | none => simp only [pfF_coreCode, hc, Option.map_none, Option.elim_none]
    | some F =>
      simp only [pfF_coreCode, hc, Option.map_some, Option.elim_some]
      exact (pfF_loop_eq TA TB n a b L big z (min a b + 1) 1 F).symm

/-- The code of the larger-bucket fallback, by cases on the bucket comparison. -/
theorem pfF_code_largerModel (A B : Finset BitString) :
    canonicalFiniteSetCode (largerModel A B) =
      if Nat.log 2 A.card ≤ Nat.log 2 B.card then canonicalFiniteSetCode B
      else canonicalFiniteSetCode A := by
  unfold largerModel
  split_ifs <;> rfl

/-- **The table trial is the code-level trial** at the table shape `tableShape TA TB |z| a b`
(definitionally `outShape (tableOut TA) (tableOut TB) z`), with the larger-bucket fallback. -/
theorem pfF_outTrial_eq (cs e r : ℕ) (TA TB : List (BitString × BitString)) (z : BitString) :
    (canonicalFiniteSetCode (outTrial cs e r (tableOut TA) (tableOut TB) z).1,
      (outTrial cs e r (tableOut TA) (tableOut TB) z).2) =
      pfF_runCode TA TB z.length (Nat.log 2 (parseModel (tableOut TA z)).card)
        (Nat.log 2 (parseModel (tableOut TB z)).card) (trialStep cs z.length e r)
        (canonicalFiniteSetCode (largerModel (parseModel (tableOut TA z))
          (parseModel (tableOut TB z)))) z := by
  unfold outTrial
  exact pfF_trialRun_code TA TB z.length (Nat.log 2 (parseModel (tableOut TA z)).card)
    (Nat.log 2 (parseModel (tableOut TB z)).card) (trialStep cs z.length e r)
    (largerModel (parseModel (tableOut TA z)) (parseModel (tableOut TB z))) z

/-- **One trial read from tables is primitive recursive** in `(c_*, e, r)`, the two tables and
`z`: the code of the candidate and the stopping index.  The trial on the table shape is the
code-level trial `pfF_runCode` (`pfF_outTrial_eq`): the selected-core codes come from M_CORES'
`vertexCores_codes_primrec` (`pfF_coreCode_primrec`), and the loop is the code-level round
`pfF_step` on states `(done, j, current code)`, iterated `min a b + 1` times
(`Primrec.nat_iterate`) and read off by `pfF_finish`; it agrees with `trialLoop` by induction on
the fuel (`pfF_loop_eq`). -/
theorem outTrial_table_primrec :
    Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
        List (BitString × BitString))) × BitString =>
      (canonicalFiniteSetCode (outTrial q.1.1.1 q.1.1.2.1 q.1.1.2.2 (tableOut q.1.2.1)
        (tableOut q.1.2.2) q.2).1, (outTrial q.1.1.1 q.1.1.2.1 q.1.1.2.2 (tableOut q.1.2.1)
        (tableOut q.1.2.2) q.2).2) := by
  have hz : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.2 := Primrec.snd
  have hcs : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hr : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hT : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hoA := tableOut_primrec.comp (Primrec.fst.comp hT) hz
  have hoB := tableOut_primrec.comp (Primrec.snd.comp hT) hz
  have haA := parseModel_logCard_primrec.comp hoA
  have hbB := parseModel_logCard_primrec.comp hoB
  have hn := Primrec.list_length.comp hz
  have hL : Primrec fun q : ((ℕ × ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString =>
      trialStep q.1.1.1 q.2.length q.1.1.2.1 q.1.1.2.2 :=
    (Primrec.nat_mul.comp hcs (Primrec.nat_add.comp (baseBudget_primrec.comp hn he) hr)).of_eq
      fun _ => rfl
  have hcode : Primrec fun w : BitString => canonicalFiniteSetCode (parseModel w) :=
    (canonicalFiniteSetCode_toFinset_primrec.comp canonicalPointListOfCode_primrec).of_eq
      fun _ => rfl
  have hbig := Primrec.ite (Primrec.nat_le.comp haA hbB) (hcode.comp hoB) (hcode.comp hoA)
  have htup := hT.pair ((hn.pair (haA.pair hbB)).pair (hL.pair (hbig.pair hz)))
  have h := pfF_runCode_primrec.comp htup
  refine h.of_eq fun q => ?_
  rw [pfF_outTrial_eq, pfF_code_largerModel]

/-- **The portfolio read from tables is primitive recursive**, given the trial
(`outTrial_table_primrec`): the cost `(j + 1) c_* (H + r)` (`baseBudget_primrec`), the minimizer
`argminUpTo` as a `List.foldl` over `List.range (|z| + 1)` (`Primrec.list_foldl`), the guard
(`parseModel_mem_primrec`) and the default (`singleton_code_primrec`). -/
theorem outPortfolio_table_primrec :
    Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) × List (BitString × BitString))) ×
        BitString =>
      canonicalFiniteSetCode (outPortfolio q.1.1.1 q.1.1.2 (tableOut q.1.2.1) (tableOut q.1.2.2)
        q.2) := by
  have hz : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.2 := Primrec.snd
  have hcs : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hTA : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hTB : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have htupj : Primrec fun p : (((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString) × ℕ =>
      (((p.1.1.1.1, p.1.1.1.2, p.2), (p.1.1.2.1, p.1.1.2.2)), p.1.2) :=
    (((hcs.comp Primrec.fst).pair ((he.comp Primrec.fst).pair Primrec.snd)).pair
      ((hTA.comp Primrec.fst).pair (hTB.comp Primrec.fst))).pair (hz.comp Primrec.fst)
  have hj := Primrec.snd.comp (outTrial_table_primrec.comp htupj)
  have hcost := Primrec.nat_mul.comp (Primrec.succ.comp hj) (Primrec.nat_mul.comp
    (hcs.comp Primrec.fst) (Primrec.nat_add.comp (baseBudget_primrec.comp
      (Primrec.list_length.comp (hz.comp Primrec.fst)) (he.comp Primrec.fst)) Primrec.snd))
  have hcost' : Primrec₂ fun (q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString) (r : ℕ) =>
      outCost q.1.1.1 q.1.1.2 r (tableOut q.1.2.1) (tableOut q.1.2.2) q.2 := by
    refine hcost.of_eq fun p => ?_
    simp only [outCost, trialStep, Nat.succ_eq_add_one]
  have hh : Primrec₂ fun (q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString) (p : ℕ × ℕ) =>
      if outCost q.1.1.1 q.1.1.2 p.2 (tableOut q.1.2.1) (tableOut q.1.2.2) q.2 <
        outCost q.1.1.1 q.1.1.2 p.1 (tableOut q.1.2.1) (tableOut q.1.2.2) q.2 then p.2 else p.1 :=
    Primrec.ite (Primrec.nat_lt.comp (hcost'.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (hcost'.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have hfold := Primrec.list_foldl
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp hz)))
    (Primrec.const 0) hh
  have harg : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString =>
      argminUpTo (fun r => outCost q.1.1.1 q.1.1.2 r (tableOut q.1.2.1) (tableOut q.1.2.2) q.2)
        q.2.length := by
    refine hfold.of_eq fun q => ?_
    simp only [argminUpTo, Nat.succ_eq_add_one]
  have htup : Primrec fun q : ((ℕ × ℕ) × (List (BitString × BitString) ×
      List (BitString × BitString))) × BitString =>
      (((q.1.1.1, q.1.1.2, argminUpTo (fun r => outCost q.1.1.1 q.1.1.2 r (tableOut q.1.2.1)
        (tableOut q.1.2.2) q.2) q.2.length), (q.1.2.1, q.1.2.2)), q.2) :=
    ((hcs.pair (he.pair harg)).pair (hTA.pair hTB)).pair hz
  have hD := Primrec.fst.comp (outTrial_table_primrec.comp htup)
  have hoA := tableOut_primrec.comp hTA hz
  have hoB := tableOut_primrec.comp hTB hz
  have hmemA := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoA)
  have hmemB := Primrec.primrecPred (parseModel_mem_primrec.comp hz hoB)
  have hguard := (Primrec.nat_le.comp (Primrec.list_length.comp hz) (Primrec.const 1)).or
    (hmemA.not.or hmemB.not)
  refine (Primrec.ite hguard (singleton_code_primrec.comp hz) hD).of_eq fun q => ?_
  simp only [outPortfolio]
  split_ifs <;> simp_all

/-- The output of the portfolio program from the decoded point packet `(e, p_A, p_B)` on the input
`z`: complete runs of both witnesses at length `|z|`, then the table portfolio. -/
noncomputable def portOut (cs e : ℕ) (pA pB z : BitString) : Part BitString :=
  (runTable pA z.length).bind fun TA => (runTable pB z.length).map fun TB =>
    canonicalFiniteSetCode (outPortfolio cs e (tableOut TA) (tableOut TB) z)

/-- **The literal portfolio program** `q₀` for the step constant `c_*`: it reads the point packet
`pointPacket e pA pB` and the input `z`. -/
noncomputable def portfolioDecoder (cs : ℕ) : Map := fun q =>
  portOut cs (numFieldDecode q.1).1 (decodeTotalProgramPairFirst (numFieldDecode q.1).2)
    (decodeTotalProgramPairSecond (numFieldDecode q.1).2) q.2

/-- **The portfolio program is partial recursive**: packet parsing, the two complete runs
(`runTable_partrec`) and the primitive recursive table portfolio. -/
theorem portfolioDecoder_partrec (cs : ℕ) : isDecompressor (portfolioDecoder cs) := by
  have he : Computable fun q : BitString × BitString => (numFieldDecode q.1).1 :=
    Computable.fst.comp (numFieldDecode_computable.comp Computable.fst)
  have hbody : Computable fun q : BitString × BitString => (numFieldDecode q.1).2 :=
    Computable.snd.comp (numFieldDecode_computable.comp Computable.fst)
  have hpA := decodeTotalProgramPairFirst_computable.comp hbody
  have hpB := decodeTotalProgramPairSecond_computable.comp hbody
  have hlen : Computable fun q : BitString × BitString => q.2.length :=
    (Primrec.list_length.comp Primrec.snd).to_comp
  have hfst : Computable fun r : (BitString × BitString) × List (BitString × BitString) => r.1 :=
    Computable.fst
  have hfinal : Computable₂ fun (r : (BitString × BitString) × List (BitString × BitString))
      (TB : List (BitString × BitString)) =>
      canonicalFiniteSetCode (outPortfolio cs (numFieldDecode r.1.1).1 (tableOut r.2)
        (tableOut TB) r.1.2) :=
    (outPortfolio_table_primrec.to_comp.comp
      ((((Computable.const cs).pair (he.comp (Computable.fst.comp Computable.fst))).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)).pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst)))).of_eq fun _ => rfl
  have hinner : Partrec₂ fun (r : BitString × BitString) (TA : List (BitString × BitString)) =>
      (runTable (decodeTotalProgramPairSecond (numFieldDecode r.1).2) r.2.length).map fun TB =>
        canonicalFiniteSetCode (outPortfolio cs (numFieldDecode r.1).1 (tableOut TA)
          (tableOut TB) r.2) :=
    Partrec.map (runTable_partrec.comp (hpB.comp hfst) (hlen.comp hfst)) hfinal
  exact (Partrec.bind (runTable_partrec.comp hpA hlen) hinner).of_eq fun q => rfl

/-- **The portfolio program on its packet**: for total witnesses it halts on every input `z` with
the code of the semantic selector `portfolioModel`.  Totality uses only witness totality
(`runTable_dom`) and finite searches. -/
theorem portfolioDecoder_spec (cs e : ℕ) (pA pB z : BitString)
    (hpA : IsTotalProgram universalDecompressor pA)
    (hpB : IsTotalProgram universalDecompressor pB) :
    portfolioDecoder cs (pointPacket e pA pB, z) =
      Part.some (canonicalFiniteSetCode (portfolioModel cs e pA pB z)) := by
  obtain ⟨TA, hTA⟩ := Part.dom_iff_mem.mp (runTable_dom hpA z.length)
  obtain ⟨TB, hTB⟩ := Part.dom_iff_mem.mp (runTable_dom hpB z.length)
  have hsel : outPortfolio cs e (tableOut TA) (tableOut TB) z = portfolioModel cs e pA pB z :=
    outPortfolio_congr cs e z fun y hy =>
      ⟨tableOut_of_mem_runTable hTA hy, tableOut_of_mem_runTable hTB hy⟩
  unfold portfolioDecoder portOut
  simp only [pointPacket, numFieldDecode_numField, decodeTotalProgramPairFirst_pair,
    decodeTotalProgramPairSecond_pair]
  rw [Part.eq_some_iff, Part.mem_bind_iff]
  refine ⟨TA, hTA, ?_⟩
  rw [Part.mem_map_iff]
  exact ⟨TB, hTB, congrArg canonicalFiniteSetCode hsel⟩

/-! ### T04: the universal portfolio -/

/-- **T04: the universal portfolio (blueprint `UpperPortfolio`).**  For the step constant `c_*`
there is a constant `c₀` such that for every `e` and all total witnesses `p_A, p_B` of length at
most `e` one globally total program `q₀` of length at most `7 (e + 1) + c₀` outputs, on every
input `z`, the code of the portfolio selection `portfolioModel c_* e p_A p_B z`.  The program
carries only `p_A, p_B, e`; it computes no profile, mutual information or complexity value, and
no instance-specific `r`, budget or rank. -/
theorem upperPortfolio (cs : ℕ) :
    ∃ c₀ : ℕ, ∀ (e : ℕ) (pA pB : BitString), IsBoundedTotalWitness e pA →
      IsBoundedTotalWitness e pB →
        ∃ q0 : BitString, IsTotalProgram universalDecompressor q0 ∧
          q0.length ≤ 7 * (e + 1) + c₀ ∧
          ∀ z : BitString, produces universalDecompressor q0 z
            (canonicalFiniteSetCode (portfolioModel cs e pA pB z)) := by
  obtain ⟨pre, hpre⟩ :=
    Lower.exists_compiled_totalProgram (portfolioDecoder cs) (portfolioDecoder_partrec cs)
  refine ⟨pre.length, fun e pA pB hA hB => ?_⟩
  have hspec := fun z => portfolioDecoder_spec cs e pA pB z hA.1 hB.1
  have hdom : ∀ y : BitString, (portfolioDecoder cs (pointPacket e pA pB, y)).Dom := fun y => by
    rw [hspec y]
    trivial
  obtain ⟨htot, hlen, hprod⟩ := hpre _ hdom
  refine ⟨pre ++ pointPacket e pA pB, htot, ?_, fun z => hprod z _ ?_⟩
  · rw [hlen]
    have := length_pointPacket_le e pA pB hA.2 hB.2
    omega
  · rw [hspec z]
    exact Part.mem_some _

/-- The program `q₀` read as a model selector is the portfolio. -/
theorem progModel_eq_of_produces {q0 : BitString} {Q : BitString → Finset BitString}
    (h : ∀ z : BitString, produces universalDecompressor q0 z (canonicalFiniteSetCode (Q z)))
    (z : BitString) : progModel q0 z = Q z := by
  unfold progModel
  rw [progOut_eq_of_mem (h z), parseModel_canonicalFiniteSetCode]

/-! ### The portfolio at a qualifying instance -/

/-- At a qualifying instance the trial read through `progOut` is the instance trial. -/
theorem outTrial_eq_instTrial {V : Map} {n e : ℕ} {pA pB x : BitString} {A B : Finset BitString}
    (h : IsCoreInstance V n e pA pB x A B) (cs r : ℕ) :
    outTrial cs e r (progOut pA) (progOut pB) x = instTrial cs n e r pA pB x A B := by
  have hoA : progOut pA x = canonicalFiniteSetCode A := progOut_eq_of_mem h.prodA
  have hoB : progOut pB x = canonicalFiniteSetCode B := progOut_eq_of_mem h.prodB
  unfold outTrial instTrial outShape coreShape instShape
  rw [hoA, hoB, parseModel_canonicalFiniteSetCode, parseModel_canonicalFiniteSetCode,
    h.length_x]

/-- **The portfolio at a qualifying instance** (tex ~912): for `n ≥ 2` the selector returns the
candidate of a trial `r* ≤ n` whose observable cost is least among all trials `r ≤ n`. -/
theorem portfolioModel_spec {V : Map} {n e : ℕ} {pA pB x : BitString} {A B : Finset BitString}
    (h : IsCoreInstance V n e pA pB x A B) (hn : 2 ≤ n) (cs : ℕ) :
    ∃ r₀ ≤ n, portfolioModel cs e pA pB x = (instTrial cs n e r₀ pA pB x A B).1 ∧
      ∀ r ≤ n, ((instTrial cs n e r₀ pA pB x A B).2 + 1) * trialStep cs n e r₀ ≤
        ((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r := by
  have hoA : progOut pA x = canonicalFiniteSetCode A := progOut_eq_of_mem h.prodA
  have hoB : progOut pB x = canonicalFiniteSetCode B := progOut_eq_of_mem h.prodB
  have hcost : ∀ r, outCost cs e r (progOut pA) (progOut pB) x =
      ((instTrial cs n e r pA pB x A B).2 + 1) * trialStep cs n e r := by
    intro r
    unfold outCost
    rw [outTrial_eq_instTrial h, h.length_x]
  obtain ⟨hle, hmin⟩ := argminUpTo_spec (fun r => outCost cs e r (progOut pA) (progOut pB) x)
    x.length
  rw [h.length_x] at hle hmin
  refine ⟨_, hle, ?_, fun r hr => ?_⟩
  · unfold portfolioModel outPortfolio
    have hne : ¬ (x.length ≤ 1 ∨ x ∉ parseModel (progOut pA x) ∨
        x ∉ parseModel (progOut pB x)) := by
      rw [hoA, hoB, parseModel_canonicalFiniteSetCode, parseModel_canonicalFiniteSetCode,
        h.length_x]
      simp only [not_or, not_le, not_not]
      exact ⟨by omega, h.sufA.1, h.sufB.1⟩
    rw [ite_eq_right hne, outTrial_eq_instTrial h, h.length_x]
  · have := hmin r hr
    rw [hcost, hcost] at this
    exact this

end Kolmogorov.StrongMerging.Upper
