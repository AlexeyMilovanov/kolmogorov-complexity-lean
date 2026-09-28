import KolmogorovMathlib.MonotoneComplexity.TreeSemimeasureSanitizer

/-!
# Uniform (index-parameterized) computability of the tree sanitizer

`TreeSemimeasureSanitizer` proves that `treeSanitize approx` is computable for a
*fixed* computable approximation `approx`.  For the mixture construction one
needs the same statement *uniformly* in an index: for a jointly computable
family `b : ℕ → ℕ → BitString → BitString → ℕ`, the map
`(i, s, x) ↦ treeSanitize (b i) s x` is computable.

The proofs mirror the fixed-index versions from `SimpleTreeApproximation`; the
index is carried inside the packed natural-number parameter code (an extra
`Nat.pair` component), which keeps all the intermediate `Computable` goals at
the same product depth as in the fixed-index proofs.
-/

namespace Kolmogorov

open scoped ENNReal
open Encodable

attribute [local irreducible] simpleApproxBits levelStep closureLevel simpleApprox
attribute [local irreducible] paramS paramK paramX paramRecode paramCode

/-! ### Index-carrying parameter codes -/

/-- The index component of an index-carrying parameter code. -/
def uparamI (u : ℕ) : ℕ := (Nat.unpair u).1
/-- The `paramCode` component of an index-carrying parameter code. -/
def uparamC (u : ℕ) : ℕ := (Nat.unpair u).2
/-- Pack an index together with a `paramCode`. -/
def uparamCode (i c : ℕ) : ℕ := Nat.pair i c
/-- Replace the depth component of the inner parameter code. -/
def uparamRecode (u k : ℕ) : ℕ := Nat.pair (uparamI u) (paramRecode (uparamC u) k)

/-- The machine index is recovered from the uniform parameter code. -/
@[simp] lemma uparamI_code (i c : ℕ) : uparamI (uparamCode i c) = i := by
  simp [uparamI, uparamCode]
/-- The inner parameter is recovered from the uniform parameter code. -/
@[simp] lemma uparamC_code (i c : ℕ) : uparamC (uparamCode i c) = c := by
  simp [uparamC, uparamCode]
/-- Recoding a uniform parameter leaves the machine index unchanged. -/
@[simp] lemma uparamI_recode (u k : ℕ) : uparamI (uparamRecode u k) = uparamI u := by
  simp [uparamI, uparamRecode]
/-- Recoding a uniform parameter recodes its inner parameter. -/
@[simp] lemma uparamC_recode (u k : ℕ) :
    uparamC (uparamRecode u k) = paramRecode (uparamC u) k := by
  simp [uparamC, uparamRecode]

/-- Extracting the machine index from a uniform parameter is computable. -/
lemma computable_uparamI : Computable uparamI :=
  (Primrec.fst.comp Primrec.unpair).to_comp
/-- Extracting the inner parameter from a uniform parameter is computable. -/
lemma computable_uparamC : Computable uparamC :=
  (Primrec.snd.comp Primrec.unpair).to_comp
/-- Packing a machine index and an inner parameter into a uniform parameter is computable. -/
lemma computable_uparamCode : Computable (fun p : ℕ × ℕ => uparamCode p.1 p.2) :=
  Primrec₂.natPair.to_comp
/-- Recoding a uniform parameter is computable. -/
lemma computable_uparamRecode : Computable (fun p : ℕ × ℕ => uparamRecode p.1 p.2) :=
  Primrec₂.natPair.to_comp.comp (computable_uparamI.comp Computable.fst)
    (computable_paramRecode.comp
      (Computable.pair (computable_uparamC.comp Computable.fst) Computable.snd))

attribute [local irreducible] uparamI uparamC uparamCode uparamRecode

variable (b : ℕ → ℕ → BitString → BitString → ℕ)

/-- Uniform version of `computable_levelStepC`. -/
lemma computable_levelStep_uniform
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun q : ℕ × List ℕ =>
      levelStep (b (uparamI q.1)) (paramS (uparamC q.1)) (paramX (uparamC q.1))
        (paramK (uparamC q.1)) q.2) := by
  have hu : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hprev : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hj : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2) := Computable.snd
  have hmain : Computable (fun q : ℕ × List ℕ =>
      (List.range (2 ^ paramK (uparamC q.1))).map (fun j =>
        max (b (uparamI q.1) (paramS (uparamC q.1))
            (paramX (uparamC q.1) ++ simpleApproxBits (paramK (uparamC q.1)) j) [])
          (q.2.getD (2 * j) 0 + q.2.getD (2 * j + 1) 0))) := by
    refine computable_range_map _ _ ?_ ?_
    · exact primrec_two_pow_aux.to_comp.comp
        (computable_paramK.comp (computable_uparamC.comp Computable.fst))
    · have hc : Computable (fun p : (ℕ × List ℕ) × ℕ => uparamC p.1.1) :=
        computable_uparamC.comp hu
      have hbits : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          simpleApproxBits (paramK (uparamC p.1.1)) p.2) :=
        computable_simpleApproxBits.comp (Computable.pair (computable_paramK.comp hc) hj)
      have happrox : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          b (uparamI p.1.1) (paramS (uparamC p.1.1))
            (paramX (uparamC p.1.1) ++ simpleApproxBits (paramK (uparamC p.1.1)) p.2) []) :=
        hb.comp (Computable.pair (computable_uparamI.comp hu)
          (Computable.pair (computable_paramS.comp hc)
            (Computable.pair
              (Computable.list_append.comp (computable_paramX.comp hc) hbits)
              (Computable.const []))))
      have h2j : Computable (fun p : (ℕ × List ℕ) × ℕ => 2 * p.2) :=
        Primrec.nat_mul.to_comp.comp (Computable.const 2) hj
      have hgetD : Computable₂ (fun (l : List ℕ) (n : ℕ) => l.getD n 0) :=
        (Primrec.list_getD (0 : ℕ)).to_comp
      have hsum : Computable (fun p : (ℕ × List ℕ) × ℕ =>
          p.1.2.getD (2 * p.2) 0 + p.1.2.getD (2 * p.2 + 1) 0) :=
        Primrec.nat_add.to_comp.comp (hgetD.comp hprev h2j)
          (hgetD.comp hprev (Computable.succ.comp h2j))
      exact Primrec.nat_max.to_comp.comp happrox hsum
  exact hmain.of_eq (fun q => by rw [levelStep])

/-- Uniform version of `computable_closureLevelC`. -/
lemma computable_closureLevel_uniform
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun a : ℕ × ℕ =>
      closureLevel (b (uparamI a.1)) (paramS (uparamC a.1)) (paramX (uparamC a.1))
        (paramK (uparamC a.1)) a.2) := by
  have hstepC := computable_levelStep_uniform b hb
  have hbase : Computable (fun a : ℕ × ℕ =>
      levelStep (b (uparamI a.1)) (paramS (uparamC a.1)) (paramX (uparamC a.1))
        (paramK (uparamC a.1)) []) :=
    hstepC.comp (Computable.pair Computable.fst (Computable.const []))
  have hstep : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
      levelStep (b (uparamI q.1.1)) (paramS (uparamC q.1.1)) (paramX (uparamC q.1.1))
        (paramK (uparamC q.1.1) - (q.2.1 + 1)) q.2.2) := by
    have hu : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) => q.1.1) :=
      Computable.fst.comp Computable.fst
    have hcode : Computable (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
        uparamRecode q.1.1 (paramK (uparamC q.1.1) - (q.2.1 + 1))) :=
      computable_uparamRecode.comp (Computable.pair hu
        (Primrec.nat_sub.to_comp.comp
          (computable_paramK.comp (computable_uparamC.comp hu))
          (Computable.succ.comp (Computable.fst.comp Computable.snd))))
    exact (hstepC.comp (Computable.pair hcode (Computable.snd.comp Computable.snd))).of_eq
      (fun q => by simp)
  exact (Computable.nat_rec Computable.snd hbase hstep.to₂).of_eq
    (fun a => (closureLevel_rec (b (uparamI a.1)) (paramS (uparamC a.1)) (paramX (uparamC a.1))
      (paramK (uparamC a.1)) a.2).symm)

/-- Uniform version of `computable_simpleApprox`. -/
lemma computable_simpleApprox_uniform
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString => simpleApprox (b p.1) p.2.1 p.2.2) := by
  have hi : Computable (fun p : ℕ × ℕ × BitString => p.1) := Computable.fst
  have hs : Computable (fun p : ℕ × ℕ × BitString => p.2.1) := Computable.fst.comp Computable.snd
  have hx : Computable (fun p : ℕ × ℕ × BitString => p.2.2) := Computable.snd.comp Computable.snd
  have hlen : Computable (fun p : ℕ × ℕ × BitString => p.2.2.length) :=
    Computable.list_length.comp hx
  have hd : Computable (fun p : ℕ × ℕ × BitString => p.2.1 - p.2.2.length) :=
    Primrec.nat_sub.to_comp.comp hs hlen
  have hcode : Computable (fun p : ℕ × ℕ × BitString =>
      uparamCode p.1 (paramCode p.2.1 (p.2.1 - p.2.2.length) p.2.2)) :=
    computable_uparamCode.comp (Computable.pair hi
      (computable_paramCode.comp (Computable.pair (Computable.pair hs hd) hx)))
  have hlevel : Computable (fun p : ℕ × ℕ × BitString =>
      closureLevel (b p.1) p.2.1 p.2.2 (p.2.1 - p.2.2.length) (p.2.1 - p.2.2.length)) :=
    ((computable_closureLevel_uniform b hb).comp
      (Computable.pair hcode hd)).of_eq (fun p => by simp)
  have hval : Computable (fun p : ℕ × ℕ × BitString =>
      (closureLevel (b p.1) p.2.1 p.2.2 (p.2.1 - p.2.2.length)
        (p.2.1 - p.2.2.length)).getD 0 0) :=
    (Primrec.list_getD (0 : ℕ)).to_comp.comp hlevel (Computable.const 0)
  have hc1 : Computable (fun p : ℕ × ℕ × BitString => decide (p.2.1 < p.2.2.length)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hs hlen
  have hc2 : Computable (fun p : ℕ × ℕ × BitString => decide (p.2.2.length = 0)) :=
    (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp hlen (Computable.const 0)
  have hpow : Computable (fun p : ℕ × ℕ × BitString => 2 ^ p.2.1) :=
    primrec_two_pow_aux.to_comp.comp hs
  exact (Computable.cond hc1 (Computable.const 0)
    (Computable.cond hc2 hpow hval)).of_eq
    (fun p => (simpleApprox_eq_cond (b p.1) p.2.1 p.2.2).symm)

/-- Boolean form of the root-budget test, in the shape used by the recursion
computing `freezeStage`. -/
def budgetB (b : ℕ → ℕ → BitString → BitString → ℕ) (i s : ℕ) : Bool :=
  decide (simpleApprox (b i) s [false] + simpleApprox (b i) s [true] ≤ 2 ^ s)

/-- The Boolean budget test for machine `i` at stage `s` is true exactly when the root mass of that
machine still respects its budget. -/
lemma budgetB_iff (i s : ℕ) : budgetB b i s = true ↔ rootBudgetOK (b i) s := by
  simp [budgetB, rootBudgetOK]

/-- Uniform version of `computable_rootBudgetOK`. -/
lemma computable_budgetB
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ => budgetB b p.1 p.2) := by
  have hsa := computable_simpleApprox_uniform b hb
  have hF : Computable (fun p : ℕ × ℕ => simpleApprox (b p.1) p.2 [false]) :=
    hsa.comp (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const [false])))
  have hT : Computable (fun p : ℕ × ℕ => simpleApprox (b p.1) p.2 [true]) :=
    hsa.comp (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const [true])))
  have hadd : Computable (fun p : ℕ × ℕ =>
      simpleApprox (b p.1) p.2 [false] + simpleApprox (b p.1) p.2 [true]) :=
    Primrec.nat_add.to_comp.comp hF hT
  have hpow : Computable (fun p : ℕ × ℕ => 2 ^ p.2) :=
    primrec_two_pow_aux.to_comp.comp Computable.snd
  exact (PrimrecRel.decide Primrec.nat_le).to_comp.comp hadd hpow

/-- `freezeStage` written with the boolean test `budgetB`. -/
def freezeStageB (b : ℕ → ℕ → BitString → BitString → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => cond (decide (freezeStageB b i s = s))
      (cond (budgetB b i (s + 1)) (s + 1) (freezeStageB b i s)) (freezeStageB b i s)

/-- The uniform freeze stage of machine `i` agrees with the freeze stage of that machine taken
individually. -/
lemma freezeStageB_eq (i s : ℕ) : freezeStageB b i s = freezeStage (b i) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [freezeStageB, ih]
    by_cases h1 : freezeStage (b i) s = s
    · by_cases h2 : rootBudgetOK (b i) s.succ
      · have hB : budgetB b i (s + 1) = true := (budgetB_iff b i (s + 1)).mpr h2
        simp [freezeStage, h1, h2, hB]
      · have hB : budgetB b i (s + 1) = false := by
          simpa using fun h => h2 ((budgetB_iff b i (s + 1)).mp h)
        simp [freezeStage, h1, h2, hB]
    · simp [freezeStage, h1]

/-- The freeze stage is computed by the primitive recursion that advances one stage while the budget
holds, the form used to establish its computability. -/
lemma freezeStageB_rec (i s : ℕ) :
    freezeStageB b i s =
      Nat.rec (motive := fun _ => ℕ) 0
        (fun n IH => cond (decide (IH = n)) (cond (budgetB b i (n + 1)) (n + 1) IH) IH) s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [freezeStageB, ih]

/-- Uniform version of `computable_freezeStage`. -/
lemma computable_freezeStage_uniform
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ => freezeStage (b p.1) p.2) := by
  have hbud := computable_budgetB b hb
  have h_i : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.1) :=
    Computable.fst.comp Computable.fst
  have h_n : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.1) :=
    Computable.fst.comp Computable.snd
  have h_IH : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.2) :=
    Computable.snd.comp Computable.snd
  have h_np1 : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.1 + 1) := Computable.succ.comp h_n
  have h_eq : Computable (fun q : (ℕ × ℕ) × (ℕ × ℕ) => decide (q.2.2 = q.2.1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp h_IH h_n
  have h_ok := hbud.comp (Computable.pair h_i h_np1)
  have h_step := (Computable.cond h_eq (Computable.cond h_ok h_np1 h_IH) h_IH).to₂
  have h_rec := Computable.nat_rec (f := fun p : ℕ × ℕ => p.2) (g := fun _ : ℕ × ℕ => 0)
    Computable.snd (Computable.const 0) h_step
  exact h_rec.of_eq
    (fun p => (freezeStageB_rec b p.1 p.2).symm.trans (freezeStageB_eq b p.1 p.2))

/-- Uniform version of `computable_treeSanitize`. -/
theorem computable_treeSanitize_uniform
    (hb : Computable (fun p : ℕ × ℕ × BitString × BitString => b p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Computable (fun p : ℕ × ℕ × BitString => treeSanitize (b p.1) p.2.1 p.2.2) := by
  have hi : Computable (fun p : ℕ × ℕ × BitString => p.1) := Computable.fst
  have hs : Computable (fun p : ℕ × ℕ × BitString => p.2.1) := Computable.fst.comp Computable.snd
  have hx : Computable (fun p : ℕ × ℕ × BitString => p.2.2) := Computable.snd.comp Computable.snd
  have hF := (computable_freezeStage_uniform b hb).comp (Computable.pair hi hs)
  have hsub := Primrec.nat_sub.to_comp.comp hs hF
  have hpow := primrec_two_pow_aux.to_comp.comp hsub
  have happrox := (computable_simpleApprox_uniform b hb).comp
    (Computable.pair hi (Computable.pair hF hx))
  exact (Primrec.nat_mul.to_comp.comp hpow happrox).of_eq (fun _ => rfl)

end Kolmogorov
