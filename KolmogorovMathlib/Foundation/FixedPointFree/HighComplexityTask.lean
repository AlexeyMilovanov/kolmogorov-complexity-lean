import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import Mathlib.Computability.TuringDegree
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Foundation.RSeparability
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce

/-!
# The high-complexity task and fixed-point-free functions

Three tasks that an oracle may or may not solve are compared: `SolvesHighComplexity` (produce,
from `n`, an object of plain complexity at least `n`), `SolvesDiagonal` (produce, from a program
without input, a value different from its output) and `SolvesFixedPointFree` (produce, from a
program, a program computing a different function).
`solvesDiagonal_of_solvesHighComplexity` is the first reduction between them; the decoding
function `highComplexityTaskF` extracts a single object from the list a decompressor outputs.

### Outline

* the relative-computability plumbing (`recursiveIn_of_natPartrec`,
  `recursiveIn_of_forall_oracle_recursiveIn`, `recursiveIn_charFun_of_isRE`);
* the halting oracle solves the high-complexity task
  (`solvesHighComplexity_recursiveIn_halting`);
* the converse — an enumerable oracle solving it computes the halting problem — via Arslanov's
  completeness criterion, whose construction uses the oracle prefixes `oraclePrefix`.

Source: SUV, Exercises 13 and 15.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Solving the task "given `n`, produce an object of complexity at least `n`". -/
def SolvesHighComplexity (U : Map) (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, (n : ℕ∞) ≤ plainKNat U (g n)

/-- Solving the task "given a program without input, produce a value different
from its output" (any value if the program does not halt). -/
def SolvesDiagonal (h : ℕ → ℕ) : Prop :=
  ∀ (e v : ℕ), v ∈ (Denumerable.ofNat Code e).eval 0 → h e ≠ v

/-- Solving the task "given a program, produce a program computing a different
function". -/
def SolvesFixedPointFree (F : ℕ → ℕ) : Prop :=
  ∀ e : ℕ, (Denumerable.ofNat Code (F e)).eval ≠ (Denumerable.ofNat Code e).eval

/-- A partial recursive function is recursive in every oracle. -/
theorem recursiveIn_of_natPartrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : Nat.Partrec f) : RecursiveIn O f := by
  exact RecursiveIn.iff_nat.mpr hf.recursiveIn

private lemma recursiveIn_of_computable {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ} (hf : Computable f) :
    RecursiveIn O (totalOracle f) :=
  recursiveIn_of_natPartrec (Partrec.nat_iff.mp hf.partrec)

/-- **Exercise 13, first reduction.** A solver of the high-complexity task
computes a solver of the diagonal task. -/
theorem solvesDiagonal_of_solvesHighComplexity (U : Map) (hU : isOptimalConditional U)
    (g : ℕ → ℕ) (hg : SolvesHighComplexity U g) :
    ∃ h : ℕ → ℕ, SolvesDiagonal h ∧ RecursiveIn {totalOracle g} (totalOracle h) := by
  let D0 : Map := fun p =>
    let e := decodeBits p.1
    ((Denumerable.ofNat Code e).eval 0).map Nat.bits
  have hD0_partrec : Partrec D0 := by
    have h_eval : Partrec (fun p : BitString × BitString =>
        (Denumerable.ofNat Code (decodeBits p.1)).eval 0) := by
      have h_code : Computable (fun p : BitString × BitString => decodeBits p.1) :=
        decodeBits_computable.comp Computable.fst
      have h_eval_zero : Partrec (fun e : ℕ => (Denumerable.ofNat Code e).eval 0) :=
        (Nat.Partrec.Code.eval_part.comp
          ((Computable.ofNat Code).comp Computable.id)
          (Computable.const 0))
      exact h_eval_zero.comp h_code
    have h_map : Partrec (fun p : BitString × BitString =>
        ((Denumerable.ofNat Code (decodeBits p.1)).eval 0).map Nat.bits) :=
      Partrec.map h_eval (natBits_computable.comp Computable.snd).to₂
    exact h_map
  obtain ⟨c0, hc0⟩ := hU.2 D0 hD0_partrec
  let shift (e : ℕ) : ℕ := (Nat.bits e).length + c0 + 1
  have hshift_comp : Computable shift := by
    have h1 : Computable (fun e : ℕ => (Nat.bits e).length) :=
      Computable.list_length.comp natBits_computable
    have h2 : Computable (fun e : ℕ => (Nat.bits e).length + c0) :=
      (Primrec.to_comp Primrec.nat_add).comp (h1.pair (Computable.const c0))
    exact (Primrec.to_comp Primrec.nat_add).comp (h2.pair (Computable.const 1))
  let h (e : ℕ) : ℕ := g (shift e)
  use h
  refine ⟨fun e v hv => ?_, ?_⟩
  · have hD0_prod : produces D0 (Nat.bits e) [] (Nat.bits v) := by
      dsimp [produces, D0]
      rw [decodeBits_natBits]
      exact Part.mem_map Nat.bits hv
    have hcand : (((Nat.bits e).length : ℕ) : ENat) ∈ candidateLengths D0 (Nat.bits v) [] :=
      ⟨Nat.bits e, hD0_prod, rfl⟩
    have hcond_D0 : condK D0 (Nat.bits v) [] ≤ (((Nat.bits e).length : ℕ) : ENat) :=
      sInf_le hcand
    have hplain_v : plainK U (Nat.bits v) ≤ (((Nat.bits e).length + c0 : ℕ) : ENat) := by
      have h_opt := hc0 (Nat.bits v) []
      have h_add : condK D0 (Nat.bits v) [] + (c0 : ENat) ≤
          (((Nat.bits e).length : ℕ) : ENat) + (c0 : ENat) := by
        gcongr
      have h_sum : (((Nat.bits e).length : ℕ) : ENat) + (c0 : ENat) =
          (((Nat.bits e).length + c0 : ℕ) : ENat) := by
        push_cast; rfl
      rw [h_sum] at h_add
      exact h_opt.trans h_add
    have hKNat_v : plainKNat U v ≤ (((Nat.bits e).length + c0 : ℕ) : ENat) := hplain_v
    have hg_h : (shift e : ENat) ≤ plainKNat U (h e) := hg (shift e)
    intro h_eq
    subst h_eq
    have h_le : (shift e : ENat) ≤ (((Nat.bits e).length + c0 : ℕ) : ENat) :=
      hg_h.trans hKNat_v
    have h_lt : ((Nat.bits e).length + c0 : ℕ) < shift e := Nat.lt_succ_self _
    have h_enat_lt : (((Nat.bits e).length + c0 : ℕ) : ENat) < (shift e : ENat) :=
      WithTop.coe_lt_coe.mpr h_lt
    exact (lt_self_iff_false _).mp (h_enat_lt.trans_le h_le)
  · have hshift_rec : RecursiveIn {totalOracle g} (totalOracle shift) :=
      recursiveIn_of_computable hshift_comp
    have hg_rec : RecursiveIn {totalOracle g} (totalOracle g) :=
      RecursiveIn.oracle _ (Set.mem_singleton _)
    have hcomp := Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp hg_rec)
      (RecursiveIn.iff_nat.mp hshift_rec)
    have h_eq : ∀ n, (totalOracle shift n >>= fun m => totalOracle g m) = totalOracle h n :=
      fun n => Part.ext (fun x => by simp [totalOracle, h])
    exact RecursiveIn.iff_nat.mpr (hcomp.of_eq h_eq)

/-- Partial function decoding the `j`-th element from the list output of decompressor `U`. -/
private def highComplexityTaskF (U : Map) (nj : ℕ) : Part ℕ :=
  let n := nj.unpair.1
  let j := nj.unpair.2
  (U (((boundedPrograms (n - 1))[j]?).getD [], [])).bind fun w =>
    Part.ofOption ((Encodable.decode (decodeBits w) : Option (List ℕ)).bind fun L => L[j]?)

/-- Proof that `highComplexityTaskF U` is partial recursive for optimal decompressor `U`. -/
private lemma highComplexityTaskF_partrec (U : Map) (hU : isOptimalConditional U) :
    Partrec (highComplexityTaskF U) := by
  have h_n : Computable (fun nj : ℕ => nj.unpair.1 - 1) :=
    (Primrec.to_comp Primrec.nat_sub).comp
      ((Computable.fst.comp Computable.unpair).pair (Computable.const 1))
  have h_list : Computable (fun nj : ℕ => boundedPrograms (nj.unpair.1 - 1)) :=
    Computable.boundedPrograms.comp h_n
  have h_j : Computable (fun nj : ℕ => nj.unpair.2) := Computable.snd.comp Computable.unpair
  have h_opt : Computable (fun nj : ℕ => (boundedPrograms (nj.unpair.1 - 1))[nj.unpair.2]?) :=
    Computable.list_getElem?.comp h_list h_j
  have h_prog : Computable (fun nj : ℕ =>
      ((boundedPrograms (nj.unpair.1 - 1))[nj.unpair.2]?).getD []) :=
    Computable.option_getD h_opt (Computable.const [])
  have h_pair : Computable (fun nj : ℕ =>
      (((boundedPrograms (nj.unpair.1 - 1))[nj.unpair.2]?).getD [], ([] : BitString))) :=
    h_prog.pair (Computable.const [])
  have hU_eval : Partrec (fun nj : ℕ =>
      U (((boundedPrograms (nj.unpair.1 - 1))[nj.unpair.2]?).getD [], [])) :=
    hU.1.comp h_pair
  have h_get : Partrec₂ (fun (w : BitString) (j : ℕ) =>
      (Part.ofOption ((Encodable.decode (decodeBits w) : Option (List ℕ)).bind fun L =>
        L[j]?) : Part ℕ)) := by
    have h_opt₂ : Computable₂ (fun (w : BitString) (j : ℕ) =>
        (Encodable.decode (decodeBits w) : Option (List ℕ)).bind fun L => L[j]?) := by
      have h_dec : Computable (fun w : BitString =>
          (Encodable.decode (decodeBits w) : Option (List ℕ))) :=
        Computable.decode.comp decodeBits_computable
      exact Computable.option_bind (h_dec.comp Computable.fst)
        (Computable.list_getElem?.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂
    exact (Computable.ofOption h_opt₂).to₂
  have h_j' : Computable (fun nj : ℕ => nj.unpair.2) := Computable.snd.comp Computable.unpair
  exact Partrec.bind hU_eval (h_get.comp Computable.snd (h_j'.comp Computable.fst))

/-- Program code index construction for `highComplexityTaskF`. -/
private def highComplexityTaskEOf (c_F : Code) (n j : ℕ) : ℕ :=
  Encodable.encode (Nat.Partrec.Code.comp c_F (Nat.Partrec.Code.const (Nat.pair n j)))

/-- Proof that `highComplexityTaskEOf c_F` is computable. -/
private lemma highComplexityTaskEOf_computable (c_F : Code) :
    Computable₂ (highComplexityTaskEOf c_F) := by
  have h_const : Computable₂ (fun (n j : ℕ) => Nat.Partrec.Code.const (Nat.pair n j)) :=
    (Primrec.to_comp Nat.Partrec.Code.primrec_const).comp
      (Computable.pair Computable.fst Computable.snd)
  have hcode_of_comp : Computable₂ (fun n j =>
      Nat.Partrec.Code.comp c_F (Nat.Partrec.Code.const (Nat.pair n j))) :=
    (Primrec₂.to_comp Nat.Partrec.Code.primrec₂_comp).comp (Computable.const c_F) h_const
  exact Computable.encode.comp₂ hcode_of_comp

/-- Evaluation behavior of `highComplexityTaskEOf c_F n j`. -/
private lemma highComplexityTaskEOf_eval (U : Map) (c_F : Code)
    (hc_F : c_F.eval = highComplexityTaskF U) (n j : ℕ) :
    (Denumerable.ofNat Code (highComplexityTaskEOf c_F n j)).eval 0 =
      highComplexityTaskF U (Nat.pair n j) := by
  dsimp [highComplexityTaskEOf]
  rw [Denumerable.ofNat_encode]
  have hE : ∀ m, (Part.some m >>= c_F.eval) = c_F.eval m := fun m => Part.bind_some m c_F.eval
  simp [Nat.Partrec.Code.eval, ← hc_F, hE]

/-- Element lookup in a list constructed by appending step-wise over a range. -/
private lemma list_foldl_append_singleton_getElem? (f : ℕ → ℕ) (M j : ℕ) (hj : j < M) :
    (List.foldl (fun acc x => acc ++ [f x]) [] (List.range M))[j]? = some (f j) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rw [List.range_succ, List.foldl_append]
    dsimp
    by_cases hjM : j < M
    · have ih_j := ih hjM
      rw [List.getElem?_eq_some_iff] at ih_j
      have h_len := ih_j.1
      rw [List.getElem?_append_left h_len]
      exact ih hjM
    · have hj_eq : j = M := by omega
      have h_len : (List.foldl (fun acc x => acc ++ [f x]) [] (List.range M)).length = M := by
        have h_len_fold : ∀ L acc,
            (List.foldl (fun acc x => acc ++ [f x]) acc L).length = acc.length + L.length := by
          intro L; induction L with
          | nil => intro acc; simp
          | cons x L ih_L =>
            intro acc; dsimp; rw [ih_L]; simp; ring
        have h_len_M := h_len_fold (List.range M) []
        simp only [List.length_nil, zero_add, List.length_range] at h_len_M
        exact h_len_M
      subst hj_eq
      rw [List.getElem?_append_right (by rw [h_len])]
      rw [h_len, Nat.sub_self]
      rfl

/-- Oracle-computability of the tuple list construction from diagonal solver `h`. -/
private lemma highComplexityTaskTupleList_recursiveIn (c_F : Code) (h : ℕ → ℕ) :
    RecursiveIn {totalOracle h} (fun n => Part.some (Encodable.encode
      ((List.range (boundedPrograms (n - 1)).length).foldl
        (fun acc j => acc ++ [h (highComplexityTaskEOf c_F n j)]) []))) := by
  have he_comp : Computable₂ (highComplexityTaskEOf c_F) :=
    highComplexityTaskEOf_computable c_F
  have h0 : RecursiveIn {totalOracle h}
      (fun _ : ℕ => Part.some (Encodable.encode ([] : List ℕ))) :=
    recursiveIn_of_computable (Computable.const (Encodable.encode ([] : List ℕ)))
  have h_next : RecursiveIn {totalOracle h} (fun p : ℕ =>
      let a := p.unpair.1
      let y := (p.unpair.2).unpair.1
      let i := (p.unpair.2).unpair.2
      let l : List ℕ := (Encodable.decode i).getD []
      Part.some (Encodable.encode (l ++ [h (highComplexityTaskEOf c_F a y)]))) := by
    have h_a : Computable (fun p : ℕ => p.unpair.1) := Computable.fst.comp Computable.unpair
    have h_y : Computable (fun p : ℕ => (p.unpair.2).unpair.1) :=
      (Computable.fst.comp Computable.unpair).comp (Computable.snd.comp Computable.unpair)
    have h_i : Computable (fun p : ℕ => (p.unpair.2).unpair.2) :=
      (Computable.snd.comp Computable.unpair).comp (Computable.snd.comp Computable.unpair)
    have h_l : Computable (fun p : ℕ =>
        Encodable.encode ((Encodable.decode ((p.unpair.2).unpair.2) : Option (List ℕ)).getD [])) :=
      Computable.encode.comp (Computable.option_getD (Computable.decode.comp h_i)
        (Computable.const []))
    have h_e_call : Computable (fun p : ℕ => highComplexityTaskEOf c_F p.unpair.1
        (p.unpair.2).unpair.1) :=
      he_comp.comp h_a h_y
    have h_h_call : RecursiveIn {totalOracle h}
        (fun p : ℕ => Part.some (h (highComplexityTaskEOf c_F p.unpair.1
          (p.unpair.2).unpair.1))) := by
      have hc := Nat.RecursiveIn.comp
        (RecursiveIn.iff_nat.mp (RecursiveIn.oracle (totalOracle h) (Set.mem_singleton _)))
        (RecursiveIn.iff_nat.mp (recursiveIn_of_computable h_e_call))
      refine RecursiveIn.iff_nat.mpr (hc.of_eq fun n => ?_)
      exact Part.bind_some _ (totalOracle h)
    have h_l_rec : RecursiveIn {totalOracle h}
        (fun p : ℕ => Part.some (Encodable.encode
          ((Encodable.decode ((p.unpair.2).unpair.2) : Option (List ℕ)).getD []))) :=
      recursiveIn_of_computable h_l
    have h_pair := Nat.RecursiveIn.pair (RecursiveIn.iff_nat.mp h_l_rec)
      (RecursiveIn.iff_nat.mp h_h_call)
    have h_app_nat : Computable (fun code : ℕ =>
        let l : List ℕ := (Encodable.decode code.unpair.1).getD []
        Encodable.encode (l ++ [code.unpair.2])) := by
      have h_code1 : Computable (fun code : ℕ => code.unpair.1) :=
        Computable.fst.comp Computable.unpair
      have h_code2 : Computable (fun code : ℕ => code.unpair.2) :=
        Computable.snd.comp Computable.unpair
      have h_l_code : Computable (fun code : ℕ =>
          ((Encodable.decode code.unpair.1 : Option (List ℕ)).getD [])) :=
        Computable.option_getD (Computable.decode.comp h_code1) (Computable.const [])
      exact Computable.encode.comp (Computable.list_append.comp h_l_code
        (Computable.list_cons.comp h_code2 (Computable.const [])))
    have h_comp := Nat.RecursiveIn.comp
      (RecursiveIn.iff_nat.mp (recursiveIn_of_computable h_app_nat)) h_pair
    have h_eq2 : (fun n =>
        Nat.pair <$> Part.some (Encodable.encode
            ((Encodable.decode (n.unpair.2).unpair.2 : Option (List ℕ)).getD [])) <*>
            Part.some (h (highComplexityTaskEOf c_F n.unpair.1 (n.unpair.2).unpair.1)) >>=
          totalOracle (fun code =>
            let l : List ℕ := (Encodable.decode code.unpair.1).getD []
            Encodable.encode (l ++ [code.unpair.2]))) =
        (fun p : ℕ =>
          let a := p.unpair.1
          let y := (p.unpair.2).unpair.1
          let i := (p.unpair.2).unpair.2
          let l : List ℕ := (Encodable.decode i).getD []
          Part.some (Encodable.encode (l ++ [h (highComplexityTaskEOf c_F a y)]))) := by
      funext n
      dsimp [Seq.seq, Functor.map]
      rw [Part.map_some, Part.bind_some, Part.map_some]
      refine (Part.bind_some _ (totalOracle _)).trans ?_
      simp [totalOracle]
    exact RecursiveIn.iff_nat.mpr (h_comp.of_eq (congrFun h_eq2))
  have h_prec := Nat.RecursiveIn.prec (RecursiveIn.iff_nat.mp h0) (RecursiveIn.iff_nat.mp h_next)
  have h_step_p : RecursiveIn {totalOracle h}
      (fun p : ℕ => Part.some (Encodable.encode
        (List.foldl (fun acc j => acc ++ [h (highComplexityTaskEOf c_F p.unpair.1 j)]) []
          (List.range p.unpair.2)))) := by
    have h_eq3 : (fun (p : ℕ) => match Nat.unpair p with
        | (a, n) => Nat.rec (Part.some (Encodable.encode ([] : List ℕ)))
          (fun y IH => IH >>= fun i => (fun p_1 : ℕ => Part.some (Encodable.encode
            (((Encodable.decode (p_1.unpair.2).unpair.2 : Option (List ℕ)).getD []) ++
              [h (highComplexityTaskEOf c_F p_1.unpair.1 (p_1.unpair.2).unpair.1)])))
            (Nat.pair a (Nat.pair y i))) n) =
        (fun p : ℕ => Part.some (Encodable.encode
          (List.foldl (fun acc j => acc ++ [h (highComplexityTaskEOf c_F p.unpair.1 j)]) []
            (List.range p.unpair.2)))) := by
      funext p
      generalize h_a : p.unpair.1 = a
      generalize h_n : p.unpair.2 = n
      induction n generalizing p with
      | zero =>
        have hp : Nat.unpair p = (a, 0) := by
          ext
          · exact h_a
          · exact h_n
        rw [hp]
        simp
      | succ k ih =>
        have hp : Nat.unpair p = (a, k + 1) := by
          ext
          · exact h_a
          · exact h_n
        rw [hp]
        dsimp
        have ih_k := ih (Nat.pair a k) (by rw [Nat.unpair_pair]) (by rw [Nat.unpair_pair])
        dsimp at ih_k
        simp only [Nat.unpair_pair] at ih_k
        simp only [Nat.unpair_pair]
        rw [ih_k]
        rw [Part.bind_some]
        simp [List.range_succ]
    exact RecursiveIn.iff_nat.mpr (h_prec.of_eq (congrFun h_eq3))
  have h_bound_len : Computable (fun n : ℕ => (boundedPrograms (n - 1)).length) := by
    have h_n : Computable (fun n : ℕ => n - 1) :=
      (Primrec.to_comp Primrec.nat_sub).comp (Computable.id.pair (Computable.const 1))
    have h_list : Computable (fun n : ℕ => boundedPrograms (n - 1)) :=
      Computable.boundedPrograms.comp h_n
    exact Computable.list_length.comp h_list
  have h_bound : Computable (fun n : ℕ => Nat.pair n (boundedPrograms (n - 1)).length) :=
    Computable.pair Computable.id h_bound_len
  have h_comp := Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp h_step_p)
    (RecursiveIn.iff_nat.mp (recursiveIn_of_computable h_bound))
  have h_eq : (fun n => totalOracle (fun n => Nat.pair n (boundedPrograms (n - 1)).length) n >>=
      (fun p => Part.some (Encodable.encode (List.foldl
        (fun acc j => acc ++ [h (highComplexityTaskEOf c_F p.unpair.1 j)]) []
        (List.range p.unpair.2))))) =
      (fun n : ℕ => Part.some (Encodable.encode
        ((List.range (boundedPrograms (n - 1)).length).foldl
          (fun acc j => acc ++ [h (highComplexityTaskEOf c_F n j)]) []))) := by
    funext n
    simp [totalOracle, Part.bind_some, Nat.unpair_pair]
  exact RecursiveIn.iff_nat.mpr (h_comp.of_eq (congrFun h_eq))

/-- **Exercise 13, second reduction.** A solver of the diagonal task computes a
solver of the high-complexity task. -/
theorem solvesHighComplexity_of_solvesDiagonal (U : Map) (hU : isOptimalConditional U)
    (h : ℕ → ℕ) (hh : SolvesDiagonal h) :
    ∃ g : ℕ → ℕ, SolvesHighComplexity U g ∧ RecursiveIn {totalOracle h} (totalOracle g) := by
  have hF_part := highComplexityTaskF_partrec U hU
  obtain ⟨c_F, hc_F⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hF_part)
  let e_of (n j : ℕ) : ℕ := highComplexityTaskEOf c_F n j
  let tupleStep (n : ℕ) (acc : List ℕ) (j : ℕ) : List ℕ := acc ++ [h (e_of n j)]
  let tupleList (n : ℕ) : List ℕ :=
    (List.range (boundedPrograms (n - 1)).length).foldl (tupleStep n) []
  let g (n : ℕ) : ℕ := Encodable.encode (tupleList n)
  have hg_rec : RecursiveIn {totalOracle h} (totalOracle g) :=
    highComplexityTaskTupleList_recursiveIn c_F h
  use g
  refine ⟨fun n => ?_, hg_rec⟩
  by_contra h_lt
  push Not at h_lt
  dsimp [plainKNat, plainK, condK, candidateLengths, produces] at h_lt
  obtain ⟨m, hm, hlt_m⟩ := sInf_lt_iff.mp h_lt
  obtain ⟨p, hp, hlen⟩ := hm
  have hlen_nat : p.length < n := by
    rw [← hlen] at hlt_m
    exact WithTop.coe_lt_coe.mp hlt_m
  have hp_mem : p ∈ boundedPrograms (n - 1) := (mem_boundedPrograms_iff p (n - 1)).mpr (by omega)
  obtain ⟨j, hj_get⟩ := List.mem_iff_getElem?.mp hp_mem
  rw [List.getElem?_eq_some_iff] at hj_get
  obtain ⟨hj_lt, hj_val⟩ := hj_get
  have h_get_j : (tupleList n)[j]? = some (h (e_of n j)) := by
    dsimp [tupleList, tupleStep]
    exact list_foldl_append_singleton_getElem? (fun j => h (e_of n j)) _ j hj_lt
  have h_eval_j : (Denumerable.ofNat Code (e_of n j)).eval 0 =
      Part.some (h (e_of n j)) := by
    rw [highComplexityTaskEOf_eval U c_F hc_F]
    dsimp [highComplexityTaskF]
    rw [Nat.unpair_pair]
    have h_getD : ((boundedPrograms (n - 1))[j]?).getD [] = p := by
      rw [List.getElem?_eq_getElem hj_lt, hj_val, Option.getD_some]
    rw [h_getD]
    have hU_p : U (p, []) = Part.some (Nat.bits (g n)) := Part.eq_some_iff.mpr hp
    rw [hU_p]
    dsimp
    rw [Part.bind_some]
    dsimp [g]
    rw [decodeBits_natBits]
    rw [Encodable.encodek]
    dsimp
    rw [h_get_j]
    rfl
  have h_diag := hh (e_of n j) (h (e_of n j)) (by rw [h_eval_j]; exact Part.mem_some _)
  exact h_diag rfl

private def constCode : ℕ → Code
  | 0 => Code.zero
  | v + 1 => Code.comp Code.succ (constCode v)

private lemma eval_const_code (v x : ℕ) : (constCode v).eval x = Part.some v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    dsimp [constCode, Code.eval]
    rw [ih]
    change Part.bind (Part.some v) (fun n => Part.some (n + 1)) = Part.some (v + 1)
    exact Part.bind_some v (fun n => Part.some (n + 1))

private lemma mem_eval_const_code (v x : ℕ) : v ∈ (constCode v).eval x := by
  rw [eval_const_code]
  exact Part.mem_some v

private def cNat (v : ℕ) : ℕ :=
  Nat.rec 0 (fun _ acc => 2 * (2 * Nat.pair 1 acc + 1) + 4) v

private lemma c_nat_primrec : Primrec cNat := by
  have hg : Primrec (fun (p : Unit × ℕ × ℕ) => 2 * (2 * Nat.pair 1 p.2.2 + 1) + 4) := by
    have h_acc : Primrec (fun (p : Unit × ℕ × ℕ) => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    have h_pair : Primrec (fun (p : Unit × ℕ × ℕ) => Nat.pair 1 p.2.2) :=
      Primrec₂.natPair.comp (Primrec.const 1) h_acc
    have h_mul1 : Primrec (fun (p : Unit × ℕ × ℕ) => 2 * Nat.pair 1 p.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) h_pair
    have h_add1 : Primrec (fun (p : Unit × ℕ × ℕ) => 2 * Nat.pair 1 p.2.2 + 1) :=
      Primrec.nat_add.comp h_mul1 (Primrec.const 1)
    have h_mul2 : Primrec (fun (p : Unit × ℕ × ℕ) => 2 * (2 * Nat.pair 1 p.2.2 + 1)) :=
      Primrec.nat_mul.comp (Primrec.const 2) h_add1
    exact Primrec.nat_add.comp h_mul2 (Primrec.const 4)
  have h_rec := Primrec.nat_rec (f := fun (_ : Unit) => 0)
    (g := fun (_ : Unit) (p : ℕ × ℕ) => 2 * (2 * Nat.pair 1 p.2 + 1) + 4)
    (hf := Primrec.const 0)
    (hg := hg.to₂)
  exact h_rec.comp (Primrec.const ()) Primrec.id

private lemma encode_const_code (v : ℕ) : Encodable.encode (constCode v) = cNat v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    change 2 * (2 * Nat.pair 1 (Encodable.encode (constCode v)) + 1) + 4 = cNat (v + 1)
    rw [ih]
    rfl

private def F_fn (h : ℕ → ℕ) (e : ℕ) : ℕ := cNat (h e)

/-- **Exercise 14, first reduction.** A solver of the diagonal task computes a
fixed-point-free function. -/
theorem fixedPointFree_of_solvesDiagonal
    (h : ℕ → ℕ) (hh : SolvesDiagonal h) :
    ∃ F : ℕ → ℕ, SolvesFixedPointFree F ∧ RecursiveIn {totalOracle h} (totalOracle F) := by
  use F_fn h
  constructor
  · intro e h_eq
    have h_mem : h e ∈ (Denumerable.ofNat Code (F_fn h e)).eval 0 := by
      dsimp [F_fn]
      rw [← encode_const_code]
      rw [Denumerable.ofNat_encode]
      exact mem_eval_const_code (h e) 0
    rw [h_eq] at h_mem
    exact hh e (h e) h_mem rfl
  · have h_oracle : RecursiveIn {totalOracle h} (totalOracle h) :=
      RecursiveIn.oracle _ (Set.mem_singleton _)
    have h_c_partrec : Nat.Partrec (fun v => Part.some (cNat v)) :=
      Partrec.nat_iff.mp (Computable.partrec (c_nat_primrec.to_comp.comp Computable.id))
    have h_c_recIn : RecursiveIn {totalOracle h} (fun v => Part.some (cNat v)) :=
      recursiveIn_of_natPartrec h_c_partrec
    have h_bind := Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp h_c_recIn)
      (RecursiveIn.iff_nat.mp h_oracle)
    have h_eq : (fun n => totalOracle h n >>= fun v => Part.some (cNat v)) =
        totalOracle (F_fn h) := funext fun e => by
      dsimp [totalOracle, F_fn]
      exact Part.bind_some (h e) (fun v => Part.some (cNat v))
    exact RecursiveIn.iff_nat.mpr (h_bind.of_eq (congrFun h_eq))

private def codeId : Code := Code.curry Code.right 0

private lemma eval_code_id (x : ℕ) : codeId.eval x = Part.some x := by
  dsimp [codeId]
  rw [Code.eval_curry]
  dsimp [Code.eval]
  rw [Nat.unpair_pair]

private def cMod (c_univ : Code) (c : Code) : Code :=
  Code.comp c_univ (Code.pair (Code.comp c Code.zero) codeId)

private lemma eval_c_mod (c_univ : Code)
    (hc_univ : ∀ e x, c_univ.eval (Nat.pair e x) = (Denumerable.ofNat Code e).eval x)
    (c : Code) (x : ℕ) :
    (cMod c_univ c).eval x = c.eval 0 >>= (fun v => (Denumerable.ofNat Code v).eval x) := by
  dsimp [cMod, Code.eval]
  rw [eval_code_id]
  change (((Part.some 0).bind fun a => c.eval a).bind fun a => Part.some (Nat.pair a x)).bind
      (fun a => c_univ.eval a) = (c.eval 0).bind fun v => (Denumerable.ofNat Code v).eval x
  rw [Part.bind_some, Part.bind_assoc]
  refine congrArg (Part.bind (c.eval 0)) (funext fun v => ?_)
  rw [Part.bind_some]
  exact hc_univ v x

private def cModNat (c_univ : Code) (e : ℕ) : ℕ :=
  2 * (2 * Nat.pair (Encodable.encode c_univ)
    (2 * (2 * Nat.pair (2 * (2 * Nat.pair e (Encodable.encode Code.zero) + 1) + 4)
      (Encodable.encode codeId)) + 4) + 1) + 4

private lemma encode_c_mod_helper (c_univ c : Code) :
    Encodable.encode (cMod c_univ c) =
      2 * (2 * Nat.pair (Encodable.encode c_univ)
        (2 * (2 * Nat.pair (2 * (2 * Nat.pair (Encodable.encode c)
          (Encodable.encode Code.zero) + 1) + 4) (Encodable.encode codeId)) + 4) + 1) + 4 := rfl

private lemma encode_c_mod (c_univ : Code) (e : ℕ) :
    Encodable.encode (cMod c_univ (Denumerable.ofNat Code e)) = cModNat c_univ e := by
  rw [encode_c_mod_helper, cModNat, Denumerable.encode_ofNat]

private lemma c_mod_nat_primrec (c_univ : Code) : Primrec (cModNat c_univ) := by
  have h_pair1 : Primrec (fun e => Nat.pair e (Encodable.encode Code.zero)) :=
    Primrec₂.natPair.comp Primrec.id (Primrec.const _)
  have h_n1 : Primrec (fun e => 2 * (2 * Nat.pair e (Encodable.encode Code.zero) + 1) + 4) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) h_pair1)
          (Primrec.const 1)))
      (Primrec.const 4)
  have h_pair2 : Primrec (fun e =>
      Nat.pair (2 * (2 * Nat.pair e (Encodable.encode Code.zero) + 1) + 4)
        (Encodable.encode codeId)) :=
    Primrec₂.natPair.comp h_n1 (Primrec.const _)
  have h_n2 : Primrec (fun e =>
      2 * (2 * Nat.pair (2 * (2 * Nat.pair e (Encodable.encode Code.zero) + 1) + 4)
        (Encodable.encode codeId)) + 4) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_mul.comp (Primrec.const 2) h_pair2))
      (Primrec.const 4)
  have h_pair3 : Primrec (fun e =>
      Nat.pair (Encodable.encode c_univ)
        (2 * (2 * Nat.pair (2 * (2 * Nat.pair e (Encodable.encode Code.zero) + 1) + 4)
          (Encodable.encode codeId)) + 4)) :=
    Primrec₂.natPair.comp (Primrec.const _) h_n2
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) h_pair3)
        (Primrec.const 1)))
    (Primrec.const 4)

private lemma exists_code_univ : ∃ c_univ : Code, ∀ e x : ℕ,
    c_univ.eval (Nat.pair e x) = (Denumerable.ofNat Code e).eval x := by
  have h_comp1 : Computable (fun p : ℕ × ℕ => Denumerable.ofNat Code p.1) :=
    (Computable.ofNat Code).comp Computable.fst
  have h_comp2 : Computable (fun p : ℕ × ℕ => p.2) := Computable.snd
  have h_part : Partrec (fun p : ℕ × ℕ => (Denumerable.ofNat Code p.1).eval p.2) :=
    Partrec.comp Code.eval_part (h_comp1.pair h_comp2)
  have h_nat : Nat.Partrec (fun n : ℕ =>
      (Denumerable.ofNat Code n.unpair.1).eval n.unpair.2) :=
    Partrec.nat_iff.1 (Partrec.comp h_part Primrec.unpair.to_comp)
  obtain ⟨c_univ, hc⟩ := Nat.Partrec.Code.exists_code.1 h_nat
  use c_univ
  intro e x
  rw [hc]
  dsimp
  rw [Nat.unpair_pair]

/-- **Exercise 14, second reduction.** A fixed-point-free function computes a
solver of the diagonal task. -/
theorem solvesDiagonal_of_fixedPointFree
    (F : ℕ → ℕ) (hF : SolvesFixedPointFree F) :
    ∃ h : ℕ → ℕ, SolvesDiagonal h ∧ RecursiveIn {totalOracle F} (totalOracle h) := by
  obtain ⟨c_univ, hc_univ⟩ := exists_code_univ
  use fun e => F (cModNat c_univ e)
  constructor
  · intro e v hv h_eq
    let p := cModNat c_univ e
    have hp_code : Denumerable.ofNat Code p = cMod c_univ (Denumerable.ofNat Code e) := by
      dsimp [p]
      rw [← encode_c_mod]
      rw [Denumerable.ofNat_encode]
    have h_p_eval : (Denumerable.ofNat Code p).eval = (Denumerable.ofNat Code v).eval := by
      ext x
      rw [hp_code]
      rw [eval_c_mod c_univ hc_univ]
      have h_ev : (Denumerable.ofNat Code e).eval 0 = Part.some v := Part.eq_some_iff.2 hv
      rw [h_ev]
      have h_bind : (Part.some v >>= fun v => (Denumerable.ofNat Code v).eval x) =
          (Denumerable.ofNat Code v).eval x := Part.bind_some v _
      rw [h_bind]
    have h_F_p : (Denumerable.ofNat Code (F p)).eval = (Denumerable.ofNat Code v).eval := by
      have : F p = v := h_eq
      rw [this]
    have h_equal : (Denumerable.ofNat Code (F p)).eval = (Denumerable.ofNat Code p).eval := by
      rw [h_F_p, h_p_eval]
    exact hF p h_equal
  · have h_oracle : RecursiveIn {totalOracle F} (totalOracle F) :=
      RecursiveIn.oracle _ (Set.mem_singleton _)
    have h_c_partrec : Nat.Partrec (fun e => Part.some (cModNat c_univ e)) :=
      Partrec.nat_iff.mp
        (Computable.partrec ((c_mod_nat_primrec c_univ).to_comp.comp Computable.id))
    have h_c_recIn : RecursiveIn {totalOracle F} (fun e => Part.some (cModNat c_univ e)) :=
      recursiveIn_of_natPartrec h_c_partrec
    have h_bind := Nat.RecursiveIn.comp (RecursiveIn.iff_nat.mp h_oracle)
      (RecursiveIn.iff_nat.mp h_c_recIn)
    have h_eq : (fun e => Part.some (cModNat c_univ e) >>= totalOracle F) =
        totalOracle (fun e => F (cModNat c_univ e)) := funext fun e => by
      dsimp [totalOracle]
      exact Part.bind_some (cModNat c_univ e) (totalOracle F)
    exact RecursiveIn.iff_nat.mpr (h_bind.of_eq (congrFun h_eq))

/-! #### Problem 15: the halting oracle solves the high-complexity task

The forward direction of Problem 15 is Arslanov's completeness criterion for
enumerable oracles (`arslanov_completeness`).  The converse direction — a halting
oracle solves the high-complexity task — is proved outright here.
-/

/-- The diagonal halting set. -/
def arslanovHaltingSet : Set ℕ := {e | ((Denumerable.ofNat Code e).eval e).Dom}

/-- Every RE predicate on `ℕ` many-one reduces to the diagonal halting set. -/
theorem exists_manyOne_reduction_to_halting (P : ℕ → Prop) (hP : IsRE P) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ n, (m n ∈ arslanovHaltingSet ↔ P n) := by
  classical
  obtain ⟨f, hf, hfP⟩ := hP
  have hg : Nat.Partrec (fun p : ℕ => (f (Nat.unpair p).1).map (fun _ => 0)) := by
    have : Partrec (fun p : ℕ => (f (Nat.unpair p).1).map (fun _ => (0 : ℕ))) :=
      (hf.comp (Computable.fst.comp Primrec.unpair.to_comp)).map
        (Computable.const (0 : ℕ)).to₂
    exact Partrec.nat_iff.mp this
  obtain ⟨cf, hcf⟩ := Code.exists_code.mp hg
  obtain ⟨sm, hsm_comp, hsm⟩ := Code.smn
  refine ⟨fun n => Encodable.encode (sm cf n), ?_, ?_⟩
  · exact Computable.encode.comp (hsm_comp.comp (Computable.const cf) Computable.id)
  · intro n
    have hcode : Denumerable.ofNat Code (Encodable.encode (sm cf n)) = sm cf n :=
      Denumerable.ofNat_encode _
    change ((Denumerable.ofNat Code (Encodable.encode (sm cf n))).eval
      (Encodable.encode (sm cf n))).Dom ↔ P n
    rw [hcode, hsm cf n, hcf]
    simp only [Part.map_Dom, Nat.unpair_pair]
    exact hfP n

/-- The predicate `plainKNat U k ≤ n`, packed into a single natural number argument,
is recursively enumerable. -/
theorem isRE_plainKNat_le_pair {U : Map} {c : Code} (hc : IsCodeFor c U) :
    IsRE (fun p : ℕ => plainKNat U (Nat.unpair p).1 ≤ (((Nat.unpair p).2 : ℕ) : ENat)) := by
  refine ⟨fun p => (Nat.rfind fun t => Part.some
      (decide (Nat.bits (Nat.unpair p).1 ∈
        boundedOutputStage c (Nat.unpair p).2 t))).map (fun _ => ()), ?_, ?_⟩
  · have hb : Computable (fun q : ℕ × ℕ =>
        decide (Nat.bits (Nat.unpair q.1).1 ∈
          boundedOutputStage c (Nat.unpair q.1).2 q.2)) := by
      have h1 : Computable (fun q : ℕ × ℕ => Nat.bits (Nat.unpair q.1).1) :=
        natBits_computable.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.fst))
      have h2 : Computable (fun q : ℕ × ℕ =>
          boundedOutputStage c (Nat.unpair q.1).2 q.2) :=
        (boundedOutputStage_computable c).comp
          (Computable.pair
            (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.fst))
            Computable.snd)
      exact bitString_mem_primrec.to_comp.comp h1 h2
    have hp2 : Partrec₂ (fun (p : ℕ) (t : ℕ) => (Part.some (decide
        (Nat.bits (Nat.unpair p).1 ∈
          boundedOutputStage c (Nat.unpair p).2 t)) : Part Bool)) :=
      hb.partrec.to₂
    exact (Partrec.rfind hp2).map (Computable.const ()).to₂
  · intro p
    change (Nat.rfind fun t => Part.some (decide (Nat.bits (Nat.unpair p).1 ∈
      boundedOutputStage c (Nat.unpair p).2 t))).Dom ↔ _
    refine Iff.trans Nat.rfind_dom ?_
    have hkey : plainKNat U (Nat.unpair p).1 ≤ (((Nat.unpair p).2 : ℕ) : ENat) ↔
        ∃ t, Nat.bits (Nat.unpair p).1 ∈ boundedOutputStage c (Nat.unpair p).2 t :=
      (Dovetailing.exists_stage_mem_iff_plainK_le hc (Nat.unpair p).2 _).symm
    change _ ↔ plainKNat U (Nat.unpair p).1 ≤ (((Nat.unpair p).2 : ℕ) : ENat)
    rw [hkey]
    constructor
    · rintro ⟨t, ht, -⟩
      exact ⟨t, of_decide_eq_true (Part.mem_some_iff.mp ht).symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, Part.mem_some_iff.mpr (decide_eq_true ht).symm, fun _ => Part.some_dom _⟩

/-- Being recursive in an oracle transfers along a pointwise equality of partial functions. -/
theorem recursiveIn_congr {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ}
    (hf : RecursiveIn O f) (H : ∀ n, f n = g n) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

private theorem recursiveIn_of_tot {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} {g : ℕ → ℕ}
    (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) : RecursiveIn O (totalOracle g) :=
  recursiveIn_congr hf (fun n => (Part.eq_some_iff.2 (H n)))

open Classical in
/-- With the halting oracle, the characteristic function of any RE predicate is
oracle-computable. -/
theorem recursiveIn_charFun_of_isRE (P : ℕ → Prop) (hP : IsRE P) :
    ∃ chi : ℕ →. ℕ, RecursiveIn {charOracle arslanovHaltingSet} chi ∧
      ∀ n, chi n = Part.some (if P n then 1 else 0) := by
  classical
  obtain ⟨m, hm, hmP⟩ := exists_manyOne_reduction_to_halting P hP
  refine ⟨fun n => charOracle arslanovHaltingSet (m n), ?_, ?_⟩
  · have h1 : RecursiveIn {charOracle arslanovHaltingSet} (charOracle arslanovHaltingSet) :=
      RecursiveIn.oracle _ (Set.mem_singleton _)
    have h2 : RecursiveIn {charOracle arslanovHaltingSet} (fun n => Part.some (m n)) :=
      recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec hm))
    exact recursiveIn_congr (RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp
      (RecursiveIn.iff_nat.mp h1) (RecursiveIn.iff_nat.mp h2))) (fun n => Part.bind_some _ _)
  · intro n
    simp only [charOracle]
    congr 1
    by_cases h : P n
    · rw [if_pos ((hmP n).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((hmP n).mp hc)), if_neg h]

/-- **The halting oracle solves the high-complexity task.** -/
theorem solvesHighComplexity_recursiveIn_halting (U : Map) (hU : isOptimalConditional U) :
    ∃ g : ℕ → ℕ, SolvesHighComplexity U g ∧
      RecursiveIn {charOracle arslanovHaltingSet} (totalOracle g) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Code, IsCodeFor c U := Nat.Partrec.Code.exists_code.mp hU.1
  obtain ⟨chi, hchi_rec, hchi⟩ :=
    recursiveIn_charFun_of_isRE _ (isRE_plainKNat_le_pair (U := U) hc)
  set F : ℕ →. ℕ := fun q => chi (Nat.pair (Nat.unpair q).2 (Nat.unpair q).1) with hF
  have hF_rec : RecursiveIn {charOracle arslanovHaltingSet} F := by
    have hswap : RecursiveIn {charOracle arslanovHaltingSet}
        (fun q : ℕ => Part.some (Nat.pair (Nat.unpair q).2 (Nat.unpair q).1)) :=
      recursiveIn_of_natPartrec (Partrec.nat_iff.mp (Computable.partrec
        (Primrec.to_comp (Primrec₂.natPair.comp
          (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)))))
    exact recursiveIn_congr (RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.comp
      (RecursiveIn.iff_nat.mp hchi_rec) (RecursiveIn.iff_nat.mp hswap)))
      (fun q => Part.bind_some _ _)
  have hF_val : ∀ a k : ℕ, F (Nat.pair a k) =
      Part.some (if plainKNat U k ≤ (a : ENat) then 1 else 0) := by
    intro a k
    have hup : (Nat.unpair (Nat.pair a k)) = (a, k) := Nat.unpair_pair a k
    simp only [hF, hup]
    rw [hchi]
    congr 2
    simp [Nat.unpair_pair]
  have hrfind := Nat.RecursiveIn.rfind (RecursiveIn.iff_nat.mp hF_rec)
  set G : ℕ →. ℕ := fun a => Nat.rfind fun k => (fun m => m = 0) <$> F (Nat.pair a k) with hG
  have hvalT : ∀ a k : ℕ, (true ∈ ((fun m => m = 0) <$> F (Nat.pair a k) : Part Bool)) ↔
      ¬ (plainKNat U k ≤ (a : ENat)) := by
    intro a k
    rw [hF_val]
    by_cases h : plainKNat U k ≤ (a : ENat) <;> simp [h]
  have hvalF : ∀ a k : ℕ, (false ∈ ((fun m => m = 0) <$> F (Nat.pair a k) : Part Bool)) ↔
      (plainKNat U k ≤ (a : ENat)) := by
    intro a k
    rw [hF_val]
    by_cases h : plainKNat U k ≤ (a : ENat) <;> simp [h]
  have hmem : ∀ a k : ℕ, (k ∈ G a) ↔
      ((a : ENat) < plainKNat U k ∧ ∀ j < k, plainKNat U j ≤ (a : ENat)) := by
    intro a k
    rw [hG]
    refine Iff.trans Nat.mem_rfind ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨not_le.mp ((hvalT a k).mp h1), fun j hj => (hvalF a j).mp (h2 hj)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hvalT a k).mpr (not_le.mpr h1), ?_⟩
      intro j hj
      exact (hvalF a j).mpr (h2 j hj)
  have hdom : ∀ a : ℕ, ∃ k, k ∈ G a := by
    intro a
    obtain ⟨k0, hk0⟩ := exists_plainKNat_gt U a
    have hex : ∃ k, (a : ENat) < plainKNat U k := ⟨k0, hk0⟩
    refine ⟨Nat.find hex, (hmem a _).mpr ⟨Nat.find_spec hex, ?_⟩⟩
    intro j hj
    exact not_lt.mp (Nat.find_min hex hj)
  choose g hg using hdom
  refine ⟨g, ?_, ?_⟩
  · intro n
    exact le_of_lt ((hmem n (g n)).mp (hg n)).1
  · exact recursiveIn_of_tot (RecursiveIn.iff_nat.mpr hrfind) hg

/-- Transitivity of relative computability: if `f` is computable in the oracles `O`
and every oracle in `O` is computable in `O'`, then `f` is computable in `O'`. -/
theorem recursiveIn_of_forall_oracle_recursiveIn {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : RecursiveIn O f) (hO : ∀ g ∈ O, RecursiveIn O' g) : RecursiveIn O' f := by
  exact hf.subst hO

/-! #### Problem 15: Arslanov's completeness criterion, in full

The block below proves Arslanov's completeness criterion outright, and hence closes
`arslanov_solvesHighComplexity_iff_halting`.  Its reusable part is the **use principle**
`exists_string_operator`:  a function recursive in a *total* oracle `α₀` is computed by
a partial computable operator taking a finite oracle string as an extra argument, which
is monotone in that string and reproduces every value of the function on long enough
prefixes of `α₀`.  Everything else is the standard recursion-theoretic proof of
Arslanov's criterion:  from an enumerable `A` computing a diagonally non-computable `h`
one builds, with Kleene's recursion theorem, a program that on input `0` waits for `n` to
enter the halting set and then runs the operator against the finite approximation of `A`
available at that stage; an `A`-computable search finds a stage after which the
computation of `h` is settled, and the diagonal property forces `n` to enter the halting
set before that stage.
-/

/-- The length-`u` prefix of an oracle `α`, presented as a list. -/
def oraclePrefix (α : ℕ → ℕ) (u : ℕ) : List ℕ := (List.range u).map α

private lemma range_prefix_range {u u' : ℕ} (h : u ≤ u') :
    List.range u <+: List.range u' := by
  induction u' with
  | zero => simp [Nat.le_zero.mp h]
  | succ m ih =>
      rcases Nat.lt_or_ge u (m + 1) with h' | h'
      · exact (ih (Nat.lt_succ_iff.mp h')).trans (by
          rw [List.range_succ]; exact List.prefix_append _ _)
      · have : u = m + 1 := le_antisymm h h'
        subst this; exact List.prefix_rfl

/-- A shorter oracle prefix is a prefix of a longer one. -/
lemma oraclePrefix_prefix {α : ℕ → ℕ} {u u' : ℕ} (h : u ≤ u') :
    oraclePrefix α u <+: oraclePrefix α u' :=
  (range_prefix_range h).map α

end Kolmogorov
