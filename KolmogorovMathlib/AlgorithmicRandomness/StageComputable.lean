import KolmogorovMathlib.AlgorithmicRandomness.StageIntegral
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec

/-!
# Computability of the stage-integral approximations

The list `levelList n` of all bitstrings of length `n` is primitive recursive,
and finite sums over it of a computable function are computable.  Consequently
the approximate integral `stageNum`, the error mass `stageMass`, the precision
`stagePrec` and the acceptance test `stageAccept` are computable, uniformly in
any computable parameters.
-/

namespace Kolmogorov

open MeasureTheory ENNReal

/-! ## Summing a computable function over a computable list -/

/-- The index-recursive form of a list sum. -/
lemma natRec_take_map_sum {β : Type} [Inhabited β] (l : List β) (f : β → ℕ) :
    ∀ n, n ≤ l.length →
      (Nat.rec (motive := fun _ => ℕ) 0 (fun k IH => IH + f ((l[k]?).getD default)) n)
        = ((l.take n).map f).sum := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ l.length := Nat.le_of_succ_le hn
      have hlt : n < l.length := hn
      have hget : l[n]? = some (l[n]'hlt) := List.getElem?_eq_getElem hlt
      simp only [ih hn', List.take_add_one, hget, Option.toList_some,
        List.map_append, List.sum_append, Option.getD_some, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]

/-- The sum of `f` over a list equals the value obtained by recursion on its length, reading the
entries through indexed lookup. -/
lemma natRec_map_sum {β : Type} [Inhabited β] (l : List β) (f : β → ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k IH => IH + f ((l[k]?).getD default)) l.length)
      = (l.map f).sum := by
  rw [natRec_take_map_sum l f l.length le_rfl, List.take_length]

/-- Summing a computable function over a computably given list is computable. -/
lemma computable_list_sum_map {α β : Type} [Primcodable α] [Primcodable β] [Inhabited β]
    {L : α → List β} {f : α → β → ℕ} (hL : Computable L) (hf : Computable₂ f) :
    Computable (fun z => ((L z).map (f z)).sum) := by
  have hidx : Computable (fun q : α × ℕ × ℕ => (((L q.1)[q.2.1]?).getD default)) :=
    Computable.option_getD
      (Computable.list_getElem?.comp (hL.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
      (Computable.const default)
  have hstep : Computable₂ (fun (z : α) (q : ℕ × ℕ) =>
      q.2 + f z ((((L z)[q.1]?)).getD default)) := by
    have := Computable₂.comp (Primrec.nat_add.to_comp)
      (Computable.snd.comp Computable.snd)
      (Computable₂.comp hf Computable.fst hidx)
    exact this
  have hrec : Computable (fun z : α =>
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun k IH => IH + f z ((((L z)[k]?)).getD default)) ((L z).length))) :=
    Computable.nat_rec (Computable.list_length.comp hL) (Computable.const 0) hstep
  exact hrec.of_eq fun z => natRec_map_sum (L z) (f z)

/-! ## The list of bitstrings of a fixed length -/

/-- The list of all length-`n` bit strings is obtained by `n`-fold extension of the singleton
list containing the empty string. -/
lemma levelList_eq_natRec (n : ℕ) :
    levelList n = Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ IH => IH.map (fun x => x ++ [false]) ++ IH.map (fun x => x ++ [true])) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [levelList, ih]

/-- The function sending `n` to the list of all bit strings of length `n` is primitive
recursive. -/
lemma primrec_levelList : Primrec levelList := by
  have hstep : Primrec₂ (fun (_ : Unit) (q : ℕ × List BitString) =>
      q.2.map (fun x => x ++ [false]) ++ q.2.map (fun x => x ++ [true])) := by
    have h1 : Primrec (fun q : Unit × (ℕ × List BitString) =>
        q.2.2.map (fun x => x ++ [false])) :=
      Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_append.comp Primrec.snd (Primrec.const [false])).to₂
    have h2 : Primrec (fun q : Unit × (ℕ × List BitString) =>
        q.2.2.map (fun x => x ++ [true])) :=
      Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_append.comp Primrec.snd (Primrec.const [true])).to₂
    exact (Primrec.list_append.comp h1 h2).to₂
  have hrec := Primrec.nat_rec (f := fun _ : Unit => [([] : BitString)])
    (Primrec.const _) hstep
  have : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ IH => IH.map (fun x => x ++ [false]) ++ IH.map (fun x => x ++ [true])) n) :=
    (hrec.comp (Primrec.const ()) Primrec.id).of_eq (fun _ => rfl)
  exact this.of_eq fun n => (levelList_eq_natRec n).symm

/-- The function sending `n` to the list of all bit strings of length `n` is computable. -/
lemma computable_levelList : Computable levelList := primrec_levelList.to_comp

/-! ## Computability of the stage quantities -/

variable {α : Type} [Primcodable α]

/-- The total mass assigned by a computable stage function at a computable stage is
computable. -/
lemma computable_stageMass {G : α → BitString → ℕ} {S : α → ℕ}
    (hG : Computable₂ G) (hS : Computable S) :
    Computable (fun z => stageMass (G z) (S z)) :=
  computable_list_sum_map (computable_levelList.comp hS) hG

/-- The numerator emitted at a stage of the construction is computable in the data it is built
from. -/
lemma computable_stageNum {G : α → BitString → ℕ} {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) {S P : α → ℕ}
    (hG : Computable₂ G) (hS : Computable S) (hP : Computable P) :
    Computable (fun z => stageNum (G z) a (S z) (P z)) := by
  have hf : Computable₂ (fun (z : α) (x : BitString) => G z x * a x (P z)) :=
    Computable₂.comp (Primrec.nat_mul.to_comp) hG
      (Computable₂.comp ha Computable.snd (hP.comp Computable.fst))
  exact computable_list_sum_map (computable_levelList.comp hS) hf

/-- The precision used at a stage of the construction is computable in the data it is built
from. -/
lemma computable_stagePrec {G : α → BitString → ℕ} {S : α → ℕ}
    (hG : Computable₂ G) (hS : Computable S) :
    Computable (fun z => stagePrec (G z) (S z)) := by
  have hmass := computable_stageMass hG hS
  have hlog : Computable (fun z => Nat.log 2 (stageMass (G z) (S z) + 1)) :=
    computable_natLogTwo.comp (Computable.succ.comp hmass)
  have hsum : Computable (fun z => Nat.log 2 (stageMass (G z) (S z) + 1) + 3) :=
    Computable₂.comp (Primrec.nat_add.to_comp) hlog (Computable.const 3)
  exact hsum

/-- The acceptance test of a stage of the construction is computable in the data it is built
from. -/
lemma computable_stageAccept {G : α → BitString → ℕ} {a : BitString → ℕ → ℕ}
    (ha : Computable₂ a) {S : α → ℕ}
    (hG : Computable₂ G) (hS : Computable S) :
    Computable (fun z => stageAccept (G z) a (S z)) := by
  have hprec := computable_stagePrec hG hS
  have hnum := computable_stageNum ha hG hS hprec
  have hlhs : Computable (fun z => stageNum (G z) a (S z) (stagePrec (G z) (S z)) * 2 ^ 2) :=
    Computable₂.comp (Primrec.nat_mul.to_comp) hnum (Computable.const 4)
  have hrhs : Computable (fun z => 6 * 2 ^ (S z + stagePrec (G z) (S z))) := by
    have hexp : Computable (fun z => S z + stagePrec (G z) (S z)) :=
      Computable₂.comp (Primrec.nat_add.to_comp) hS hprec
    have hpow : Computable (fun z => 2 ^ (S z + stagePrec (G z) (S z))) :=
      primrec_two_pow_aux.to_comp.comp hexp
    exact Computable₂.comp (Primrec.nat_mul.to_comp) (Computable.const 6) hpow
  have hle : Computable (fun z => decide
      (stageNum (G z) a (S z) (stagePrec (G z) (S z)) * 2 ^ 2
        ≤ 6 * 2 ^ (S z + stagePrec (G z) (S z)))) := by
    have hle₂ : Computable₂ (fun m n : ℕ => decide (m ≤ n)) := by
      obtain ⟨_, hnatle⟩ := Primrec.nat_le
      exact (Primrec₂.of_eq hnatle.to₂ (fun m n => by simp)).to_comp
    exact Computable₂.comp hle₂ hlhs hrhs
  exact hle.of_eq fun z => rfl

end Kolmogorov
