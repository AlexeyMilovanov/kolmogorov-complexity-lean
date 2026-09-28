import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.Uncomputability
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Computability.Reduce



namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### Theorem 7: enumerable families and complexity bounds -/

open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-! ### Theorem 7: enumerable families and complexity bounds -/

/-- **Theorem 7(a).** The family `S n = {x | C(x) < n}` is an enumerable family of
sets and `|S n| < 2 ^ n`. -/
theorem isEnumerableFamily_complexityBelow_and_card_lt_two_pow (U : Map)
    (hU : isOptimalConditional U) :
    IsEnumerableFamily (fun n : ℕ => {x : BitString | plainK U x < (n : ℕ∞)}) ∧
      ∀ n : ℕ, {x : BitString | plainK U x < (n : ℕ∞)}.Finite ∧
        {x : BitString | plainK U x < (n : ℕ∞)}.ncard < 2 ^ n := by
  have h_enum : IsEnumerableFamily (fun n : ℕ => {x : BitString | plainK U x < (n : ℕ∞)}) := by
    dsimp [IsEnumerableFamily, IsRE]
    obtain ⟨f, hf_partrec, hf_dom⟩ := condK_le_isRE U hU
    have hR_re : IsRE (fun (p : (ℕ × BitString) × ℕ) => condK U p.1.2 [] ≤ (p.2 : ℕ∞)) := by
      change IsRE (fun (p : (ℕ × BitString) × ℕ) =>
        (fun (ab : ℕ × BitString) (k : ℕ) => condK U ab.2 [] ≤ (k : ℕ∞)) p.1 p.2)
      use fun p => f (p.1.2, [], p.2)
      refine ⟨Partrec.comp hf_partrec ?_, fun (p : (ℕ × BitString) × ℕ) => by rw [hf_dom]⟩
      exact Computable.pair (Computable.snd.comp Computable.fst)
        (Computable.pair (Computable.const ([] : BitString)) Computable.snd)
    have h_range_comp : Computable (fun (p : ℕ × BitString) => List.range p.1) :=
      Primrec.to_comp (Primrec.list_range.comp Primrec.fst)
    have h_curry := IsRE.existsInList (α := ℕ × BitString) (β := ℕ)
      (R := fun (ab : ℕ × BitString) (k : ℕ) => condK U ab.2 [] ≤ (k : ℕ∞))
      (bound := fun (p : ℕ × BitString) => List.range p.1) hR_re h_range_comp
    obtain ⟨g, hg_partrec, hg_dom⟩ := h_curry
    use g
    refine ⟨hg_partrec, fun ⟨n, x⟩ => ?_⟩
    rw [hg_dom]
    dsimp
    constructor
    · rintro ⟨k, hk, hk_le⟩
      rw [List.mem_range] at hk
      exact lt_of_le_of_lt hk_le (WithTop.coe_lt_coe.mpr hk)
    · intro h
      have h_cond : condK U x [] < (n : ℕ∞) := h
      generalize h_eq : condK U x [] = a at h_cond
      induction a using ENat.recTopCoe with
      | top =>
        exact False.elim (not_top_lt h_cond)
      | coe m =>
        have hm : m < n := WithTop.coe_lt_coe.mp h_cond
        exact ⟨m, List.mem_range.mpr hm, h_eq.symm ▸ le_rfl⟩
  refine ⟨h_enum, fun n => ?_⟩
  cases n with
  | zero =>
    have h_empty : {x : BitString | plainK U x < ((0 : ℕ) : ℕ∞)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact zero_le _
    rw [h_empty]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty]
    exact Nat.one_pos
  | succ m =>
    have h_set_eq : {x : BitString | plainK U x < ((m + 1 : ℕ) : ℕ∞)} =
        (compressibleWords U [] m : Set BitString) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Kolmogorov.mem_compressibleWords_iff, plainK]
      constructor
      · intro h
        have h_cond := h
        generalize h_eq : condK U x [] = a at h_cond ⊢
        induction a using ENat.recTopCoe with
        | top =>
          exact False.elim (not_top_lt h_cond)
        | coe k =>
          have hk : k < m + 1 := WithTop.coe_lt_coe.mp h_cond
          exact WithTop.coe_le_coe.mpr (Nat.lt_succ_iff.mp hk)
      · intro h
        exact lt_of_le_of_lt h (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m))
    rw [h_set_eq]
    refine ⟨Finset.finite_toSet _, ?_⟩
    rw [Set.ncard_coe_finset]
    exact card_compressibleWordsLt U [] m

/-! ### Theorem 8: semicomputability and minimality -/

/-- **Theorem 8(a).** Plain complexity is upper semicomputable and satisfies the
counting bound `|{x | C(x) < n}| < 2 ^ n`. -/
theorem isUpperSemicomputable_plainK_and_card_lt_two_pow (U : Map) (hU : isOptimalConditional U) :
    IsUpperSemicomputable (plainK U) ∧
      ∀ n : ℕ, {x : BitString | plainK U x < (n : ℕ∞)}.Finite ∧
        {x : BitString | plainK U x < (n : ℕ∞)}.ncard < 2 ^ n := by
  classical
  constructor
  · unfold IsUpperSemicomputable
    have h_equiv : (fun (p : BitString × ℕ) => plainK U p.1 < (p.2 : ℕ∞)) =
        (fun p => ∃ m ∈ List.range p.2, plainK U p.1 ≤ (m : ℕ∞)) := by
      ext ⟨x, n⟩
      simp only
      constructor
      · intro hlt
        obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, plainK U x = (k : ℕ∞) := by
          cases h : plainK U x with
          | top => rw [h] at hlt; contradiction
          | coe k => exact ⟨k, rfl⟩
        rw [hk_eq] at hlt
        have hk_lt : k < n := by exact_mod_cast hlt
        refine ⟨k, List.mem_range.mpr hk_lt, ?_⟩
        rw [hk_eq]
      · rintro ⟨m, hm_range, hle⟩
        have hm_lt : m < n := List.mem_range.mp hm_range
        have hm_cast : (m : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hm_lt
        exact lt_of_le_of_lt hle hm_cast
    rw [h_equiv]
    have h_re : IsRE (fun (p : (BitString × ℕ) × ℕ) => plainK U p.1.1 ≤ (p.2 : ℕ∞)) := by
      have h_cond := condK_le_isRE U hU
      let g : (BitString × ℕ) × ℕ → BitString × BitString × ℕ :=
        fun p => (p.1.1, [], p.2)
      have hg : Computable g :=
        Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.const []) Computable.snd)
      obtain ⟨f, hf, hdom⟩ := h_cond
      refine ⟨fun b => f (g b), Partrec.comp hf hg, fun b => ?_⟩
      rw [hdom (g b)]
      rfl
    have h_bound : Computable (fun (p : BitString × ℕ) => List.range p.2) :=
      Primrec.list_range.to_comp.comp Computable.snd
    exact IsRE.existsInList h_re _ h_bound
  · intro n
    cases n with
    | zero =>
      have h_empty : {x : BitString | plainK U x < ((0 : ℕ) : ℕ∞)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact not_lt_of_ge (zero_le _)
      rw [h_empty]
      refine ⟨Set.finite_empty, ?_⟩
      rw [Set.ncard_empty]
      exact Nat.zero_lt_one
    | succ m =>
      have h_iff : ∀ x, plainK U x < ((m + 1 : ℕ) : ℕ∞) ↔ plainK U x ≤ (m : ℕ∞) := by
        intro x
        constructor
        · intro h
          cases h_k : plainK U x with
          | top => rw [h_k] at h; contradiction
          | coe k =>
            have hk : k < m + 1 := by rw [h_k] at h; exact_mod_cast h
            exact_mod_cast Nat.le_of_lt_succ hk
        · intro h
          have h_lt : (m : ℕ∞) < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self m
          exact lt_of_le_of_lt h h_lt
      have h_set : {x : BitString | plainK U x < ((m + 1 : ℕ) : ℕ∞)} =
          {x : BitString | ∃ p ∈ boundedPrograms m, produces U p [] x} := by
        ext x
        simp only [Set.mem_setOf_eq]
        rw [h_iff x]
        change condK U x [] ≤ (m : ℕ∞) ↔ _
        rw [condK_le_iff U x [] m]
        constructor
        · rintro ⟨p, hlen, hprod⟩
          exact ⟨p, (mem_boundedPrograms_iff p m).mpr hlen, hprod⟩
        · rintro ⟨p, hmem, hprod⟩
          exact ⟨p, (mem_boundedPrograms_iff p m).mp hmem, hprod⟩
      rw [h_set]
      let S := {x : BitString | ∃ p ∈ boundedPrograms m, produces U p [] x}
      let pOf (x : BitString) : BitString :=
        if hx : x ∈ S then Classical.choose hx else []
      have hpOf_spec : ∀ x ∈ S, pOf x ∈ boundedPrograms m ∧ produces U (pOf x) [] x := by
        intro x hx
        dsimp [pOf]
        rw [dif_pos hx]
        exact Classical.choose_spec hx
      have hpOf_maps : Set.MapsTo pOf S ((boundedPrograms m).toFinset : Set BitString) := by
        intro x hx
        rw [Finset.mem_coe, List.mem_toFinset]
        exact (hpOf_spec x hx).1
      have hpOf_inj : S.InjOn pOf := by
        intro x hx y hy heq
        have hx_prod := (hpOf_spec x hx).2
        have hy_prod := (hpOf_spec y hy).2
        rw [heq] at hx_prod
        exact Part.mem_unique hx_prod hy_prod
      have ht_fin : ((boundedPrograms m).toFinset : Set BitString).Finite :=
        Finset.finite_toSet _
      have h_fin : S.Finite := Set.Finite.of_injOn hpOf_maps hpOf_inj ht_fin
      refine ⟨h_fin, ?_⟩
      have h_le := Set.ncard_le_ncard_of_injOn pOf hpOf_maps hpOf_inj ht_fin
      rw [Set.ncard_coe_finset] at h_le
      rw [List.toFinset_card_of_nodup (boundedPrograms_nodup m)] at h_le
      have h_lt := length_boundedPrograms_lt m
      exact lt_of_le_of_lt h_le h_lt

private def step_halt (c_semi : Code) (s : ℕ) (n : ℕ) (x : BitString) : Bool :=
  (Nat.Partrec.Code.evaln s c_semi (Encodable.encode (x, n))).isSome

private def new_items (c_semi : Code) (s : ℕ) (n : ℕ) (prev : List BitString) :
    List BitString :=
  (boundedPrograms s).filter (fun x => step_halt c_semi s n x && decide (x ∉ prev))

private def cumList (c_semi : Code) (s : ℕ) (n : ℕ) : List BitString :=
  match s with
  | 0 => []
  | s + 1 => cumList c_semi s n ++
      new_items c_semi (s + 1) n (cumList c_semi s n)

@[irreducible] private def thm08_idx (p : BitString) : ℕ :=
  @List.idxOf BitString instBEqOfDecidableEq p (exactLengthPrograms p.length)

@[irreducible] private def thm08_check_stage_pair (c_semi : Code) (p : BitString × ℕ) : Bool :=
  decide (thm08_idx p.1 < (cumList c_semi p.2 p.1.length).length)

private def check_stage (c_semi : Code) (p : BitString) (s : ℕ) : Bool :=
  thm08_check_stage_pair c_semi (p, s)

private def eval_D (c_semi : Code) (p : BitString) : Part BitString :=
  (Nat.rfind (fun s => Part.some (check_stage c_semi p s))).bind
    (fun s => Part.ofOption (cumList c_semi s p.length)[thm08_idx p]?)

private lemma beq_eq_decide_local (a b : BitString) : List.beq a b = decide (a = b) := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs =>
      dsimp [List.beq]
      rw [ih bs]
      cases a <;> cases b <;> simp

/-- The two `BEq` instances on `BitString` compute the same `List.idxOf`. -/
lemma idxOf_eq_idxOf (p : BitString) (l : List BitString) :
    @List.idxOf BitString instBEqOfDecidableEq p l = @List.idxOf BitString List.instBEq p l := by
  dsimp [List.idxOf, instBEqOfDecidableEq, BEq.beq]
  congr 1
  ext x
  exact (beq_eq_decide_local x p).symm

private lemma idx_spec (n ix : ℕ) (h_ix : ix < (exactLengthPrograms n).length) :
    thm08_idx ((exactLengthPrograms n)[ix]'h_ix) = ix := by
  unfold thm08_idx
  have h_len : ((exactLengthPrograms n)[ix]'h_ix).length = n :=
    exactLengthPrograms_length_eq n _ (List.getElem_mem h_ix)
  rw [h_len, idxOf_eq_idxOf]
  exact List.Nodup.idxOf_getElem (exactLengthPrograms_nodup n) ix h_ix

private lemma cumList_prefix (c_semi : Code) (s : ℕ) (n : ℕ) :
    cumList c_semi s n <+: cumList c_semi (s + 1) n := by
  dsimp [cumList]
  exact List.prefix_append _ _

private lemma cumList_prefix_le (c_semi : Code) {s1 s2 : ℕ} (h : s1 ≤ s2) (n : ℕ) :
    cumList c_semi s1 n <+: cumList c_semi s2 n := by
  induction h with
  | refl => exact List.prefix_rfl
  | step _ ih => exact ih.trans (cumList_prefix c_semi _ n)

private lemma cumList_nodup (c_semi : Code) (s : ℕ) (n : ℕ) :
    (cumList c_semi s n).Nodup := by
  induction s with
  | zero =>
    dsimp [cumList]
    exact List.nodup_nil
  | succ s ih =>
    dsimp [cumList]
    unfold new_items
    refine List.Nodup.append ih (boundedPrograms_nodup (s + 1) |>.filter _) ?_
    intro x hx hy
    rw [List.mem_filter] at hy
    have hy_not_mem : x ∉ cumList c_semi s n := by
      have h_dec : (step_halt c_semi (s + 1) n x &&
          decide (x ∉ cumList c_semi s n)) = true := hy.2
      have h_dec2 : decide (x ∉ cumList c_semi s n) = true := Bool.and_elim_right h_dec
      exact decide_eq_true_eq.mp h_dec2
    exact hy_not_mem hx

private lemma cumList_mem (c_semi : Code) (s : ℕ) (n : ℕ) (x : BitString) :
    x ∈ cumList c_semi s n → x ∈ boundedPrograms s ∧ step_halt c_semi s n x := by
  induction s with
  | zero =>
    dsimp [cumList]
    intro h
    cases h
  | succ s ih =>
    dsimp [cumList]
    rw [List.mem_append]
    rintro (h_prev | h_new)
    · obtain ⟨h_bp, h_halt⟩ := ih h_prev
      have h_bp_succ : boundedPrograms s <+: boundedPrograms (s + 1) := by
        dsimp [boundedPrograms]
        have h_take : List.take (s + 1) (List.range (s + 2)) = List.range (s + 1) :=
          List.take_range.trans (by rw [min_eq_left (by omega)])
        have h_r : List.range (s + 1) <+: List.range (s + 2) := by
          rw [← h_take]
          exact List.take_prefix (s + 1) (List.range (s + 2))
        exact h_r.flatMap exactLengthPrograms
      refine ⟨h_bp_succ.subset h_bp, ?_⟩
      unfold step_halt at h_halt ⊢
      obtain ⟨r_x, hr_x⟩ := Option.isSome_iff_exists.mp h_halt
      exact Option.isSome_iff_exists.mpr ⟨r_x, Nat.Partrec.Code.evaln_mono (Nat.le_succ s) hr_x⟩
    · unfold new_items at h_new
      rw [List.mem_filter] at h_new
      have h_halt : step_halt c_semi (s + 1) n x = true := Bool.and_elim_left h_new.2
      exact ⟨h_new.1, h_halt⟩

private lemma new_items_primrec (c_semi : Code) :
    Primrec (fun (p : (ℕ × List BitString) × ℕ) => new_items c_semi p.1.1 p.2 p.1.2) := by
  dsimp [new_items, step_halt]
  have h_bound : Primrec (fun (p : (ℕ × List BitString) × ℕ) => boundedPrograms p.1.1) :=
    primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)
  have h_evaln : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
      Nat.Partrec.Code.evaln q.1.1.1 c_semi (Encodable.encode (q.2, q.1.2))) := by
    have h1 : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) => q.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have h2 : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
        Encodable.encode (q.2, q.1.2)) :=
      Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
    have h3 : Primrec (fun (p : ℕ × ℕ) => Nat.Partrec.Code.evaln p.1 c_semi p.2) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c_semi)) Primrec.snd)
    exact h3.comp (Primrec.pair h1 h2)
  have h_isSome : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
      (Nat.Partrec.Code.evaln q.1.1.1 c_semi (Encodable.encode (q.2, q.1.2))).isSome) :=
    Primrec.option_isSome.comp h_evaln
  have h_mem : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
      decide (q.2 ∈ q.1.1.2)) :=
    bitString_mem_primrec.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have h_not_mem : Primrec (fun (b : Bool) => !b) := Primrec.not
  have h_not : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
      decide (q.2 ∉ q.1.1.2)) :=
    (h_not_mem.comp h_mem).of_eq (fun q => by simp)
  have h_and : Primrec (fun (q : ((ℕ × List BitString) × ℕ) × BitString) =>
      (Nat.Partrec.Code.evaln q.1.1.1 c_semi (Encodable.encode (q.2, q.1.2))).isSome &&
        decide (q.2 ∉ q.1.1.2)) := by
    have h_band : Primrec (fun (p : Bool × Bool) => p.1 && p.2) :=
      (Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).of_eq
        (fun p => by cases p.1 <;> cases p.2 <;> rfl)
    exact h_band.comp (Primrec.pair h_isSome h_not)
  exact (list_filter_primrec h_bound h_and.to₂).of_eq (fun _ => rfl)

private lemma nat_rec_eq_cumList (c_semi : Code) (a n : ℕ) :
    Nat.rec [] (fun m IH => IH ++ new_items c_semi (m + 1) a IH) n =
      cumList c_semi n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [cumList]
    rw [ih]

private lemma cumList_primrec (c_semi : Code) :
    Primrec (fun (p : ℕ × ℕ) => cumList c_semi p.1 p.2) := by
  have h_f : Primrec (fun (_ : ℕ) => ([] : List BitString)) := Primrec.const []
  have h_g : Primrec₂ (fun (a : ℕ) (p : ℕ × List BitString) =>
      p.2 ++ new_items c_semi (p.1 + 1) a p.2) := by
    have h_append : Primrec (fun (q : List BitString × List BitString) => q.1 ++ q.2) :=
      Primrec.list_append
    have h_fst : Primrec (fun (q : ℕ × ℕ × List BitString) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have h_s1 : Primrec (fun (q : ℕ × ℕ × List BitString) => q.2.1 + 1) :=
      Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
    have h_n : Primrec (fun (q : ℕ × ℕ × List BitString) => q.1) := Primrec.fst
    have h_prev : Primrec (fun (q : ℕ × ℕ × List BitString) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have h_pair_new : Primrec (fun (q : ℕ × ℕ × List BitString) => ((q.2.1 + 1, q.2.2), q.1)) :=
      Primrec.pair (Primrec.pair h_s1 h_prev) h_n
    have h_new := (new_items_primrec c_semi).comp h_pair_new
    have h_pair_app := Primrec.pair h_fst h_new
    exact (h_append.comp h_pair_app).to₂
  have h_rec := Primrec.nat_rec h_f h_g
  have h_swap := h_rec.comp Primrec.snd Primrec.fst
  exact h_swap.of_eq (fun p => nat_rec_eq_cumList c_semi p.2 p.1)

private lemma cumList_computable (c_semi : Code) :
    Computable (fun (p : ℕ × ℕ) => cumList c_semi p.1 p.2) :=
  (cumList_primrec c_semi).to_comp

private lemma idx_computable : Computable thm08_idx := by
  unfold thm08_idx
  have h_exact : Primrec (fun (p : BitString) => exactLengthPrograms p.length) :=
    primrec_exactLengthPrograms.comp Primrec.list_length
  exact (Primrec₂.comp Primrec.list_idxOf Primrec.id h_exact).to_comp

private lemma check_stage_pair_computable (c_semi : Code) :
    Computable (thm08_check_stage_pair c_semi) := by
  unfold thm08_check_stage_pair
  have h_len : Computable (fun (q : BitString × ℕ) =>
      (cumList c_semi q.2 q.1.length).length) := by
    have h_pair : Computable (fun (q : BitString × ℕ) => (q.2, q.1.length)) :=
      Computable.pair Computable.snd (Computable.list_length.comp Computable.fst)
    exact Computable.list_length.comp ((cumList_computable c_semi).comp h_pair)
  have h_idx_snd : Computable (fun (q : BitString × ℕ) => thm08_idx q.1) :=
    idx_computable.comp Computable.fst
  have h_nat_lt : Primrec (fun (p : ℕ × ℕ) => decide (p.1 < p.2)) :=
    PrimrecPred.decide Primrec.nat_lt
  have h_pair : Computable (fun (q : BitString × ℕ) =>
      (thm08_idx q.1, (cumList c_semi q.2 q.1.length).length)) :=
    Computable.pair h_idx_snd h_len
  exact h_nat_lt.to_comp.comp h_pair

private lemma check_stage_computable (c_semi : Code) :
    Computable (fun (p : BitString × ℕ) => check_stage c_semi p.1 p.2) :=
  check_stage_pair_computable c_semi

private lemma eval_D_partrec (c_semi : Code) : Partrec (eval_D c_semi) := by
  have h_rfind : Partrec (fun p =>
      Nat.rfind (fun s => Part.some (check_stage c_semi p s))) :=
    Partrec.rfind (check_stage_computable c_semi).to₂.partrec
  have h_list_pair : Computable (fun (q : BitString × ℕ) =>
      cumList c_semi q.2 q.1.length) := by
    have h_pair : Computable (fun (q : BitString × ℕ) => (q.2, q.1.length)) :=
      Computable.pair Computable.snd (Computable.list_length.comp Computable.fst)
    exact (cumList_computable c_semi).comp h_pair
  have h_idx_pair : Computable (fun (q : BitString × ℕ) => thm08_idx q.1) :=
    idx_computable.comp Computable.fst
  have h_pair : Computable (fun (q : BitString × ℕ) =>
      (cumList c_semi q.2 q.1.length, thm08_idx q.1)) :=
    Computable.pair h_list_pair h_idx_pair
  have h_get : Computable (fun (q : BitString × ℕ) =>
      (cumList c_semi q.2 q.1.length)[thm08_idx q.1]?) :=
    Computable.comp Computable.list_getElem? h_pair
  have h_option : Partrec (fun (q : BitString × ℕ) =>
      (Part.ofOption (cumList c_semi q.2 q.1.length)[thm08_idx q.1]? : Part BitString)) :=
    Computable.ofOption h_get
  exact Partrec.bind h_rfind h_option.to₂

private lemma list_length_le_ncard {α : Type*} (l : List α) (S : Set α)
    (hS : S.Finite) (h_nodup : l.Nodup) (h_mem : ∀ x ∈ l, x ∈ S) : l.length ≤ S.ncard := by
  classical
  have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup h_nodup).symm
  have h2 : (l.toFinset : Set α) ⊆ S := by
    intro x hx
    rw [Finset.mem_coe, List.mem_toFinset] at hx
    exact h_mem x hx
  rw [h1]
  have h3 := Set.ncard_le_ncard h2 hS
  rw [Set.ncard_coe_finset] at h3
  exact h3

/-- **Theorem 8(b).** Plain complexity is minimal, up to an additive constant,
among upper-semicomputable functions obeying the counting bound. -/
theorem plainK_le_of_isUpperSemicomputable_of_card_lt_two_pow (U : Map)
    (hU : isOptimalConditional U)
    (C' : BitString → ℕ∞) (hsemi : IsUpperSemicomputable C')
    (hfin : ∀ n : ℕ, {x : BitString | C' x < (n : ℕ∞)}.Finite)
    (hcard : ∀ n : ℕ, {x : BitString | C' x < (n : ℕ∞)}.ncard < 2 ^ n) :
    ∃ c : ℕ, ∀ x : BitString, plainK U x ≤ C' x + (c : ℕ∞) := by
  classical
  obtain ⟨f_semi, hf_semi, hdom_semi⟩ := hsemi
  obtain ⟨c_semi, hc_semi⟩ := Nat.Partrec.Code.exists_code.mp hf_semi
  let D : Map := fun (p, _) => eval_D c_semi p
  have hD : isDecompressor D := (eval_D_partrec c_semi).comp Computable.fst
  obtain ⟨cD, hcD⟩ := hU.2 D hD
  have h_D_bound : ∀ (x : BitString) (n : ℕ), C' x < (n : ℕ∞) → condK D x [] ≤ (n : ℕ∞) := by
    intro x n hx
    have h_f_dom : (f_semi (x, n)).Dom := (hdom_semi (x, n)).mpr hx
    have h_c_dom : (c_semi.eval (Encodable.encode (x, n))).Dom := by
      rw [hc_semi]
      change ((Part.ofOption (Encodable.decode (Encodable.encode (x, n)))).bind
        (fun a => Part.map Encodable.encode (f_semi a))).Dom
      rw [Encodable.encodek]
      dsimp [Part.ofOption, Part.map]
      rw [Part.bind_some]
      exact h_f_dom
    obtain ⟨r0, hr0⟩ := Part.dom_iff_mem.mp h_c_dom
    obtain ⟨k0, hk0⟩ := Nat.Partrec.Code.evaln_complete.mp hr0
    have h_len_x : x ∈ boundedPrograms x.length :=
      (mem_boundedPrograms_iff x x.length).mpr le_rfl
    let s0 := max k0 x.length
    have hk0_le : k0 ≤ s0 := le_max_left k0 x.length
    have hxlen_le : x.length ≤ s0 := le_max_right k0 x.length
    have h_evaln_s0 :
        (Nat.Partrec.Code.evaln s0 c_semi (Encodable.encode (x, n))).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨_, Nat.Partrec.Code.evaln_mono hk0_le hk0⟩
    have hx_mem_s0 : x ∈ boundedPrograms s0 := (mem_boundedPrograms_iff x s0).mpr hxlen_le
    have hx_in_cum_s0 : x ∈ cumList c_semi (s0 + 1) n := by
      dsimp [cumList]
      rw [List.mem_append]
      by_cases h_prev : x ∈ cumList c_semi s0 n
      · left; exact h_prev
      · right
        unfold new_items
        rw [List.mem_filter]
        have hx_bp : x ∈ boundedPrograms (s0 + 1) := by
          rw [mem_boundedPrograms_iff]
          omega
        have h_halt : step_halt c_semi (s0 + 1) n x = true := by
          unfold step_halt
          obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_exists.mpr ⟨r0, hk0⟩)
          have hs : k0 ≤ s0 + 1 := by omega
          exact Option.isSome_iff_exists.mpr ⟨r, Nat.Partrec.Code.evaln_mono hs hr⟩
        have h_not : decide (x ∉ cumList c_semi s0 n) = true :=
          decide_eq_true_eq.mpr h_prev
        refine ⟨hx_bp, ?_⟩
        exact Bool.and_eq_true_iff.mpr ⟨h_halt, h_not⟩
    have h_nodup_s0 := cumList_nodup c_semi (s0 + 1) n
    have h_mem_s0 : ∀ z ∈ cumList c_semi (s0 + 1) n, z ∈ {w | C' w < (n : ℕ∞)} := by
      intro z hz
      obtain ⟨_, hz_isSome⟩ := cumList_mem c_semi (s0 + 1) n z hz
      obtain ⟨r_z, hr_z⟩ := Option.isSome_iff_exists.mp hz_isSome
      have hz_eval : Encodable.encode r_z ∈ c_semi.eval (Encodable.encode (z, n)) :=
        Nat.Partrec.Code.evaln_sound hr_z
      rw [hc_semi] at hz_eval
      dsimp only at hz_eval
      rw [Encodable.encodek] at hz_eval
      dsimp [Part.ofOption, Part.map] at hz_eval
      rw [Part.bind_some] at hz_eval
      obtain ⟨hz_dom, _⟩ := hz_eval
      exact (hdom_semi (z, n)).mp hz_dom
    have h_card_s0 := list_length_le_ncard (cumList c_semi (s0 + 1) n)
      {w | C' w < (n : ℕ∞)} (hfin n) h_nodup_s0 h_mem_s0
    have h_K_lt : (cumList c_semi (s0 + 1) n).length < 2 ^ n :=
      lt_of_le_of_lt h_card_s0 (hcard n)
    let ix := (cumList c_semi (s0 + 1) n).idxOf x
    have h_ix_lt : ix < (cumList c_semi (s0 + 1) n).length :=
      List.idxOf_lt_length_iff.mpr hx_in_cum_s0
    have h_ix_lt_pow : ix < 2 ^ n := lt_trans h_ix_lt h_K_lt
    have h_exact_len : (exactLengthPrograms n).length = 2 ^ n := length_exactLengthPrograms n
    have h_ix_lt_exact : ix < (exactLengthPrograms n).length := by
      rw [h_exact_len]
      exact h_ix_lt_pow
    let p := (exactLengthPrograms n)[ix]'h_ix_lt_exact
    have hp_exact : p ∈ exactLengthPrograms n := List.getElem_mem h_ix_lt_exact
    have hp_len : p.length = n := exactLengthPrograms_length_eq n p hp_exact
    have hp_idx : thm08_idx p = ix := idx_spec n ix h_ix_lt_exact
    have h_check_s0 : check_stage c_semi p (s0 + 1) = true := by
      unfold check_stage thm08_check_stage_pair
      rw [hp_len, hp_idx]
      exact decide_eq_true_eq.mpr h_ix_lt
    have h_rfind_dom : (Nat.rfind (fun s => Part.some (check_stage c_semi p s))).Dom := by
      rw [Nat.rfind_dom]
      refine ⟨s0 + 1, by simp [h_check_s0], fun _ => Part.some_dom _⟩
    obtain ⟨s_found, hs_found⟩ := Part.dom_iff_mem.mp h_rfind_dom
    have hs_found_spec := (Nat.mem_rfind).mp hs_found
    have hs_check : check_stage c_semi p s_found = true := by
      have h1 := hs_found_spec.1
      simp only [Part.mem_some_iff] at h1
      exact h1.symm
    have hs_found_le : s_found ≤ s0 + 1 := by
      by_contra hc
      have h_lt : s0 + 1 < s_found := lt_of_not_ge hc
      have h_false := hs_found_spec.2 h_lt
      rw [Part.mem_some_iff] at h_false
      rw [h_check_s0] at h_false
      contradiction
    have h_ix_lt_found : ix < (cumList c_semi s_found n).length := by
      dsimp [check_stage] at hs_check
      unfold thm08_check_stage_pair at hs_check
      rw [hp_len, hp_idx] at hs_check
      exact decide_eq_true_eq.mp hs_check
    have h_s0_eq : (cumList c_semi (s0 + 1) n)[ix]'h_ix_lt = x :=
      List.getElem_idxOf h_ix_lt
    have h_sub_found : cumList c_semi s_found n <+: cumList c_semi (s0 + 1) n :=
      cumList_prefix_le c_semi hs_found_le n
    have h_get_found : (cumList c_semi s_found n)[ix]'h_ix_lt_found = x := by
      have h_pref_get := h_sub_found.getElem h_ix_lt_found
      rw [h_pref_get, h_s0_eq]
    have h_D_prod : x ∈ eval_D c_semi p := by
      unfold eval_D
      rw [Part.mem_bind_iff]
      refine ⟨s_found, hs_found, ?_⟩
      dsimp [Part.ofOption]
      rw [hp_len, hp_idx]
      have h_get_opt : (cumList c_semi s_found n)[ix]? = some x := by
        rw [List.getElem?_eq_getElem h_ix_lt_found, h_get_found]
      rw [h_get_opt]
      exact Part.mem_some x
    have h_D_le : condK D x [] ≤ (n : ℕ∞) := by
      rw [condK_le_iff D x [] n]
      refine ⟨p, hp_len.le, h_D_prod⟩
    exact h_D_le
  refine ⟨cD + 1, ?_⟩
  intro x
  cases hCx : C' x with
  | top =>
    exact le_top
  | coe m =>
    have h_lt : C' x < ((m + 1 : ℕ) : ℕ∞) := by
      rw [hCx]
      exact_mod_cast Nat.lt_succ_self m
    have h_cond_le := h_D_bound x (m + 1) h_lt
    have h_plain_le := hcD x []
    have h_step : condK D x [] + (cD : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) + (cD : ℕ∞) := by gcongr
    have h_arith : ((m + 1 : ℕ) : ℕ∞) + (cD : ℕ∞) = (m : ℕ∞) + ((cD + 1 : ℕ) : ℕ∞) := by
      norm_cast
      omega
    calc plainK U x
      _ ≤ condK D x [] + (cD : ℕ∞) := h_plain_le
      _ ≤ ((m + 1 : ℕ) : ℕ∞) + (cD : ℕ∞) := h_step
      _ = (m : ℕ∞) + ((cD + 1 : ℕ) : ℕ∞) := h_arith

/-! ### Theorem 9: axiomatic characterization -/

/-- **Theorem 9.** A natural-valued function satisfying the enumerability axiom,
the non-growth axiom and the calibration axiom coincides with plain complexity up
to an additive constant. -/
lemma plainK_le_of_isUpperSemicomputable_of_card_le_two_pow (U : Map)
    (hU : isOptimalConditional U) (k : BitString → ℕ)
    (henum : IsUpperSemicomputable (fun x => (k x : ℕ∞)))
    (c₂ : ℕ)
    (hcard_upper : ∀ n : ℕ, {x : BitString | k x < n}.ncard ≤ 2 ^ (n + c₂))
    (hfin : ∀ n : ℕ, {x : BitString | k x < n}.Finite) :
    ∃ c : ℕ, ∀ x : BitString, plainK U x ≤ (k x : ℕ∞) + (c : ℕ∞) := by
  let C' : BitString → ℕ∞ := fun x => ((k x + c₂ + 1 : ℕ) : ℕ∞)
  have hsemi : IsUpperSemicomputable C' := by
    dsimp [IsUpperSemicomputable] at henum ⊢
    obtain ⟨f, hf_part, hf_dom⟩ := henum
    let g : BitString × ℕ →. Unit := fun p =>
      if hc : c₂ + 1 < p.2 then f (p.1, p.2 - (c₂ + 1)) else Part.none
    have hg_part : Partrec g := by
      have h_cond : Computable (fun p : BitString × ℕ => decide (c₂ + 1 < p.2)) :=
        Computable.natLt.comp (Computable.pair (Computable.const (c₂ + 1)) Computable.snd)
      have h_sub : Computable (fun p : BitString × ℕ => p.2 - (c₂ + 1)) :=
        (Primrec.to_comp Primrec.nat_sub).comp
          (Computable.pair Computable.snd (Computable.const (c₂ + 1)))
      have h_arg : Computable (fun p : BitString × ℕ => (p.1, p.2 - (c₂ + 1))) :=
        Computable.pair Computable.fst h_sub
      have h_f_comp : Partrec (fun p : BitString × ℕ => f (p.1, p.2 - (c₂ + 1))) :=
        Partrec.comp hf_part h_arg
      exact (Partrec.cond h_cond.to₂ h_f_comp Partrec.none).of_eq (by
        intro p; dsimp [g]
        cases h : decide (c₂ + 1 < p.2)
        · dsimp; rw [if_neg (of_decide_eq_false h)]
        · dsimp; rw [if_pos (of_decide_eq_true h)])
    use g
    refine ⟨hg_part, fun p => ?_⟩
    dsimp [g]
    split_ifs with hc
    · rw [hf_dom]
      constructor
      · intro h
        have hlt : k p.1 < p.2 - (c₂ + 1) := WithTop.coe_lt_coe.mp h
        have : k p.1 + c₂ + 1 < p.2 := by omega
        exact WithTop.coe_lt_coe.mpr this
      · intro h
        have hlt : k p.1 + c₂ + 1 < p.2 := WithTop.coe_lt_coe.mp h
        have : k p.1 < p.2 - (c₂ + 1) := by omega
        exact_mod_cast this
    · constructor
      · intro h
        exact False.elim h
      · intro h
        have hlt : k p.1 + c₂ + 1 < p.2 := WithTop.coe_lt_coe.mp h
        omega
  have hfin_C' : ∀ n : ℕ, {x : BitString | C' x < (n : ℕ∞)}.Finite := by
    intro n
    by_cases hn : c₂ + 1 < n
    · have h_eq : {x : BitString | C' x < (n : ℕ∞)} = {x : BitString | k x < n - (c₂ + 1)} := by
        ext x
        simp only [Set.mem_setOf_eq, C']
        constructor
        · intro h
          have : k x + c₂ + 1 < n := WithTop.coe_lt_coe.mp h
          omega
        · intro h
          have : k x + c₂ + 1 < n := by omega
          exact WithTop.coe_lt_coe.mpr this
      rw [h_eq]
      exact hfin (n - (c₂ + 1))
    · have h_empty : {x : BitString | C' x < (n : ℕ∞)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, C']
        intro h
        have : k x + c₂ + 1 < n := WithTop.coe_lt_coe.mp h
        omega
      rw [h_empty]
      exact Set.finite_empty
  have hcard_C' : ∀ n : ℕ, {x : BitString | C' x < (n : ℕ∞)}.ncard < 2 ^ n := by
    intro n
    by_cases hn : c₂ + 1 < n
    · have h_eq : {x : BitString | C' x < (n : ℕ∞)} = {x : BitString | k x < n - (c₂ + 1)} := by
        ext x
        simp only [Set.mem_setOf_eq, C']
        constructor
        · intro h
          have : k x + c₂ + 1 < n := WithTop.coe_lt_coe.mp h
          omega
        · intro h
          have : k x + c₂ + 1 < n := by omega
          exact WithTop.coe_lt_coe.mpr this
      rw [h_eq]
      have h_card := hcard_upper (n - (c₂ + 1))
      have h_pow_le : 2 ^ (n - (c₂ + 1) + c₂) ≤ 2 ^ (n - 1) := by
        apply Nat.pow_le_pow_right (by decide)
        omega
      have h_lt : 2 ^ (n - 1) < 2 ^ n := by
        apply Nat.pow_lt_pow_of_lt (by decide)
        omega
      omega
    · have h_empty : {x : BitString | C' x < (n : ℕ∞)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, C']
        intro h
        have : k x + c₂ + 1 < n := WithTop.coe_lt_coe.mp h
        omega
      rw [h_empty, Set.ncard_empty]
      exact Nat.two_pow_pos n
  obtain ⟨c_1, hc_1⟩ :=
    plainK_le_of_isUpperSemicomputable_of_card_lt_two_pow U hU C' hsemi hfin_C' hcard_C'
  refine ⟨c₂ + 1 + c_1, fun x => ?_⟩
  have h1 := hc_1 x
  dsimp [C'] at h1
  have h2 : ((k x + c₂ + 1 : ℕ) : ℕ∞) + (c_1 : ℕ∞) = (k x : ℕ∞) + ((c₂ + 1 + c_1 : ℕ) : ℕ∞) := by
    push_cast
    ring
  rwa [h2] at h1

end Kolmogorov
