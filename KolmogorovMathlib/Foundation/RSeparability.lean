import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Computability.Reduce
import KolmogorovMathlib.Complexity.Uncomputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.Complexity.Properties
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.DifferentDecompressors
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# `r`-separability of complexity sets

A pair of disjoint sets is `r`-separable when a computable set separates them. The results here
decide this for the sets attached to plain complexity:
`isRSeparable_upperGraph_plainK` for the upper graph `{(x, k) | C(x) < k}`,
`isRSeparable_compressibleStrings` for the compressible strings, and
`isRSeparable_of_manyOneReducible` transporting the property along `m`-reductions.
`exists_isEnumerableSet_not_isRSeparable` shows the property is not automatic: some enumerable
set fails it. The supporting lemmas provide the computable stage filters
(`computable_decodedEvalnFilter`, `computable_boundReachedCheck`) and the bound
`exists_plainK_le_plainKNat_encode` between a string and its code.

Source: SUV, Exercise 12.
-/

namespace Kolmogorov
open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

private lemma IsRE.exists_nat {β : Type*} [Primcodable β] {R : β → ℕ → Prop}
    (hR : IsRE (fun p : β × ℕ => R p.1 p.2)) :
    IsRE (fun b => ∃ n : ℕ, R b n) := by
  obtain ⟨g, hg_partrec, hg_dom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg_partrec
  let check : β → ℕ → Bool := fun b m =>
    (Nat.Partrec.Code.evaln (m.unpair.2 + 1) c (Encodable.encode (b, m.unpair.1))).isSome
  have hcheck : Computable₂ check := by
    have h_steps : Computable (fun q : β × ℕ => q.2.unpair.2 + 1) := by
      have hp : Primrec (fun q : β × ℕ => q.2.unpair.2 + 1) :=
        Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      exact Primrec.to_comp hp
    have h_input : Computable (fun q : β × ℕ => Encodable.encode (q.1, q.2.unpair.1)) := by
      have h_u1 : Computable (fun q : β × ℕ => q.2.unpair.1) :=
        Computable.fst.comp (Computable.unpair.comp Computable.snd)
      exact Computable.comp Computable.encode (Computable.pair Computable.fst h_u1)
    have h_evaln : Primrec (fun p : ℕ × ℕ => Nat.Partrec.Code.evaln p.1 c p.2) := by
      convert Nat.Partrec.Code.primrec_evaln using 1
      constructor <;> intro h
      · convert Nat.Partrec.Code.primrec_evaln using 1
      · convert h.comp (show Primrec (fun p : ℕ × ℕ => ((p.1, c), p.2)) from ?_) using 1
        exact Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd
    have h_evaln_comp : Computable (fun q : β × ℕ =>
        Nat.Partrec.Code.evaln (q.2.unpair.2 + 1) c (Encodable.encode (q.1, q.2.unpair.1))) :=
      Computable.comp (Primrec.to_comp h_evaln) (Computable.pair h_steps h_input)
    exact Computable.comp (Primrec.to_comp Primrec.option_isSome) h_evaln_comp
  have h_rfind : Partrec (fun b => Nat.rfind (fun m => Part.some (check b m))) :=
    Partrec.rfind hcheck.partrec
  refine ⟨fun b => (Nat.rfind (fun m => Part.some (check b m))).map (fun _ => ()),
    h_rfind.map (Computable.const ()).to₂, ?_⟩
  intro b
  change (Nat.rfind (fun m => Part.some (check b m))).Dom ↔ _
  rw [Nat.rfind_dom]; simp_rw [Part.mem_some_iff]
  have hrfind_simp : (∃ m, true = check b m ∧ ∀ {k : ℕ}, k < m →
      (Part.some (check b k)).Dom) ↔ (∃ m, check b m = true) := by
    constructor
    · rintro ⟨m, hm, _⟩; exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩; exact ⟨m, hm.symm, fun _ => Part.some_dom _⟩
  rw [hrfind_simp]
  have code_dom (p : β × ℕ) : (g p).Dom ↔ ∃ k,
    (Nat.Partrec.Code.evaln k c (Encodable.encode p)).isSome := by
    have h_eval : (c.eval (Encodable.encode p)).Dom ↔ (g p).Dom := by
      rw [hc]; aesop
    convert h_eval.symm using 1
    simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete]
    constructor
    · rintro ⟨k, hk⟩
      cases h : Nat.Partrec.Code.evaln k c (Encodable.encode p) <;> aesop
    · rintro ⟨y, k, hk⟩
      exact ⟨k, by aesop⟩
  constructor
  · rintro ⟨m, hm⟩
    dsimp [check] at hm
    have h_dom : (g (b, m.unpair.1)).Dom := (code_dom (b, m.unpair.1)).mpr ⟨m.unpair.2 + 1, hm⟩
    exact ⟨m.unpair.1, (hg_dom (b, m.unpair.1)).mp h_dom⟩
  · rintro ⟨n, hn⟩
    have h_dom : (g (b, n)).Dom := (hg_dom (b, n)).mpr hn
    obtain ⟨k, hk⟩ := (code_dom (b, n)).mp h_dom
    refine ⟨Nat.pair n k, ?_⟩
    dsimp [check]
    rw [Nat.unpair_pair]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Option.isSome_iff_exists.mpr
      ⟨x, Option.mem_def.mp (Nat.Partrec.Code.evaln_mono
        (Nat.le_succ k) (Option.mem_def.mpr hx))⟩

private lemma IsEnumerableSet.image {α β : Type*} [Primcodable α] [Primcodable β]
    {V : Set α} (hV : IsEnumerableSet V) {f : α → β} (hf : Computable f) :
    IsEnumerableSet (f '' V) := by
  change IsRE (fun b => b ∈ f '' V)
  obtain ⟨gV, hgV_partrec, hgV_dom⟩ := hV
  have h_eq : (fun b => b ∈ f '' V) = (fun b => ∃ n : ℕ,
      ∃ a : α, Encodable.decode (α := α) n = some a ∧ a ∈ V ∧ f a = b) := by
    ext b
    constructor
    · rintro ⟨a, haV, rfl⟩
      exact ⟨Encodable.encode a, a, Encodable.encodek a, haV, rfl⟩
    · rintro ⟨n, a, _, haV, rfl⟩
      exact ⟨a, haV, rfl⟩
  rw [h_eq]
  apply IsRE.exists_nat
  let g₂ : β × ℕ →. Unit := fun p =>
    (Part.ofOption (Encodable.decode (α := α) p.2)).bind (fun a =>
      (gV a).bind (fun _ =>
                    if Encodable.encode (f a)
        == Encodable.encode p.1 then Part.some () else Part.none))
  have hg₂_partrec : Partrec g₂ := by
    have h1 : Partrec (fun p : β × ℕ => Part.ofOption (Encodable.decode (α := α) p.2)) :=
      Computable.ofOption (Computable.decode.comp Computable.snd)
    have h2 : Partrec₂ (fun (p : β × ℕ) (a : α) =>
        (gV a).bind (fun _ =>
                      if Encodable.encode (f a)
          == Encodable.encode p.1 then Part.some () else Part.none)) := by
      have hb1 : Partrec (fun q : (β × ℕ) × α => gV q.2) := hgV_partrec.comp Computable.snd
      have hb2 : Partrec₂ (fun (q : (β × ℕ) × α) (_ : Unit) =>
          if Encodable.encode (f q.2)
            == Encodable.encode q.1.1 then (Part.some () : Part Unit) else Part.none) := by
        have hc1 : Computable (fun q : (β × ℕ) × α => Encodable.encode (f q.2)) :=
          Computable.encode.comp (hf.comp Computable.snd)
        have hc2 : Computable (fun q : (β × ℕ) × α => Encodable.encode q.1.1) :=
          Computable.encode.comp (Computable.fst.comp Computable.fst)
        have h_beq : Computable (fun q : (β × ℕ) × α =>
                                  (Encodable.encode (f q.2) == Encodable.encode q.1.1)) :=
          Primrec.to_comp Primrec.beq |>.comp (Computable.pair hc1 hc2)
        have h_none : Computable (fun _ : (β × ℕ) × α => (none : Option Unit)) :=
          Computable.const none
        have h_some : Computable (fun _ : (β × ℕ) × α => (some () : Option Unit)) :=
          Computable.const (some ())
        have hc_eq : Computable (fun q : (β × ℕ) × α =>
            bif Encodable.encode (f q.2)
              == Encodable.encode q.1.1 then (some () : Option Unit) else (none : Option Unit)) :=
          Computable.cond h_beq h_some h_none
        have hc_eq' : Partrec (fun q : (β × ℕ) × α =>
            if Encodable.encode (f q.2)
              == Encodable.encode q.1.1 then (Part.some () : Part Unit) else Part.none) := by
          have h_comp : Computable (fun q : (β × ℕ) × α =>
              if Encodable.encode (f q.2)
                == Encodable.encode q.1.1 then (some () : Option Unit) else (none : Option
                                                                              Unit)) := by
            convert hc_eq using 1
            ext q
            cases Encodable.encode (f q.2) == Encodable.encode q.1.1 <;> rfl
          have h_part := Computable.ofOption h_comp
          convert h_part using 1
          ext q
          dsimp [Part.ofOption]
          split_ifs <;> rfl
        exact hc_eq'.comp Computable.fst |>.to₂
      exact Partrec.bind hb1 hb2
    exact Partrec.bind h1 h2
  refine ⟨g₂, hg₂_partrec, ?_⟩
  intro p
  dsimp [g₂]
  rw [Part.bind_dom]
  constructor
  · rintro ⟨h_dom, hstep⟩
    have h_dom_isSome : (Encodable.decode (α := α) p.2).isSome := by
      rwa [Part.ofOption_dom] at h_dom
    obtain ⟨a, ha_eq⟩ := Option.isSome_iff_exists.mp h_dom_isSome
    refine ⟨a, ha_eq, ?_⟩
    have ha_mem : a ∈ Part.ofOption (Encodable.decode (α := α) p.2) := by
      rw [Part.mem_ofOption, ha_eq]
      exact Option.mem_def.mpr rfl
    have h_get : (Part.ofOption (Encodable.decode (α := α) p.2)).get h_dom = a :=
      Part.get_eq_of_mem ha_mem h_dom
    rw [h_get] at hstep
    rw [Part.bind_dom] at hstep
    obtain ⟨hV_dom, hstep2⟩ := hstep
    rw [hgV_dom] at hV_dom
    refine ⟨hV_dom, ?_⟩
    split_ifs at hstep2 with h_if
    · rw [beq_iff_eq] at h_if
      exact Encodable.encode_injective h_if
    · contradiction
  · rintro ⟨a, hdec, haV, heq⟩
    have ha_mem : a ∈ Part.ofOption (Encodable.decode (α := α) p.2) := by
      rw [Part.mem_ofOption, hdec]
      exact Option.mem_def.mpr rfl
    have h_dom : (Part.ofOption (Encodable.decode (α := α) p.2)).Dom := by
      rw [Part.ofOption_dom, hdec]
      rfl
    refine ⟨h_dom, ?_⟩
    have h_get : (Part.ofOption (Encodable.decode (α := α) p.2)).get h_dom = a :=
      Part.get_eq_of_mem ha_mem h_dom
    rw [h_get]
    rw [Part.bind_dom]
    rw [hgV_dom]
    refine ⟨haV, ?_⟩
    have h_eq : (Encodable.encode (f a) == Encodable.encode p.1) = true := by
      rw [beq_iff_eq, heq]
    rw [h_eq]
    dsimp
    trivial

private def listMemBool {α : Type*} [Encodable α] (L : List α) (a : α) : Bool :=
  match L with
  | [] => false
  | x :: L' => (Encodable.encode x == Encodable.encode a) || listMemBool L' a

private lemma computable_listMemBool {α : Type*} [Primcodable α] (L : List α) :
    Computable (listMemBool L) := by
  induction L with
  | nil =>
    exact Computable.const false
  | cons x L' ih =>
    dsimp [listMemBool]
    have h_beq : Computable (fun a : α => Encodable.encode x == Encodable.encode a) :=
      Primrec.to_comp Primrec.beq
        |>.comp (Computable.pair (Computable.const (Encodable.encode x)) Computable.encode)
    have h_bif : Computable (fun a : α =>
                              bif Encodable.encode x
      == Encodable.encode a then true else listMemBool L' a) :=
      Computable.cond h_beq (Computable.const true) ih
    have h_eq : (fun a : α => (Encodable.encode x == Encodable.encode a) || listMemBool L' a) =
        (fun a => bif Encodable.encode x == Encodable.encode a then true else listMemBool L' a) :=
          by
      ext a
      cases Encodable.encode x == Encodable.encode a <;> rfl
    rwa [h_eq]

private lemma listMemBool_iff {α : Type*} [Encodable α] (L : List α) (a : α) :
    listMemBool L a = true ↔ a ∈ L := by
  induction L with
  | nil => simp [listMemBool]
  | cons x L' ih =>
    dsimp [listMemBool]
    rw [Bool.or_eq_true, beq_iff_eq, Encodable.encode_inj, ih, List.mem_cons]
    tauto

private lemma isDecidableSet_of_finite {α : Type*} [Primcodable α] (S : Set α)
    (hS : S.Finite) : IsDecidableSet S := by
  let L := hS.toFinset.toList
  refine ⟨listMemBool L, computable_listMemBool L, fun a => ?_⟩
  rw [listMemBool_iff]
  change a ∈ hS.toFinset.toList ↔ a ∈ S
  rw [Finset.mem_toList]
  exact hS.mem_toFinset

private lemma mem_compressibleWords_zero_iff (U : Map) (k : ℕ) (hk : 0 < k) (x : BitString) :
    x ∈ compressibleWords U [] (k - 1) ↔ plainK U x < (k : ℕ∞) := by
  have hk_eq : (k : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; omega
  rw [hk_eq, ENat.lt_add_one_iff (ENat.coe_ne_top _)]
  constructor
  · intro hx
    rw [compressibleWords, Finset.mem_filter] at hx
    exact hx.2
  · intro hx
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, hx⟩
    dsimp [plainK, condK] at hx
    have h_le : ∃ p, produces U p [] x ∧ (p.length : ℕ∞) ≤ (k - 1 : ℕ∞) := by
      by_contra h_none
      push_neg at h_none
      have h_lb : ∀ n ∈ candidateLengths U x [], (k : ℕ∞) ≤ n := by
        rintro n ⟨p, hp, rfl⟩
        have h_not := h_none p hp
        have hp_gt : k - 1 < p.length := ENat.coe_lt_coe.mp h_not
        have h_k : k ≤ p.length := by omega
        exact ENat.coe_le_coe.mpr h_k
      have h_inf_lb : (k : ℕ∞) ≤ sInf (candidateLengths U x []) := le_sInf h_lb
      have h_lt : (k - 1 : ℕ∞) < (k : ℕ∞) := by norm_cast; omega
      have h_ge : (k : ℕ∞) ≤ (k - 1 : ℕ∞) := le_trans h_inf_lb hx
      exact lt_irrefl _ (lt_of_lt_of_le h_lt h_ge)
    obtain ⟨p, hp_prod, hp_len⟩ := h_le
    have hpLen : p.length ≤ k - 1 := ENat.coe_le_coe.mp hp_len
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    refine ⟨p, mem_programsLe (k - 1) p hpLen, ?_⟩
    exact progToOut_eq_some.mpr hp_prod

private lemma upperGraph_separable_of_bounded (U : Map) (N : ℕ)
    (V : Set (BitString × ℕ)) (hV_bounded : ∀ p ∈ V, p.2 ≤ N)
    (hdisj : Disjoint {p : BitString × ℕ | plainK U p.1 < (p.2 : ℕ∞)} V) :
    ∃ R : Set (BitString × ℕ), IsDecidableSet R ∧ V ⊆ R ∧
      Disjoint {p : BitString × ℕ | plainK U p.1 < (p.2 : ℕ∞)} R := by
  let F_fin : Set (BitString × ℕ) :=
    { p : BitString × ℕ | p.2 ≤ N ∧ plainK U p.1 < (p.2 : ℕ∞) }
  have hF_fin : F_fin.Finite := by
    have h_eq : F_fin = ⋃ (k ∈ Set.Iic N), { x : BitString | plainK U x < (k : ℕ∞) } ×ˢ {k} := by
      ext ⟨x, k⟩
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hk, hx⟩
        exact ⟨k, hk, hx, rfl⟩
      · rintro ⟨k', hk', hx, rfl⟩
        exact ⟨hk', hx⟩
    rw [h_eq]
    refine Set.Finite.biUnion (Set.finite_Iic N) (fun k hk => ?_)
    have h_k_fin : { x : BitString | plainK U x < (k : ℕ∞) }.Finite := by
      by_cases hk0 : k = 0
      · subst hk0
        have h_emp : { x : BitString | plainK U x < (0 : ℕ∞) } = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact not_lt_bot
        exact h_emp ▸ Set.finite_empty
      · have hp_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have h_sub_comp :
            { x : BitString | plainK U x < (k : ℕ∞) } =
              (compressibleWords U [] (k - 1) : Set BitString) := by
          ext x
          exact (mem_compressibleWords_zero_iff U k hp_pos x).symm
        rw [h_sub_comp]
        exact (compressibleWords U [] (k - 1)).finite_toSet
    exact h_k_fin.prod (Set.finite_singleton k)
  obtain ⟨chk_F, hchk_F_comp, hchk_F_iff⟩ := isDecidableSet_of_finite F_fin hF_fin
  let chk_R : BitString × ℕ → Bool := fun p => (p.2 - N == 0) && !(chk_F p)
  have hchk_R_comp : Computable chk_R := by
    have h_sub : Computable (fun p : BitString × ℕ => p.2 - N) :=
      (Primrec.to_comp Primrec.nat_sub).comp (Computable.pair Computable.snd (Computable.const N))
    have h_le : Computable (fun p : BitString × ℕ => p.2 - N == 0) :=
      Computable.of_eq ((Primrec.to_comp Primrec.beq).comp (Computable.pair h_sub (Computable.const
                                                                                    0)))
        (by intro p; rfl)
    have h_notF : Computable (fun p : BitString × ℕ => !(chk_F p)) :=
      Computable.cond hchk_F_comp (Computable.const false) (Computable.const true)
    have h_and : Computable (fun p : BitString × ℕ =>
                              bif p.2 - N == 0 then !(chk_F p) else false) :=
      Computable.cond h_le h_notF (Computable.const false)
    have h_eq : chk_R = (fun p => bif p.2 - N == 0 then !(chk_F p) else false) := by
      ext p
      dsimp [chk_R]
      cases p.2 - N == 0 <;> rfl
    rwa [h_eq]
  refine ⟨{p | chk_R p = true}, ⟨chk_R, hchk_R_comp, fun p => Iff.rfl⟩, ?_, ?_⟩
  · intro p hp
    change chk_R p = true
    dsimp [chk_R]
    rw [Bool.and_eq_true, beq_iff_eq, Nat.sub_eq_zero_iff_le, Bool.not_eq_true']
    refine ⟨hV_bounded p hp, ?_⟩
    by_contra hchk
    rw [Bool.not_eq_false] at hchk
    have hp_F : p ∈ F_fin := (hchk_F_iff p).mp hchk
    rw [Set.disjoint_left] at hdisj
    exact hdisj hp_F.2 hp
  · rw [Set.disjoint_left]
    intro p hp_graph hp_R
    change chk_R p = true at hp_R
    dsimp [chk_R] at hp_R
    rw [Bool.and_eq_true, beq_iff_eq, Nat.sub_eq_zero_iff_le, Bool.not_eq_true'] at hp_R
    obtain ⟨hp_leN, hp_notF⟩ := hp_R
    have hchk_true : chk_F p = true := (hchk_F_iff p).mpr ⟨hp_leN, hp_graph⟩
    rw [hp_notF] at hchk_true
    exact Bool.noConfusion hchk_true

/-- The stage-indexed filter that decodes a pair and keeps it once the enumerating code has
halted on it within the allotted number of steps is computable. -/
private lemma computable_decodedEvalnFilter (c : Nat.Partrec.Code) :
    Computable (fun m : ℕ =>
      match Encodable.decode (α := BitString × ℕ) m.unpair.1 with
      | some p =>
        if (Nat.Partrec.Code.evaln (m.unpair.2 + 1) c (Encodable.encode p)).isSome
        then some p
        else none
      | none => none) := by
  have h1 : Computable (fun m : ℕ => Encodable.decode (α := BitString × ℕ) m.unpair.1) :=
    Computable.decode.comp (Computable.fst.comp Computable.unpair)
  have h_steps : Computable (fun p : ℕ × (BitString × ℕ) => p.1.unpair.2 + 1) :=
    Computable.succ.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst))
  have h_input : Computable (fun p : ℕ × (BitString × ℕ) => Encodable.encode p.2) :=
    Computable.encode.comp Computable.snd
  have h_evaln : Primrec (fun p : ℕ × ℕ => Nat.Partrec.Code.evaln p.1 c p.2) := by
    convert Nat.Partrec.Code.primrec_evaln using 1
    constructor <;> intro h
    · convert Nat.Partrec.Code.primrec_evaln using 1
    · convert h.comp (show Primrec (fun p : ℕ × ℕ => ((p.1, c), p.2)) from ?_) using 1
      exact Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd
  have h_isSome : Computable (fun p : ℕ × (BitString × ℕ) =>
      (Nat.Partrec.Code.evaln (p.1.unpair.2 + 1) c (Encodable.encode p.2)).isSome) :=
    (Primrec.to_comp Primrec.option_isSome).comp (Computable.comp (Primrec.to_comp h_evaln)
                                                   (Computable.pair h_steps h_input))
  have h_cond : Computable (fun p : ℕ × (BitString × ℕ) =>
      bif (Nat.Partrec.Code.evaln (p.1.unpair.2
                                    + 1) c (Encodable.encode p.2)).isSome then (some p.2 : Option
                                                                                 (BitString ×
                                                                                   ℕ))
        else none) :=
    Computable.cond h_isSome (Computable.option_some.comp Computable.snd) (Computable.const (none
                                                                                              :
      Option (BitString × ℕ)))
  have h_cond' : Computable₂ (fun (m : ℕ) (p : BitString × ℕ) =>
      if (Nat.Partrec.Code.evaln (m.unpair.2
                                   + 1) c (Encodable.encode p)).isSome then some p
        else none) := by
    have h_eq : (fun (m : ℕ) (p : BitString × ℕ) =>
        if (Nat.Partrec.Code.evaln (m.unpair.2
                                     + 1) c (Encodable.encode p)).isSome then some p else none) =
        (fun m p =>
          bif (Nat.Partrec.Code.evaln (m.unpair.2
                                        + 1) c (Encodable.encode p)).isSome then some p
          else none) := by
      ext m p
      cases (Nat.Partrec.Code.evaln (m.unpair.2 + 1) c (Encodable.encode p)).isSome <;> rfl
    rw [h_eq]
    exact h_cond.to₂
  have h_full := Computable.option_bind h1 h_cond'
  exact h_full.of_eq (fun m => by
    cases Encodable.decode (α := BitString × ℕ) (Nat.unpair m).1 <;> rfl)

/-- Testing whether a filtered pair has reached a given bound is computable in the bound and
the stage. -/
private lemma computable_boundReachedCheck {check_V : ℕ → Option (BitString × ℕ)}
    (hcheck_V : Computable check_V) :
    Computable₂ (fun (M m : ℕ) =>
      match check_V m with
      | some p => M - p.2 == 0
      | none => false) := by
  have h_fst1 : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have h_snd2 : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have h_sub : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) => p.1.1 - p.2.2) :=
    (Primrec.to_comp Primrec.nat_sub).comp (Computable.pair h_fst1 h_snd2)
  have h_le_comp : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) => p.1.1 - p.2.2 == 0) :=
    Computable.of_eq ((Primrec.to_comp Primrec.beq).comp (Computable.pair h_sub (Computable.const
                                                                                  0)))
      (by intro p; rfl)
  have h_check_M : Computable (fun q : ℕ × ℕ =>
      match check_V q.2 with
      | some p => q.1 - p.2 == 0
      | none => false) := by
    have h_bind : Computable (fun q : ℕ × ℕ => (check_V q.2).bind (fun p =>
                                                                    if q.1 - p.2
      == 0 then (some () : Option Unit) else none)) := by
      have hb : Computable₂ (fun (q : ℕ × ℕ) (p : BitString × ℕ) =>
                              if q.1 - p.2 == 0 then (some () : Option Unit) else none) := by
        have hc_bif : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) =>
                                   bif p.1.1 - p.2.2
          == 0 then (some () : Option Unit) else (none : Option Unit)) :=
          Computable.cond h_le_comp (Computable.const (some ()))
            (Computable.const (α := (ℕ × ℕ) × (BitString × ℕ)) (none : Option Unit))
        have hc_if : Computable (fun p : (ℕ × ℕ) × (BitString × ℕ) =>
                                  if p.1.1 - p.2.2
          == 0 then (some () : Option Unit) else none) := by
          convert hc_bif using 1
          ext p
          cases p.1.1 - p.2.2 == 0 <;> rfl
        exact hc_if.to₂
      exact Computable.option_bind (hcheck_V.comp Computable.snd) hb
    have h_isSome : Computable (fun o : Option Unit => o.isSome) :=
      Primrec.to_comp Primrec.option_isSome
    have h_full : Computable (fun q : ℕ × ℕ => ((check_V q.2).bind (fun p =>
                                                                     if q.1 - p.2
      == 0 then (some () : Option Unit) else none)).isSome) :=
      h_isSome.comp h_bind
    convert h_full using 1
    ext q
    dsimp
    cases h : check_V q.2 with
    | none => rfl
    | some p =>
      dsimp
      cases q.1 - p.2 == 0 <;> rfl
  exact h_check_M.to₂

/-- The plain complexity of a string is bounded by the plain complexity of its code as a
natural number, up to an additive constant. -/
private lemma exists_plainK_le_plainKNat_encode (U : Map) (hU : isOptimalConditional U) :
    ∃ C_str : ℕ, ∀ s : BitString,
      plainK U s ≤ plainKNat U (Encodable.encode s) + (C_str : ℕ∞) := by
  let g_dec (n : ℕ) : BitString :=
    match Encodable.decode (α := BitString) n with | some s => s | none => []
  have hg_dec : Computable g_dec :=
    (Computable.option_getD Computable.decode (Computable.const ([] : BitString))).of_eq
      (fun n => by dsimp [g_dec]; cases (Encodable.decode (α := BitString) n) <;> rfl)
  obtain ⟨C_dec, hC_dec⟩ :=
    plainK_map_le U hU (fun s => g_dec (decodeBits s)) (hg_dec.comp decodeBits_computable)
  refine ⟨C_dec, fun s => ?_⟩
  have h1 := hC_dec (Nat.bits (Encodable.encode s))
  dsimp [g_dec, plainKNat] at h1 ⊢
  rw [decodeBits_natBits, Encodable.encodek] at h1
  dsimp [g_dec] at h1
  exact h1

private lemma exists_bounded_of_disjoint_upperGraph (U : Map) (hU : isOptimalConditional U)
    (V : Set (BitString × ℕ)) (hV : IsEnumerableSet V)
    (hdisj : Disjoint {p : BitString × ℕ | plainK U p.1 < (p.2 : ℕ∞)} V) :
    ∃ N : ℕ, ∀ p ∈ V, p.2 ≤ N := by
  by_contra h_unb
  push_neg at h_unb
  obtain ⟨gV, hgV_partrec, hgV_dom⟩ := hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hgV_partrec
  let check_V : ℕ → Option (BitString × ℕ) := fun m =>
    match Encodable.decode (α := BitString × ℕ) m.unpair.1 with
    | some p =>
      if (Nat.Partrec.Code.evaln (m.unpair.2 + 1) c (Encodable.encode p)).isSome
      then some p
      else none
    | none => none
  have hcheck_V : Computable check_V := computable_decodedEvalnFilter c
  let check_M : ℕ → ℕ → Bool := fun M m =>
    match check_V m with
    | some p => M - p.2 == 0
    | none => false
  have hcheck_M : Computable₂ check_M := computable_boundReachedCheck hcheck_V
  have h_ex_M : ∀ M : ℕ, ∃ m : ℕ, check_M M m = true := by
    intro M
    obtain ⟨p, hpV, hpM⟩ := h_unb M
    have hp_dom : (gV p).Dom := (hgV_dom p).mpr hpV
    have code_dom : ∃ k, (Nat.Partrec.Code.evaln k c (Encodable.encode p)).isSome := by
      have h_eval : (c.eval (Encodable.encode p)).Dom ↔ (gV p).Dom := by rw [hc]; aesop
      have h1 : (c.eval (Encodable.encode p)).Dom := h_eval.mpr hp_dom
      simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete] at h1
      obtain ⟨y, k, hk⟩ := h1
      exact ⟨k, by aesop⟩
    obtain ⟨k, hk⟩ := code_dom
    refine ⟨Nat.pair (Encodable.encode p) k, ?_⟩
    dsimp [check_M, check_V]
    rw [Nat.unpair_pair, Encodable.encodek]
    dsimp
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    have h_evaln_succ : (Nat.Partrec.Code.evaln (k + 1) c (Encodable.encode p)).isSome :=
      Option.isSome_iff_exists.mpr ⟨x, Option.mem_def.mp
        (Nat.Partrec.Code.evaln_mono (Nat.le_succ k) (Option.mem_def.mpr hx))⟩
    rw [h_evaln_succ]
    dsimp
    rw [beq_iff_eq, Nat.sub_eq_zero_iff_le]
    omega
  let search_V : ℕ → ℕ := fun M => Nat.find (h_ex_M M)
  have hsearch_V : Computable search_V :=
    Computable.natFind (P := fun M m => check_M M m = true)
      (Computable.of_eq hcheck_M (fun p => by simp)) h_ex_M
  let f_str : ℕ → BitString := fun M =>
    match check_V (search_V M) with
    | some p => p.1
    | none => []
  have hf_str : Computable f_str := by
    have h_check_V_search : Computable (fun M => check_V (search_V M)) :=
      hcheck_V.comp hsearch_V
    have h_map : Computable (fun o : Option (BitString × ℕ) =>
        match o with | some p => p.1 | none => ([] : BitString)) := by
      have h1 : Computable (fun o : Option (BitString × ℕ) => o.map Prod.fst) :=
        Computable.option_map Computable.id (Computable.fst.comp Computable.snd).to₂
      exact (Computable.option_getD h1 (Computable.const ([] : BitString))).of_eq
        (fun o => by cases o <;> rfl)
    exact h_map.comp h_check_V_search
  let f_nat : ℕ → ℕ := fun M => Encodable.encode (f_str M)
  have hf_nat : Computable f_nat := Computable.encode.comp hf_str
  obtain ⟨C_g, hC_g⟩ := plainKNat_comp_le U hU f_nat hf_nat
  obtain ⟨C_len, hC_len⟩ := plainKNat_le_length U hU
  obtain ⟨C_pow, hC_pow⟩ := plainKNat_comp_le U hU (fun k => 2 ^ k) Computable.pow2
  obtain ⟨C_str, hC_str⟩ := exists_plainK_le_plainKNat_encode U hU
  let C_total := C_g + C_len + C_str + C_pow
  obtain ⟨k, hk_growth⟩ := growth_lemma C_total
  let M := 2^k
  have h_rfind_spec : check_M M (search_V M) = true := Nat.find_spec (h_ex_M M)
  dsimp [check_M] at h_rfind_spec
  cases h_check : check_V (search_V M) with
  | none => rw [h_check] at h_rfind_spec; contradiction
  | some p =>
    rw [h_check] at h_rfind_spec
    dsimp at h_rfind_spec
    rw [beq_iff_eq, Nat.sub_eq_zero_iff_le] at h_rfind_spec
    have hp_ge : M ≤ p.2 := h_rfind_spec
    have h_check' : check_V (search_V M) = some p := h_check
    dsimp [check_V] at h_check
    have h_evaln : (Nat.Partrec.Code.evaln ((Nat.unpair (search_V M)).2 + 1) c
        (Encodable.encode p)).isSome = true := by
      cases hdec : (Encodable.decode (α := BitString × ℕ) (Nat.unpair (search_V M)).1) with
      | none =>
        rw [hdec] at h_check
        simp at h_check
      | some q =>
        simp only [hdec] at h_check
        by_cases he : (Nat.Partrec.Code.evaln ((Nat.unpair (search_V M)).2 + 1) c
            (Encodable.encode q)).isSome = true
        · rw [if_pos he] at h_check
          have hq : q = p := Option.some_inj.mp h_check
          rwa [hq] at he
        · rw [if_neg he] at h_check
          exact absurd h_check (by simp)
    have h_p_in_V : p ∈ V := by
      refine (hgV_dom p).mp ?_
      have h_eval : (c.eval (Encodable.encode p)).Dom ↔ (gV p).Dom := by
        rw [hc]; simp [Encodable.encodek]
      refine h_eval.mp ?_
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h_evaln
      exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound (Option.mem_def.mp hx)⟩
    have h_not_graph : (p.2 : ℕ∞) ≤ plainK U p.1 := by
      rw [Set.disjoint_left] at hdisj
      exact not_lt.mp (fun hgraph => hdisj hgraph h_p_in_V)
    have h_f_str : f_str M = p.1 := by
      dsimp [f_str]
      rw [h_check']
    have h_M_le_K : (M : ℕ∞) ≤ plainK U (f_str M) := by
      rw [h_f_str]
      exact le_trans (ENat.coe_le_coe.mpr hp_ge) h_not_graph
    have hM_bound : plainKNat U M ≤ (programLength (Nat.bits k) : ℕ∞) + ((C_pow
                                                                           + C_len : ℕ) : ℕ∞) := by
      have h1 : plainKNat U M ≤ plainKNat U k + (C_pow : ℕ∞) := hC_pow k
      have h2 : plainKNat U k ≤ (programLength (Nat.bits k) : ℕ∞) + (C_len : ℕ∞) := hC_len k
      calc plainKNat U M ≤ plainKNat U k + (C_pow : ℕ∞) := h1
        _ ≤ ((programLength (Nat.bits k) : ℕ∞) + (C_len : ℕ∞)) + (C_pow : ℕ∞) := by gcongr
        _ = (programLength (Nat.bits k) : ℕ∞) + ((C_pow + C_len : ℕ) : ℕ∞) := by
          push_cast; ring
    have h_chain : plainK U (f_str M) ≤ (programLength (Nat.bits k) : ℕ∞) + (C_total : ℕ∞) := by
      calc
        plainK U (f_str M)
          ≤ plainKNat U (f_nat M) + (C_str : ℕ∞) := hC_str (f_str M)
        _ ≤ (plainKNat U M + (C_g : ℕ∞)) + (C_str : ℕ∞) := by gcongr; exact hC_g M
        _ ≤ (((programLength (Nat.bits k) : ℕ∞) + ((C_pow + C_len : ℕ) : ℕ∞))
              + (C_g : ℕ∞)) + (C_str : ℕ∞) := by gcongr
        _ = (programLength (Nat.bits k) : ℕ∞) + ((C_total : ℕ) : ℕ∞) := by
          dsimp [C_total]
          push_cast
          ring
    have h_lt : (programLength (Nat.bits k) : ℕ∞) + (C_total : ℕ∞) < (M : ℕ∞) := hk_growth
    have h_bad := lt_of_le_of_lt (le_trans h_M_le_K h_chain) h_lt
    exact lt_irrefl _ h_bad

/-- **Exercise 12(a), upper graph.** The upper graph `{(x, k) | C(x) < k}` is
`r`-separable. -/
theorem isRSeparable_upperGraph_plainK (U : Map) (hU : isOptimalConditional U) :
    IsRSeparable {p : BitString × ℕ | plainK U p.1 < (p.2 : ℕ∞)} := by
  intro V hV hdisj
  obtain ⟨N, hV_bounded⟩ := exists_bounded_of_disjoint_upperGraph U hU V hV hdisj
  obtain ⟨R, hR_dec, hV_sub, hdisj_R⟩ := upperGraph_separable_of_bounded U N V hV_bounded hdisj
  exact ⟨R, hR_dec, hV_sub, hdisj_R⟩

/-- **Exercise 12(b).** `r`-separability is inherited along `m`-reductions. -/
theorem isRSeparable_of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β]
    (U₁ : Set α) (U₂ : Set β) (hred : ManyOneReducible (fun a => a ∈ U₁) (fun b => b ∈ U₂))
    (h₂ : IsRSeparable U₂) : IsRSeparable U₁ := by
  obtain ⟨f, hf_comp, hf_iff⟩ := hred
  intro V₁ hV₁ hdisj₁
  have hV₂ : IsEnumerableSet (f '' V₁) := IsEnumerableSet.image hV₁ hf_comp
  have hdisj₂ : Disjoint U₂ (f '' V₁) := by
    rw [Set.disjoint_left] at hdisj₁ ⊢
    rintro b hbU₂ ⟨a, haV₁, rfl⟩
    have haU₁ : a ∈ U₁ := hf_iff a |>.mpr hbU₂
    exact hdisj₁ haU₁ haV₁
  obtain ⟨R₂, hR₂_dec, hV₂_sub, hdisj₂_R₂⟩ := h₂ (f '' V₁) hV₂ hdisj₂
  obtain ⟨chk, hchk_comp, hchk_iff⟩ := hR₂_dec
  let R₁ : Set α := { a : α | f a ∈ R₂ }
  refine ⟨R₁, ?_, ?_, ?_⟩
  · refine ⟨chk ∘ f, hchk_comp.comp hf_comp, fun a => ?_⟩
    change chk (f a) = true ↔ f a ∈ R₂
    exact hchk_iff (f a)
  · intro a haV₁
    change f a ∈ R₂
    exact hV₂_sub ⟨a, haV₁, rfl⟩
  · rw [Set.disjoint_left] at hdisj₂_R₂ ⊢
    intro a haU₁ haR₁
    have hfaU₂ : f a ∈ U₂ := hf_iff a |>.mp haU₁
    have hfaR₂ : f a ∈ R₂ := haR₁
    exact hdisj₂_R₂ hfaU₂ hfaR₂

/-- **Exercise 12(a), compressible strings.** The set of compressible strings is
`r`-separable. -/
theorem isRSeparable_compressibleStrings (U : Map) (hU : isOptimalConditional U) :
    IsRSeparable {x : BitString | plainK U x < (x.length : ℕ∞)} := by
  let f : BitString → BitString × ℕ := fun x => (x, x.length)
  have hf_comp : Computable f := Computable.pair Computable.id Computable.list_length
  have hred : ManyOneReducible (fun x : BitString => plainK U x < (x.length : ℕ∞))
      (fun p : BitString × ℕ => plainK U p.1 < (p.2 : ℕ∞)) := by
    refine ⟨f, hf_comp, fun x => Iff.rfl⟩
  exact isRSeparable_of_manyOneReducible _ _ hred (isRSeparable_upperGraph_plainK U hU)

/-- **Exercise 12(c).** There is an enumerable set that is not `r`-separable. -/
theorem exists_isEnumerableSet_not_isRSeparable :
    ∃ A : Set ℕ, IsEnumerableSet A ∧ ¬ IsRSeparable A := by
  let A : Set ℕ := { e : ℕ | 0 ∈ (Denumerable.ofNat Code e).eval e }
  let V : Set ℕ := { e : ℕ | 1 ∈ (Denumerable.ofNat Code e).eval e }
  have h_code : Computable (fun e : ℕ => Denumerable.ofNat Code e) := Computable.ofNat Code
  have h_pair : Computable (fun e : ℕ => (Denumerable.ofNat Code e, e)) :=
    Computable.pair h_code Computable.id
  have h_eval_code : Partrec (fun e : ℕ => (Denumerable.ofNat Code e).eval e) :=
    Partrec.comp Code.eval_part h_pair
  have hA : IsEnumerableSet A := by
    have hb : Partrec₂ (fun (e : ℕ) (v : ℕ) =>
                         if v = 0 then (Part.some () : Part Unit) else Part.none) := by
      have h_beq : Computable (fun p : ℕ × ℕ => p.2 == 0) :=
        Primrec.to_comp Primrec.beq |>.comp (Computable.pair Computable.snd (Computable.const 0))
      have h_cond :=
        Computable.cond h_beq (Computable.const (some ())) (Computable.const (α := ℕ × ℕ) (none :
                                                                                            Option
        Unit))
      have hc : Computable (fun p : ℕ × ℕ => if p.2 = 0 then (some () : Option Unit) else none) :=
        by
        have h_eq : (fun p : ℕ × ℕ => if p.2 = 0 then (some () : Option Unit) else none) =
            (fun p => bif p.2 == 0 then (some () : Option Unit) else none) := by
          ext p
          split_ifs with h_if
          · rw [h_if]; rfl
          · have : (p.2 == 0) = false := by rw [beq_eq_false_iff_ne]; exact h_if
            rw [this]; simp
        rwa [h_eq]
      have hc' : Partrec (fun p : ℕ × ℕ =>
                           if p.2 = 0 then (Part.some () : Part Unit) else Part.none) := by
        have h_part := Computable.ofOption hc
        have h_eq : (fun p : ℕ × ℕ => if p.2 = 0 then (Part.some () : Part Unit) else Part.none) =
            (fun p => Part.ofOption (if p.2 = 0 then (some () : Option Unit) else none)) := by
          ext p
          split_ifs <;> rfl
        rwa [h_eq]
      exact hc'.to₂
    have h_bind : Partrec (fun e : ℕ => ((Denumerable.ofNat Code e).eval e).bind
        (fun v => if v = 0 then Part.some () else Part.none)) := Partrec.bind h_eval_code hb
    refine ⟨_, h_bind, fun e => ?_⟩
    rw [Part.bind_dom]
    constructor
    · rintro ⟨hdom, hstep⟩
      rw [Part.dom_iff_mem] at hdom
      obtain ⟨v, hv⟩ := hdom
      have h_get : ((Denumerable.ofNat Code e).eval e).get hdom = v := Part.get_eq_of_mem hv hdom
      rw [h_get] at hstep
      split_ifs at hstep with hv0
      · subst hv0
        exact hv
      · contradiction
    · intro h0
      have hdom : ((Denumerable.ofNat Code e).eval e).Dom := Part.dom_iff_mem.mpr ⟨0, h0⟩
      refine ⟨hdom, ?_⟩
      have h_get : ((Denumerable.ofNat Code e).eval e).get hdom = 0 := Part.get_eq_of_mem h0 hdom
      rw [h_get]
      dsimp
      trivial
  have hV : IsEnumerableSet V := by
    have hb : Partrec₂ (fun (e : ℕ) (v : ℕ) =>
                         if v = 1 then (Part.some () : Part Unit) else Part.none) := by
      have h_beq : Computable (fun p : ℕ × ℕ => p.2 == 1) :=
        Primrec.to_comp Primrec.beq |>.comp (Computable.pair Computable.snd (Computable.const 1))
      have h_cond :=
        Computable.cond h_beq (Computable.const (some ())) (Computable.const (α := ℕ × ℕ) (none :
                                                                                            Option
        Unit))
      have hc : Computable (fun p : ℕ × ℕ => if p.2 = 1 then (some () : Option Unit) else none) :=
        by
        have h_eq : (fun p : ℕ × ℕ => if p.2 = 1 then (some () : Option Unit) else none) =
            (fun p => bif p.2 == 1 then (some () : Option Unit) else none) := by
          ext p
          split_ifs with h_if
          · rw [h_if]; rfl
          · have : (p.2 == 1) = false := by rw [beq_eq_false_iff_ne]; exact h_if
            rw [this]; simp
        rwa [h_eq]
      have hc' : Partrec (fun p : ℕ × ℕ =>
                           if p.2 = 1 then (Part.some () : Part Unit) else Part.none) := by
        have h_part := Computable.ofOption hc
        have h_eq : (fun p : ℕ × ℕ => if p.2 = 1 then (Part.some () : Part Unit) else Part.none) =
            (fun p => Part.ofOption (if p.2 = 1 then (some () : Option Unit) else none)) := by
          ext p
          split_ifs <;> rfl
        rwa [h_eq]
      exact hc'.to₂
    have h_bind : Partrec (fun e : ℕ => ((Denumerable.ofNat Code e).eval e).bind
        (fun v => if v = 1 then Part.some () else Part.none)) := Partrec.bind h_eval_code hb
    refine ⟨_, h_bind, fun e => ?_⟩
    rw [Part.bind_dom]
    constructor
    · rintro ⟨hdom, hstep⟩
      rw [Part.dom_iff_mem] at hdom
      obtain ⟨v, hv⟩ := hdom
      have h_get : ((Denumerable.ofNat Code e).eval e).get hdom = v := Part.get_eq_of_mem hv hdom
      rw [h_get] at hstep
      split_ifs at hstep with hv1
      · subst hv1
        exact hv
      · contradiction
    · intro h1
      have hdom : ((Denumerable.ofNat Code e).eval e).Dom := Part.dom_iff_mem.mpr ⟨1, h1⟩
      refine ⟨hdom, ?_⟩
      have h_get : ((Denumerable.ofNat Code e).eval e).get hdom = 1 := Part.get_eq_of_mem h1 hdom
      rw [h_get]
      dsimp
      trivial
  have hdisj : Disjoint A V := by
    rw [Set.disjoint_left]
    intro e hAe hVe
    dsimp [A, V] at hAe hVe
    have := Part.mem_unique hAe hVe
    contradiction
  refine ⟨A, hA, fun hsep => ?_⟩
  obtain ⟨R, hR_dec, hV_sub, hdisj_R⟩ := hsep V hV hdisj
  obtain ⟨chk, hchk_comp, hchk_iff⟩ := hR_dec
  let g : ℕ → ℕ := fun e => bif chk e then 0 else 1
  have hg_comp : Computable g :=
    Computable.cond hchk_comp (Computable.const 0) (Computable.const 1)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg_comp.partrec
  let e0 := Encodable.encode c
  have hc_eval : (Denumerable.ofNat Code e0).eval e0 = Part.some (g e0) := by
    dsimp [e0]
    rw [Denumerable.ofNat_encode]
    rw [hc]
    ext v
    simp [Part.map_some]
  by_cases h_chk : chk e0 = true
  · have h_e0_in_R : e0 ∈ R := hchk_iff e0 |>.mp h_chk
    have h_g0 : g e0 = 0 := by dsimp [g]; rw [h_chk]; rfl
    have h_e0_in_A : e0 ∈ A := by
      dsimp [A]
      rw [hc_eval, h_g0]
      exact Part.mem_some 0
    rw [Set.disjoint_left] at hdisj_R
    exact hdisj_R h_e0_in_A h_e0_in_R
  · have h_chk_false : chk e0 = false := Bool.not_eq_true _ |>.mp h_chk
    have h_g0 : g e0 = 1 := by dsimp [g]; rw [h_chk_false]; rfl
    have h_e0_in_V : e0 ∈ V := by
      dsimp [V]
      rw [hc_eval, h_g0]
      exact Part.mem_some 1
    have h_e0_in_R : e0 ∈ R := hV_sub h_e0_in_V
    have h_e0_in_R' : e0 ∈ R := h_e0_in_R
    rw [← hchk_iff] at h_e0_in_R'
    rw [h_e0_in_R'] at h_chk_false
    contradiction

end Kolmogorov
