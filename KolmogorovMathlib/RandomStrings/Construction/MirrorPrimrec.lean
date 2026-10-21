/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.Construction.MirrorReply

/-!
# Primitive recursiveness of the mirrored stage

Primitive recursiveness of `replyFn` and of the bookkeeping functions of the mirrored stage.

Part of `KolmogorovMathlib.RandomStrings.Construction`.
-/

namespace Kolmogorov.RandomStrings

variable [Family]

section

omit [Family]

/-! #### Primitive recursiveness of `replyFn` -/

/-- Primitive recursiveness of `fitsO`. -/
theorem fitsO_primrec : Primrec₂ fitsO := by
  have h := Primrec.option_casesOn (Primrec.fst : Primrec fun p : Option ℕ × ℕ => p.1)
    (Primrec.const false)
    ((Primrec.nat_le.decide.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂ :
      Primrec₂ fun (p : Option ℕ × ℕ) (E : ℕ) => decide (p.2 ≤ E))
  refine h.of_eq fun p => ?_
  obtain ⟨o, k⟩ := p
  cases o <;> rfl

/-- Primitive recursiveness of `subOC`. -/
theorem subOC_primrec : Primrec₂ subOC := by
  have h := Primrec.option_casesOn (Primrec.fst : Primrec fun p : Option ℕ × ℕ => p.1)
    (Primrec.const (none : Option ℕ))
    ((Primrec.ite (Primrec.nat_le.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
      (Primrec.const none)).to₂ :
      Primrec₂ fun (p : Option ℕ × ℕ) (E : ℕ) => if p.2 ≤ E then some (E - p.2) else none)
  refine h.of_eq fun p => ?_
  obtain ⟨o, k⟩ := p
  cases o <;> rfl

/-- Primitive recursiveness of `EYC`. -/
theorem EYC_primrec : Primrec₂ EYC := by
  have h := floorO_primrec.comp ((GD.primrec_bud.comp Primrec.fst).pair
    ((GD.primrec_N.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) :
      Primrec fun p : GD × GStC => (p.1.bud, p.1.N, p.2.2.1))
  exact h.of_eq fun p => rfl

/-- Primitive recursiveness of `ENC`. -/
theorem ENC_primrec : Primrec₂ ENC := by
  have h := floorO_primrec.comp ((GD.primrec_bud.comp Primrec.fst).pair
    ((GD.primrec_N.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) :
      Primrec fun p : GD × GStC => (p.1.bud, p.1.N, p.2.2.2.1))
  exact h.of_eq fun p => rfl

/-- Primitive recursiveness of `mcC`. -/
theorem mcC_primrec : Primrec fun q : GD × GStC × List BitString => mcC q.1 q.2.1 q.2.2 := by
  have h := GD.primrec_mc.comp (Primrec.fst.pair
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
      (dedupL_primrec.comp (Primrec.snd.comp Primrec.snd))) :
      Primrec fun q : GD × GStC × List BitString => (q.1, q.2.1.1, dedupL q.2.2))
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `afterC`. -/
theorem afterC_primrec : Primrec fun q : GD × GStC × List BitString => afterC q.1 q.2.1 q.2.2 := by
  have hG : Primrec fun q : GD × GStC × List BitString => q.1 := Primrec.fst
  have hst : Primrec fun q : GD × GStC × List BitString => q.2.1 := Primrec.fst.comp Primrec.snd
  have hL : Primrec fun q : GD × GStC × List BitString => q.2.2 := Primrec.snd.comp Primrec.snd
  have ht : Primrec fun q : GD × GStC × List BitString => q.2.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have hEY0 := EYC_primrec.comp hG hst
  have hEY : Primrec fun q : GD × GStC × List BitString => EYC q.1 q.2.1 := hEY0
  have hEN0 := ENC_primrec.comp hG hst
  have hEN : Primrec fun q : GD × GStC × List BitString => ENC q.1 q.2.1 := hEN0
  have hmc : Primrec fun q : GD × GStC × List BitString => mcC q.1 q.2.1 q.2.2 := mcC_primrec
  have hc : PrimrecPred fun q : GD × GStC × List BitString => q.2.1.2.2.2 = true :=
    Primrec.eq.comp ht (Primrec.const true)
  have h1 := Primrec.ite hc (subOC_primrec.comp hEY hmc) hEY
  have h2 := Primrec.ite hc hEN (subOC_primrec.comp hEN hmc)
  have h := (dedupL_primrec.comp hL).pair (h1.pair (h2.pair (Primrec.not.comp ht)))
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `legalTest`. -/
theorem legalTest_primrec :
    Primrec fun q : GD × GStC × List BitString => legalTest q.1 q.2.1 q.2.2 := by
  have hG : Primrec fun q : GD × GStC × List BitString => q.1 := Primrec.fst
  have hst : Primrec fun q : GD × GStC × List BitString => q.2.1 := Primrec.fst.comp Primrec.snd
  have hL : Primrec fun q : GD × GStC × List BitString => q.2.2 := Primrec.snd.comp Primrec.snd
  have ht : Primrec fun q : GD × GStC × List BitString => q.2.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have hEY0 := EYC_primrec.comp hG hst
  have hEY : Primrec fun q : GD × GStC × List BitString => EYC q.1 q.2.1 := hEY0
  have hEN0 := ENC_primrec.comp hG hst
  have hEN : Primrec fun q : GD × GStC × List BitString => ENC q.1 q.2.1 := hEN0
  have hc : PrimrecPred fun q : GD × GStC × List BitString => q.2.1.2.2.2 = true :=
    Primrec.eq.comp ht (Primrec.const true)
  have hfit := fitsO_primrec.comp (Primrec.ite hc hEY hEN) mcC_primrec
  have hs1 := subB_primrec.comp (Primrec.fst.comp hst) hL
  have hs2 := subB_primrec.comp hL (GD.primrec_X.comp hG)
  have h := Primrec.and.comp (Primrec.and.comp hs1 hs2) hfit
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `safeTest`. -/
theorem safeTest_primrec :
    Primrec fun q : GD × Bool × GStC × List BitString => safeTest q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have ha0 := afterC_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd) :
    Primrec fun q : GD × Bool × GStC × List BitString => (q.1, q.2.2.1, q.2.2.2))
  have ha : Primrec fun q : GD × Bool × GStC × List BitString => afterC q.1 q.2.2.1 q.2.2.2 := ha0
  have hy0 := safeYesC_primrec.comp (Primrec.fst.pair ha)
  have hn0 := safeNoC_primrec.comp (Primrec.fst.pair ha)
  have hc : PrimrecPred fun q : GD × Bool × GStC × List BitString => q.2.1 = true :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)
  have h := Primrec.ite hc hy0 hn0
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `replyTest`. -/
theorem replyTest_primrec :
    Primrec fun q : GD × Bool × GStC × List BitString => replyTest q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hl0 := legalTest_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd) :
    Primrec fun q : GD × Bool × GStC × List BitString => (q.1, q.2.2.1, q.2.2.2))
  have h := Primrec.and.comp hl0 safeTest_primrec
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `candC`. -/
theorem candC_primrec : Primrec₂ candC := by
  have h := Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd :
    Primrec fun p : List BitString × ℕ =>
      (Encodable.decode p.2 : Option (List BitString))) Primrec.fst
  exact h.of_eq fun p => rfl

/-- Primitive recursiveness of `replyBound`. -/
theorem replyBound_primrec : Primrec replyBound := by
  have h := Primrec.list_foldr (σ := ℕ) (allSub_primrec.comp GD.primrec_Xd)
    (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂ :
      Primrec₂ fun (G : GD) (p : List BitString × ℕ) => max (Encodable.encode p.1) p.2)
  exact h.of_eq fun G => rfl

/-- Primitive recursiveness of `replyK`. -/
theorem replyK_primrec : Primrec fun q : GD × Bool × GStC => replyK q.1 q.2.1 q.2.2 := by
  have hn : Primrec fun q : GD × Bool × GStC => replyBound q.1 + 1 :=
    Primrec.nat_add.comp (replyBound_primrec.comp Primrec.fst) (Primrec.const 1)
  have hcand0 := candC_primrec.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) :
      Primrec fun p : (GD × Bool × GStC) × ℕ × ℕ => p.1.2.2.1)
    (Primrec.fst.comp Primrec.snd : Primrec fun p : (GD × Bool × GStC) × ℕ × ℕ => p.2.1)
  have htest0 := replyTest_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair hcand0)) :
    Primrec fun p : (GD × Bool × GStC) × ℕ × ℕ =>
      (p.1.1, p.1.2.1, p.1.2.2, candC p.1.2.2.1 p.2.1))
  have hc : PrimrecPred fun p : (GD × Bool × GStC) × ℕ × ℕ =>
      replyTest p.1.1 p.1.2.1 p.1.2.2 (candC p.1.2.2.1 p.2.1) = true :=
    Primrec.eq.comp htest0 (Primrec.const true)
  have h := Primrec.list_foldr (σ := ℕ) (Primrec.list_range.comp hn) hn
    (Primrec.ite hc (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun q => rfl

/-- Primitive recursiveness of `replyFn`. -/
theorem replyFn_primrec : Primrec fun q : GD × Bool × GStC => replyFn q.1 q.2.1 q.2.2 := by
  have hn : Primrec fun q : GD × Bool × GStC => replyBound q.1 + 1 :=
    Primrec.nat_add.comp (replyBound_primrec.comp Primrec.fst) (Primrec.const 1)
  have hS : Primrec fun q : GD × Bool × GStC => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcand0 := candC_primrec.comp hS replyK_primrec
  have hy := sortStr_toFinset_primrec.comp hcand0
  have hno := sortStr_toFinset_primrec.comp hS
  have h := Primrec.ite (Primrec.nat_lt.comp replyK_primrec hn) hy hno
  exact h.of_eq fun q => rfl

end

/-- Our reply `ourReply` in a game given by finite data, from a finite game state, as the
canonical list `sortStr`, is computable: `replyFn` on the finite game `GD` of the data
(`replyFn_spec`, `replyFn_primrec`), transferred to the real game by `ourReply_congr`. -/
theorem replyC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    ∃ r : GameDataC × Bool × GStC → List BitString, Computable r ∧
      ∀ (D : GameDataC) (h : BitString → ℕ) (we : Bool) (st : GStC), D.Describes γ h →
        r (D, we, st) = sortStr (ourReply (gameOfF A (γ D.1).1 (γ D.1).2 D.2.1 h
          ((2 : ℝ)⁻¹ ^ D.2.2.2.2) D.2.2.1.toFinset) we st.toG) := by
  classical
  obtain ⟨code, hc, hcode⟩ := effEnum_code γ hγ
  obtain ⟨_, hAc⟩ := hA
  obtain ⟨ph, hph, hphi⟩ := phiD_computable A γ code hc hcode hγ.clock hAc
  refine ⟨fun p => replyFn ⟨code p.1.1, Family.clk (γ p.1.1).2 p.1.2.1.length, p.1.2.1,
    p.1.2.2.2.1, p.1.2.2.2.2, p.1.2.2.1, (ph p.1).1, (ph p.1).2⟩ p.2.1 p.2.2, ?_,
    fun D h we st hD => ?_⟩
  · have hmk : Primrec fun p : ℕ × ℕ × BitString × List (BitString × ℕ) × ℕ × List BitString ×
        Bool × Bool =>
        GD.equiv.symm p := Primrec.of_equiv_symm
    have hD : Computable fun p : GameDataC × Bool × GStC => p.1 := Computable.fst
    have hph' : Computable fun p : GameDataC × Bool × GStC => ph p.1 := hph.comp hD
    have hgD0 := hmk.to_comp.comp ((hc.comp (Computable.fst.comp hD)).pair
      ((Family.clk_computable.comp (hγ.clock.comp (Computable.fst.comp hD))
        (Primrec.list_length.to_comp.comp (Computable.fst.comp (Computable.snd.comp hD)))).pair
        ((Computable.fst.comp (Computable.snd.comp hD)).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp hD)))).pair
          ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp hD)))).pair
            ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hD))).pair
              ((Computable.fst.comp hph').pair (Computable.snd.comp hph'))))))))
    have h0 := replyFn_primrec.to_comp.comp (hgD0.pair Computable.snd)
    exact h0.of_eq fun p => rfl
  · change replyFn ⟨code D.1, Family.clk (γ D.1).2 D.2.1.length, D.2.1, D.2.2.2.1, D.2.2.2.2,
      D.2.2.1, (ph D).1, (ph D).2⟩ we st = _
    rw [replyFn_spec]
    congr 1
    refine ourReply_congr (gameOfF A (γ D.1).1 (γ D.1).2 D.2.1 h ((2 : ℝ)⁻¹ ^ D.2.2.2.2)
      D.2.2.1.toFinset) _ _ ?_ ?_ we st.toG
    · intro z hz
      exact gameD_h₀ γ D h hD z hz
    · intro S _
      exact gameD_outcome A γ code hcode D _ _ (hphi D).1 (hphi D).2 h hD S

section

omit [Family]

/-- Primitive recursiveness of `StateC.kTab`. -/
theorem StateC.kTab_primrec : Primrec StateC.kTab :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := StateC.equiv)))

/-- Primitive recursiveness of `StateC.games`. -/
theorem StateC.games_primrec : Primrec StateC.games :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := StateC.equiv))))

/-- Primitive recursiveness of `StateC.injList`. -/
theorem StateC.injList_primrec : Primrec StateC.injList :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := StateC.equiv))))

/-- Primitive recursiveness of `StateC.mk`. -/
theorem StateC.mk_primrec : Primrec fun p : List (BitString × ℕ) × List (BitString × ℕ) ×
    List (ℕ × Option GameC) × List ℕ => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : StateC) :=
  Primrec.of_equiv_symm (e := StateC.equiv)

/-- The game lookup is primitive recursive. -/
theorem gLook_primrec : Primrec₂ gLook := by
  have h : Primrec fun a : List (ℕ × Option GameC) × ℕ =>
      a.1.foldr (fun p acc => if p.1 = a.2 then p.2 else acc) (none : Option GameC) :=
    Primrec.list_foldr Primrec.fst (Primrec.const none)
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact h

/-- Mirror of `updateK` is computable. -/
theorem updateKC_computable (enumK : ℕ → BitString × ℕ) (hK : Computable enumK) :
    Computable₂ fun (s : ℕ) (σC : StateC) => updateKC enumK s σC :=
  (StateC.mk_primrec.to_comp.comp
    ((StateC.fTab_primrec.to_comp.comp Computable.snd).pair
      ((Computable.list_cons.comp (hK.comp Computable.fst)
          (StateC.kTab_primrec.to_comp.comp Computable.snd)).pair
        ((StateC.games_primrec.to_comp.comp Computable.snd).pair
          (StateC.injList_primrec.to_comp.comp Computable.snd))))).of_eq fun _ => rfl

/-- `Nat.find` of a computable Boolean predicate with a witness everywhere is computable. -/
theorem computable_nat_find {α : Type} [Primcodable α] (p : α → ℕ → Bool) (hp : Computable₂ p)
    (hex : ∀ a, ∃ n, p a n = true) : Computable fun a => Nat.find (hex a) := by
  have hr := Partrec.rfind (p := fun a => ((p a : ℕ → Bool) : ℕ →. Bool)) hp.partrec₂
  refine Partrec.of_eq_tot hr fun a => ?_
  rw [Nat.mem_rfind]
  refine ⟨?_, fun {m} hm => ?_⟩
  · have h1 := Nat.find_spec (hex a)
    simp only [PFun.coe_val, Part.mem_some_iff]
    exact h1.symm
  · have h2 : p a m = false := by simpa using Nat.find_min (hex a) hm
    simp only [PFun.coe_val, Part.mem_some_iff]
    exact h2.symm

/-- `fLook` is unchanged outside its modification range. -/
theorem fLook_eq_of_not_mem (l : List (BitString × ℕ)) (x : BitString) (hx : x ∉ l.map Prod.fst) :
    fLook l x = F₀ x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    change (if p.1 = x then p.2 else fLook l x) = F₀ x
    rw [ite_eq_right (Ne.symm hx.1), ih hx.2]

/-- `kLook` is unchanged outside its modification range. -/
theorem kLook_eq_of_not_mem (l : List (BitString × ℕ)) (x : BitString) (hx : x ∉ l.map Prod.fst) :
    kLook l x = ⊤ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    change (if p.1 = x then min (p.2 : ℕ∞) (kLook l x) else kLook l x) = ⊤
    rw [ite_eq_right (Ne.symm hx.1), ih hx.2]

/-- A finite state has finitely many changes of `F*`. -/
theorem toState_fin (σC : StateC) : {x | σC.toState.Fstar x ≠ F₀ x}.Finite := by
  refine ((σC.fTab.map Prod.fst).toFinset.finite_toSet).subset fun x hx => ?_
  by_contra h
  exact hx (fLook_eq_of_not_mem σC.fTab x
    (fun h' => h (Finset.mem_coe.2 (List.mem_toFinset.2 h'))))

/-- A finite state has finitely many finite values of `K*`. -/
theorem toState_finK (σC : StateC) : {x | σC.toState.Kstar x ≠ ⊤}.Finite := by
  refine ((σC.kTab.map Prod.fst).toFinset.finite_toSet).subset fun x hx => ?_
  by_contra h
  exact hx (kLook_eq_of_not_mem σC.kTab x
    (fun h' => h (Finset.mem_coe.2 (List.mem_toFinset.2 h'))))

end

open Classical in
/-- The witness test on finite states. -/
noncomputable def isWitC (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (q : StateC × ℕ × BitString) : Bool :=
  decide (IsWitness A γ q.1.toState q.2.1 q.2.2)

omit [Family] in
/-- Filtering a list by a primitive recursive predicate with parameters. -/
theorem primrec_filter_param {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) := by
  have h := Primrec.listFilterMap hf
    ((Primrec.ite (Primrec.eq.comp hp (Primrec.const true)) (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)).to₂ : Primrec₂ fun a b => if p a b = true then some b else none)
  refine h.of_eq fun a => ?_
  generalize f a = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    cases hb : p a b <;> simp [ih]
omit [Family] in
/-- Primitive recursiveness of `iLook`. -/
theorem iLook_primrec : Primrec₂ iLook := by
  have h := Primrec.list_length.comp (primrec_filter_param (Primrec.fst : Primrec
    fun a : List ℕ × ℕ => a.1) ((Primrec.nat_lt.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)).to₂ : Primrec₂ fun (a : List ℕ × ℕ) (n : ℕ) =>
        decide (n < a.2)))
  exact h.of_eq fun a => rfl

/-- The play lists of the records of the requirements `< e`. -/
def exclC (σC : StateC) (e : ℕ) : List BitString :=
  (List.range e).flatMap fun e' => (gLook σC.games e').elim [] fun g => g.2.1
omit [Family] in
/-- Primitive recursiveness of `exclC`. -/
theorem exclC_primrec : Primrec₂ exclC := by
  have hg := (Primrec.option_casesOn
    (gLook_primrec.comp (StateC.games_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd :
      Primrec fun p : (StateC × ℕ) × ℕ => gLook p.1.1.games p.2)
    (Primrec.const ([] : List BitString))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) :
      Primrec fun p : ((StateC × ℕ) × ℕ) × GameC => p.2.2.1).to₂).to₂
  have h := Primrec.list_flatMap
    (Primrec.list_range.comp (Primrec.snd : Primrec fun a : StateC × ℕ => a.2)) hg
  refine h.of_eq fun a => ?_
  unfold exclC
  congr 1
  funext e'
  cases gLook a.1.games e' <;> rfl

omit [Family] in
/-- Membership characterization for `exclC`. -/
theorem mem_exclC (σC : StateC) (e : ℕ) (z : BitString) :
    z ∈ exclC σC e ↔ ∃ e' < e, z ∈ (σC.toState.game e').elim ∅ fun g => g.2.1 := by
  unfold exclC
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨e', he', hz⟩
    refine ⟨e', List.mem_range.1 he', ?_⟩
    change z ∈ ((gLook σC.games e').map GameC.toRec).elim ∅ fun g => g.2.1
    cases h : gLook σC.games e' with
    | none => rw [h] at hz; simp at hz
    | some g => rw [h] at hz; simpa [GameC.toRec] using hz
  · rintro ⟨e', he', hz⟩
    refine ⟨e', List.mem_range.2 he', ?_⟩
    change z ∈ ((gLook σC.games e').map GameC.toRec).elim ∅ (fun g => g.2.1) at hz
    cases h : gLook σC.games e' with
    | none => rw [h] at hz; simp at hz
    | some g => rw [h] at hz; simpa [GameC.toRec] using hz

/-- The play list of a new game of `e`, from a list `Q` of the strings `qsetF`. -/
def playListC (Q : List BitString) (σC : StateC) (e : ℕ) : List BitString :=
  Q.filter fun z => !memStr z (exclC σC e)

omit [Family] in
/-- Primitive recursiveness of `playListC`. -/
theorem playListC_primrec :
    Primrec fun b : List BitString × StateC × ℕ => playListC b.1 b.2.1 b.2.2 := by
  have h := primrec_filter_param (Primrec.fst : Primrec fun b : List BitString × StateC × ℕ => b.1)
    ((Primrec.not.comp (memStr_primrec.comp Primrec.snd
      (exclC_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂ :
      Primrec₂ fun (b : List BitString × StateC × ℕ) (z : BitString) =>
        !memStr z (exclC b.2.1 b.2.2))
  exact h.of_eq fun b => rfl

/-- The set of strings in `playListC`. -/
theorem playListC_toFinset (γ : ℕ → OTMCode × ℕ) (Q : List BitString) (σC : StateC) (e : ℕ)
    (x : BitString)
    (hQ : Q.toFinset = qsetF ((reqγ γ) e).1 ((reqγ γ) e).2 x) :
    (playListC Q σC e).toFinset = playSet (reqγ γ) σC.toState e x := by
  classical
  ext z
  rw [List.mem_toFinset]
  unfold playListC playSet
  rw [List.mem_filter, Finset.mem_sdiff, ← hQ, List.mem_toFinset]
  have hex : (z ∈ (Finset.range e).biUnion fun e' => (σC.toState.game e').elim ∅ fun g => g.2.1)
      ↔ z ∈ exclC σC e := by
    rw [Finset.mem_biUnion, mem_exclC]; simp only [Finset.mem_range]
  rw [hex]
  constructor
  · rintro ⟨hz, hm⟩
    refine ⟨hz, fun h => ?_⟩
    rw [(memStr_iff z _).2 h] at hm; simp at hm
  · rintro ⟨hz, hm⟩
    refine ⟨hz, ?_⟩
    cases hb : memStr z (exclC σC e)
    · rfl
    · exact absurd ((memStr_iff z _).1 hb) hm

/-- The witness test on finite states is computable: `IsWitness` is `val (newGame …) = true ↔
x ∉ A`; `val` by `valC_computable` on the finite data of `newGame`, `x ∈ A` by the decider. -/
theorem isWitC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable fun q : StateC × ℕ × BitString => isWitC A (reqγ γ) q := by
  classical
  obtain ⟨q, hqc, hq⟩ := queryList_computable γ hγ
  obtain ⟨v, hvc, hv⟩ := valD_computable A hA γ hγ
  obtain ⟨_, hAc⟩ := hA
  have hsub : Computable fun a : StateC × ℕ × BitString => a.2.1 - 1 :=
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).to_comp
  have hQ0 := hqc.comp hsub (Computable.snd.comp Computable.snd)
  have hQc : Computable fun a : StateC × ℕ × BitString => q (a.2.1 - 1) a.2.2 := hQ0
  have hP0 := playListC_primrec.to_comp.comp
    (hQc.pair (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  have hPc : Computable fun a : StateC × ℕ × BitString =>
      playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1 := hP0
  have hT : Primrec fun b : List BitString × StateC => b.1.map fun z => (z, hvalTab b.2 z) :=
    Primrec.list_map Primrec.fst ((Primrec.snd.pair
      (hvalTab_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
  have hT0 := hT.to_comp.comp ((Computable.list_append.comp hQc hPc).pair Computable.fst)
  have hm : Computable fun a : StateC × ℕ × BitString => a.2.1 + iLook a.1.injList a.2.1 + 6 :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (iLook_primrec.comp (StateC.injList_primrec.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))) (Primrec.const 6)).to_comp
  have hD0 := hsub.pair ((Computable.snd.comp Computable.snd).pair (hPc.pair (hT0.pair hm)))
  have hD : ∀ a : StateC × ℕ × BitString, v (a.2.1 - 1, a.2.2,
      playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1,
      (q (a.2.1 - 1) a.2.2 ++ playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1).map
        (fun z => (z, hvalTab a.1 z)), a.2.1 + iLook a.1.injList a.2.1 + 6) =
      val (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2) := by
    intro a
    have hQa : (q (a.2.1 - 1) a.2.2).toFinset =
        qsetF ((reqγ γ) a.2.1).1 ((reqγ γ) a.2.1).2 a.2.2 := hq _ _
    rw [hv _ a.1.toState.hval ⟨q (a.2.1 - 1) a.2.2 ++ playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1,
      ?_, ?_, ?_⟩]
    · unfold newGame
      rw [← playListC_toFinset γ _ a.1 a.2.1 a.2.2 hQa]
      rfl
    · change List.map _ _ = List.map _ _
      congr 1
      funext z
      rw [hval_eq_hvalTab]
    · intro z hz
      have hz' : z ∈ (q (a.2.1 - 1) a.2.2).toFinset := by rw [hQa]; exact hz
      exact List.mem_append_left _ (List.mem_toFinset.1 hz')
    · intro z hz
      exact List.mem_append_right _ hz
  have hres := Computable.cond (hvc.comp hD0)
    ((Primrec.not.to_comp).comp (hAc.comp (Computable.snd.comp Computable.snd)))
    (hAc.comp (Computable.snd.comp Computable.snd))
  refine hres.of_eq fun a => ?_
  show cond (v _) _ _ = _
  rw [hD a]
  unfold isWitC IsWitness
  by_cases hx : a.2.2 ∈ A <;>
    cases hval : val (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2) <;> simp [hx]

/-- The witness search of the construction on finite states is computable: `Nat.find` over the
codes with the computable test `isWitC`; a witness exists on every finite state by
`WitnessesExist`. -/
theorem chooseWitnessC_computable (A : Set BitString)
    (hA : ComputablePred fun x : BitString => x ∈ A)
    (hW : ∀ γ', WitnessesExist A γ') (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable₂ fun (σC : StateC) (e : ℕ) => chooseWitness A (reqγ γ) σC.toState e := by
  classical
  have hex : ∀ q : StateC × ℕ, ∃ k, isWitC A (reqγ γ)
      (q.1, q.2, (Encodable.decode k : Option BitString).getD []) = true := by
    intro q
    obtain ⟨x, -, hx⟩ := hW (reqγ γ) q.1.toState q.2 0 (toState_fin q.1)
      (toState_finK q.1)
    refine ⟨Encodable.encode x, ?_⟩
    simp only [isWitC, Encodable.encodek, Option.getD_some, decide_eq_true_eq]
    exact hx
  have hw := isWitC_computable A hA γ hγ
  have hp0 := hw.comp ((Computable.fst.comp Computable.fst).pair
    ((Computable.snd.comp Computable.fst).pair
      (Computable.option_getD (Primrec.decode.to_comp.comp Computable.snd)
        (Computable.const ([] : BitString)))) :
      Computable fun p : (StateC × ℕ) × ℕ =>
        (p.1.1, p.1.2, (Encodable.decode p.2 : Option BitString).getD []))
  have hp : Computable₂ fun (q : StateC × ℕ) (k : ℕ) =>
      isWitC A (reqγ γ) (q.1, q.2, (Encodable.decode k : Option BitString).getD []) := hp0
  have hf := computable_nat_find _ hp hex
  have hres := Computable.option_some.comp (Computable.option_getD
    (Primrec.decode.to_comp.comp hf) (Computable.const ([] : BitString)))
  refine hres.of_eq fun q => ?_
  change _ = chooseWitness A (reqγ γ) q.1.toState q.2
  have hP : ∃ k : ℕ, IsWitness A (reqγ γ) q.1.toState q.2
      ((Encodable.decode k : Option BitString).getD []) := by
    obtain ⟨k, hk⟩ := hex q
    exact ⟨k, by simpa [isWitC] using hk⟩
  have hfind : Nat.find (hex q) = Nat.find hP := by
    rw [Nat.find_eq_iff]
    refine ⟨by simpa [isWitC] using Nat.find_spec hP, fun n hn => ?_⟩
    simpa [isWitC] using Nat.find_min hP hn
  unfold chooseWitness
  rw [dite_eq_left hP, hfind]

/-! #### Primitive recursive bookkeeping -/

section

omit [Family]

/-- Primitive recursiveness of `List.dedup`. -/
theorem dedup_primrec : Primrec (List.dedup : List BitString → List BitString) := by
  have h := Primrec.list_foldr (σ := List BitString)
    (Primrec.id : Primrec fun l : List BitString => l)
    (Primrec.const [])
    ((Primrec.ite (Primrec.eq.comp (memStr_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.const true))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂)
  refine h.of_eq fun l => ?_
  change List.foldr (fun b s => if memStr b s = true then s else b :: s) [] l = l.dedup
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    by_cases ha : a ∈ l
    · rw [ite_eq_left ((memStr_iff a _).2 (List.mem_dedup.2 ha)), List.dedup_cons_of_mem ha]
    · rw [ite_eq_right (fun h => ha (List.mem_dedup.1 ((memStr_iff a _).1 h))),
        List.dedup_cons_of_notMem ha]

/-- Primitive recursiveness of `flipCostC`. -/
theorem flipCostC_primrec : Primrec₂ flipCostC :=
  (Primrec.ite (Primrec.nat_le.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.const 1)) Primrec.fst)
    (Primrec.list_cons.comp (Primrec.pair (Primrec.const true) (Primrec.nat_sub.comp
        (Primrec.list_length.comp Primrec.snd) (Primrec.const 1)))
      (Primrec.list_cons.comp (Primrec.pair (Primrec.const false) Primrec.fst)
        (Primrec.const [])))
    (Primrec.const [])).to₂

/-- Primitive recursiveness of `moveCostC`. -/
theorem moveCostC_primrec :
    Primrec fun p : StateC × List BitString × List BitString => moveCostC p.1 p.2.1 p.2.2 := by
  have hfil := primrec_filter_param
    (dedup_primrec.comp (Primrec.snd.comp Primrec.snd) :
      Primrec fun p : StateC × List BitString × List BitString => p.2.2.dedup)
    ((Primrec.not.comp (memStr_primrec.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).to₂ :
      Primrec₂ fun (p : StateC × List BitString × List BitString) (z : BitString) =>
        !memStr z p.2.1)
  have h := Primrec.list_flatMap hfil
    ((flipCostC_primrec.comp (hvalTab_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      Primrec.snd).to₂ :
      Primrec₂ fun (p : StateC × List BitString × List BitString) (z : BitString) =>
        flipCostC (hvalTab p.1 z) z)
  refine h.of_eq fun p => ?_
  have hl : (p.2.2.dedup.filter fun b => !memStr b p.2.1) =
      p.2.2.dedup.filter (fun x => decide (x ∉ p.2.1)) := by
    congr 1
    funext z
    by_cases hz : z ∈ p.2.1
    · rw [(memStr_iff z _).2 hz]; simp [hz]
    · have hm : memStr z p.2.1 = false := by
        cases hb : memStr z p.2.1
        · rfl
        · exact absurd ((memStr_iff z _).1 hb) hz
      rw [hm]; simp [hz]
  change (p.2.2.dedup.filter fun b => !memStr b p.2.1).flatMap
    (fun z => flipCostC (hvalTab p.1 z) z) = moveCostC p.1 p.2.1 p.2.2
  unfold moveCostC
  rw [hl]
  congr 1
  funext z
  rw [hval_eq_hvalTab]
/-- Primitive recursiveness of `setGameC`. -/
theorem setGameC_primrec : Primrec fun p : ℕ × GameC × StateC => setGameC p.1 p.2.1 p.2.2 := by
  have h := StateC.mk_primrec.comp ((StateC.fTab_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
    ((StateC.kTab_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.list_cons.comp (Primrec.fst.pair (Primrec.option_some.comp
          (Primrec.fst.comp Primrec.snd)))
        (StateC.games_primrec.comp (Primrec.snd.comp Primrec.snd))).pair
        (StateC.injList_primrec.comp (Primrec.snd.comp Primrec.snd)))))
  exact h.of_eq fun p => rfl
/-- Primitive recursiveness of `destroyC`. -/
theorem destroyC_primrec : Primrec₂ destroyC := by
  have h := StateC.mk_primrec.comp ((StateC.fTab_primrec.comp Primrec.snd).pair
    ((StateC.kTab_primrec.comp Primrec.snd).pair
      ((Primrec.list_cons.comp (Primrec.fst.pair (Primrec.const (none : Option GameC)))
        (StateC.games_primrec.comp Primrec.snd)).pair
        (StateC.injList_primrec.comp Primrec.snd))))
  exact h.of_eq fun p => rfl
/-- Primitive recursiveness of `injureC`. -/
theorem injureC_primrec : Primrec₂ injureC := by
  have hf := primrec_filter_param
    (StateC.games_primrec.comp Primrec.snd : Primrec fun p : ℕ × StateC => p.2.games)
    ((Primrec.nat_le.decide.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).to₂ :
      Primrec₂ fun (p : ℕ × StateC) (g : ℕ × Option GameC) => decide (g.1 ≤ p.1))
  have h := StateC.mk_primrec.comp ((StateC.fTab_primrec.comp Primrec.snd).pair
    ((StateC.kTab_primrec.comp Primrec.snd).pair
      (hf.pair (Primrec.list_cons.comp Primrec.fst (StateC.injList_primrec.comp Primrec.snd)))))
  exact h.of_eq fun p => rfl

/-- Primitive recursiveness of `applyFlipsC`. -/
theorem applyFlipsC_primrec : Primrec₂ applyFlipsC := by
  have hm := Primrec.list_map (Primrec.fst : Primrec fun p : List BitString × StateC => p.1)
    ((Primrec.snd.pair (Primrec.nat_min.comp
      (fLook_primrec.comp (StateC.fTab_primrec.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 4)))).to₂ :
      Primrec₂ fun (p : List BitString × StateC) (z : BitString) =>
        (z, min (fLook p.2.fTab z) (z.length - 4)))
  have h := StateC.mk_primrec.comp ((Primrec.list_append.comp hm
      (StateC.fTab_primrec.comp Primrec.snd)).pair
    ((StateC.kTab_primrec.comp Primrec.snd).pair
      ((StateC.games_primrec.comp Primrec.snd).pair
        (StateC.injList_primrec.comp Primrec.snd))))
  exact h.of_eq fun p => rfl

/-- Primitive recursiveness of `GStC.applyMove`. -/
theorem GStC.applyMove_primrec :
    Primrec fun p : StateC × GStC × List BitString => GStC.applyMove p.1 p.2.1 p.2.2 := by
  have hst : Primrec fun p : StateC × GStC × List BitString => p.2.1 := Primrec.fst.comp Primrec.snd
  have hR : Primrec fun p : StateC × GStC × List BitString => p.2.2 := Primrec.snd.comp Primrec.snd
  have h21 : Primrec fun p : StateC × GStC × List BitString => p.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hst)
  have h221 : Primrec fun p : StateC × GStC × List BitString => p.2.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have h222 : Primrec fun p : StateC × GStC × List BitString => p.2.1.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))
  have hmc0 := moveCostC_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp hst).pair hR))
  have hmc : Primrec fun p : StateC × GStC × List BitString => moveCostC p.1 p.2.1.1 p.2.2 := hmc0
  have hy0 := hR.pair ((Primrec.list_append.comp h21 hmc).pair (h221.pair (Primrec.const false)))
  have hy : Primrec fun p : StateC × GStC × List BitString =>
      ((p.2.2, p.2.1.2.1 ++ moveCostC p.1 p.2.1.1 p.2.2, p.2.1.2.2.1, false) : GStC) := hy0
  have hn0 := hR.pair (h21.pair ((Primrec.list_append.comp h221 hmc).pair (Primrec.const true)))
  have hn : Primrec fun p : StateC × GStC × List BitString =>
      ((p.2.2, p.2.1.2.1, p.2.1.2.2.1 ++ moveCostC p.1 p.2.1.1 p.2.2, true) : GStC) := hn0
  have h := Primrec.cond h222 hy hn
  refine h.of_eq fun p => ?_
  change (bif p.2.1.2.2.2 then _ else _) = GStC.applyMove p.1 p.2.1 p.2.2
  unfold GStC.applyMove
  cases p.2.1.2.2.2 <;> rfl

end

/-- The finite data of `newGame A (reqγ γ) σC.toState e x` (`a = (σC, e, x)`), from a query-list
function `q`. -/
def newGameDataC (q : ℕ → BitString → List BitString) (a : StateC × ℕ × BitString) : GameDataC :=
  (a.2.1 - 1, a.2.2, playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1,
    (q (a.2.1 - 1) a.2.2 ++ playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1).map
      (fun z => (z, hvalTab a.1 z)), a.2.1 + iLook a.1.injList a.2.1 + 6)

omit [Family] in
/-- `newGameDataC` is a computable function. -/
theorem newGameDataC_computable (q : ℕ → BitString → List BitString) (hqc : Computable₂ q) :
    Computable (newGameDataC q) := by
  have hsub : Computable fun a : StateC × ℕ × BitString => a.2.1 - 1 :=
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).to_comp
  have hQ0 := hqc.comp hsub (Computable.snd.comp Computable.snd)
  have hQc : Computable fun a : StateC × ℕ × BitString => q (a.2.1 - 1) a.2.2 := hQ0
  have hP0 := playListC_primrec.to_comp.comp
    (hQc.pair (Computable.fst.pair (Computable.fst.comp Computable.snd)))
  have hPc : Computable fun a : StateC × ℕ × BitString =>
      playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1 := hP0
  have hT : Primrec fun b : List BitString × StateC => b.1.map fun z => (z, hvalTab b.2 z) :=
    Primrec.list_map Primrec.fst ((Primrec.snd.pair
      (hvalTab_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)
  have hT0 := hT.to_comp.comp ((Computable.list_append.comp hQc hPc).pair Computable.fst)
  have hm : Computable fun a : StateC × ℕ × BitString => a.2.1 + iLook a.1.injList a.2.1 + 6 :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (iLook_primrec.comp (StateC.injList_primrec.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))) (Primrec.const 6)).to_comp
  exact hsub.pair ((Computable.snd.comp Computable.snd).pair (hPc.pair (hT0.pair hm)))

/-- `newGameDataC` evaluates correctly and bounds the computational cost. -/
theorem newGameDataC_spec (A : Set BitString) (γ : ℕ → OTMCode × ℕ)
    (q : ℕ → BitString → List BitString)
    (hq : ∀ e x, (q e x).toFinset = qsetF (γ e).1 (γ e).2 x)
    (a : StateC × ℕ × BitString) :
    (newGameDataC q a).Describes γ a.1.toState.hval ∧
      gameOfF A (γ (newGameDataC q a).1).1 (γ (newGameDataC q a).1).2 (newGameDataC q a).2.1
        a.1.toState.hval ((2 : ℝ)⁻¹ ^ (newGameDataC q a).2.2.2.2)
        (newGameDataC q a).2.2.1.toFinset = newGame A (reqγ γ) a.1.toState a.2.1 a.2.2 := by
  have hQa : (q (a.2.1 - 1) a.2.2).toFinset =
      qsetF ((reqγ γ) a.2.1).1 ((reqγ γ) a.2.1).2 a.2.2 := hq _ _
  refine ⟨⟨q (a.2.1 - 1) a.2.2 ++ playListC (q (a.2.1 - 1) a.2.2) a.1 a.2.1, ?_, ?_, ?_⟩, ?_⟩
  · change List.map _ _ = List.map _ _
    congr 1
    funext z
    rw [hval_eq_hvalTab]
  · intro z hz
    have hz' : z ∈ (q (a.2.1 - 1) a.2.2).toFinset := by rw [hQa]; exact hz
    exact List.mem_append_left _ (List.mem_toFinset.1 hz')
  · intro z hz
    exact List.mem_append_right _ hz
  · unfold newGame
    rw [← playListC_toFinset γ _ a.1 a.2.1 a.2.2 hQa]
    rfl

/-- The start of a game on finite states is computable (value and first reply by
`valC_computable`/`replyC_computable` on `newGameDataC`, the rest primitive recursive). -/
theorem startOnC_computable (A : Set BitString) (hA : ComputablePred fun x : BitString => x ∈ A)
    (γ : ℕ → OTMCode × ℕ) (hγ : EffEnum γ) :
    Computable fun q : StateC × ℕ × BitString => startOnC A (reqγ γ) q.2.1 q.1 q.2.2 := by
  classical
  obtain ⟨q, hqc, hq⟩ := queryList_computable γ hγ
  obtain ⟨v, hvc, hv⟩ := valD_computable A hA γ hγ
  obtain ⟨r, hrc, hr⟩ := replyC_computable A hA γ hγ
  have hDc := newGameDataC_computable q hqc
  have hspec := newGameDataC_spec A γ q hq
  have hwe : ∀ a, v (newGameDataC q a) = val (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2) :=
    fun a => by rw [hv _ _ (hspec a).1, (hspec a).2]
  have hR : ∀ a, r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a))) =
      sortStr (ourReply (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2)
        (val (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2))
        (firstState (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2)
          (val (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2)))) := fun a => by
    rw [hr _ _ _ _ (hspec a).1, (hspec a).2, hwe a,
      firstStateC_toG (newGame A (reqγ γ) a.1.toState a.2.1 a.2.2)]
  have hWc : Computable fun a : StateC × ℕ × BitString => v (newGameDataC q a) := hvc.comp hDc
  have hF0 : Computable fun a : StateC × ℕ × BitString => firstStateC (v (newGameDataC q a)) :=
    (Computable.const ([] : List BitString)).pair ((Computable.const ([] : FSum)).pair
      ((Computable.const ([] : FSum)).pair hWc))
  have hRc0 := hrc.comp (hDc.pair (hWc.pair hF0))
  have hRc : Computable fun a : StateC × ℕ × BitString =>
      r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a))) := hRc0
  have hPS0 := sortStr_toFinset_primrec.to_comp.comp
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hDc)))
  have hPS : Computable fun a : StateC × ℕ × BitString =>
      sortStr (newGameDataC q a).2.2.1.toFinset := hPS0
  have hAM0 := GStC.applyMove_primrec.to_comp.comp (Computable.fst.pair (hF0.pair hRc))
  have hAM : Computable fun a : StateC × ℕ × BitString => GStC.applyMove a.1
      (firstStateC (v (newGameDataC q a)))
      (r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a)))) := hAM0
  have hm : Computable fun a : StateC × ℕ × BitString => a.2.1 + iLook a.1.injList a.2.1 + 6 :=
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (iLook_primrec.comp (StateC.injList_primrec.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))) (Primrec.const 6)).to_comp
  have hrec : Computable fun a : StateC × ℕ × BitString =>
      ((a.2.2, sortStr (newGameDataC q a).2.2.1.toFinset, a.2.1 + iLook a.1.injList a.2.1 + 6,
        GStC.applyMove a.1 (firstStateC (v (newGameDataC q a)))
          (r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a))))) :
        GameC) :=
    (Computable.snd.comp Computable.snd).pair (hPS.pair (hm.pair hAM))
  have hset0 := setGameC_primrec.to_comp.comp
    ((Computable.fst.comp Computable.snd).pair (hrec.pair Computable.fst))
  have hflip0 := applyFlipsC_primrec.to_comp.comp hRc hset0
  have hinj0 := injureC_primrec.to_comp.comp (Computable.fst.comp Computable.snd) hflip0
  have hres := hinj0.pair (Computable.const true)
  refine hres.of_eq fun a => ?_
  change (injureC a.2.1 (applyFlipsC
      (r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a))))
      (setGameC a.2.1 (a.2.2, sortStr (newGameDataC q a).2.2.1.toFinset,
        a.2.1 + iLook a.1.injList a.2.1 + 6,
        GStC.applyMove a.1 (firstStateC (v (newGameDataC q a)))
          (r (newGameDataC q a, v (newGameDataC q a), firstStateC (v (newGameDataC q a)))))
        a.1)), true) = startOnC A (reqγ γ) a.2.1 a.1 a.2.2
  have hPl : (newGameDataC q a).2.2.1.toFinset = playSet (reqγ γ) a.1.toState a.2.1 a.2.2 :=
    playListC_toFinset γ _ a.1 a.2.1 a.2.2 (hq _ _)
  rw [hR a, hwe a, hPl]
  rfl

end Kolmogorov.RandomStrings
