import KolmogorovMathlib.Complexity.GeneralScheme.Comparing.RegularRelations

/-!
# Optimal Modes

Optimal description modes and their complexities, following Section 6.2 of the book by Shen,
Uspensky and Vereshchagin ("Kolmogorov complexity and algorithmic randomness").

Main declarations:

* `exists_const_modeComplexity_compat_eq_KPPlain`: the optimal `≍`-`=` complexity is prefix
  complexity `K` up to `O(1)` (Theorem 128).
* `isOptimalDescriptionMode_compat_compat_iff`: the optimal `≍`-`≍` description modes are the
  optimal consistent relations of Problem 137.
* `exists_const_modeComplexity_compat_compat_KMOf`: the optimal `≍`-`≍` complexity is monotone
  complexity (Theorem 128).
* `exists_const_modeComplexity_eq_compat_KROf`: the optimal `=`-`≍` complexity is decision
  complexity (Theorem 128).
* `exists_const_plainK_le_KROf_add_log`, `exists_const_KPPlain_le_KROf_add_log`: all
  complexities of the pentagon differ by `O(log n)` on strings of length `n`.
-/

namespace Kolmogorov
namespace GeneralScheme

/-- A functional RE relation is the graph of a partial computable function. -/
private lemma exists_const_modeComplexity_compat_eq_KPPlain_functional {α β : Type*}
    [Primcodable α] [Primcodable β] {R : α → β → Prop}
    (hR : IsRE (fun q : α × β => R q.1 q.2)) (hfun : ∀ a b b', R a b → R a b' → b = b') :
    ∃ f : α →. β, Partrec f ∧ ∀ a b, b ∈ f a ↔ R a b := by
  obtain ⟨g, hg, hdom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hg
  let step : α → ℕ → Option β := fun a n =>
    (Encodable.decode (α := β) n.unpair.1).bind fun b =>
      if (Nat.Partrec.Code.evaln (n.unpair.2 + 1) c (Encodable.encode (a, b))).isSome
      then some b else none
  have hstep : Computable₂ step := by
    have hdec : Computable (fun p : α × ℕ => Encodable.decode (α := β) p.2.unpair.1) :=
      Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    have hk : Computable (fun q : (α × ℕ) × β => q.1.2.unpair.2 + 1) :=
      Primrec.to_comp (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
    have hin : Computable (fun q : (α × ℕ) × β => Encodable.encode (q.1.1, q.2)) :=
      Computable.comp Computable.encode
        (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
    have hev : Computable (fun q : (α × ℕ) × β =>
        (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c (Encodable.encode (q.1.1, q.2))).isSome) :=
      Primrec.option_isSome.to_comp.comp
        ((evalnCoreComputable c).comp (Computable.pair hk hin))
    have hbody : Computable₂ (fun (p : α × ℕ) (b : β) =>
        if (Nat.Partrec.Code.evaln (p.2.unpair.2 + 1) c (Encodable.encode (p.1, b))).isSome
        then some b else none) := by
      refine (Computable.cond hev (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq fun q => ?_
      cases hh : (Nat.Partrec.Code.evaln (q.1.2.unpair.2 + 1) c
        (Encodable.encode (q.1.1, q.2))).isSome <;> simp only [hh] <;> rfl
    exact Computable.option_bind hdec hbody
  have hsound : ∀ a b, b ∈ Nat.rfindOpt (step a) → R a b := by
    intro a b hb
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hb
    simp only [step, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨b', -, hb'⟩ := hn
    split_ifs at hb' with hsome
    · obtain rfl : b' = b := Option.some.inj hb'
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      have hx' := Nat.Partrec.Code.evaln_sound hx
      rw [hc] at hx'
      have hd : (g (a, b')).Dom := by
        have := Part.dom_iff_mem.mpr ⟨x, hx'⟩
        simpa [Part.bind_dom] using this
      exact (hdom (a, b')).mp hd
  refine ⟨fun a => Nat.rfindOpt (step a), Partrec.rfindOpt hstep,
    fun a b => ⟨hsound a b, fun hab => ?_⟩⟩
  have hd : (g (a, b)).Dom := (hdom (a, b)).mpr hab
  have hev : (c.eval (Encodable.encode (a, b))).Dom := by
    rw [hc]
    simpa [Part.bind_dom] using hd
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hev
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
  have hk' := Nat.Partrec.Code.evaln_mono (Nat.le_succ k) hk
  have hmem : b ∈ step a (Nat.pair (Encodable.encode b) k) := by
    simp only [step, Nat.unpair_pair, Encodable.encodek, Option.mem_def, Option.bind_some]
    rw [ite_eq_left (Option.isSome_iff_exists.mpr ⟨x, hk'⟩)]
  have hdm : (Nat.rfindOpt (step a)).Dom := Nat.rfindOpt_dom.mpr ⟨_, _, hmem⟩
  obtain ⟨b', hb'⟩ := Part.dom_iff_mem.mp hdm
  have hb'' := hsound a b' hb'
  rw [hfun a b' b hb'' hab] at hb'
  exact hb'

private lemma exists_const_modeComplexity_compat_eq_KPPlain_primrec_prefix :
    Primrec (fun q : BitString × BitString => decide (q.2 <+: q.1)) := by
  have htake : Primrec (fun p : BitString × BitString => p.1.take p.2.length) :=
    Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst
  have hrel : PrimrecPred (fun p : BitString × BitString => p.1.take p.2.length = p.2) :=
    PrimrecRel.comp Primrec.eq htake Primrec.snd
  refine hrel.decide.of_eq fun p => ?_
  simp only [decide_eq_decide]
  exact eq_comm.trans List.prefix_iff_eq_take.symm

/-- Step 1 of the proof of `exists_const_modeComplexity_compat_eq_KPPlain`: an
enumerable `≍`-`=`-regular relation `R` yields a prefix-stable decompressor `M` (computable,
prefix stable in the program for every condition, ignoring the condition) that maps every
description to its object: `R p x` implies `x ∈ M (p, [])`. Take `M (p, c)` to be the object `x`
for the first enumerated pair `(p', x)` of `R` with `p'` a prefix of `p` (Problem 197 (a),
`exists_prefixStableFun_of_isRegular_compat_eq`, made computable by the enumeration of `R`);
this is single valued and prefix stable by `≍`-`=`-regularity. -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_prefixStable
    {R : BitString → BitString → Prop} (hR : IsDescriptionMode .compat .eq R) :
    ∃ M : Map, isDecompressor M ∧ IsPrefixStableMachine M ∧ ∀ p x, R p x → x ∈ M (p, []) := by
  obtain ⟨hRE, hreg⟩ := hR
  have hpre : IsRE (fun q : (BitString × BitString) × BitString => q.2 <+: q.1.1) := by
    have hp : Computable (fun q : (BitString × BitString) × BitString =>
        decide (q.2 <+: q.1.1)) :=
      (exists_const_modeComplexity_compat_eq_KPPlain_primrec_prefix.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to_comp
    exact (IsRE_of_computable hp).of_iff fun q => by simp
  have hA : IsRE (fun q : (BitString × BitString) × BitString =>
      q.2 <+: q.1.1 ∧ R q.2 q.1.2) :=
    hpre.and (hRE.comp_computable (g := fun q : (BitString × BitString) × BitString =>
      (q.2, q.1.2)) (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
  have hQ := IsRE.exists_encodable
    (R := fun (a : BitString × BitString) (b : BitString) => b <+: a.1 ∧ R b a.2) hA
  obtain ⟨f, hf, hfQ⟩ := exists_const_modeComplexity_compat_eq_KPPlain_functional
    (R := fun u x => ∃ p', p' <+: u ∧ R p' x) hQ (by
      rintro u x x' ⟨p₁, h₁, h₁'⟩ ⟨p₂, h₂, h₂'⟩
      exact hreg h₁' h₂' (List.prefix_or_prefix_of_prefix h₁ h₂))
  refine ⟨fun q => f q.1, hf.comp Computable.fst, ?_, ?_⟩
  · intro c u v z hz huv
    obtain ⟨p', hp', hR'⟩ := (hfQ u z).1 hz
    exact (hfQ v z).2 ⟨p', hp'.trans huv, hR'⟩
  · intro p x hpx
    exact (hfQ p x).2 ⟨p, List.prefix_refl p, hpx⟩

/-- Step 1 of the proof of
`exists_const_modeComplexity_compat_eq_KPPlain_prefixFree`:
the stage-`n` halting computation `M (p, []) = x` of the code of `M` (the pair `(p, x)`), if any. -/
private def exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_enum
    (code : Nat.Partrec.Code) (n : ℕ) : Option (BitString × BitString) :=
  (stabTriple code n).bind fun t => if t.1.2 = [] then some (t.1.1, t.2) else none

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_primrec_enum
    (code : Nat.Partrec.Code) :
    Primrec (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_enum code) := by
  have h1 : Primrec (fun n : ℕ => stabTriple code n) :=
    stabTriple_primrec.comp (Primrec.pair (Primrec.const code) Primrec.id)
  have hc : PrimrecPred (fun t : (BitString × BitString) × BitString => t.1.2 = []) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const [])
  have h2 : Primrec₂ (fun (_ : ℕ) (t : (BitString × BitString) × BitString) =>
      if t.1.2 = [] then some (t.1.1, t.2) else none) :=
    Primrec.ite (hc.comp Primrec.snd)
      (Primrec.option_some.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
      (Primrec.const none)
  exact Primrec.option_bind h1 h2

/-- Step 1 of the proof of
`exists_const_modeComplexity_compat_eq_KPPlain_prefixFree`:
a decompressor has a primitive recursive enumeration of its halting computations in the empty
context: `T n = some (p, x)` only if `x ∈ M (p, [])`, and every halting computation occurs. -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_enum
    {M : Map} (hM : isDecompressor M) :
    ∃ T : ℕ → Option (BitString × BitString), Primrec T ∧
      (∀ n p x, T n = some (p, x) → x ∈ M (p, [])) ∧
      ∀ p x, x ∈ M (p, []) → ∃ n, T n = some (p, x) := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hM
  refine ⟨_, exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_primrec_enum code,
    ?_, ?_⟩
  · intro n p x h
    unfold exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_enum at h
    obtain ⟨⟨⟨q, y⟩, z⟩, ht, h'⟩ := Option.bind_eq_some_iff.mp h
    by_cases hy : y = []
    · subst hy
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      obtain ⟨e, he, hdec⟩ := stabTriple_sound ht
      rw [hc] at he
      simp only [Encodable.encodek, Part.mem_bind_iff, Part.mem_ofOption, Option.mem_def,
        Option.some.injEq, exists_eq_left', Part.mem_map_iff] at he
      obtain ⟨x', hx', rfl⟩ := he
      rw [Encodable.encodek] at hdec
      cases hdec
      exact hx'
    · simp [hy] at h'
  · intro p x hx
    have hmem : Encodable.encode x ∈ Nat.Partrec.Code.eval code
        (Encodable.encode (p, ([] : BitString))) := by
      rw [hc]
      simp only [Encodable.encodek, Part.mem_bind_iff, Part.mem_ofOption, Option.mem_def,
        Option.some.injEq, exists_eq_left', Part.mem_map_iff]
      exact ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := stabTriple_complete hmem
    exact ⟨n, by
      simp [exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_enum, hn]⟩

/-- The Kraft-Chaitin request stream of the proof: at stage `n`, the `n`-th halting computation
`(p, x)` of the enumeration `T` requests length `l(p) + 2` provided `p` is strictly shorter than
every program of `x` listed before. -/
private def exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok
    (T : ℕ → Option (BitString × BitString)) (n : ℕ) (px : BitString × BitString) : Bool :=
  (List.range n).foldl (fun acc m => acc && (T m).elim true fun qx =>
    bif decide (qx.2 = px.2) then decide (px.1.length < qx.1.length) else true) true

private def exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req
    (T : ℕ → Option (BitString × BitString)) (n : ℕ) : Option ℕ :=
  (T n).bind fun px =>
    bif exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok T n px
    then some (px.1.length + 2) else none

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_foldl_and
    (f : ℕ → Bool) (l : List ℕ) (a : Bool) :
    l.foldl (fun acc m => acc && f m) a = true ↔ a = true ∧ ∀ m ∈ l, f m = true := by
  induction l generalizing a with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req_eq_some
    (T : ℕ → Option (BitString × BitString)) (n l : ℕ) :
    exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T n = some l ↔
      ∃ p x, T n = some (p, x) ∧ l = p.length + 2 ∧
        ∀ m < n, ∀ p', T m = some (p', x) → p.length < p'.length := by
  have hkey : ∀ p x : BitString,
      exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok T n (p, x) = true ↔
        ∀ m < n, ∀ p', T m = some (p', x) → p.length < p'.length := by
    intro p x
    unfold exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok
    rw [exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_foldl_and
      (fun m => (T m).elim true fun qx =>
        bif decide (qx.2 = (p, x).2) then decide ((p, x).1.length < qx.1.length) else true)]
    simp only [true_and, List.mem_range]
    refine forall_congr' fun m => forall_congr' fun hm => ?_
    cases hTm : T m with
    | none => simp
    | some qx =>
      obtain ⟨q, y⟩ := qx
      by_cases hy : y = x <;> simp [hy]
  unfold exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨p, x⟩, hT, h⟩
    rw [Bool.cond_eq_ite] at h
    split_ifs at h with hb
    exact ⟨p, x, hT, (Option.some.inj h).symm, (hkey p x).1 hb⟩
  · rintro ⟨p, x, hT, rfl, hall⟩
    refine ⟨(p, x), hT, ?_⟩
    rw [Bool.cond_eq_ite, ite_eq_left ((hkey p x).2 hall)]

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_computable_req
    {T : ℕ → Option (BitString × BitString)} (hT : Primrec T) :
    Computable (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T) := by
  have hok : Primrec₂ (fun (n : ℕ) (px : BitString × BitString) =>
      exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok T n px) := by
    have hdec : PrimrecPred (fun a : ((ℕ × (BitString × BitString)) × (Bool × ℕ)) ×
        (BitString × BitString) => a.2.2 = a.1.1.2.2) :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have hlt : PrimrecPred (fun a : ((ℕ × (BitString × BitString)) × (Bool × ℕ)) ×
        (BitString × BitString) => a.1.1.2.1.length < a.2.1.length) :=
      Primrec.nat_lt.comp
        (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
    have hinner : Primrec₂ (fun (a : (ℕ × (BitString × BitString)) × (Bool × ℕ))
        (qx : BitString × BitString) =>
        bif decide (qx.2 = a.1.2.2) then decide (a.1.2.1.length < qx.1.length) else true) :=
      Primrec.cond hdec.decide hlt.decide (Primrec.const true)
    have hcases : Primrec (fun a : (ℕ × (BitString × BitString)) × (Bool × ℕ) =>
        (T a.2.2).elim true fun qx =>
          bif decide (qx.2 = a.1.2.2) then decide (a.1.2.1.length < qx.1.length) else true) :=
      (Primrec.option_casesOn (hT.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true)
        hinner).of_eq fun a => by cases T a.2.2 <;> rfl
    have hfold := Primrec.list_foldl
      (f := fun a : ℕ × (BitString × BitString) => List.range a.1) (g := fun _ => true)
      (h := fun a b => b.1 && (T b.2).elim true fun qx =>
          bif decide (qx.2 = a.2.2) then decide (a.2.1.length < qx.1.length) else true)
      (Primrec.list_range.comp Primrec.fst) (Primrec.const true)
      (Primrec.and.comp (Primrec.fst.comp Primrec.snd) hcases)
    exact hfold
  have hbody : Primrec₂ (fun (n : ℕ) (px : BitString × BitString) =>
      bif exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_ok T n px
      then some (px.1.length + 2) else none) :=
    Primrec.cond hok
      (Primrec.option_some.comp (Primrec.succ.comp (Primrec.succ.comp
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))))
      (Primrec.const none)
  exact (Primrec.option_bind hT hbody).to_comp

/-- Step 2 of the proof of
`exists_const_modeComplexity_compat_eq_KPPlain_prefixFree`:
the requests issued for one output `x` have total weight at most `2^{-(k+1)}`, where `k` is a lower
bound for the lengths of the listed programs of `x`. (The requested lengths `l(p) + 2` for `x` are
pairwise distinct, because each request is for a strictly shorter program than all earlier ones,
and all are `≥ k + 2`; so the weight is at most `∑_{j ≥ k + 2} 2^{-j} = 2^{-(k+1)}`.) -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_perOutput
    (T : ℕ → Option (BitString × BitString)) (x : BitString) (k : ℕ)
    (hk : ∀ n p, T n = some (p, x) → k ≤ p.length) :
    ∑' n, (if (T n).map Prod.snd = some x then
        (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T n).elim 0
          (fun l => ((2 : ENNReal)⁻¹) ^ l) else 0) ≤ ((2 : ENNReal)⁻¹) ^ (k + 1) := by
  set R := exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T with hR
  set f : ℕ → ENNReal := fun n => (if (T n).map Prod.snd = some x then
        (R n).elim 0 (fun l => ((2 : ENNReal)⁻¹) ^ l) else 0) with hf
  set g : ℕ → ENNReal := fun j => if k + 2 ≤ j then ((2 : ENNReal)⁻¹) ^ j else 0 with hg
  set S : Set ℕ := {n | ∃ l, R n = some l ∧ (T n).map Prod.snd = some x} with hS
  set L : ℕ → ℕ := fun n => (R n).getD 0 with hL
  have hfS : ∀ n, n ∉ S → f n = 0 := by
    intro n hn
    simp only [hf]
    by_cases h : (T n).map Prod.snd = some x
    · cases hRn : R n with
      | none => simp [h]
      | some l => exact absurd ⟨l, hRn, h⟩ hn
    · simp [h]
  have hfg : ∀ n ∈ S, f n = g (L n) := by
    rintro n ⟨l, hl, hTn⟩
    obtain ⟨p, x', hT, rfl, -⟩ :=
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req_eq_some T n l).1 hl
    have hx : x' = x := by
      rw [hT] at hTn; simpa using hTn
    subst hx
    have hkp := hk n p hT
    simp only [hf, hg, hL, hl, hTn, ite_true, Option.elim_some, Option.getD_some]
    rw [ite_eq_left (by omega)]
  have hinj : Function.Injective (fun n : S => L n) := by
    rintro ⟨a, la, hla, hTa⟩ ⟨b, lb, hlb, hTb⟩ hab
    simp only [hL, hla, hlb, Option.getD_some] at hab
    subst hab
    obtain ⟨pa, xa, hTa', rfl, hlta⟩ :=
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req_eq_some T a la).1 hla
    obtain ⟨pb, xb, hTb', hlen, hltb⟩ :=
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req_eq_some T b
        (pa.length + 2)).1 hlb
    have hxa : xa = x := by rw [hTa'] at hTa; simpa using hTa
    have hxb : xb = x := by rw [hTb'] at hTb; simpa using hTb
    subst hxa; subst hxb
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hltb a h pa hTa'
      omega
    · have := hlta b h pb hTb'
      omega
  have h1 : ∑' n, f n = ∑' n : S, f n := by
    rw [tsum_subtype S f]
    refine tsum_congr fun n => ?_
    by_cases hn : n ∈ S
    · simp [Set.indicator_of_mem hn]
    · simp [Set.indicator_of_notMem hn, hfS n hn]
  have h2 : ∑' n : S, f n = ∑' n : S, g (L n) :=
    tsum_congr fun n => hfg n n.2
  have h3 : ∑' n : S, g (L n) ≤ ∑' j, g j :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj g
  have h4 : ∑' j, g j = ((2 : ENNReal)⁻¹) ^ (k + 1) := by
    have hsum : ∑' i, g (i + (k + 2)) = ∑' j, g j := by
      refine Function.Injective.tsum_eq (g := fun i => i + (k + 2))
        (fun a b h => by simpa using h) ?_
      intro j hj
      by_contra hjr
      apply hj
      simp only [hg]
      rw [ite_eq_right]
      intro hle
      exact hjr ⟨j - (k + 2), by simp only; omega⟩
    rw [← hsum]
    have : ∀ i, g (i + (k + 2)) = ((2 : ENNReal)⁻¹) ^ (k + 2) * ((2 : ENNReal)⁻¹) ^ i := by
      intro i
      simp only [hg]
      rw [ite_eq_left (by omega), add_comm i, pow_add]
    simp only [this]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    have h22 : ((2 : ENNReal)⁻¹) ^ (k + 2) = ((2 : ENNReal)⁻¹) ^ (k + 1) * 2⁻¹ := pow_succ _ _
    rw [h22, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  rw [h1, h2]
  exact h3.trans h4.le

/-- Step 3 of the proof of
`exists_const_modeComplexity_compat_eq_KPPlain_prefixFree`:
Kraft's inequality for the shortest descriptions of a prefix-stable decompressor: the shortest
programs of distinct outputs are incomparable (a proper prefix of a shortest program `p_x` that
halts with output `x'` forces, by prefix stability, `M p_x = x'`, so `x' = x` with a shorter
program), hence `∑_x 2^{-K_M(x)} ≤ 1` over the outputs `x` of `M (·, [])`. -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_kraft
    {M : Map} (hM : IsPrefixStableDecompressor M) :
    ∑' x : BitString, Set.indicator {x | ∃ p, x ∈ M (p, [])}
      (fun x => ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat) x ≤ 1 := by
  classical
  have hs := hM.2
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun t => ?_
  have hex : ∀ x : BitString, ∃ p, x ∈ {x | ∃ p, x ∈ M (p, [])} →
      produces M p [] x ∧ (programLength p : ENat) = KP M x [] := by
    intro x
    by_cases hx : x ∈ {x | ∃ p, x ∈ M (p, [])}
    · obtain ⟨q, hq⟩ := hx
      have hne : KP M x [] ≠ ⊤ := KP_ne_top_iff_exists_program.2 ⟨q, hq⟩
      obtain ⟨p, hp, hl⟩ := exists_program_of_KP_ne_top hne
      exact ⟨p, fun _ => ⟨hp, hl⟩⟩
    · exact ⟨[], fun h => absurd h hx⟩
  choose p hp using hex
  set t' := t.filter (fun x => x ∈ {x | ∃ p, x ∈ M (p, [])}) with ht'
  have hsum : ∑ x ∈ t, Set.indicator {x | ∃ p, x ∈ M (p, [])}
      (fun x => ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat) x
      = ∑ x ∈ t', ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat := by
    rw [ht', Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ {x | ∃ p, x ∈ M (p, [])}
    · simp [hx]
    · simp [hx]
  rw [hsum]
  have hmem : ∀ x ∈ t', x ∈ {x | ∃ p, x ∈ M (p, [])} := fun x hx =>
    (Finset.mem_filter.1 hx).2
  have hinj : Set.InjOn p (t' : Set BitString) := by
    intro w1 h1 w2 h2 h
    have a1 := (hp w1 (hmem w1 h1)).1
    have a2 := (hp w2 (hmem w2 h2)).1
    rw [h] at a1
    exact Part.mem_unique a1 a2
  have hpf : IsPrefixFree ((t'.image p : Finset BitString) : Set BitString) := by
    intro q1 hq1 q2 hq2 hpre
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hq1 hq2
    obtain ⟨w1, h1, rfl⟩ := hq1
    obtain ⟨w2, h2, rfl⟩ := hq2
    have hmem' : w1 ∈ M (p w2, []) :=
      hs [] (p w1) (p w2) w1 (hp w1 (hmem w1 h1)).1 hpre
    have : w1 = w2 := Part.mem_unique hmem' (hp w2 (hmem w2 h2)).1
    rw [this]
  have hkr := finset_kraft_progWeight_le_one _ hpf
  rw [Finset.sum_image hinj] at hkr
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun w hw => ?_)) hkr
  have hn : ((KP M w []).toNat : ℕ) = programLength (p w) := by
    have := (hp w (hmem w hw)).2
    rw [← this]; simp
  rw [hn, progWeight]

/-- Step 4 of the proof of
`exists_const_modeComplexity_compat_eq_KPPlain_prefixFree`:
the total Kraft weight of the request stream is at most `1`. (Group the requests by output `x`;
by step 2 the weight for `x` is at most `2^{-(K_M(x)+1)}`, and by step 3 these sum to at most
`1/2`.) -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_weight
    {M : Map} (hM : IsPrefixStableDecompressor M) {T : ℕ → Option (BitString × BitString)}
    (hsound : ∀ n p x, T n = some (p, x) → x ∈ M (p, [])) :
    requestKraftWeight
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T) ≤ 1 := by
  classical
  set req := exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T with hreq
  let g : BitString → ℕ → ENNReal := fun x n =>
    if (T n).map Prod.snd = some x then (req n).elim 0 (fun l => ((2 : ENNReal)⁻¹) ^ l) else 0
  have hrow : ∀ n, ∑' x, g x n = (match req n with
      | some l => (2 : ENNReal)⁻¹ ^ l
      | none => 0) := by
    intro n
    cases hTn : T n with
    | none =>
      have : req n = none := by
        simp [hreq, exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req, hTn]
      simp [g, hTn, this]
    | some px =>
      obtain ⟨p, x0⟩ := px
      have : ∀ x, g x n = if x = x0 then (match req n with
          | some l => (2 : ENNReal)⁻¹ ^ l
          | none => 0) else 0 := by
        intro x
        by_cases hx : x = x0
        · subst hx
          rcases hr : req n with _ | l <;> simp [g, hTn, hr]
        · simp [g, hTn, hx, Ne.symm hx]
      simp_rw [this]
      rw [tsum_ite_eq]
  have h1 : requestKraftWeight req = ∑' x, ∑' n, g x n := by
    rw [requestKraftWeight, ENNReal.tsum_comm]
    exact tsum_congr fun n => (hrow n).symm
  have h2 : ∀ x, ∑' n, g x n ≤ ((2 : ENNReal)⁻¹) *
      Set.indicator {x | ∃ p, x ∈ M (p, [])}
        (fun x => ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat) x := by
    intro x
    by_cases hx : x ∈ {x | ∃ p, x ∈ M (p, [])}
    · rw [Set.indicator_of_mem hx]
      have hne : KP M x [] ≠ ⊤ := KP_ne_top_iff_exists_program.2 hx
      have := exists_const_modeComplexity_compat_eq_KPPlain_perOutput T x
        (KP M x []).toNat (fun n p hn => by
          have h := KP_le_programLength_of_produces (M := M) (hsound n p x hn)
          exact ENat.toNat_le_of_le_natCast (by simpa [programLength] using h))
      calc ∑' n, g x n ≤ _ := this
        _ = _ := by rw [pow_succ, mul_comm]
    · have : ∀ n, g x n = 0 := by
        intro n
        simp only [g]
        split_ifs with h
        · cases hTn : T n with
          | none => simp [hTn] at h
          | some px =>
            obtain ⟨p, x'⟩ := px
            simp only [hTn, Option.map_some, Option.some.injEq] at h
            subst h
            exact absurd ⟨p, hsound n p x' hTn⟩ hx
        · rfl
      simp [this]
  calc requestKraftWeight req = ∑' x, ∑' n, g x n := h1
    _ ≤ ∑' x, ((2 : ENNReal)⁻¹) *
      Set.indicator {x | ∃ p, x ∈ M (p, [])}
        (fun x => ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat) x := ENNReal.tsum_le_tsum h2
    _ = ((2 : ENNReal)⁻¹) * ∑' x, Set.indicator {x | ∃ p, x ∈ M (p, [])}
        (fun x => ((2 : ENNReal)⁻¹) ^ (KP M x []).toNat) x := ENNReal.tsum_mul_left
    _ ≤ ((2 : ENNReal)⁻¹) * 1 :=
      by gcongr; exact exists_const_modeComplexity_compat_eq_KPPlain_kraft hM
    _ ≤ 1 := by simp

/-- The decompressor read off an online Kraft-Chaitin allocation: the code allocated to the `k`-th
request is decompressed to the output of the `k`-th enumerated computation. -/
private def exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine
    (E alloc : ℕ → Option BitString) : Map :=
  fun q => (Nat.rfind fun n => Part.some (decide (alloc n = some q.1))).map
    fun n => (E n).getD ([] : BitString)

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_partrec_machine
    {E alloc : ℕ → Option BitString} (hE : Computable E) (halloc : Computable alloc) :
    Partrec (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine E alloc) := by
  have hp : Primrec fun p : Option BitString × Option BitString => decide (p.1 = p.2) := by
    have ⟨_, H⟩ : PrimrecRel (@Eq (Option BitString)) := Primrec.eq
    convert H
  have heq : Computable₂ fun o₁ o₂ : Option BitString => decide (o₁ = o₂) := hp.to_comp
  have hchk : Computable₂ fun (q : BitString × BitString) (n : ℕ) =>
      decide (alloc n = some q.1) :=
    heq.comp (halloc.comp Computable.snd)
      (Computable.option_some.comp (Computable.fst.comp Computable.fst))
  have hrfind : Partrec fun q : BitString × BitString =>
      Nat.rfind fun n => Part.some (decide (alloc n = some q.1)) :=
    Partrec.rfind hchk.partrec
  have hout : Computable₂ fun (_ : BitString × BitString) (n : ℕ) =>
      (E n).getD ([] : BitString) :=
    Computable.option_getD (hE.comp Computable.snd) (Computable.const [])
  exact hrfind.map hout

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine_produces
    {E alloc : ℕ → Option BitString}
    (hpf : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm)
    {k : ℕ} {z c : BitString} (hEk : E k = some z) (hck : alloc k = some c) (y : BitString) :
    produces (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine E alloc)
      c y z := by
  have hinj : ∀ n, alloc n = some c → n = k := by
    intro n hn
    by_contra hne
    exact hpf n k c c hn hck hne (List.prefix_refl c)
  have hmem : k ∈ Nat.rfind fun n => Part.some (decide (alloc n = some c)) := by
    refine Nat.mem_rfind.2 ⟨?_, ?_⟩
    · simp [hck]
    · intro m hm
      have hne : alloc m ≠ some c := by
        intro h
        have := hinj m h
        omega
      simp [hne]
  have h2 := Part.mem_map (fun n => (E n).getD ([] : BitString)) hmem
  simpa [produces, exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine,
    hEk] using h2

private lemma exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_isPrefixMachine
    {E alloc : ℕ → Option BitString}
    (hpf : ∀ n m cn cm, alloc n = some cn → alloc m = some cm → n ≠ m →
      ¬ List.IsPrefix cn cm) :
    IsPrefixMachine
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine E alloc) := by
  have hdom : ∀ y p : BitString, p ∈ domainAt
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine E alloc) y →
      ∃ n, alloc n = some p := by
    intro y p hp
    have hdomrf : (Nat.rfind fun n => Part.some (decide (alloc n = some p))).Dom := hp
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.1 hdomrf
    exact ⟨n, by simpa using hn⟩
  intro y p hp q hq hpre
  obtain ⟨n, hn⟩ := hdom y p hp
  obtain ⟨m, hm⟩ := hdom y q hq
  by_cases hnm : n = m
  · subst hnm
    exact Option.some_injective _ (hn.symm.trans hm)
  · exact absurd hpre (hpf n m p q hn hm hnm)

/-- Step 2 of the proof of `exists_const_modeComplexity_compat_eq_KPPlain`
(SUV Theorem 55, the direction "prefix-free complexity is at most prefix-stable complexity"):
a prefix-stable decompressor `M` has a prefix decompressor `D` with
`KP D x [] ≤ KP M x [] + c` for all `x`. (Kraft–Chaitin: for each output `x` request, in order of
decreasing efficiency, only descriptions strictly shorter than those requested before for `x`,
with length `l(p) + 2`; the `KP M`-minimal descriptions of distinct outputs are incomparable by
prefix stability and single-valuedness of `M`, so the total weight is at most `1`.) -/
private theorem exists_const_modeComplexity_compat_eq_KPPlain_prefixFree {M : Map}
    (hM : IsPrefixStableDecompressor M) :
    ∃ D : Map, IsPrefixDecompressor D ∧ ∃ c : ℕ, ∀ x, KP D x [] ≤ KP M x [] + c := by
  obtain ⟨T, hTp, hTs, hTc⟩ :=
    exists_const_modeComplexity_compat_eq_KPPlain_enum hM.1
  obtain ⟨alloc, halloc, hlen, -, hpf⟩ :=
    exists_online_prefixFree_of_kraft_le_one
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T)
      (exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_computable_req hTp)
      (exists_const_modeComplexity_compat_eq_KPPlain_weight hM hTs)
  have hE : Computable fun n => (T n).map Prod.snd :=
    Computable.option_map hTp.to_comp (Computable.snd.comp Computable.snd)
  refine ⟨exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine
      (fun n => (T n).map Prod.snd) alloc,
    ⟨exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_partrec_machine hE halloc,
      exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_isPrefixMachine hpf⟩,
    2, fun x => ?_⟩
  by_cases h : KP M x [] = ⊤
  · rw [h]; simp
  obtain ⟨p, hp, hplen⟩ := KP_mem_candidateLengths_of_ne_top h
  -- the least stage listing a shortest program of `x`
  have hex : ∃ n p', T n = some (p', x) ∧ (p'.length : ℕ∞) = KP M x [] := by
    obtain ⟨n, hn⟩ := hTc p x hp
    exact ⟨n, p, hn, hplen⟩
  classical
  let n₀ := Nat.find hex
  obtain ⟨p₀, hn₀, hp₀len⟩ := Nat.find_spec hex
  have hge : ∀ n q, T n = some (q, x) → KP M x [] ≤ q.length := fun n q hq =>
    KP_le_programLength_of_produces (M := M) (hTs n q x hq)
  have hreq : exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req T n₀ =
      some (p₀.length + 2) := by
    rw [exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_req_eq_some]
    refine ⟨p₀, x, hn₀, rfl, fun m hm p' hp' => ?_⟩
    have h1 : KP M x [] ≤ p'.length := hge m p' hp'
    have h2 : (p'.length : ℕ∞) ≠ p₀.length := by
      intro heq
      exact Nat.find_min hex hm ⟨p', hp', heq.trans hp₀len⟩
    have h3 : p₀.length < p'.length := by
      rw [← hp₀len] at h1
      have := lt_of_le_of_ne h1 (Ne.symm h2)
      exact_mod_cast this
    exact h3
  obtain ⟨c, hc, hclen⟩ := hlen n₀ (p₀.length + 2) hreq
  have hprod := exists_const_modeComplexity_compat_eq_KPPlain_prefixFree_machine_produces
    hpf (E := fun n => (T n).map Prod.snd) (k := n₀) (z := x)
        (by show (T n₀).map Prod.snd = some x; rw [hn₀]; rfl) hc []
  calc _ ≤ (programLength c : ℕ∞) := KP_le_programLength_of_produces hprod
    _ = ((p₀.length + 2 : ℕ) : ℕ∞) := by rw [programLength, hclen]
    _ = KP M x [] + ((2 : ℕ) : ℕ∞) := by rw [← hp₀len]; push_cast; rfl

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), case `≍`-`=`.** The optimal ≍-=-complexity
is prefix complexity `K` (here `KPPlain` for an optimal prefix-free decompressor).

Proof idea: ≍-=-regular relations give prefix-stable decompressors (Problem 197 (a)). Prefix-stable
and prefix-free complexity agree up to `O(1)` (Theorem 55,
`prefixStable_prefixFree_complexity_eq`). -/
theorem exists_const_modeComplexity_compat_eq_KPPlain {R : BitString → BitString → Prop}
    (hR : IsOptimalDescriptionMode .compat .eq R) {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x,
      modeComplexity R x ≤ KPPlain U x + c ∧ KPPlain U x ≤ modeComplexity R x + c := by
  -- `U` itself is a `≍`-`=` description mode, so `R` is at most `K + O(1)`
  have hmode : modeComplexity (fun p x => x ∈ U (p, [])) = KPPlain U := by
    funext x
    unfold modeComplexity KPPlain KP condK candidateLengths
    congr 1
    ext l
    simp only [Set.mem_ofPred_eq, produces, programLength]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  have hT : IsDescriptionMode .compat .eq (fun p x => x ∈ U (p, [])) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨f, hf, hd⟩ := Partrec.graphIsRe U hU.isDecompressor
      refine ⟨fun q => f ((q.1, []), q.2), hf.comp (Computable.pair
        (Computable.pair Computable.fst (Computable.const [])) Computable.snd), fun q => hd _⟩
    · intro p₁ x₁ p₂ x₂ h₁ h₂ hp
      have hpp : p₁ = p₂ := by
        rcases hp with hp | hp
        · exact hU.isPrefixMachine.eq_of_prefix h₁ h₂ hp
        · exact (hU.isPrefixMachine.eq_of_prefix h₂ h₁ hp).symm
      subst hpp
      exact Part.mem_unique h₁ h₂
  obtain ⟨c₁, hc₁⟩ := hR.2 _ hT
  rw [hmode] at hc₁
  -- conversely, `R` gives a prefix-stable decompressor, hence a prefix-free one
  obtain ⟨M, hMdec, hMst, hMR⟩ :=
    exists_const_modeComplexity_compat_eq_KPPlain_prefixStable hR.1
  obtain ⟨D, hD, c₂, hc₂⟩ :=
    exists_const_modeComplexity_compat_eq_KPPlain_prefixFree ⟨hMdec, hMst⟩
  obtain ⟨c₃, hc₃⟩ := hU.2 D hD
  refine ⟨c₁ + c₂ + c₃, fun x => ⟨?_, ?_⟩⟩
  · refine (hc₁ x).trans ?_
    gcongr
    omega
  · have hM : KP M x [] ≤ modeComplexity R x := by
      refine le_sInf ?_
      rintro l ⟨p, hp, rfl⟩
      exact KP_le_programLength_of_produces (M := M) (hMR p x hp)
    calc KPPlain U x ≤ KP D x [] + c₃ := hc₃ x []
      _ ≤ (KP M x [] + c₂) + c₃ := by gcongr; exact hc₂ x
      _ ≤ (modeComplexity R x + c₂) + c₃ := by gcongr
      _ = modeComplexity R x + ((c₂ + c₃ : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ modeComplexity R x + ((c₁ + c₂ + c₃ : ℕ) : ℕ∞) := by
        gcongr
        omega

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), helper for the case `≍`-`≍`.** The optimal
≍-≍ description modes are the optimal consistent relations of SUV Problem 137: both are
enumerable consistent relations, minimal up to `O(1)` in the same class. -/
theorem isOptimalDescriptionMode_compat_compat_iff (R : BitString → BitString → Prop) :
    IsOptimalDescriptionMode .compat .compat R ↔ IsOptimalConsistentRelation R := by
  constructor
  · rintro ⟨⟨hre, hreg⟩, hopt⟩
    exact ⟨(isRegular_compat_compat_iff R).1 hreg, hre,
      fun S hS hSre => hopt S ⟨hSre, (isRegular_compat_compat_iff S).2 hS⟩⟩
  · rintro ⟨hreg, hre, hopt⟩
    exact ⟨⟨hre, (isRegular_compat_compat_iff R).2 hreg⟩,
      fun S hS => hopt S ((isRegular_compat_compat_iff S).1 hS.2) hS.1⟩

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), case `≍`-`≍`.** The optimal ≍-≍-complexity
is monotone complexity. This follows from the library's Problem 137
(`exists_const_KMOf_consistentRelationKMOf_equiv`). -/
theorem exists_const_modeComplexity_compat_compat_KMOf {R : BitString → BitString → Prop}
    (hR : IsOptimalDescriptionMode .compat .compat R) {D : BitStream → BitStream}
    (hD : IsOptimalMonotoneDecompressor D) :
    ∃ c : ℕ, ∀ x, modeComplexity R x ≤ KMOf D x + c ∧ KMOf D x ≤ modeComplexity R x + c := by
  obtain ⟨c, hc⟩ := exists_const_KMOf_consistentRelationKMOf_equiv hD
    ((isOptimalDescriptionMode_compat_compat_iff R).1 hR)
  exact ⟨c, fun x => ⟨(hc x).2, (hc x).1⟩⟩

/-- **SUV Theorem 128 (Section 6.2, printed p. 198), case `=`-`≍`.** The optimal
=-≍-complexity is decision complexity.

Proof idea: a decision decompressor is a =-≍ description mode with the same complexity, and
conversely Problem 197 (c) turns a =-≍ description mode into a decision decompressor whose
complexity is not larger. -/
theorem exists_const_modeComplexity_eq_compat_KROf {R : BitString → BitString → Prop}
    (hR : IsOptimalDescriptionMode .eq .compat R) {M : DecisionDecompressor} (hM : M.IsOptimal) :
    ∃ c : ℕ, ∀ x, modeComplexity R x ≤ KROf M x + c ∧ KROf M x ≤ modeComplexity R x + c := by
  obtain ⟨c₁, hc₁⟩ := hR.2 M.rel ⟨M.re, M.regular⟩
  obtain ⟨M', hM'⟩ := exists_decisionDecompressor_of_isDescriptionMode_eq_compat hR.1
  obtain ⟨c₂, hc₂⟩ := hM M'
  refine ⟨max c₁ c₂, fun x => ⟨?_, ?_⟩⟩
  · have hle : ((c₁ : ℕ) : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_left c₁ c₂
    exact (hc₁ x).trans (add_le_add le_rfl hle)
  · have h1 : KROf M' x ≤ modeComplexity R x := by
      refine le_sInf ?_
      rintro l ⟨p, hp, rfl⟩
      exact modeComplexity_le_length (R := M'.rel)
        ((hM' p x).2 (Or.inr ⟨x, List.prefix_refl x, hp⟩))
    have hle : ((c₂ : ℕ) : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_right c₁ c₂
    exact (hc₂ x).trans (add_le_add h1 hle)

/-- **SUV Section 6.2 (printed p. 199), unnumbered.** All the complexities of the pentagon
differ by `O(log n)` on strings of length `n`. The bottom step is
`C(x) ≤ C(x | l(x)) + C(l(x)) + O(1) ≤ KR(x) + O(log n)`, using Theorem 127 (f).

Proof idea: Theorem 127 (f) together with the pair bound of Theorem 16 for the condition
`l(x)`. -/
theorem exists_const_plainK_le_KROf_add_log {R : DecisionDecompressor} (hR : R.IsOptimal)
    {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x, plainK U x ≤ KROf R x + ((c * Nat.log 2 x.length + c : ℕ) : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := exists_const_condK_length_le_KROf hR hU
  obtain ⟨k, hk⟩ := plainK_sub_condK_le_two_mul_plainK U hU
  obtain ⟨c2, hc2⟩ := plainK_le_length U hU
  refine ⟨c1 + k + 2 * c2 + 2, fun x => ?_⟩
  have h1 := hc1 x
  have h2 := (hk x (Nat.bits x.length)).2
  have h3 : cVal U (Nat.bits x.length) ≤ (Nat.bits x.length).length + c2 := by
    have := hc2 (Nat.bits x.length)
    exact ENat.toNat_le_of_le_natCast (by simpa [programLength] using this)
  have h4 := length_natBits_le_log x.length
  have h5 : c1 + (2 * cVal U (Nat.bits x.length) + k) ≤
      (c1 + k + 2 * c2 + 2) * Nat.log 2 x.length + (c1 + k + 2 * c2 + 2) := by
    nlinarith
  calc plainK U x ≤ condK U x (Nat.bits x.length) +
        ((2 * cVal U (Nat.bits x.length) + k : ℕ) : ℕ∞) := h2
    _ ≤ KROf R x + (c1 : ℕ∞) + ((2 * cVal U (Nat.bits x.length) + k : ℕ) : ℕ∞) := by gcongr
    _ = KROf R x + ((c1 + (2 * cVal U (Nat.bits x.length) + k) : ℕ) : ℕ∞) := by
      rw [add_assoc]; push_cast; rfl
    _ ≤ _ := by gcongr

private lemma exists_const_KPPlain_le_KROf_add_log_bits_length_le (k n c : ℕ) (h : k ≤ n + c) :
    (Nat.bits k).length ≤ Nat.log 2 n + c + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : c < 2 ^ c := Nat.lt_two_pow_self
  have h3 : 2 ^ (Nat.log 2 n + c + 1) = 2 ^ (Nat.log 2 n + 1) * 2 ^ c := by
    rw [← pow_add]; congr 1; omega
  rw [h3]
  generalize 2 ^ (Nat.log 2 n + 1) = A at *
  generalize 2 ^ c = B at *
  nlinarith

/-- **SUV Section 6.2 (printed p. 199), unnumbered.** The two most distant complexities of the
pentagon, prefix complexity `K` (top) and decision complexity `KR` (bottom), differ by
`O(log n)` on strings of length `n`.

Proof idea: `K(x) ≤ C(x) + O(log C(x))` (Theorem 65, `KPPlain_le_plainK_add_KPPlain_plainK`),
`C(x) ≤ l(x) + O(1)`, and `exists_const_plainK_le_KROf_add_log`. -/
theorem exists_const_KPPlain_le_KROf_add_log {R : DecisionDecompressor} (hR : R.IsOptimal)
    {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, KPPlain U x ≤ KROf R x + ((c * Nat.log 2 x.length + c : ℕ) : ℕ∞) := by
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨a, ha⟩ := exists_const_plainK_le_KROf_add_log hR hV
  obtain ⟨c4, h4⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨c5, h5⟩ := plainK_le_length V hV
  obtain ⟨c6, h6⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨a + 2 * c5 + 2 + c4 + c6, fun x => ?_⟩
  by_cases hKR : KROf R x = ⊤
  · rw [hKR]; simp
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hKR
  have hCx : plainK V x ≠ ⊤ := ne_top_of_le_natCast_add (h5 x)
  obtain ⟨kC, hkC⟩ := ENat.ne_top_iff_exists.mp hCx
  have hk5 : kC ≤ x.length + c5 := by
    have := h5 x
    rw [← hkC] at this
    change (kC : ℕ∞) ≤ ((x.length : ℕ) : ℕ∞) + (c5 : ℕ∞) at this
    exact_mod_cast this
  have hbits := exists_const_KPPlain_le_KROf_add_log_bits_length_le kC x.length c5 hk5
  have h4x := h4 x kC hkC.symm
  have h6x := h6 (Nat.bits kC)
  have hax := ha x
  rw [← hkC, ← hm] at hax
  have hka : kC ≤ m + (a * Nat.log 2 x.length + a) := by
    have : (kC : ℕ∞) ≤ ((m + (a * Nat.log 2 x.length + a) : ℕ) : ℕ∞) := by
      push_cast
      exact hax
    exact_mod_cast this
  rw [← hm]
  calc KPPlain U x ≤ (kC : ℕ∞) + KPPlain U (Nat.bits kC) + (c4 : ℕ∞) := h4x
    _ ≤ (kC : ℕ∞) + (2 * ((Nat.bits kC).length : ℕ∞) + (c6 : ℕ∞)) + (c4 : ℕ∞) := by gcongr
    _ ≤ ((m + ((a + 2 * c5 + 2 + c4 + c6) * Nat.log 2 x.length +
          (a + 2 * c5 + 2 + c4 + c6)) : ℕ) : ℕ∞) := by
      have : kC + (2 * (Nat.bits kC).length + c6) + c4 ≤
          m + ((a + 2 * c5 + 2 + c4 + c6) * Nat.log 2 x.length + (a + 2 * c5 + 2 + c4 + c6)) := by
        nlinarith
      exact_mod_cast this
    _ = _ := by push_cast; ring

end GeneralScheme

end Kolmogorov
