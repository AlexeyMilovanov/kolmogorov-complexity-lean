import KolmogorovMathlib.Complexity.GeneralScheme.SetConditions
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.LemmaOmpBlockCounting
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic

/-!
# Plain Jump Limit

The limit of the complexity `C(x ‖ ≥ n)` under a growing set condition `{m | m ≥ n}` equals, up
to an additive constant, the plain complexity of `x` relative to the halting oracle `0'`
(the "jump"), in the plain-complexity version of the large-conditions scheme of Section 6.4.2 of
the book by Shen, Uspensky and Vereshchagin.

Main declarations:
* `exists_const_iInf_setCondK_atLeast_eq_plainK_jump`: `inf_n C(x ‖ ≥ n) = C(x | 0') + O(1)`;
* `exists_const_iSup_condK_le_setCondK_atLeast`: `sup_{m ≥ n} C(x | m) ≤ C(x ‖ ≥ n) + O(1)`;
* `encard_eventually_condK_lt_lt_two_pow`: fewer than `2 ^ k` strings `x` have `C(x | n) < k`
  for all large `n`.

The proof builds, for an optimal decompressor `U` for set conditions, a decompressor relative to
`0'` that searches for a threshold `N` beyond which no program output differs, and conversely a
decompressor that approximates `0'` by running `N` steps.
-/

namespace Kolmogorov

namespace GeneralScheme

open Encodable in
open Nat.Partrec (Code) in
/-- A computable `Σ⁰₁` test for "some `m ≥ N'` has `G (p, bits m)` halting with an output
different from `y`" (the triple `(p, N', y)` is the argument; `k = ⟨s, m⟩` codes a run time and
the number `m`). -/
private theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump_search_aux_bad {G : Map}
    (hG : isDecompressor G) :
    ∃ (c : Code) (g : BitString × ℕ × BitString → ℕ → Bool),
      (∀ n, Code.eval c n = Part.bind (decode (α := BitString × BitString) n)
        fun a => (G a).map encode) ∧ Computable₂ g ∧
      ∀ a, (∃ k, g a k = true) ↔
        ∃ m, a.2.1 ≤ m ∧ ∃ z, z ≠ a.2.2 ∧ z ∈ G (a.1, Nat.bits m) := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hG
  have hc' : ∀ n, Code.eval c n = Part.bind (decode (α := BitString × BitString) n)
      fun a => (G a).map encode := fun n => by rw [hc]
  have hm : Primrec fun q : (BitString × ℕ × BitString) × ℕ => (Nat.unpair q.2).2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have h1 : Primrec fun q : (BitString × ℕ × BitString) × ℕ => (Nat.unpair q.2).1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have h2 : Primrec fun q : (BitString × ℕ × BitString) × ℕ =>
      encode (q.1.1, Nat.bits (Nat.unpair q.2).2) :=
    Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (primrec_natBits.comp hm))
  have he : Primrec fun q : (BitString × ℕ × BitString) × ℕ =>
      Code.evaln (Nat.unpair q.2).1 c (encode (q.1.1, Nat.bits (Nat.unpair q.2).2)) :=
    Code.primrec_evaln.comp (Primrec.pair (Primrec.pair h1 (Primrec.const c)) h2)
  have hle : Primrec fun q : (BitString × ℕ × BitString) × ℕ =>
      decide (q.1.2.1 ≤ (Nat.unpair q.2).2) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) hm)
  have hn1 : Primrec fun q : (BitString × ℕ × BitString) × ℕ =>
      !decide (Code.evaln (Nat.unpair q.2).1 c (encode (q.1.1, Nat.bits (Nat.unpair q.2).2)) =
        none) :=
    Primrec.not.comp (PrimrecPred.decide (PrimrecRel.comp Primrec.eq he (Primrec.const none)))
  have hn2 : Primrec fun q : (BitString × ℕ × BitString) × ℕ =>
      !decide (Code.evaln (Nat.unpair q.2).1 c (encode (q.1.1, Nat.bits (Nat.unpair q.2).2)) =
        some (encode q.1.2.2)) :=
    Primrec.not.comp (PrimrecPred.decide (PrimrecRel.comp Primrec.eq he
      (Primrec.option_some.comp (Primrec.encode.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
  refine ⟨c, fun a k => decide (a.2.1 ≤ (Nat.unpair k).2) &&
      !decide (Code.evaln (Nat.unpair k).1 c (encode (a.1, Nat.bits (Nat.unpair k).2)) = none) &&
      !decide (Code.evaln (Nat.unpair k).1 c (encode (a.1, Nat.bits (Nat.unpair k).2)) =
        some (encode a.2.2)), hc', ?_, ?_⟩
  · exact Primrec.to_comp (Primrec.and.comp (Primrec.and.comp hle hn1) hn2)
  · intro a
    constructor
    · rintro ⟨k, hk⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        at hk
      obtain ⟨⟨hle', hne⟩, hne2⟩ := hk
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
      have hev := Code.evaln_sound hw
      rw [hc', encodek] at hev
      obtain ⟨z, hz, rfl⟩ := Part.mem_map_iff _ |>.1 (by simpa using hev)
      refine ⟨_, hle', z, fun hzy => hne2 ?_, hz⟩
      rw [hw, hzy]
    · rintro ⟨m, hle', z, hzy, hz⟩
      have hev : encode z ∈ Code.eval c (encode (a.1, Nat.bits m)) := by
        rw [hc', encodek]
        have : encode z ∈ Part.map encode (G (a.1, Nat.bits m)) :=
          Part.mem_map_iff _ |>.2 ⟨z, hz, rfl⟩
        simpa using this
      obtain ⟨s, hs⟩ := Code.evaln_complete.1 hev
      refine ⟨Nat.pair s m, ?_⟩
      dsimp only
      rw [Nat.unpair_pair, hs]
      simp [hle', hzy]

/-- Step 1 of the proof of `exists_const_iInf_setCondK_atLeast_eq_plainK_jump`:
the `0'`-search. For every computable decompressor `G` there is a `haltingOracle`-computable
decompressor `D` such that whenever a program `p` satisfies `G (p, Nat.bits m) = x` for all
`m ≥ N`, then `D (p, []) = x`.

Proof idea: with `0'` search for a pair `(N', y)` such that no `m ≥ N'` has `G (p, bits m)`
halting with an output different from `y` (a `Π⁰₁`, i.e. co-enumerable, property, decided by
`0'` through `exists_computableInJump_semidecide`) and output `y`. The pair `(N, x)` satisfies
the property, so the search halts; for every `m ≥ max N N'` we get `G (p, bits m) = x` defined
and equal to `y`, hence `y = x`. -/
private theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump_search {G : Map}
    (hG : isDecompressor G) :
    ∃ D : Map, IsDecompressorIn haltingOracle D ∧
      ∀ (p x : BitString) (N : ℕ), (∀ m ≥ N, produces G p (Nat.bits m) x) →
        produces D p [] x := by
  classical
  obtain ⟨c, g, hc', hg, hgspec⟩ :=
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_search_aux_bad hG
  obtain ⟨h, hh, hspec⟩ := exists_computableInJump_semidecide hg
  have hhalt : haltingChi = haltingOracle := by
    funext n
    simp only [haltingChi, haltingOracle, charOracle, haltingSet, Set.mem_ofPred_eq]
    congr
  have hh' : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ)) h := by
    simpa [ComputableInJump, hhalt] using hh
  let yOf : ℕ → BitString := fun k =>
    (Encodable.decode (α := BitString) (Nat.unpair (Nat.unpair k).2).2).getD []
  let E : BitString × ℕ → Bool := fun q =>
    decide (Nat.Partrec.Code.evaln (Nat.unpair (Nat.unpair q.2).2).1 c
      (Encodable.encode (q.1, Nat.bits (Nat.unpair q.2).1)) = some (Encodable.encode (yOf q.2)))
  let P : BitString × ℕ → Bool := fun q =>
    (!h (q.1, (Nat.unpair q.2).1, yOf q.2)) && E q
  have hyOf : Primrec yOf :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))) (Primrec.const [])
  have hyOf' : Primrec fun q : BitString × ℕ => yOf q.2 := hyOf.comp Primrec.snd
  have hE : Primrec E := by
    have h1 : Primrec fun q : BitString × ℕ => (Nat.unpair (Nat.unpair q.2).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
    have h2 : Primrec fun q : BitString × ℕ =>
        Encodable.encode (q.1, Nat.bits (Nat.unpair q.2).1) :=
      Primrec.encode.comp (Primrec.pair Primrec.fst
        (primrec_natBits.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
    have he : Primrec fun q : BitString × ℕ =>
        Nat.Partrec.Code.evaln (Nat.unpair (Nat.unpair q.2).2).1 c
          (Encodable.encode (q.1, Nat.bits (Nat.unpair q.2).1)) :=
      Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair h1 (Primrec.const c)) h2)
    exact PrimrecPred.decide (PrimrecRel.comp Primrec.eq he
      (Primrec.option_some.comp (Primrec.encode.comp hyOf')))
  have hP : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ)) P := by
    have hpart : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ))
        fun q : BitString × ℕ => h (q.1, (Nat.unpair q.2).1, yOf q.2) :=
      hh'.comp (ComputableIn.pair ComputableIn.fst
        (ComputableIn.pair
          (Computable.computableIn (Primrec.to_comp (Primrec.fst.comp
            (Primrec.unpair.comp Primrec.snd))))
          (Computable.computableIn hyOf'.to_comp)))
    have hnot : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ))
        fun q : BitString × ℕ => !h (q.1, (Nat.unpair q.2).1, yOf q.2) :=
      (Computable.computableIn (Primrec.not.to_comp)).comp hpart
    have hand : ComputableIn ({haltingOracle} : Set (ℕ →. ℕ))
        fun p : Bool × Bool => p.1 && p.2 :=
      Computable.computableIn Primrec.and.to_comp
    exact hand.comp (hnot.pair hE.to_comp.computableIn)
  have hP2 : ComputableIn₂ ({haltingOracle} : Set (ℕ →. ℕ))
      fun (a : BitString × BitString) (k : ℕ) => P (a.1, k) :=
    ComputableIn₂.mk (hP.comp (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst)
      ComputableIn.snd))
  have hrf : PartrecIn ({haltingOracle} : Set (ℕ →. ℕ))
      fun a : BitString × BitString => Nat.rfind fun k => (Part.some (P (a.1, k)) : Part Bool) :=
    PartrecIn.rfind (hP2.partrecIn₂)
  have hmap := PartrecIn.map hrf
    (g := fun (_ : BitString × BitString) (k : ℕ) => yOf k)
    (ComputableIn₂.mk (Computable.computableIn (Primrec.to_comp (hyOf.comp Primrec.snd))))
  refine ⟨fun a => (Nat.rfind fun k => (Part.some (P (a.1, k)) : Part Bool)).map yOf, ?_, ?_⟩
  · exact (PointToSet.isDecompressorIn_iff_partrecIn _ _).2 hmap
  · intro p x N hN
    have hxN : ∀ m, N ≤ m → x ∈ G (p, Nat.bits m) := fun m hm => hN m hm
    -- the search halts
    have hex : ∃ k, P (p, k) = true := by
      have hev : Encodable.encode x ∈ Nat.Partrec.Code.eval c
          (Encodable.encode (p, Nat.bits N)) := by
        rw [hc', Encodable.encodek]
        have : Encodable.encode x ∈ Part.map Encodable.encode (G (p, Nat.bits N)) :=
          Part.mem_map_iff _ |>.2 ⟨x, hxN N le_rfl, rfl⟩
        simpa using this
      obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.1 hev
      refine ⟨Nat.pair N (Nat.pair s (Encodable.encode x)), ?_⟩
      have hh0 : h (p, N, x) = false := by
        by_contra hne
        have hne' : h (p, N, x) = true := by simpa using hne
        obtain ⟨m, hm, z, hzx, hz⟩ := (hgspec (p, N, x)).1 ((hspec (p, N, x)).1 hne')
        exact hzx (Part.mem_unique hz (hxN m hm))
      simpa [P, E, yOf, hh0] using Option.mem_def.1 hs
    have hmem : Nat.find hex ∈ Nat.rfind fun k => (Part.some (P (p, k)) : Part Bool) :=
      Nat.mem_rfind.2 ⟨by simp [Nat.find_spec hex], fun {m} hm => by
        simp [Nat.find_min hex hm]⟩
    refine Part.mem_map_iff _ |>.2 ⟨Nat.find hex, hmem, ?_⟩
    have hPk := Nat.find_spec hex
    set k := Nat.find hex
    simp only [P, E, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hPk
    obtain ⟨hnb, -⟩ := hPk
    by_contra hne
    have hne' : x ≠ yOf k := fun e => hne e.symm
    have hbad := (hspec (p, (Nat.unpair k).1, yOf k)).2 ?_
    · rw [hnb] at hbad
      exact Bool.false_ne_true hbad
    · refine (hgspec (p, (Nat.unpair k).1, yOf k)).2 ?_
      exact ⟨max N (Nat.unpair k).1, le_max_right _ _, x, hne', hxN _ (le_max_left _ _)⟩

/-- Finite approximations of a `0'`-computable map: a computable list-valued function `L` of the
stage `m` whose entries `(p, u, z)` are sound for short oracle prefixes `u' ≤ u` from some stage
on, and complete. -/
private theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_approx {V : Map}
    (hV : IsDecompressorIn (charOracle jumpSet) V) :
    ∃ L : ℕ → List (BitString × ℕ × BitString), Computable L ∧
      (∀ u, ∃ M, ∀ m ≥ M, ∀ p u' z, (p, u', z) ∈ L m → u' ≤ u → produces V p [] z) ∧
      (∀ p x, produces V p [] x → ∃ u M, ∀ m ≥ M, (p, u, x) ∈ L m) := by
  classical
  obtain ⟨Φ, hΦ, -, hex⟩ := PointToSet.exists_exact_string_operator
    (fun k => if k ∈ jumpSet then 1 else 0) (mapToNatFun V) hV
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hΦ
  have hceval : ∀ w : List ℕ × ℕ, c.eval (Encodable.encode w) = Φ w := by
    intro w
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.map_id' (fun _ => rfl) _
  -- the stage-`m` approximation of the first `u` bits of `0'`
  let pre : ℕ → ℕ → List ℕ := fun m u =>
    (List.range u).map fun k => bif (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k)
                                  k).isSome then 1 else 0
  let entry : ℕ → ℕ → Option (BitString × ℕ × BitString) := fun m r =>
    (Encodable.decode (α := BitString) r.unpair.1).bind fun p =>
      (Nat.Partrec.Code.evaln m c (Encodable.encode (pre m r.unpair.2,
        Encodable.encode (p, ([] : BitString))))).bind fun v =>
        (Encodable.decode (α := BitString) v).map fun z => (p, r.unpair.2, z)
  have hpre_prim : Primrec₂ pre := by
    have hg : Primrec₂ (fun (a : ℕ × ℕ) (k : ℕ) =>
        bif (Nat.Partrec.Code.evaln a.1 (Denumerable.ofNat Nat.Partrec.Code k) k).isSome then 1 else
          0) := by
      have hev : Primrec (fun b : (ℕ × ℕ) × ℕ =>
          Nat.Partrec.Code.evaln b.1.1 (Denumerable.ofNat Nat.Partrec.Code b.2) b.2) :=
        Nat.Partrec.Code.primrec_evaln.comp (((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.snd)).pair Primrec.snd)
      exact (Primrec.cond (Primrec.option_isSome.comp hev) (Primrec.const 1)
        (Primrec.const 0)).to₂
    exact (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hg).to₂
  have hentry_prim : Primrec₂ entry := by
    have hdec : Primrec (fun a : ℕ × ℕ => Encodable.decode (α := BitString) a.2.unpair.1) :=
      Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
    have hu : Primrec (fun b : (ℕ × ℕ) × BitString => b.1.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
    have hin : Primrec (fun b : (ℕ × ℕ) × BitString => Encodable.encode (pre b.1.1 b.1.2.unpair.2,
        Encodable.encode (b.2, ([] : BitString)))) :=
      Primrec.encode.comp ((hpre_prim.comp (Primrec.fst.comp Primrec.fst) hu).pair
        (Primrec.encode.comp (Primrec.snd.pair (Primrec.const ([] : BitString)))))
    have hev : Primrec (fun b : (ℕ × ℕ) × BitString => Nat.Partrec.Code.evaln b.1.1 c
        (Encodable.encode (pre b.1.1 b.1.2.unpair.2, Encodable.encode (b.2, ([] : BitString))))) :=
      Nat.Partrec.Code.primrec_evaln.comp (((Primrec.fst.comp Primrec.fst).pair
          (Primrec.const c)).pair hin)
    have hlast : Primrec₂ (fun (b : (ℕ × ℕ) × BitString) (v : ℕ) =>
        (Encodable.decode (α := BitString) v).map fun z => (b.2, b.1.2.unpair.2, z)) :=
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((hu.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂).to₂
    exact (Primrec.option_bind hdec (Primrec.option_bind hev hlast).to₂).to₂
  -- the approximations of `0'` converge on `[0, u)`
  have hconv : ∀ u, ∃ M, ∀ m ≥ M, ∀ k < u,
      (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome = true ↔
        k ∈ jumpSet := by
    intro u
    induction u with
    | zero => exact ⟨0, fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ u ih =>
      obtain ⟨M, hM⟩ := ih
      by_cases hu : u ∈ jumpSet
      · have hu' : ((Denumerable.ofNat Nat.Partrec.Code u).eval u).Dom := hu
        obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hu'
        obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hv
        refine ⟨max M s, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m (le_of_max_le_left hm) k hk
        · refine ⟨fun _ => hu, fun _ => ?_⟩
          exact Option.isSome_iff_exists.mpr
            ⟨v, Nat.Partrec.Code.evaln_mono (le_of_max_le_right hm) hs⟩
      · refine ⟨M, fun m hm k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hM m hm k hk
        · refine ⟨fun h => ?_, fun h => absurd h hu⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩
  have hpre_eq : ∀ u, ∃ M, ∀ m ≥ M, ∀ u' ≤ u,
      pre m u' = (List.range u').map (fun k => if k ∈ jumpSet then 1 else 0) := by
    intro u
    obtain ⟨M, hM⟩ := hconv u
    refine ⟨M, fun m hm u' hu' => List.map_congr_left fun k hk => ?_⟩
    have hiff := hM m hm k (lt_of_lt_of_le (List.mem_range.mp hk) hu')
    by_cases hj : k ∈ jumpSet
    · simp [hj, hiff.mpr hj]
    · have hf : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome =
          false := by
        cases h : (Nat.Partrec.Code.evaln m (Denumerable.ofNat Nat.Partrec.Code k) k).isSome
        · rfl
        · exact absurd (hiff.mp h) hj
      simp [hj, hf]
  refine ⟨fun m => (List.range m).filterMap (entry m),
    (Primrec.listFilterMap Primrec.list_range hentry_prim).to_comp, ?_, ?_⟩
  · intro u
    obtain ⟨M, hM⟩ := hpre_eq u
    refine ⟨M, fun m hm p u' z hmem hu' => ?_⟩
    obtain ⟨r, -, hr⟩ := List.mem_filterMap.mp hmem
    simp only [entry, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
    obtain ⟨p', hp', v, hv, z', hz', heq⟩ := hr
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rw [hM m hm _ hu'] at hv
    have hvΦ := Nat.Partrec.Code.evaln_sound hv
    rw [hceval] at hvΦ
    have hvf := (hex _ v).mpr ⟨_, hvΦ⟩
    simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some,
      Part.mem_map_iff] at hvf
    obtain ⟨z'', hz'', rfl⟩ := hvf
    rw [Encodable.encodek, Option.some_inj] at hz'
    rw [← hz']
    exact hz''
  · intro p x hpx
    have hmemf : Encodable.encode x ∈ mapToNatFun V (Encodable.encode (p, ([] : BitString))) := by
      simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some]
      exact Part.mem_map _ hpx
    obtain ⟨u, hu⟩ := (hex _ _).mp hmemf
    rw [← hceval] at hu
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hu
    obtain ⟨M, hM⟩ := hpre_eq u
    refine ⟨u, max (max M t) (Nat.pair (Encodable.encode p) u + 1), fun m hm => ?_⟩
    have hmM : M ≤ m := le_trans (le_max_left _ _) (le_of_max_le_left hm)
    have hmt : t ≤ m := le_trans (le_max_right _ _) (le_of_max_le_left hm)
    have hmr : Nat.pair (Encodable.encode p) u < m := le_of_max_le_right hm
    refine List.mem_filterMap.mpr ⟨Nat.pair (Encodable.encode p) u, List.mem_range.mpr hmr, ?_⟩
    have hev := Nat.Partrec.Code.evaln_mono hmt ht
    rw [← hM m hmM u le_rfl] at hev
    simp only [entry, Nat.unpair_pair, Encodable.encodek, Option.bind_some]
    rw [Option.mem_def.mp hev]
    simp [Encodable.encodek]

/-- The candidate values of the program `p` at stage `m` in a list of approximation entries, with
their oracle-prefix length. -/
private def exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand
    (a : BitString × List (BitString × ℕ × BitString)) : List (ℕ × BitString) :=
  a.2.filterMap fun e => if e.1 = a.1 then some (e.2.1, e.2.2) else none

/-- The selected value: the candidate with the shortest oracle prefix. -/
private def exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel
    (a : BitString × List (BitString × ℕ × BitString)) : Option BitString :=
  ((exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand a).argmin
    Prod.fst).map Prod.snd

private theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel_primrec :
    Primrec exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel := by
  unfold exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand List.argmin List.argAux
  have hc : Primrec (fun a : BitString × List (BitString × ℕ × BitString) =>
      a.2.filterMap fun e => if e.1 = a.1 then some (e.2.1, e.2.2) else none) := by
    refine Primrec.listFilterMap Primrec.snd ?_
    refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)) ?_ (Primrec.const none)
    exact Primrec.option_some.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hstep : Primrec₂ (fun (_ : BitString × List (BitString × ℕ × BitString))
      (q : Option (ℕ × BitString) × (ℕ × BitString)) =>
      (Option.casesOn q.1 (some q.2) fun c => if q.2.1 < c.1 then some q.2 else some c :
        Option (ℕ × BitString))) := by
    refine Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) ?_
    refine Primrec.ite (Primrec.nat_lt.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp Primrec.snd)) ?_ (Primrec.option_some.comp Primrec.snd)
    exact Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.option_map (Primrec.list_foldl hc (Primrec.const none) hstep)
    (Primrec.snd.comp Primrec.snd)

/-- Step 2 of the proof of `exists_const_iInf_setCondK_atLeast_eq_plainK_jump`:
the limit lemma. For every `haltingOracle`-computable decompressor `D` there is a computable
decompressor `G` such that whenever `D (p, []) = x`, then `G (p, Nat.bits m) = x` for all
sufficiently large `m`.

Proof idea: `G (p, bits m)` runs the oracle machine for `D` on `(p, [])` for `m` steps, answering
each oracle query `e` by "`φ_e (e)` halts within `m` steps". For large `m` the answers of the
(finitely many) queries of the true computation are correct, and the computation halts within `m`
steps; formally by induction on `RecursiveIn`, with an approximation `g a m` of each function. -/
private theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit {D : Map}
    (hD : IsDecompressorIn haltingOracle D) :
    ∃ G : Map, isDecompressor G ∧
      ∀ (p x : BitString), produces D p [] x →
        ∃ N : ℕ, ∀ m ≥ N, produces G p (Nat.bits m) x := by
  classical
  obtain ⟨L, hLc, hsound, hcomp⟩ :=
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_approx
      (by rw [charOracle_jumpSet]; exact hD)
  let g : BitString × BitString → Option BitString := fun a =>
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel (a.1, L (bitsToNat a.2))
  have hg : Computable g :=
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel_primrec.to_comp.comp
      (Computable.fst.pair (hLc.comp (bitsToNat_primrec.to_comp.comp Computable.snd)))
  refine ⟨fun a => (g a : Part BitString), Computable.ofOption hg, fun p x hpx => ?_⟩
  obtain ⟨u, M, hM⟩ := hcomp p x hpx
  obtain ⟨M', hM'⟩ := hsound u
  refine ⟨max M M', fun m hm => ?_⟩
  have hxm : (p, u, x) ∈ L m := hM m (le_of_max_le_left hm)
  have hmem : (u, x) ∈ (exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand
      (p, L m)) := by
    unfold exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand
    exact List.mem_filterMap.mpr ⟨(p, u, x), hxm, by simp⟩
  have hne : (exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand (p, L m)).argmin
      Prod.fst ≠ none := by
    rw [Ne, List.argmin_eq_none]
    exact List.ne_nil_of_mem hmem
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
  have hamem := List.argmin_mem ha
  have hale : a.1 ≤ u := List.le_of_mem_argmin hmem ha
  have hax : a.2 = x := by
    unfold exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_cand at hamem
    obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hamem
    split_ifs at hea with hep
    · simp only [Option.some.injEq] at hea
      have hprod : produces D p [] a.2 := by
        have := hM' m (le_of_max_le_right hm) e.1 e.2.1 e.2.2 he
        subst hea
        rw [hep] at this
        exact this (by simpa using hale)
      exact Part.mem_unique hprod hpx
  change x ∈ ((g (p, Nat.bits m) : Option BitString) : Part BitString)
  have : g (p, Nat.bits m) = some x := by
    simp only [g, bitsToNat_bits,
      exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit_sel, ha, Option.map_some,
      hax]
  rw [this]
  exact Part.mem_some _

/-- **SUV Theorem 131 (Section 6.4.2, printed p. 204).**
`lim_{n → ∞} C(x ‖ ≥ n) = C^{0'}(x) + O(1)`. The sequence `n ↦ C(x ‖ ≥ n)` is non-increasing
(`antitone_setCondK_atLeast`), so its limit is the infimum `⨅ n`.

Proof idea: `≥` — a program that maps all large numbers to `x` is a `0'`-description of `x`.
With `0'` one finds `N` and `y` such that the program maps no `n ≥ N` to an object other than
`y`, a co-enumerable property. `≤` — for a `0'`-description `y` of `x`, the program "with input
`N`, run `N` steps of the enumeration of `0'` and decompress `y` with this approximation" has
complexity `≤ l(y) + O(1)` and outputs `x` for all large `N`. -/
theorem exists_const_iInf_setCondK_atLeast_eq_plainK_jump {U : Map} (hU : IsOptimalSetCond U)
    {V : Map} (hV : IsOptimalConditionalIn haltingOracle V) :
    ∃ c : ℕ, ∀ x,
      (⨅ n, setCondK U x (atLeast n)) ≤ plainK V x + c ∧
        plainK V x ≤ (⨅ n, setCondK U x (atLeast n)) + c := by
  obtain ⟨G, hG, hGprop⟩ :=
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_limit hV.1
  obtain ⟨D, hD, hDprop⟩ :=
    exists_const_iInf_setCondK_atLeast_eq_plainK_jump_search hU.1
  obtain ⟨c₁, hc₁⟩ := hV.2 D hD
  obtain ⟨c₂, hc₂⟩ := hU.2 G hG
  have hc₁' : (c₁ : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_left c₁ c₂
  have hc₂' : (c₂ : ℕ∞) ≤ ((max c₁ c₂ : ℕ) : ℕ∞) := by exact_mod_cast le_max_right c₁ c₂
  refine ⟨max c₁ c₂, fun x => ⟨?_, ?_⟩⟩
  · by_cases htop : plainK V x = ⊤
    · rw [htop, top_add]; exact le_top
    obtain ⟨p, hp, hpl⟩ : plainK V x ∈ candidateLengths V x [] :=
      csInf_mem (s := candidateLengths V x []) (by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        exact htop (by simp [plainK, condK, hne]))
    obtain ⟨N, hN⟩ := hGprop p x hp
    have h3 : setCondK G x (atLeast N) ≤ p.length := by
      refine sInf_le ⟨p, ?_, rfl⟩
      rintro y ⟨m, hm, rfl⟩
      exact hN m hm
    calc (⨅ n, setCondK U x (atLeast n)) ≤ setCondK U x (atLeast N) := iInf_le _ N
      _ ≤ setCondK G x (atLeast N) + c₂ := hc₂ x (atLeast N)
      _ ≤ plainK V x + ((max c₁ c₂ : ℕ) : ℕ∞) := by
        rw [← hpl]; exact add_le_add h3 hc₂'
  · rw [ENat.iInf_add]
    refine le_iInf fun n => ?_
    have h4 : plainK D x ≤ setCondK U x (atLeast n) := by
      refine le_sInf ?_
      rintro l ⟨p, hp, rfl⟩
      refine sInf_le ⟨p, hDprop p x n fun m hm => hp _ ⟨m, hm, rfl⟩, rfl⟩
    calc plainK V x ≤ plainK D x + c₁ := hc₁ x []
      _ ≤ setCondK U x (atLeast n) + ((max c₁ c₂ : ℕ) : ℕ∞) := add_le_add h4 hc₁'

/-- **SUV Section 6.4.2 (printed p. 205), unnumbered.** `sup_{m ≥ n} C(x | m) ≤ C(x ‖ ≥ n)` up to
`O(1)`: a program that works for all `m ≥ n` works for each of them. -/
theorem exists_const_iSup_condK_le_setCondK_atLeast {U : Map} (hU : IsOptimalSetCond U)
    {V : Map} (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ x n, (⨆ m ≥ n, condK V x (Nat.bits m)) ≤ setCondK U x (atLeast n) + c := by
  obtain ⟨c, hc⟩ := hV.2 U hU.1
  refine ⟨c, fun x n => iSup₂_le fun m hm => (hc x (Nat.bits m)).trans (add_le_add ?_ le_rfl)⟩
  exact sInf_le_sInf fun _ ⟨p, hp, hn⟩ => ⟨p, hp _ ⟨m, hm, rfl⟩, hn.symm⟩

/-- **SUV Section 6.4.2 (printed p. 205), lemma in the proof of Theorem 132.** For every `k`,
fewer than `2 ^ k` strings `x` have `C(x | n) < k` for all sufficiently large `n`. This holds for
every decompressor `D`.

Proof: otherwise take `2 ^ k` of them and an `n` beyond all their thresholds. These strings would
need pairwise different programs of length `< k` for the same condition `n`
(`exists_condK_ge_of_finset_card_pow`). -/
theorem encard_eventually_condK_lt_lt_two_pow (D : Map) (k : ℕ) :
    {x : BitString | ∀ᶠ n in Filter.atTop, condK D x (Nat.bits n) < k}.encard < 2 ^ k := by
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (not_lt.1 hcon)
  have htc' : t.encard = ((2 ^ k : ℕ) : ℕ∞) := by rw [htc]; norm_cast
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htc'
  have hcard : htfin.toFinset.card = 2 ^ k := by
    have := htfin.encard_eq_coe_toFinset_card
    rw [htc'] at this
    exact_mod_cast this.symm
  have hev : ∀ᶠ n in Filter.atTop, ∀ x ∈ t, condK D x (Nat.bits n) < k :=
    (Filter.eventually_all_finite htfin).2 fun x hx => hts hx
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨x, hx, hle⟩ :=
    exists_condK_ge_of_finset_card_pow D htfin.toFinset (Nat.bits n) k hcard.ge
  exact absurd (hn x (htfin.mem_toFinset.1 hx)) (not_lt.2 hle)

end GeneralScheme
end Kolmogorov
