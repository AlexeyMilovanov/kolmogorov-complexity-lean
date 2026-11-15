import KolmogorovMathlib.Complexity.GeneralScheme.OracleDefs
import KolmogorovMathlib.Complexity.GeneralScheme.Conditional
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.Prefix.StableDecompressors
import KolmogorovMathlib.Complexity.InfiniteSequences.PrefixComplexity
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.Oracle.PrefixComplexity.MonotonicityThreshold
import KolmogorovMathlib.Prefix.Kraft
import KolmogorovMathlib.MonotoneComplexity.ComputableListTools
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Problem Oracle Limit

Relativization of prefix complexity to an oracle `A` as a limit of conditional complexities.

For an optimal `A`-prefix decompressor `U` and an optimal conditional description mode `S`,
`exists_const_KP_oracle_eq_lim_condModeComplexity` shows that `K^A(x)` agrees up to `O(1)` with
the liminf and the limsup of the complexities `K(x | Aₙ)` of `x` given the length-`n` prefixes
`Aₙ` of the characteristic sequence of `A`. The module also contains
`exists_const_plainK_oracle_le_plainK`, stating that relativization does not increase plain
complexity (`C^A(x) ≤ C(x) + O(1)`). It formalizes problems of Section 6.4 of Shen, Uspensky and
Vereshchagin, "Kolmogorov complexity and algorithmic randomness".
-/

open scoped ENNReal

namespace Kolmogorov

namespace GeneralScheme

/-- The characteristic sequence of `A` is `A`-computable. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_charSeq
    (A : Set ℕ) : ComputableIn {charOracle A} (charSeq A) := by
  classical
  have h1 : PartrecIn {charOracle A} (fun n : ℕ => charOracle A n) :=
    PartrecIn.oracle _ (Set.mem_singleton _)
  have hp : Computable (fun a : ℕ => decide (a = 1)) :=
    ((PrimrecRel.decide Primrec.eq).comp Primrec.id (Primrec.const 1)).to_comp
  have h3 := PartrecIn.map h1
    (show ComputableIn₂ {charOracle A} (fun (_ : ℕ) (a : ℕ) => decide (a = 1)) from
      (hp.comp Computable.snd).computableIn)
  refine PartrecIn.of_eq h3 fun n => ?_
  by_cases hn : n ∈ A <;> simp [charOracle, charSeq, hn]

/-- The prefixes of the characteristic sequence of `A` are `A`-computable. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_prefix
    (A : Set ℕ) : ComputableIn {charOracle A} (cantorPrefix (charSeq A)) := by
  have hw := exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_charSeq A
  have hstep : ComputableIn {charOracle A} (fun p : ℕ × (ℕ × BitString) =>
      p.2.2 ++ [charSeq A p.2.1]) :=
    Computable.list_concat.computableIn.comp
      (ComputableIn.pair (ComputableIn.snd.comp ComputableIn.snd)
        (hw.comp (ComputableIn.fst.comp ComputableIn.snd)))
  have hrec := ComputableIn.nat_rec (f := @id ℕ) (g := fun _ => ([] : BitString))
    (h := fun _ (k, ih) => ih ++ [charSeq A k]) ComputableIn.id
    (ComputableIn.const []) hstep.to₂
  refine hrec.of_eq fun n => ?_
  change Nat.rec ([] : BitString) (fun k ih => ih ++ [charSeq A k]) n = cantorPrefix (charSeq A) n
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.rec ([] : BitString) (fun k ih => ih ++ [charSeq A k]) n ++ [charSeq A n] =
        cantorPrefix (charSeq A) (n + 1)
      rw [ih, cantorPrefix_succ]

/-- The `n`-th candidate triple of the search: the triple with code `n.unpair.1` (a default
triple if the code is invalid). -/
private def exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri (n : ℕ) :
    BitString × BitString × BitString :=
  (Encodable.decode (α := BitString × BitString × BitString) n.unpair.1).getD ([], [], [])

private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri_computable :
    Computable
      exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri :=
  Computable.option_getD
    (Computable.decode.comp (Primrec.fst.comp Primrec.unpair).to_comp)
    (Computable.const _)

private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri_pair
    (t : BitString × BitString × BitString) (s : ℕ) :
    exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri
      (Nat.pair (Encodable.encode t) s) = t := by
  simp [exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri]

open Classical in
/-- The search step: at stage `n` output `x` if the `n`-th candidate `(p', x, y)` has `chk` true
at the stage given by `n`, `p'` is a prefix of `p`, and `y` is a prefix of the characteristic
sequence of `A`. -/
private noncomputable def exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step
    (A : Set ℕ) (chk : BitString × BitString × BitString → ℕ → Bool)
    (a : BitString × BitString) (n : ℕ) : Option BitString :=
  cond (chk (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n) n.unpair.2
      && decide (a.1.take
          (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).1.length
        = (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).1)
      && decide (cantorPrefix (charSeq A)
          (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.2.length
        = (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.2))
    (some (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.1) none

private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_computable
    (A : Set ℕ) {chk : BitString × BitString × BitString → ℕ → Bool} (hchk : Computable₂ chk) :
    ComputableIn₂ {charOracle A}
      (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk) := by
  classical
  set tri := exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri with htri
  have htric : Computable tri :=
    exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri_computable
  have hpre := exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_prefix A
  have hdec : Computable (fun p : BitString × BitString => decide (p.1 = p.2)) :=
    primrec_decideEq.to_comp
  have hand : Computable (fun p : Bool × Bool => p.1 && p.2) := Primrec.and.to_comp
  have hF : Computable (fun q : Bool × BitString => cond q.1 (some q.2) none) :=
    Computable.cond Computable.fst (Computable.option_some.comp Computable.snd)
      (Computable.const none)
  have ht := htric.comp (Computable.snd (α := BitString × BitString) (β := ℕ))
  have hb1 := hchk.comp ht
    ((Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
      (α := (BitString × BitString) × ℕ))
  have hp1 := Computable.fst.comp (Computable.fst (α := BitString × BitString) (β := ℕ))
  have hq1 := Computable.fst.comp ht
  have hq3 := Computable.snd.comp (Computable.snd.comp ht)
  have hlen1 := Computable.list_length.comp hq1
  have hlen3 := Computable.list_length.comp hq3
  have htake := Primrec.list_take.to_comp.comp hlen1 hp1
  have hb2 := hdec.comp (htake.pair hq1)
  have hA3 := hpre.comp hlen3.computableIn
  have hb3 := hdec.computableIn.comp (hA3.pair hq3.computableIn)
  have hband1 := (hand.computableIn (O := {charOracle A})).comp
    (hb1.computableIn.pair hb2.computableIn)
  have hband := (hand.computableIn (O := {charOracle A})).comp (hband1.pair hb3)
  have hout := Computable.fst.comp (Computable.snd.comp ht)
  have hres := (hF.computableIn (O := {charOracle A})).comp (hband.pair hout.computableIn)
  exact hres.of_eq fun u => rfl

private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_some
    {A : Set ℕ} {chk : BitString × BitString × BitString → ℕ → Bool}
    {a : BitString × BitString} {n : ℕ} {x : BitString}
    (h : exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a n
      = some x) :
    chk (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n) n.unpair.2
        = true ∧
      (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).1 <+: a.1 ∧
      cantorPrefix (charSeq A)
          (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.2.length
        = (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.2 ∧
      (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri n).2.1 = x := by
  unfold exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step at h
  rw [Bool.cond_eq_ite] at h
  split_ifs at h with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact ⟨h1, List.prefix_iff_eq_take.mpr h2.symm, h3, Option.some.inj h⟩

private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_of
    (A : Set ℕ) {chk : BitString × BitString × BitString → ℕ → Bool}
    {a : BitString × BitString} {t : BitString × BitString × BitString} {s : ℕ}
    (hs : chk t s = true) (hp : t.1 <+: a.1)
    (hy : cantorPrefix (charSeq A) t.2.2.length = t.2.2) :
    exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a
      (Nat.pair (Encodable.encode t) s) = some t.2.1 := by
  unfold exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step
  rw [exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_tri_pair,
    Nat.unpair_pair]
  have hp' : a.1.take t.1.length = t.1 := (List.prefix_iff_eq_take.mp hp).symm
  simp [hs, hp', hy]

/-- Step 1a of the proof of `exists_const_KP_oracle_eq_lim_condModeComplexity`: the
`A`-machine that, on `p` (with condition `[]`), searches (relative to `A`, computing the prefixes
`Aₙ` from the oracle) for a triple `(p', x, y)` of `S` with `p'` a prefix of `p` and `y` a prefix of
the characteristic sequence of `A`, and outputs `x`, is an `A`-computable prefix-stable machine.
It is a function by `(≍, =) | ≍`-regularity of `S` (all prefixes of `charSeq A` are compatible),
and it outputs `x` on every `p` with `S p x Aₙ`. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable (A : Set ℕ)
    {S : BitString → BitString → BitString → Prop}
    (hS : IsCondDescriptionMode .compat .eq .compat S) :
    ∃ E : Map, IsDecompressorIn (charOracle A) E ∧ IsPrefixStableMachine E ∧
      ∀ x n p, S p x (cantorPrefix (charSeq A) n) → x ∈ E (p, []) := by
  obtain ⟨chk, hchk, -, hiff⟩ := IsRE.exists_stageApprox hS.1
  have hL : ∀ (a : BitString × BitString) (x : BitString),
      x ∈ Nat.rfindOpt
        (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a) →
      ∃ p' y, S p' x y ∧ p' <+: a.1 ∧ cantorPrefix (charSeq A) y.length = y := by
    intro a x hx
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hx
    obtain ⟨h1, h2, h3, h4⟩ :=
      exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_some
        (Option.mem_def.mp hn)
    refine ⟨_, _, ?_, h2, h3⟩
    rw [← h4]
    exact (hiff _).2 ⟨_, h1⟩
  have hR : ∀ (a : BitString × BitString) (p' x y : BitString), S p' x y → p' <+: a.1 →
      cantorPrefix (charSeq A) y.length = y →
      x ∈ Nat.rfindOpt
        (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a) := by
    intro a p' x y hS' hp hy
    obtain ⟨s, hs⟩ := (hiff (p', x, y)).1 hS'
    have hstep := exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_of A
      (a := a) hs hp hy
    have hdom : (Nat.rfindOpt
        (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a)).Dom :=
      Nat.rfindOpt_dom.2 ⟨_, _, Option.mem_def.mpr hstep⟩
    obtain ⟨x', hx'⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨p'', y'', hS'', hp'', hy''⟩ := hL a x' hx'
    have hcp : p' <+: p'' ∨ p'' <+: p' := by
      rcases le_total p'.length p''.length with h | h
      · exact Or.inl (List.prefix_of_prefix_length_le hp hp'' h)
      · exact Or.inr (List.prefix_of_prefix_length_le hp'' hp h)
    have hcy : y <+: y'' ∨ y'' <+: y := by
      rw [← hy, ← hy'']
      rcases le_total y.length y''.length with h | h
      · exact Or.inl (cantorPrefix_mono _ h)
      · exact Or.inr (cantorPrefix_mono _ h)
    have hxx : x = x' := hS.2 hS' hS'' hcp hcy
    rw [hxx]
    exact hx'
  refine ⟨fun a => Nat.rfindOpt
    (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step A chk a),
    ?_, ?_, ?_⟩
  · refine (PointToSet.isDecompressorIn_iff_partrecIn _ _).2 ?_
    exact PartrecIn.rfindOpt
      (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable_step_computable A hchk)
  · intro c p p2 z hz hp
    obtain ⟨p', y, hS', hp', hy⟩ := hL (p, c) z hz
    exact hR (p2, c) p' z y hS' (hp'.trans hp) hy
  · intro x n p h
    exact hR (p, []) p x _ h (List.prefix_refl p) (by simp)

/-- The graph relation of an `A`-computable map is `A`-enumerable. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree_aux_isREIn
    (A : Set ℕ) {E : Map} (hE : IsDecompressorIn (charOracle A) E) :
    PointToSet.IsREIn A (fun pw : BitString × BitString => produces E pw.1 [] pw.2) := by
  have hU : PartrecIn {charOracle A} E := (PointToSet.isDecompressorIn_iff_partrecIn _ _).mp hE
  refine ⟨fun pw => (E (pw.1, [])).bind fun x =>
    cond (decide (x = pw.2)) (Part.some 0) Part.none, ?_, fun pw ↦ ?_⟩
  · have hpair : ComputableIn {charOracle A}
        (fun pw : BitString × BitString => (pw.1, ([] : BitString))) :=
      (Computable.pair Computable.fst (Computable.const [])).computableIn
    have hguard : ComputableIn {charOracle A}
        (fun p : (BitString × BitString) × BitString => decide (p.2 = p.1.2)) :=
      ((PrimrecRel.decide Primrec.eq).to_comp.comp Computable.snd
        (Computable.snd.comp Computable.fst)).computableIn
    exact PartrecIn.bind (PartrecIn.comp hU hpair)
      (PartrecIn.cond hguard (ComputableIn.const 0).partrecIn PartrecIn.none)
  · rw [Part.dom_iff_mem]
    constructor
    · intro h
      exact ⟨0, Part.mem_bind_iff.mpr ⟨pw.2, h, by simp⟩⟩
    · rintro ⟨v, hv⟩
      obtain ⟨x, hx, hcond⟩ := Part.mem_bind_iff.mp hv
      by_cases hxy : x = pw.2
      · rwa [hxy] at hx
      · simp [hxy] at hcond

/-- Kraft inequality for the weights `2 ^ (-KP E x [])` of a prefix-stable machine: shortest
descriptions of distinct outputs are prefix-incomparable. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree_aux_kraft
    {E : Map} (hs : IsPrefixStableMachine E) :
    (∑' w : {x : BitString // KP E x [] ≠ ⊤},
      (2 : ℝ≥0∞) ^ (-(((KP E w.1 []).toNat : ℕ) : ℝ))) ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun t => ?_
  have hex : ∀ w : {x : BitString // KP E x [] ≠ ⊤}, ∃ p, produces E p [] w.1 ∧
      (programLength p : ENat) = KP E w.1 [] := fun w => exists_program_of_KP_ne_top w.2
  choose p hp hlen using hex
  have hinj : Function.Injective p := by
    intro w1 w2 h
    apply Subtype.ext
    have h1 := hp w1
    have h2 := hp w2
    rw [h] at h1
    exact Part.mem_unique h1 h2
  have hpf : IsPrefixFree ((t.image p : Finset BitString) : Set BitString) := by
    intro q1 hq1 q2 hq2 hpre
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hq1 hq2
    obtain ⟨w1, _, rfl⟩ := hq1
    obtain ⟨w2, _, rfl⟩ := hq2
    have hmem : w1.1 ∈ E (p w2, []) := hs [] (p w1) (p w2) w1.1 (hp w1) hpre
    have : w1 = w2 := Subtype.ext (Part.mem_unique hmem (hp w2))
    rw [this]
  have hkr := finset_kraft_progWeight_le_one _ hpf
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at hkr
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_)) hkr
  have hn : ((KP E w.1 []).toNat : ℕ) = programLength (p w) := by
    have := hlen w
    rw [← this]; simp
  rw [hn, progWeight, ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.inv_pow]

/-- Step 1b of the proof of `exists_const_KP_oracle_eq_lim_condModeComplexity`:
relativized "prefix-stable versus prefix-free" conversion (SUV Section 4.7). An `A`-computable
prefix-stable machine `E` has an `A`-computable prefix machine `D` with
`KP D x [] ≤ KP E x [] + c` for all `x`. (Kraft–Chaitin, relativized: per output `x` request only
descriptions strictly shorter than those requested before for `x`, with length `l(p) + 2`;
`KP E`-minimal descriptions of distinct outputs are incomparable by prefix stability and
functionality of `E`; the total weight per `x` is at most `2 · 2^{-KP E x [] - 2}`.) -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree (A : Set ℕ)
    {E : Map} (hE : IsDecompressorIn (charOracle A) E)
    (hs : IsPrefixStableMachine E) :
    ∃ D : Map, IsDecompressorIn (charOracle A) D ∧ IsPrefixMachine D ∧
      ∃ c : ℕ, ∀ x, KP D x [] ≤ KP E x [] + c := by
  classical
  let F : BitString → Prop := fun x => KP E x [] ≠ ⊤
  let g : Subtype F → ℝ := fun w => (((KP E w.1 []).toNat : ℕ) : ℝ)
  have hg : PointToSet.IsUpperSemicomputableOnIn A F g := by
    refine ⟨fun wq : BitString × ℚ => ∃ p, produces E p [] wq.1 ∧ (p.length : ℚ) < wq.2,
      ?_, ?_, ?_⟩
    · have hproduces : PointToSet.IsREIn A (fun t : (BitString × ℚ) × BitString =>
          produces E t.2 [] t.1.1) :=
        (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree_aux_isREIn A hE).comp
          (f := fun t : (BitString × ℚ) × BitString => (t.2, t.1.1))
          (Computable.snd.pair (Computable.fst.comp Computable.fst)).computableIn
      have hlength : Computable (fun t : (BitString × ℚ) × BitString =>
          decide ((t.2.length : ℚ) < t.1.2)) :=
        computable₂_ratLt.comp
          (computable_nat_to_rat.comp (Primrec.list_length.comp Primrec.snd).to_comp)
          (Computable.snd.comp Computable.fst)
      exact (hproduces.and (PointToSet.isREIn_of_computable_decide hlength)).exists
    · rintro w q ⟨p, hp, hlt⟩
      have hle : KP E w [] ≤ (programLength p : ENat) := KP_le_programLength_of_produces hp
      have hF : F w := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
      refine ⟨hF, ?_⟩
      have hn : (KP E w []).toNat ≤ p.length :=
        ENat.toNat_le_of_le_natCast hle
      have h1 : (((KP E w []).toNat : ℕ) : ℝ) ≤ (p.length : ℝ) := by exact_mod_cast hn
      have h2 : (p.length : ℝ) < (q : ℝ) := by exact_mod_cast hlt
      exact h1.trans_lt h2
    · intro w ε hε
      obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top w.2
      have hn : (KP E w.1 []).toNat = p.length := by
        rw [← hlen]; simp
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show g w < g w + ε by linarith)
      refine ⟨q, ⟨p, hp, ?_⟩, hq2⟩
      have : (p.length : ℝ) < (q : ℝ) := by
        have : g w = (p.length : ℝ) := by simp only [g, hn]
        rw [← this]; exact hq1
      exact_mod_cast this
  obtain ⟨c, hc⟩ := PointToSet.oracle_coding_finite_mass A F g hg 1
    (exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree_aux_kraft hs)
    ENNReal.one_lt_top
  have hspec := PointToSet.exists_optimalOraclePrefix_spec A
  refine ⟨PointToSet.optimalOraclePrefix A, hspec.1, hspec.2.1, c, fun x => ?_⟩
  by_cases hx : KP E x [] = ⊤
  · rw [hx]; simp
  · have h1 := hc ⟨x, hx⟩
    have h2 : PointToSet.oracleComplexity A x ≤ (KP E x []).toNat + c := by
      have : (PointToSet.oracleComplexity A x : ℝ) ≤ (((KP E x []).toNat + c : ℕ) : ℝ) := by
        simpa [g] using h1
      exact_mod_cast this
    have h3 : KP (PointToSet.optimalOraclePrefix A) x [] =
        (PointToSet.oracleComplexity A x : ENat) :=
      (PointToSet.oraclePrefixComplexity_coe A x []).symm
    rw [h3]
    calc (PointToSet.oracleComplexity A x : ENat)
        ≤ (((KP E x []).toNat + c : ℕ) : ENat) := by exact_mod_cast h2
      _ = KP E x [] + c := by
        rw [Nat.cast_add, ENat.natCast_toNat hx]

/-- The bits of a finite oracle `y` read as the list of its `0/1` answers. -/
private def exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits
    (y : BitString) : List ℕ :=
  y.map fun b => bif b then 1 else 0

/-- The entry of `H(y)` with index `idx = ⟨r, k⟩`: decode `q` from `r`, run `c` on the prefix of
`y` of length `k` and `(q, [])` for `l(y)` steps, and decode the output as `z`. -/
private def exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_entry
    (c : Nat.Partrec.Code) (y : BitString) (idx : ℕ) : Option (BitString × BitString) :=
  if idx.unpair.1 ≤ y.length ∧ idx.unpair.2 ≤ y.length then
    (Encodable.decode (α := BitString) idx.unpair.1).bind fun q =>
      (Nat.Partrec.Code.evaln y.length c (Encodable.encode
        (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits
          (y.take idx.unpair.2), Encodable.encode (q, ([] : BitString))))).bind fun v =>
        (Encodable.decode (α := BitString) v).map fun z => (q, z)
  else none

/-- The finite list `H(y)`. -/
private def exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_H
    (c : Nat.Partrec.Code) (y : BitString) : List (BitString × BitString) :=
  (List.range ((y.length + 1) * (y.length + 1))).filterMap
    (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_entry c y)

private lemma exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_mem_H
    (c : Nat.Partrec.Code) (y : BitString) (q z : BitString) :
    (q, z) ∈ exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_H c y ↔
      ∃ r k, r ≤ y.length ∧ k ≤ y.length ∧ Encodable.decode (α := BitString) r = some q ∧
        ∃ v, Nat.Partrec.Code.evaln y.length c (Encodable.encode
          (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits (y.take k),
            Encodable.encode (q, ([] : BitString)))) = some v ∧
          Encodable.decode (α := BitString) v = some z := by
  unfold exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_H
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨idx, -, hidx⟩
    unfold exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_entry at hidx
    split_ifs at hidx with hg
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hidx
    obtain ⟨q', hq', v, hv, z', hz', rfl, rfl⟩ := hidx
    exact ⟨idx.unpair.1, idx.unpair.2, hg.1, hg.2, hq', v, hv, hz'⟩
  · rintro ⟨r, k, hr, hk, hq, v, hv, hz⟩
    refine ⟨Nat.pair r k, ?_, ?_⟩
    · rw [List.mem_range]
      calc Nat.pair r k < (max r k + 1) ^ 2 := Nat.pair_lt_max_add_one_sq r k
        _ ≤ (y.length + 1) * (y.length + 1) := by
          rw [sq]
          exact Nat.mul_le_mul (by have := max_le hr hk; omega)
            (by have := max_le hr hk; omega)
    · unfold exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_entry
      simp only [Nat.unpair_pair]
      rw [ite_eq_left ⟨hr, hk⟩, hq, Option.bind_some, hv, Option.bind_some, hz, Option.map_some]

open Classical in
private lemma exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits_take
    (A : Set ℕ) (n k : ℕ) (hk : k ≤ n) :
    exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits
        ((cantorPrefix (charSeq A) n).take k) =
      (List.range k).map (fun j => if j ∈ A then 1 else 0) := by
  apply List.ext_getElem
  · simp [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits,
      cantorPrefix]; omega
  · intro i h1 h2
    simp only [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits,
      cantorPrefix, charSeq, List.getElem_map, List.getElem_take,
      List.getElem_ofFn, List.getElem_range]
    by_cases hi : i ∈ A <;> simp [hi]

/-- Step 2a of the proof of `exists_const_KP_oracle_eq_lim_condModeComplexity`: the
finite approximations `H(y)` of an `A`-computable `U`. Take an oracle operator `Φ` for `U`
(`PointToSet.exists_exact_string_operator`, with the oracle `charOracle A` viewed as the total
oracle `fun i => if i ∈ A then 1 else 0`), and let `H(y)` be the finite list of pairs `(q, z)` with
`l(q) ≤ l(y)` such that `Φ(y, ⌜(q, [])⌝)` halts with `⌜z⌝` within `l(y)` steps (`Code.evaln`),
where the finite oracle `y` is read as the list of its bits. Then `H` is computable, monotone in
`y` w.r.t. prefixes, functional in each `H(y)`, sound along the prefixes `Aₙ` (all the oracle
queries made are `< n` and answered correctly), and complete in the limit. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox (A : Set ℕ)
    {U : Map} (hU : IsDecompressorIn (charOracle A) U) :
    ∃ H : BitString → List (BitString × BitString), Computable H ∧
      (∀ y y' : BitString, y <+: y' → ∀ t ∈ H y, t ∈ H y') ∧
      (∀ y q z z', (q, z) ∈ H y → (q, z') ∈ H y → z = z') ∧
      (∀ n q z, (q, z) ∈ H (cantorPrefix (charSeq A) n) → z ∈ U (q, [])) ∧
      (∀ q z, z ∈ U (q, []) →
        ∀ᶠ n in Filter.atTop, (q, z) ∈ H (cantorPrefix (charSeq A) n)) := by
  classical
  obtain ⟨Φ, hΦ, hmono, hex⟩ := PointToSet.exists_exact_string_operator
    (fun k => if k ∈ A then 1 else 0) (mapToNatFun U) hU
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hΦ
  have hceval : ∀ w : List ℕ × ℕ, c.eval (Encodable.encode w) = Φ w := by
    intro w
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.map_id' (fun _ => rfl) _
  have hev : ∀ k w n v, Nat.Partrec.Code.evaln k c (Encodable.encode (w, n)) = some v →
      v ∈ Φ (w, n) := by
    intro k w n v h
    have := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr h)
    rwa [hceval] at this
  refine ⟨exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_H c,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hbits_prim : Primrec
        exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits :=
      Primrec.list_map Primrec.id
        (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)).to₂
    have hr : Primrec (fun a : BitString × ℕ => a.2.unpair.1) :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hk : Primrec (fun a : BitString × ℕ => a.2.unpair.2) :=
      Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
    have hlen : Primrec (fun a : BitString × ℕ => a.1.length) :=
      Primrec.list_length.comp Primrec.fst
    have hguard : PrimrecPred (fun a : BitString × ℕ =>
        a.2.unpair.1 ≤ a.1.length ∧ a.2.unpair.2 ≤ a.1.length) :=
      (Primrec.nat_le.comp hr hlen).and (Primrec.nat_le.comp hk hlen)
    have hdec : Primrec (fun a : BitString × ℕ =>
        Encodable.decode (α := BitString) a.2.unpair.1) :=
      Primrec.decode.comp hr
    have hin : Primrec (fun b : (BitString × ℕ) × BitString => Encodable.encode
        (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits
          (b.1.1.take b.1.2.unpair.2), Encodable.encode (b.2, ([] : BitString)))) :=
      Primrec.encode.comp ((hbits_prim.comp (Primrec.list_take.comp (hk.comp Primrec.fst)
        (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.encode.comp (Primrec.snd.pair (Primrec.const ([] : BitString)))))
    have hevn : Primrec (fun b : (BitString × ℕ) × BitString =>
        Nat.Partrec.Code.evaln b.1.1.length c (Encodable.encode
          (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits
            (b.1.1.take b.1.2.unpair.2), Encodable.encode (b.2, ([] : BitString))))) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (((hlen.comp Primrec.fst).pair (Primrec.const c)).pair hin)
    have hlast : Primrec₂ (fun (b : (BitString × ℕ) × BitString) (v : ℕ) =>
        (Encodable.decode (α := BitString) v).map fun z => (b.2, z)) :=
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).to₂).to₂
    have hentry : Primrec₂
        (exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_entry c) :=
      Primrec.ite hguard (Primrec.option_bind hdec (Primrec.option_bind hevn hlast).to₂)
        (Primrec.const none)
    exact (Primrec.listFilterMap (Primrec.list_range.comp
      (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.list_length)
        (Primrec.succ.comp Primrec.list_length))) hentry).to_comp
  · intro y y' hyy' t ht
    obtain ⟨q, z⟩ := t
    rw [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_mem_H] at ht ⊢
    obtain ⟨r, k, hr, hk, hq, v, hv, hz⟩ := ht
    have hlen := hyy'.length_le
    refine ⟨r, k, hr.trans hlen, hk.trans hlen, hq, v, ?_, hz⟩
    obtain ⟨t, rfl⟩ := hyy'
    rw [List.take_append_of_le_length hk]
    exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono (by simp)
      (Option.mem_def.mpr hv))
  · intro y q z z' h1 h2
    rw [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_mem_H] at h1 h2
    obtain ⟨r, k, hr, hk, hq, v, hv, hz⟩ := h1
    obtain ⟨r', k', hr', hk', hq', v', hv', hz'⟩ := h2
    have hvΦ := hev _ _ _ _ hv
    have hvΦ' := hev _ _ _ _ hv'
    have hpre : ∀ a b, a ≤ b → (y.take a).map
        (fun b : Bool => bif b then 1 else 0) <+: (y.take b).map
        (fun b : Bool => bif b then 1 else 0) := by
      intro a b hab
      have : y.take a <+: y.take b := by
        have := List.take_prefix a (y.take b)
        rwa [List.take_take, min_eq_left hab] at this
      exact this.map _
    have key : v = v' := by
      rcases le_total k k' with h | h
      · exact Part.mem_unique (hmono _ _ (hpre _ _ h) _ _ hvΦ) hvΦ'
      · exact Part.mem_unique hvΦ (hmono _ _ (hpre _ _ h) _ _ hvΦ')
    subst key
    rw [hz] at hz'
    exact Option.some.inj hz'
  · intro n q z h
    rw [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_mem_H] at h
    obtain ⟨r, k, hr, hk, hq, v, hv, hz⟩ := h
    rw [cantorPrefix_length] at hk
    have hvΦ := hev _ _ _ _ hv
    rw [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits_take A n k hk]
      at hvΦ
    have hvf := (hex (Encodable.encode (q, ([] : BitString))) v).mpr ⟨k, hvΦ⟩
    simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some,
      Part.mem_map_iff] at hvf
    obtain ⟨z', hz', rfl⟩ := hvf
    rw [Encodable.encodek, Option.some_inj] at hz
    rw [← hz]
    exact hz'
  · intro q z hz
    have hmemf : Encodable.encode z ∈
        mapToNatFun U (Encodable.encode (q, ([] : BitString))) := by
      simp only [mapToNatFun, Encodable.encodek, Part.coe_some, Part.bind_some]
      exact Part.mem_map _ hz
    obtain ⟨u, hu⟩ := (hex _ _).mp hmemf
    rw [← hceval] at hu
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hu
    filter_upwards [Filter.eventually_ge_atTop (max (max u s) (Encodable.encode q))] with n hn
    have hun : u ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
    have hsn : s ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
    have hqn : Encodable.encode q ≤ n := le_trans (le_max_right _ _) hn
    rw [exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_mem_H]
    refine ⟨Encodable.encode q, u, by simpa using hqn, by simpa using hun,
      Encodable.encodek q, Encodable.encode z, ?_, Encodable.encodek z⟩
    rw [cantorPrefix_length,
      exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox_bits_take A n u hun]
    exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hsn hs)

/-- Step 2b of the proof of `exists_const_KP_oracle_eq_lim_condModeComplexity`: given a
computable family `H(y)` of finite lists of pairs that is monotone in `y`, functional, sound and
complete along the prefixes `Aₙ` for a prefix machine `U`, put `(p, x, y)` into `S'` iff the set of
first components of `H(y)` is prefix-free and `(p', x) ∈ H(y)` for some prefix `p'` of `p`. Then
`S'` is a (decidable, hence enumerable) `(≍, =) | ≍`-description mode (regularity: for `y₁ ≤ y₂`,
`H(y₁) ⊆ H(y₂)`, and prefix-freeness of `H(y₂)` with functionality gives `x₁ = x₂`), and for
all large `n` the set `H(Aₙ)` is part of the graph of `U(·, [])`, so it is prefix-free and a
shortest `U`-description of `x` is an `S'`-description of `x` with condition `Aₙ`. -/
private theorem exists_const_KP_oracle_eq_lim_condModeComplexity_mode (A : Set ℕ) {U : Map}
    (hU : IsPrefixMachine U) (H : BitString → List (BitString × BitString)) (hc : Computable H)
    (hmono : ∀ y y' : BitString, y <+: y' → ∀ t ∈ H y, t ∈ H y')
    (hfun : ∀ y q z z', (q, z) ∈ H y → (q, z') ∈ H y → z = z')
    (hsound : ∀ n q z, (q, z) ∈ H (cantorPrefix (charSeq A) n) → z ∈ U (q, []))
    (hcompl : ∀ q z, z ∈ U (q, []) →
      ∀ᶠ n in Filter.atTop, (q, z) ∈ H (cantorPrefix (charSeq A) n)) :
    ∃ S' : BitString → BitString → BitString → Prop,
      IsCondDescriptionMode .compat .eq .compat S' ∧
        ∀ x, ∀ᶠ n in Filter.atTop,
          condModeComplexity S' x (cantorPrefix (charSeq A) n) ≤ KP U x [] := by
  classical
  let chk : BitString × BitString × BitString → Bool := fun q =>
    !((H q.2.2).any fun a => (H q.2.2).any fun b =>
        decide (b.1.take a.1.length = a.1) && !decide (a.1 = b.1)) &&
      (H q.2.2).any fun t => decide (t.2 = q.2.1) && decide (q.1.take t.1.length = t.1)
  have hpre : ∀ a b : BitString, a <+: b ↔ b.take a.length = a := by
    intro a b
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro h
      exact ⟨b.drop a.length, by rw [← List.take_append_drop a.length b]; simp [h]⟩
  let S' : BitString → BitString → BitString → Prop := fun p x y =>
    (∀ a ∈ H y, ∀ b ∈ H y, a.1 <+: b.1 → a.1 = b.1) ∧ ∃ t ∈ H y, t.2 = x ∧ t.1 <+: p
  have hchk : ∀ q, chk q = true ↔ S' q.1 q.2.1 q.2.2 := by
    rintro ⟨p, x, y⟩
    simp only [chk, S', Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
      List.any_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, hpre]
    constructor
    · rintro ⟨h1, t, ht, h2, h3⟩
      refine ⟨fun a ha b hb hab => ?_, t, ht, h2, h3⟩
      by_contra hne
      exact h1 a ha ⟨b, hb, hab, hne⟩
    · rintro ⟨h1, t, ht, h2, h3⟩
      refine ⟨fun a ha ⟨b, hb, hh1, hh2⟩ => hh2 (h1 a ha b hb hh1), t, ht, h2, h3⟩
  have hcomp : Computable chk := by
    have hH : Computable (fun q : BitString × BitString × BitString => H q.2.2) :=
      hc.comp (Computable.snd.comp Computable.snd)
    have hpb : Primrec (fun s : ((BitString × BitString × BitString) × (BitString × BitString)) ×
        (BitString × BitString) => decide (s.2.1.take s.1.2.1.length = s.1.2.1) &&
          !decide (s.1.2.1 = s.2.1)) := by
      have ha : Primrec (fun s : ((BitString × BitString × BitString) × (BitString × BitString)) ×
          (BitString × BitString) => s.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      have hb : Primrec (fun s : ((BitString × BitString × BitString) × (BitString × BitString)) ×
          (BitString × BitString) => s.2.1) := Primrec.fst.comp Primrec.snd
      exact Primrec.and.comp
        (Primrec.eq.decide.comp (Primrec.list_take.comp (Primrec.list_length.comp ha) hb) ha)
        (Primrec.not.comp (Primrec.eq.decide.comp ha hb))
    have hinner : Computable₂ (fun (q : BitString × BitString × BitString)
        (a : BitString × BitString) => (H q.2.2).any fun b =>
          decide (b.1.take a.1.length = a.1) && !decide (a.1 = b.1)) :=
      computable_list_any (f := fun r : (BitString × BitString × BitString) ×
        (BitString × BitString) => H r.1.2.2) (p := fun r b =>
          decide (b.1.take r.2.1.length = r.2.1) && !decide (r.2.1 = b.1))
        (hH.comp Computable.fst) hpb.to_comp
    have hout := computable_list_any (f := fun q : BitString × BitString × BitString => H q.2.2)
      (p := fun q a => (H q.2.2).any fun b =>
          decide (b.1.take a.1.length = a.1) && !decide (a.1 = b.1)) hH hinner
    have hpt : Primrec (fun s : (BitString × BitString × BitString) × (BitString × BitString) =>
        decide (s.2.2 = s.1.2.1) && decide (s.1.1.take s.2.1.length = s.2.1)) := by
      have hx : Primrec (fun s : (BitString × BitString × BitString) × (BitString × BitString) =>
          s.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      have hp : Primrec (fun s : (BitString × BitString × BitString) × (BitString × BitString) =>
          s.1.1) := Primrec.fst.comp Primrec.fst
      have ht1 : Primrec (fun s : (BitString × BitString × BitString) × (BitString × BitString) =>
          s.2.1) := Primrec.fst.comp Primrec.snd
      have ht2 : Primrec (fun s : (BitString × BitString × BitString) × (BitString × BitString) =>
          s.2.2) := Primrec.snd.comp Primrec.snd
      exact Primrec.and.comp (Primrec.eq.decide.comp ht2 hx)
        (Primrec.eq.decide.comp (Primrec.list_take.comp (Primrec.list_length.comp ht1) hp) ht1)
    have hsec := computable_list_any (f := fun q : BitString × BitString × BitString => H q.2.2)
      (p := fun q t => decide (t.2 = q.2.1) && decide (q.1.take t.1.length = t.1))
      hH hpt.to_comp
    exact Primrec.and.to_comp.comp (Primrec.not.to_comp.comp hout) hsec
  have hpf : ∀ n, ∀ a ∈ H (cantorPrefix (charSeq A) n), ∀ b ∈ H (cantorPrefix (charSeq A) n),
      a.1 <+: b.1 → a.1 = b.1 := by
    rintro n ⟨q, z⟩ ha ⟨q', z'⟩ hb hab
    exact hU.eq_of_prefix (hsound n q z ha) (hsound n q' z' hb) hab
  refine ⟨S', ⟨isRE_of_computable_bool _ chk hchk hcomp, ?_⟩, ?_⟩
  · have key : ∀ p₁ x₁ y₁ p₂ x₂ y₂, S' p₁ x₁ y₁ → S' p₂ x₂ y₂ → y₁ <+: y₂ →
        (p₁ <+: p₂ ∨ p₂ <+: p₁) → x₁ = x₂ := by
      rintro p₁ x₁ y₁ p₂ x₂ y₂ ⟨-, t₁, ht₁, rfl, hp₁⟩ ⟨hpf, t₂, ht₂, rfl, hp₂⟩ hy hp
      have h1 := hmono _ _ hy t₁ ht₁
      have hc : t₁.1 <+: t₂.1 ∨ t₂.1 <+: t₁.1 := by
        rcases hp with h | h
        · rcases le_total t₁.1.length t₂.1.length with hl | hl
          · exact Or.inl (List.prefix_of_prefix_length_le (hp₁.trans h) hp₂ hl)
          · exact Or.inr (List.prefix_of_prefix_length_le hp₂ (hp₁.trans h) hl)
        · rcases le_total t₁.1.length t₂.1.length with hl | hl
          · exact Or.inl (List.prefix_of_prefix_length_le hp₁ (hp₂.trans h) hl)
          · exact Or.inr (List.prefix_of_prefix_length_le (hp₂.trans h) hp₁ hl)
      have : t₁.1 = t₂.1 := by
        rcases hc with h | h
        · exact hpf _ h1 _ ht₂ h
        · exact (hpf _ ht₂ _ h1 h).symm
      obtain ⟨q₁, z₁⟩ := t₁
      obtain ⟨q₂, z₂⟩ := t₂
      simp only at this
      subst this
      exact hfun _ _ _ _ h1 ht₂
    intro p₁ x₁ y₁ p₂ x₂ y₂ h₁ h₂ hp hy
    rcases hy with hy | hy
    · exact key _ _ _ _ _ _ h₁ h₂ hy hp
    · exact (key _ _ _ _ _ _ h₂ h₁ hy (hp.symm)).symm
  · intro x
    by_cases htop : KP U x [] = ⊤
    · exact Filter.Eventually.of_forall fun n => by rw [htop]; exact le_top
    · obtain ⟨q, hq, hql⟩ := exists_program_of_KP_ne_top htop
      filter_upwards [hcompl q x hq] with n hn
      calc condModeComplexity S' x (cantorPrefix (charSeq A) n) ≤ q.length :=
            sInf_le ⟨q, ⟨hpf n, (q, x), hn, rfl, List.prefix_refl q⟩, rfl⟩
        _ = KP U x [] := hql

/-- **SUV Problem 204 (Section 6.4.1, printed p. 203).** Relativized prefix complexity is the
limit of the `(≍, =) | ≍` conditional complexities with the prefixes `Aₙ` of the
characteristic sequence of `A` as conditions:
`K^A(x) = lim_n K(≍,=)|≍ (x | Aₙ) + O(1)`.
We state the limit robustly. The `liminf` is at least `K^A(x) - O(1)` and the `limsup` is at
most `K^A(x) + O(1)`, so the limit exists up to `O(1)` and equals `K^A(x)`.

Deviation: the first claim of the problem is that `⟨A, x⟩ ↦ K^A(x)` can be defined uniformly in
`A` up to `O(1)`. The right-hand side gives such a uniform definition, but here `K^A` is computed
with an arbitrary optimal `A`-decompressor, so the constant may depend on `A`.

Proof idea: first conjunct — the `A`-machine that, on `p`, searches for a triple `(p', x', y')`
of `S` with `p'` a prefix of `p` and `y'` a prefix of the characteristic sequence of `A` is a
prefix-stable `A`-decompressor, and by regularity it outputs `x` whenever `S p x Aₙ` for some
`n`; so even `K^A(x) ≤ K(≍,=)|≍ (x | Aₙ) + O(1)` for every `n`. Second conjunct — fix an oracle
program `e` computing `U` with oracle `A`. For a finite oracle `y` let `H(y)` be the set of
pairs `(q, z)` with `l(q) ≤ l(y)` such that `e` with oracle `y` outputs `z` on `(q, [])` within
`l(y)` steps, querying only positions `< l(y)`; `H(y)` is finite, computable from `y`, and
monotone in `y`. Put `(p, x, y)` into `S'` iff the domain of
`H(y)` is prefix-free and `(p', x) ∈ H(y)` for some prefix `p'` of `p`. Then `S'` is decidable and
`(≍, =) | ≍`-regular, and `H(Aₙ)` is part of the graph of the prefix-free `U(·, [])`, so a
`U`-description of `x` describes `x` for all conditions `Aₙ` with `n` large. Merely collecting
the computations with finite oracles `y` is not enough: with a wrong oracle `e` need not be
prefix-free. -/
theorem exists_const_KP_oracle_eq_lim_condModeComplexity (A : Set ℕ) {U : Map}
    (hU : PointToSet.IsOptimalOraclePrefix A U) {S : BitString → BitString → BitString → Prop}
    (hS : IsOptimalCondDescriptionMode .compat .eq .compat S) :
    ∃ c : ℕ, ∀ x,
      KP U x [] ≤
          Filter.liminf (fun n => condModeComplexity S x (cantorPrefix (charSeq A) n))
            Filter.atTop + c ∧
        Filter.limsup (fun n => condModeComplexity S x (cantorPrefix (charSeq A) n))
            Filter.atTop ≤ KP U x [] + c := by
  obtain ⟨E, hE1, hE2, hE3⟩ :=
    exists_const_KP_oracle_eq_lim_condModeComplexity_prefixStable A hS.1
  obtain ⟨D, hD1, hD2, c1, hc1⟩ :=
    exists_const_KP_oracle_eq_lim_condModeComplexity_prefixFree A hE1 hE2
  obtain ⟨c0, hc0⟩ := hU.2.2 D hD1 hD2
  obtain ⟨H, hHc, hHm, hHf, hHs, hHcomp⟩ :=
    exists_const_KP_oracle_eq_lim_condModeComplexity_finiteApprox A hU.1
  obtain ⟨S', hS'1, hS'2⟩ :=
    exists_const_KP_oracle_eq_lim_condModeComplexity_mode A hU.2.1 H hHc hHm hHf hHs hHcomp
  obtain ⟨c2, hc2⟩ := hS.2 S' hS'1
  refine ⟨c0 + c1 + c2, fun x => ⟨?_, ?_⟩⟩
  · have h1 : ∀ n, KP U x [] ≤
        condModeComplexity S x (cantorPrefix (charSeq A) n) + ((c0 + c1 + c2 : ℕ) : ℕ∞) := by
      intro n
      have hE : KP E x [] ≤ condModeComplexity S x (cantorPrefix (charSeq A) n) := by
        refine le_sInf ?_
        rintro l ⟨p, hp, rfl⟩
        exact KP_le_programLength_of_produces (hE3 x n p hp)
      calc KP U x [] ≤ KP D x [] + c0 := hc0 x []
        _ ≤ (KP E x [] + c1) + c0 := by gcongr; exact hc1 x
        _ ≤ (condModeComplexity S x (cantorPrefix (charSeq A) n) + c1) + c0 := by gcongr
        _ ≤ _ := by
          rw [add_assoc]
          have hle : ((c1 : ℕ∞) + c0) ≤ ((c0 + c1 + c2 : ℕ) : ℕ∞) := by
            have : c1 + c0 ≤ c0 + c1 + c2 := by omega
            exact_mod_cast this
          exact add_le_add_right hle _
    have h2 : KP U x [] - ((c0 + c1 + c2 : ℕ) : ℕ∞) ≤
        Filter.liminf (fun n => condModeComplexity S x (cantorPrefix (charSeq A) n))
          Filter.atTop :=
      Filter.le_liminf_of_le (by isBoundedDefault)
        (Filter.Eventually.of_forall fun n => tsub_le_iff_right.2 (h1 n))
    exact tsub_le_iff_right.1 h2
  · refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hS'2 x] with n hn
    calc condModeComplexity S x (cantorPrefix (charSeq A) n)
        ≤ condModeComplexity S' x (cantorPrefix (charSeq A) n) + c2 := hc2 x _
      _ ≤ KP U x [] + c2 := by gcongr
      _ ≤ KP U x [] + ((c0 + c1 + c2 : ℕ) : ℕ∞) :=
          add_le_add_right (by exact_mod_cast (by omega : c2 ≤ c0 + c1 + c2)) _

/-- **SUV Section 6.4.1 (printed p. 203), unnumbered.** Relativized complexity does not exceed
the non-relativized one: `C^A(x) ≤ C(x) + O(1)`. An oracle machine is not obliged to use its
oracle, so every decompressor is an `A`-decompressor (`Partrec.recursiveIn`). -/
theorem exists_const_plainK_oracle_le_plainK (A : Set ℕ) {U : Map}
    (hU : isOptimalConditional U) {V : Map} (hV : IsOptimalConditionalIn (charOracle A) V) :
    ∃ c : ℕ, ∀ x, plainK V x ≤ plainK U x + c := by
  obtain ⟨c, hc⟩ :=
    hV.2 U ((PointToSet.isDecompressorIn_iff_partrecIn _ _).2 (Partrec.recursiveIn hU.1))
  exact ⟨c, fun x => hc x []⟩

end GeneralScheme
end Kolmogorov
