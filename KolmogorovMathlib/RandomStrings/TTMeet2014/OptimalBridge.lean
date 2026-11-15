/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.RandomStrings.TTMeet2014.Baseline

/-!
# Unconditional machines and the conditional API

The paper works with unconditional universal prefix-free machines `U : 2^{<ω} → 2^{<ω}`.  The
library has conditional machines `Map`, with `prefixRandom U = {x | |x| ≤ KPPlain U x}` and
`KPPlain U x = KP U x []`.  This module shows that the two give the same random sets:

* `restrictEmpty`: an optimal conditional machine, restricted to the empty condition, is a universal
  unconditional machine with the same complexity and the same random strings
  (`restrictEmpty_universal`, `KM_restrictEmpty`, `randomOf_restrictEmpty`).
* `glue V W`: a universal unconditional machine `V`, extended on non-empty conditions by a fixed
  optimal conditional machine `W`, is an optimal conditional machine with the same complexity and
  the same random strings (`glue_optimal`, `KPPlain_glue`, `prefixRandom_glue`).

So the sets of oracles coincide (`exists_optimal_iff_exists_universal`).  "Universal" means additive
optimality among prefix-free machines, in the sense in which the paper compares `K_U` and `K_V`.
Neither direction uses a syntactic property such as `U (0^e 1 σ) = M_e (σ)`, and the machines built
in `Main.lean` are only shown to be optimal in this sense (see the documentation for the impact on
the statement).
-/

namespace Kolmogorov.RandomStrings.TTMeet

open Kolmogorov

/-- An unconditional machine. -/
abbrev Machine := BitString →. BitString

/-- The paper's prefix-free machines: partial computable, with prefix-free domain. -/
def IsPrefixFreeMachine (M : Machine) : Prop := Partrec M ∧ IsPrefixFree M.Dom

/-- The complexity for an unconditional machine, with value `⊤` if there is no program. -/
noncomputable def KM (M : Machine) (x : BitString) : ENat :=
  sInf {n | ∃ p, x ∈ M p ∧ (p.length : ENat) = n}

/-- The paper's universal prefix-free machines, as additively optimal ones. -/
def IsUniversalMachine (U : Machine) : Prop :=
  IsPrefixFreeMachine U ∧ ∀ M, IsPrefixFreeMachine M → ∃ c : ℕ, ∀ x, KM U x ≤ KM M x + (c : ENat)

/-- The paper's `R_{K_U}`, with the threshold `|x| ≤ K_U (x)`. -/
def randomOf (U : Machine) : Set BitString := {x | (x.length : ℕ∞) ≤ KM U x}

/-- The restriction to the empty condition. -/
def restrictEmpty (U : Map) : Machine := fun p => U (p, [])

/-- The machine ignoring the condition. -/
def liftMachine (M : Machine) : Map := fun q => M q.1

/-- `V` on the empty condition, `W` on all others. -/
noncomputable def glue (V : Machine) (W : Map) : Map :=
  fun q => bif decide (q.2 = []) then V q.1 else W q

/-- The complexity for the restriction of `U` to the empty condition is `KPPlain U`. -/
theorem KM_restrictEmpty (U : Map) (x : BitString) : KM (restrictEmpty U) x = KPPlain U x :=
  rfl

/-- The restriction of a prefix decompressor to the empty condition is a prefix-free machine. -/
theorem isPrefixFreeMachine_restrictEmpty {U : Map} (hU : IsPrefixDecompressor U) :
    IsPrefixFreeMachine (restrictEmpty U) :=
  ⟨(Partrec.comp hU.1 (Computable.id.pair (Computable.const [])) :
    Partrec fun p : BitString => U (p, [])), hU.2 []⟩

/-- A prefix-free machine, run ignoring the condition, is a prefix decompressor. -/
theorem isPrefixDecompressor_lift {M : Machine} (hM : IsPrefixFreeMachine M) :
    IsPrefixDecompressor (liftMachine M) :=
  ⟨(Partrec.comp hM.1 Computable.fst : Partrec fun q : BitString × BitString => M q.1),
    fun _ => hM.2⟩

/-- For the lift of an unconditional machine `M`, the conditional complexity is the complexity for
`M`, whatever the condition. -/
theorem KP_lift (M : Machine) (x y : BitString) : KP (liftMachine M) x y = KM M x :=
  rfl

/-- **Restriction.**  An optimal conditional machine restricts to a universal machine. -/
theorem restrictEmpty_universal {U : Map} (hU : IsOptimalPrefixConditional U) :
    IsUniversalMachine (restrictEmpty U) := by
  refine ⟨isPrefixFreeMachine_restrictEmpty hU.1, fun M hM => ?_⟩
  obtain ⟨c, hc⟩ := hU.2 (liftMachine M) (isPrefixDecompressor_lift hM)
  exact ⟨c, fun x => hc x []⟩

/-- The random strings of the restriction to the empty condition are `prefixRandom U`. -/
theorem randomOf_restrictEmpty (U : Map) : randomOf (restrictEmpty U) = prefixRandom U :=
  rfl

/-- On the empty condition, `glue V W` runs `V`. -/
theorem glue_nil (V : Machine) (W : Map) (p : BitString) : glue V W (p, []) = V p := by
  simp [glue]

/-- On a nonempty condition, `glue V W` runs `W`. -/
theorem glue_of_ne (V : Machine) (W : Map) {y : BitString} (hy : y ≠ []) (p : BitString) :
    glue V W (p, y) = W (p, y) := by
  simp [glue, hy]

/-- Given the empty condition, the complexity for `glue V W` is the complexity for `V`. -/
theorem KP_glue_nil (V : Machine) (W : Map) (x : BitString) : KP (glue V W) x [] = KM V x := by
  have h : ∀ p, (x ∈ glue V W (p, [])) ↔ x ∈ V p := fun p => by rw [glue_nil]
  exact congrArg sInf (Set.ext fun n => exists_congr fun p => and_congr_left fun _ => h p)

/-- Given a nonempty condition, the complexity for `glue V W` is the complexity for `W`. -/
theorem KP_glue_of_ne (V : Machine) (W : Map) (x : BitString) {y : BitString} (hy : y ≠ []) :
    KP (glue V W) x y = KP W x y := by
  have h : ∀ p, (x ∈ glue V W (p, y)) ↔ x ∈ W (p, y) := fun p => by rw [glue_of_ne V W hy]
  exact congrArg sInf (Set.ext fun n => exists_congr fun p => and_congr_left fun _ => h p)

/-- The plain prefix complexity for `glue V W` is the complexity for `V`. -/
theorem KPPlain_glue (V : Machine) (W : Map) (x : BitString) : KPPlain (glue V W) x = KM V x :=
  KP_glue_nil V W x

/-- The random strings of `glue V W` are the random strings of `V`. -/
theorem prefixRandom_glue (V : Machine) (W : Map) : prefixRandom (glue V W) = randomOf V := by
  ext x
  change (x.length : ℕ∞) ≤ KPPlain (glue V W) x ↔ (x.length : ℕ∞) ≤ KM V x
  rw [KPPlain_glue]

/-- If `V` is a prefix-free machine and `W` a prefix decompressor, `glue V W` is a prefix
decompressor. -/
theorem glue_prefixDecompressor {V : Machine} {W : Map} (hV : IsPrefixFreeMachine V)
    (hW : IsPrefixDecompressor W) : IsPrefixDecompressor (glue V W) := by
  constructor
  · have hc : Computable fun q : BitString × BitString => decide (q.2 = []) :=
      (Primrec.eq.comp Primrec.snd (Primrec.const [])).decide.to_comp
    exact Partrec.cond hc (Partrec.comp hV.1 Computable.fst) hW.1
  · intro y
    by_cases hy : y = []
    · subst hy
      intro p hp q hq hpq
      have hp' : (V p).Dom := by simpa [domainAt, glue_nil] using hp
      have hq' : (V q).Dom := by simpa [domainAt, glue_nil] using hq
      exact hV.2 hp' hq' hpq
    · intro p hp q hq hpq
      have hp' : (W (p, y)).Dom := by simpa [domainAt, glue_of_ne V W hy] using hp
      have hq' : (W (q, y)).Dom := by simpa [domainAt, glue_of_ne V W hy] using hq
      exact hW.2 y hp' hq' hpq

/-- **Extension.**  A universal machine extends to an optimal conditional machine. -/
theorem glue_optimal {V : Machine} {W : Map} (hV : IsUniversalMachine V)
    (hW : IsOptimalPrefixConditional W) : IsOptimalPrefixConditional (glue V W) := by
  refine ⟨glue_prefixDecompressor hV.1 hW.1, fun M hM => ?_⟩
  obtain ⟨c₁, hc₁⟩ := hV.2 (restrictEmpty M) (isPrefixFreeMachine_restrictEmpty hM)
  obtain ⟨c₂, hc₂⟩ := hW.2 M hM
  refine ⟨max c₁ c₂, fun x y => ?_⟩
  by_cases hy : y = []
  · subst hy
    rw [KP_glue_nil]
    calc KM V x ≤ KM (restrictEmpty M) x + (c₁ : ENat) := hc₁ x
      _ ≤ KM (restrictEmpty M) x + ((max c₁ c₂ : ℕ) : ENat) := by
          gcongr
          exact le_max_left _ _
  · rw [KP_glue_of_ne V W x hy]
    calc KP W x y ≤ KP M x y + (c₂ : ENat) := hc₂ x y
      _ ≤ KP M x y + ((max c₁ c₂ : ℕ) : ENat) := by
          gcongr
          exact le_max_right _ _

/-- **The two families of random sets coincide.** -/
theorem exists_optimal_iff_exists_universal (R : Set BitString) :
    (∃ U : Map, IsOptimalPrefixConditional U ∧ prefixRandom U = R) ↔
      ∃ V : Machine, IsUniversalMachine V ∧ randomOf V = R := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨restrictEmpty U, restrictEmpty_universal hU, rfl⟩
  · rintro ⟨V, hV, rfl⟩
    obtain ⟨W, hW⟩ := exists_isOptimalPrefixConditional
    exact ⟨glue V W, glue_optimal hV hW, prefixRandom_glue V W⟩

end Kolmogorov.RandomStrings.TTMeet
