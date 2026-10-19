/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Solomonoff.ShenQuestion.FlowCompletion

/-!
# A3. The construction of `ν`

## Layout of the tree

`ν` is supported on the "comb": the spine `1^j` carries the value `2^{-j}`, and the
component `R` hangs under the label `p_R = 1^R 0` with mass `δ_R = 2^{-(R+1)}`.  The
identity `2^{-j} = 2^{-(j+1)} + δ_j` makes the spine splits **exact**, so the root value
is exactly `1` — the library convention `IsContinuousTreeSemimeasure` (root equality).
This replaces the blueprint's M3 "put the rest on the ray `0^∞`": with the geometric
weights `δ_R = 2^{-(R+1)}` no leftover mass exists.  (Blueprint deviation D1.)

## Dyadic bookkeeping (the key normalisation)

Stage-`s` values are integers over the denominator `2^s`.  A generation stores, for every
front vertex `u`, the integer `b_u = q_u · 2^{start}` where `start` is the stage at which
the generation began.  At stage `s = start + t` the value below `u` is

  `ν_s(u ++ y) = q_u · Q̂_t(y | u) = (b_u / 2^{start}) · (qHat u t y / 2^t)`
  `             = b_u · qHat u t y / 2^s`,

so the stage numerator `b_u * qHat qa u t y` is an **integer with denominator exactly
`2^s`** — no rounding anywhere.  In particular at `y = []` we get `b_u · 2^t = q_u · 2^s`,
i.e. the value at the front vertex is exactly the budget, automatically.  (This is the
device that makes the whole construction dyadically exact; blueprint deviation D2, which
replaces the informal "fix a stage clock" of B1.)

Frozen values (the exact flows above the front) are stored the same way: numerator over
`2^{start}`, rescaled by `2^{s-start}` at stage `s`.

## Component `R` is dormant until stage `R + 1`

`δ_R = 2^{-(R+1)}` has denominator `2^{R+1}`, so component `R` can only appear at stages
`s ≥ R + 1`; `genAt R n` is the generation of component `R` at stage `s = R + 1 + n`.
This is the blueprint's dovetailing A3.9, with the activation stage forced by the dyadic
normalisation rather than chosen.
-/

namespace Kolmogorov
namespace Shen

open scoped ENNReal

variable {Q : BitString → BitString → ℝ≥0∞}

/-- The label of component `R`: `p_R = 1^R 0`. -/
def pLabel (R : ℕ) : BitString := List.replicate R true ++ [false]

/-- The label `p_R = 1^R 0` has length `R + 1`. -/
@[simp] theorem pLabel_length (R : ℕ) : (pLabel R).length = R + 1 := by simp [pLabel]

/-- The number of leading `1`s of `z`; `z` lies in component `compIdx z` unless it is
all-ones (a spine vertex). -/
def compIdx (z : BitString) : ℕ := (z.takeWhile id).length

/-- **A3.2 (generation state).**  A finite, ℕ-encodable description of one generation of
one component: the stage at which it started, the common depth of its front, the front
(vertex together with its budget numerator `b_u = q_u · 2^{start}`) and the frozen exact
flow strictly above the front (same normalisation). -/
structure Gen where
  start : ℕ
  level : ℕ
  front : List (BitString × ℕ)
  frozen : List (BitString × ℕ)
  deriving DecidableEq

/-- The empty generation, the default value of `Gen`. -/
instance : Inhabited Gen := ⟨⟨0, 0, [], []⟩⟩

/-- The initial generation of component `R`: one front vertex `p_R` with budget
`δ_R = 2^{-(R+1)}`, i.e. numerator `1` at the start stage `R + 1`. -/
def initGen (R : ℕ) : Gen :=
  { start := R + 1, level := R + 1, front := [(pLabel R, 1)], frozen := [] }

/-- **A3.3 (stage value of a generation).**  `z` is assumed to extend `p_R`. -/
def compVal (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) (z : BitString) : ℕ :=
  match g.front.find? (fun p => p.1.isPrefixOf z) with
  | some p => p.2 * qHat qa p.1 (s - g.start) (z.drop p.1.length)
  | none => (List.lookup z g.frozen).getD 0 * 2 ^ (s - g.start)

/-- **A3.4 (trigger).**  Decidable comparison of two integers: the generation is replaced
as soon as *every* front vertex `u` has already accumulated discrete mass
`m_s(u) > q_u / (R+1)`.  (The blueprint's `q_u/(4R)`; `R+1` avoids the division by `0`
and makes the final constant `c·(R+1) ≥ c·R`.  Deviation D3.) -/
def trig (ma : ℕ → BitString → BitString → ℕ) (R : ℕ) (g : Gen) (s : ℕ) : Bool :=
  g.front.all (fun p => decide (p.2 * 2 ^ (s - g.start) < ma s p.1 [] * (R + 1)))

/-- The snapshot of the simulation below the front vertex `u` with budget numerator `b`
at local time `t`, normalised to the *new* denominator `2^{s+1}`:
`A(w) = 2 · b · Q̂_t(w | u)`.  Its root value is `b · 2^{t+1}`. -/
def snapshot (qa : ℕ → BitString → BitString → ℕ) (u : BitString) (b t : ℕ)
    (w : BitString) : ℕ := 2 * b * qHat qa u t w

/-- **A3.5 (transition).**  At a trigger the whole generation is replaced: each front
vertex `u` completes its snapshot to an exact flow down to relative depth `t + 1` (which
is strictly below the support of the snapshot, `qHat_vanishes`), the new front is the set
of level-`t+1` descendants with positive flow, and the completed flow above that level is
frozen. -/
def transition (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) : Gen :=
  { start := s + 1
    level := g.level + (s - g.start) + 1
    front := g.front.flatMap (fun p =>
      (binStrings (s - g.start + 1)).filterMap (fun w =>
        let v := flowVal (snapshot qa p.1 p.2 (s - g.start)) (p.2 * 2 ^ (s - g.start + 1)) w
        if v = 0 then none else some (p.1 ++ w, v)))
    frozen := g.frozen.map (fun p => (p.1, p.2 * 2 ^ (s - g.start + 1))) ++
      g.front.flatMap (fun p =>
        (binStringsUpTo (s - g.start)).map (fun w =>
          (p.1 ++ w,
            flowVal (snapshot qa p.1 p.2 (s - g.start)) (p.2 * 2 ^ (s - g.start + 1)) w))) }

/-- **A3.9 (component evolution).**  `genAt qa ma R n` is the generation of component `R`
at stage `s = R + 1 + n`. -/
def genAt (qa ma : ℕ → BitString → BitString → ℕ) (R : ℕ) : ℕ → Gen
  | 0 => initGen R
  | n + 1 =>
      if trig ma R (genAt qa ma R n) (R + 1 + n) then
        transition qa (genAt qa ma R n) (R + 1 + n)
      else genAt qa ma R n

/-- **A3.10 (the stage numerator of `ν`).**  Spine vertices `1^j` carry `2^{s-j}`
(i.e. `2^{-j}`); a vertex with `R` leading ones and a `0` afterwards belongs to
component `R`, which is dormant before stage `R + 1`.

This function is **computable** (a `def`, no `Classical.choice`): the recursion `genAt` is
structural, the trigger is a decidable integer comparison, and `qHat` is computable. -/
def nuStage (qa ma : ℕ → BitString → BitString → ℕ) (s : ℕ) (z : BitString) : ℕ :=
  if z.length = compIdx z then
    (if z.length ≤ s then 2 ^ (s - z.length) else 0)
  else if compIdx z < s then
    compVal qa (genAt qa ma (compIdx z) (s - compIdx z - 1)) s z
  else 0

/-- **A3.10.** `ν` itself. -/
noncomputable def nu (qa ma : ℕ → BitString → BitString → ℕ) (z : BitString) : ℝ≥0∞ :=
  ⨆ s, dyadicValue (nuStage qa ma s z) s

/-! ### Generic list/dyadic helpers -/

/-- `dyadicValue` bridge: doubling the numerator and the exponent is a no-op. -/
theorem dyadicValue_two_mul_succ (n s : ℕ) : dyadicValue (2 * n) (s + 1) = dyadicValue n s := by
  unfold dyadicValue
  rw [pow_succ']
  push_cast
  rw [ENNReal.mul_div_mul_left] <;> simp

/-- The ℕ-form of a one-step dyadic increase: `2·n ≤ m` is exactly
`dyadicValue n s ≤ dyadicValue m (s+1)` (the converse is `two_mul_le_of_dyadicValue_le`). -/
theorem dyadicValue_le_succ_of_two_mul_le {n m : ℕ} (s : ℕ) (h : 2 * n ≤ m) :
    dyadicValue n s ≤ dyadicValue m (s + 1) := by
  rw [← dyadicValue_two_mul_succ n s]
  exact dyadicValue_le _ _ _ h

/-- The converse bridge (the library's `two_mul_le_of_dyadicValue_le`, reproved here since
`TreeAllocation` is not in the import closure). -/
theorem two_mul_le_of_dyadic {n m s : ℕ} (h : dyadicValue n s ≤ dyadicValue m (s + 1)) :
    2 * n ≤ m := by
  rw [← dyadicValue_two_mul_succ n s] at h
  unfold dyadicValue at h
  have h2 : (2 * n : ℕ) / (2 : ℝ≥0∞) ^ (s + 1) * (2 : ℝ≥0∞) ^ (s + 1)
      ≤ (m : ℕ) / (2 : ℝ≥0∞) ^ (s + 1) * (2 : ℝ≥0∞) ^ (s + 1) := by gcongr
  rw [ENNReal.div_mul_cancel (by simp) (by simp),
    ENNReal.div_mul_cancel (by simp) (by simp)] at h2
  exact_mod_cast h2

/-- If `(k, v) ∈ L` and every entry of `L` with key `k` carries `v`, the lookup of `k` in
`L` returns `v`. -/
theorem lookup_getD_eq {β : Type*} (L : List (BitString × β)) (k : BitString) (v d : β)
    (hmem : (k, v) ∈ L) (huniq : ∀ p ∈ L, p.1 = k → p.2 = v) : (L.lookup k).getD d = v := by
  induction L with
  | nil => simp at hmem
  | cons p L ih =>
      by_cases hp : k = p.1
      · have : p.2 = v := huniq p (by simp) hp.symm
        simp [List.lookup, hp, this]
      · have hb : (k == p.1) = false := by simpa using hp
        simp only [List.lookup, hb]
        refine ih ?_ (fun q hq => huniq q (by simp [hq]))
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (by rw [← h]) hp
        · exact h

/-- A key that occurs in no entry of `L` looks up to the default value. -/
theorem lookup_getD_eq_default {β : Type*} (L : List (BitString × β)) (k : BitString) (d : β)
    (h : ∀ p ∈ L, p.1 ≠ k) : (L.lookup k).getD d = d := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hb : (k == p.1) = false := by
        have := h p (by simp); simpa using fun hh => this hh.symm
      simp only [List.lookup, hb]
      exact ih (fun q hq => h q (by simp [hq]))

/-- A key absent from `L` is looked up in `L ++ M` as in `M`. -/
theorem lookup_append_left_none {β : Type*} (L M : List (BitString × β)) (k : BitString)
    (d : β) (h : ∀ p ∈ L, p.1 ≠ k) : ((L ++ M).lookup k).getD d = (M.lookup k).getD d := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hb : (k == p.1) = false := by
        have := h p (by simp); simpa using fun hh => this hh.symm
      simp only [List.cons_append, List.lookup, hb]
      exact ih (fun q hq => h q (by simp [hq]))

/-- In an association list with pairwise distinct keys, two entries with the same key are
equal. -/
theorem eq_of_key_nodup {β : Type*} {L : List (BitString × β)} (h : (L.map Prod.fst).Nodup)
    {p q : BitString × β} (hp : p ∈ L) (hq : q ∈ L) (hk : p.1 = q.1) : p = q := by
  induction L with
  | nil => simp at hp
  | cons r L ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
      rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · exact absurd ⟨q, hq', hk.symm⟩ h.1
      · exact absurd ⟨p, hp', hk⟩ h.1
      · exact ih h.2 hp' hq'

/-- The total value recorded by a generation at a vertex: the budget if the vertex is on
the front, the frozen flow value if it is above the front, and `0` otherwise.  This is the
stage value **in units of `2 ^ g.start`**; see `compVal_eq_value_mul`. -/
def Gen.value (g : Gen) (z : BitString) : ℕ := ((g.front ++ g.frozen).lookup z).getD 0

/-! ### Invariants of a generation -/

/-- **A3.2 (invariants).**  `GenInv R g` collects everything the proof needs about the
generation `g` of component `R` living at stages `≥ g.start`:

* the front is a nonempty antichain of vertices of common length `g.level`, all extending
  `p_R`, with positive budgets;
* the budgets sum to `δ_R · 2^{g.start} = 2^{g.start - R - 1}` (the component's mass is
  conserved: A2.3);
* the frozen region is an exact flow from `p_R` down to `g.level`, dominating nothing and
  taking the value `2^{g.start-R-1}` at `p_R`;
* the vertices recorded in `frozen` are exactly the strict ancestors of front vertices
  above `p_R`, hence disjoint from the front. -/
structure GenInv (R : ℕ) (g : Gen) : Prop where
  start_ge : R + 1 ≤ g.start
  level_ge : R + 1 ≤ g.level
  front_ne : g.front ≠ []
  front_len : ∀ p ∈ g.front, p.1.length = g.level
  front_ext : ∀ p ∈ g.front, pLabel R <+: p.1
  front_pos : ∀ p ∈ g.front, 0 < p.2
  front_nodup : (g.front.map Prod.fst).Nodup
  budget_sum : (g.front.map Prod.snd).sum = 2 ^ (g.start - (R + 1))
  frozen_len : ∀ p ∈ g.frozen, p.1.length < g.level
  frozen_ext : ∀ p ∈ g.frozen, pLabel R <+: p.1
  /-- (added) the combined frozen/front value at `p_R` is the whole mass of the component -/
  value_root : g.value (pLabel R) = 2 ^ (g.start - (R + 1))
  /-- (added) inside the cone of `p_R` and above the front the values split **exactly**:
  this is the "exact flow" property of `frozen`, with the front budgets as its leaves -/
  value_split : ∀ z : BitString, pLabel R <+: z → z.length < g.level →
    g.value (z ++ [false]) + g.value (z ++ [true]) = g.value z
  /-- the stage value of `g` is a semimeasure on the cone of `p_R`, with the value
  `2^{s-R-1}` at `p_R` itself -/
  root : ∀ (qa : ℕ → BitString → BitString → ℕ) (s : ℕ), g.start ≤ s →
    compVal qa g s (pLabel R) = 2 ^ (s - (R + 1))

/-! #### Elementary consequences of the structural fields -/

section Values
variable {g : Gen}

/-- Off the front, the value of a generation is the frozen flow (`0` when not recorded). -/
theorem value_of_not_front {z : BitString} (hz : ∀ p ∈ g.front, p.1 ≠ z) :
    g.value z = (List.lookup z g.frozen).getD 0 :=
  lookup_append_left_none g.front g.frozen z 0 hz

/-- On the front, the value of a generation at a front vertex is its budget numerator. -/
theorem value_of_mem_front (hlen : ∀ p ∈ g.front, p.1.length = g.level)
    (hnodup : (g.front.map Prod.fst).Nodup) (hflen : ∀ p ∈ g.frozen, p.1.length < g.level)
    {p : BitString × ℕ} (hp : p ∈ g.front) : g.value p.1 = p.2 := by
  refine lookup_getD_eq _ _ _ _ (List.mem_append.mpr (Or.inl (by simpa using hp))) ?_
  intro q hq hqk
  rcases List.mem_append.mp hq with hq' | hq'
  · exact congrArg Prod.snd (eq_of_key_nodup hnodup hq' hp hqk)
  · have := hflen q hq'
    rw [hqk, hlen p hp] at this
    omega

/-- Strictly below the front level a generation records no value. -/
theorem value_eq_zero_of_gt (hlen : ∀ p ∈ g.front, p.1.length = g.level)
    (hflen : ∀ p ∈ g.frozen, p.1.length < g.level) {z : BitString} (hz : g.level < z.length) :
    g.value z = 0 := by
  refine lookup_getD_eq_default _ _ _ ?_
  intro p hp
  rcases List.mem_append.mp hp with hp' | hp'
  · have := hlen p hp'; intro hk; rw [hk] at this; omega
  · have := hflen p hp'; intro hk; rw [hk] at this; omega

/-- With an antichain front, `List.find?` locates the (unique) front vertex above `z`. -/
theorem find?_front (hlen : ∀ p ∈ g.front, p.1.length = g.level)
    (hnodup : (g.front.map Prod.fst).Nodup) {z : BitString} {p : BitString × ℕ}
    (hp : p ∈ g.front) (hpre : p.1 <+: z) :
    g.front.find? (fun q => q.1.isPrefixOf z) = some p := by
  cases hf : g.front.find? (fun q => q.1.isPrefixOf z) with
  | none =>
      exact absurd (List.isPrefixOf_iff_prefix.mpr hpre) (List.find?_eq_none.mp hf p hp)
  | some q =>
      have hq : q ∈ g.front := List.mem_of_find?_eq_some hf
      have hqpre : q.1 <+: z := List.isPrefixOf_iff_prefix.mp (by simpa using List.find?_some hf)
      have hkey : q.1 = p.1 := by
        rw [List.prefix_iff_eq_take.mp hqpre, hlen q hq, ← hlen p hp,
          ← List.prefix_iff_eq_take.mp hpre]
      rw [eq_of_key_nodup hnodup hq hp hkey]

/-- No front vertex is a prefix of `z`: the front search for `z` fails. -/
theorem find?_front_none {z : BitString}
    (hz : ∀ p ∈ g.front, ¬ (p.1 <+: z)) :
    g.front.find? (fun q => q.1.isPrefixOf z) = none :=
  List.find?_eq_none.mpr fun p hp hpre =>
    hz p hp (List.isPrefixOf_iff_prefix.mp (by simpa using hpre))

/-- Away from the front, the stage value is the frozen value rescaled by `2^{s-start}`. -/
theorem compVal_of_find_none (qa : ℕ → BitString → BitString → ℕ) (s : ℕ) {z : BitString}
    (hz : g.front.find? (fun q => q.1.isPrefixOf z) = none) :
    compVal qa g s z = (List.lookup z g.frozen).getD 0 * 2 ^ (s - g.start) := by
  unfold compVal; rw [hz]

/-- When the front search for `z` finds the vertex `p`, the stage value is the budget of `p`
times the sanitized conditional stage below `p`. -/
theorem compVal_of_find_some (qa : ℕ → BitString → BitString → ℕ) (s : ℕ) {z : BitString}
    {p : BitString × ℕ} (hz : g.front.find? (fun q => q.1.isPrefixOf z) = some p) :
    compVal qa g s z = p.2 * qHat qa p.1 (s - g.start) (z.drop p.1.length) := by
  unfold compVal; rw [hz]

end Values

/-- Smart constructor: the field `root` is a consequence of the structural fields together
with `value_root`. -/
theorem genInv_of_core {R : ℕ} {g : Gen}
    (hstart : R + 1 ≤ g.start) (hlevel : R + 1 ≤ g.level) (hne : g.front ≠ [])
    (hlen : ∀ p ∈ g.front, p.1.length = g.level)
    (hext : ∀ p ∈ g.front, pLabel R <+: p.1)
    (hpos : ∀ p ∈ g.front, 0 < p.2)
    (hnodup : (g.front.map Prod.fst).Nodup)
    (hbsum : (g.front.map Prod.snd).sum = 2 ^ (g.start - (R + 1)))
    (hflen : ∀ p ∈ g.frozen, p.1.length < g.level)
    (hfext : ∀ p ∈ g.frozen, pLabel R <+: p.1)
    (hvroot : g.value (pLabel R) = 2 ^ (g.start - (R + 1)))
    (hvsplit : ∀ z : BitString, pLabel R <+: z → z.length < g.level →
      g.value (z ++ [false]) + g.value (z ++ [true]) = g.value z) :
    GenInv R g := by
  refine ⟨hstart, hlevel, hne, hlen, hext, hpos, hnodup, hbsum, hflen, hfext, hvroot, hvsplit,
    ?_⟩
  intro qa s hs
  have hpow : 2 ^ (g.start - (R + 1)) * 2 ^ (s - g.start) = 2 ^ (s - (R + 1)) := by
    rw [← pow_add]; congr 1; omega
  rcases Nat.eq_or_lt_of_le hlevel with hL | hL
  · -- `g.level = R + 1`: the front is `{p_R}` itself
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have hplen : p.1.length = R + 1 := by rw [hlen p hp, ← hL]
    have hpeq : p.1 = pLabel R :=
      ((hext p hp).eq_of_length (by simp [hplen])).symm
    rw [compVal_of_find_some qa s (find?_front hlen hnodup hp (by rw [hpeq]))]
    rw [hpeq, pLabel_length]
    have : (pLabel R).drop (R + 1) = [] := by
      apply List.drop_eq_nil_of_le; simp
    rw [this, qHat_root]
    have : p.2 = 2 ^ (g.start - (R + 1)) := by
      rw [← hvroot, ← hpeq, value_of_mem_front hlen hnodup hflen hp]
    rw [this, hpow]
  · -- `g.level > R + 1`: `p_R` lies in the frozen region
    have hnf : ∀ q ∈ g.front, ¬ (q.1 <+: pLabel R) := by
      intro q hq hpre
      have := hpre.length_le
      rw [hlen q hq, pLabel_length] at this
      omega
    rw [compVal_of_find_none qa s (find?_front_none hnf)]
    rw [← value_of_not_front (fun q hq hk => hnf q hq (by rw [hk])), hvroot, hpow]

/-- The invariant holds initially.  Difficulty **E**, ~20 lines. -/
theorem genInv_initGen (R : ℕ) : GenInv R (initGen R) := by
  have hval : (initGen R).value (pLabel R) = 1 :=
    lookup_getD_eq _ _ _ _ (by simp [initGen]) (by intro q hq; simp [initGen] at hq; simp [hq])
  refine genInv_of_core (R := R) (g := initGen R) (le_refl _) (le_refl _) (by simp [initGen])
    ?_ ?_ ?_ ?_ ?_ (by simp [initGen]) (by simp [initGen]) ?_ ?_
  · intro p hp; simp only [initGen, List.mem_singleton] at hp; simp [hp, initGen]
  · intro p hp; simp only [initGen, List.mem_singleton] at hp; simp [hp]
  · intro p hp; simp only [initGen, List.mem_singleton] at hp; simp [hp]
  · simp [initGen]
  · simp [initGen]
  · rw [hval]; simp [initGen]
  · intro z hz hlt
    exfalso
    have := hz.length_le
    simp only [initGen] at hlt
    rw [pLabel_length] at this
    omega

/-- The start stage of `genAt R n` is at most the stage it lives at.  Difficulty **E**. -/
theorem genAt_start_le (qa ma : ℕ → BitString → BitString → ℕ) (R n : ℕ) :
    (genAt qa ma R n).start ≤ R + 1 + n := by
  induction n with
  | zero => simp [genAt, initGen]
  | succ n ih =>
      rw [genAt]
      split
      · simp [transition]
      · omega

/-! ### The transition: exact flows under the front vertices -/

/-- The completed flow under the front vertex `p` at local time `t`, normalised to the new
denominator `2^{s+1}`.  This is the value `transition` records. -/
def transFlow (qa : ℕ → BitString → BitString → ℕ) (t : ℕ) (p : BitString × ℕ)
    (w : BitString) : ℕ := flowVal (snapshot qa p.1 p.2 t) (p.2 * 2 ^ (t + 1)) w

/-- The front after a transition, in terms of the completed flows `transFlow`. -/
theorem transition_front (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) :
    (transition qa g s).front = g.front.flatMap (fun p =>
      (binStrings (s - g.start + 1)).filterMap (fun w =>
        if transFlow qa (s - g.start) p w = 0 then none
        else some (p.1 ++ w, transFlow qa (s - g.start) p w))) := rfl

/-- The frozen flow after a transition, in terms of the completed flows `transFlow`. -/
theorem transition_frozen (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) :
    (transition qa g s).frozen =
      g.frozen.map (fun p => (p.1, p.2 * 2 ^ (s - g.start + 1))) ++
        g.front.flatMap (fun p => (binStringsUpTo (s - g.start)).map (fun w =>
          (p.1 ++ w, transFlow qa (s - g.start) p w))) := rfl

/-- The root value of a snapshot is at most `b · 2^{t+1}`. -/
theorem snapshot_root {qa : ℕ → BitString → BitString → ℕ} {t : ℕ} {p : BitString × ℕ} :
    snapshot qa p.1 p.2 t [] ≤ p.2 * 2 ^ (t + 1) := by
  simp [snapshot, qHat_root, pow_succ]; ring_nf; omega

section Flow
variable {qa : ℕ → BitString → BitString → ℕ} {t : ℕ} {p : BitString × ℕ}
variable (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
include hcoh

/-- A snapshot of a coherent stage is coherent: the two children carry at most the parent. -/
theorem snapshot_coh (w : BitString) :
    snapshot qa p.1 p.2 t (w ++ [false]) + snapshot qa p.1 p.2 t (w ++ [true])
      ≤ snapshot qa p.1 p.2 t w := by
  unfold snapshot
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (hcoh _ _ _)

/-- The completed flow is exact: the two children carry exactly the parent. -/
theorem transFlow_split (w : BitString) :
    transFlow qa t p (w ++ [false]) + transFlow qa t p (w ++ [true]) = transFlow qa t p w :=
  flowVal_split (snapshot_coh hcoh) snapshot_root w

/-- The completed flow dominates the snapshot it completes. -/
theorem transFlow_ge (w : BitString) : 2 * p.2 * qHat qa p.1 t w ≤ transFlow qa t p w :=
  flowVal_ge (snapshot_coh hcoh) snapshot_root w

/-- At every depth `d` the completed flow sums to its root value `b · 2^{t+1}`. -/
theorem transFlow_level_sum (d : ℕ) :
    ((binStrings d).map (transFlow qa t p)).sum = p.2 * 2 ^ (t + 1) :=
  flowVal_level_sum (snapshot_coh hcoh) snapshot_root d

end Flow

/-- The root value of the completed flow is `b · 2^{t+1}`. -/
@[simp] theorem transFlow_nil (qa : ℕ → BitString → BitString → ℕ) (t : ℕ)
    (p : BitString × ℕ) : transFlow qa t p [] = p.2 * 2 ^ (t + 1) := rfl

/-- Every string of length at most `d` is listed in `binStringsUpTo d`. -/
theorem mem_binStringsUpTo {d : ℕ} {w : BitString} (h : w.length ≤ d) : w ∈ binStringsUpTo d := by
  unfold binStringsUpTo
  simp only [List.mem_flatMap, List.mem_range]
  exact ⟨w.length, by omega, mem_binStrings w⟩

/-- The strings listed in `binStringsUpTo d` have length at most `d`. -/
theorem length_of_mem_binStringsUpTo {d : ℕ} {w : BitString} (h : w ∈ binStringsUpTo d) :
    w.length ≤ d := by
  unfold binStringsUpTo at h
  simp only [List.mem_flatMap, List.mem_range] at h
  obtain ⟨k, hk, hw⟩ := h
  rw [length_of_mem_binStrings k w hw]; omega

/-- Lookup in an append: look in the left list first, then in the right one. -/
theorem lookup_append {β : Type*} (L M : List (BitString × β)) (k : BitString) :
    (L ++ M).lookup k = (L.lookup k).orElse (fun _ => M.lookup k) := by
  induction L with
  | nil => simp
  | cons q L ih =>
      by_cases h : k = q.1
      · simp [List.lookup, h]
      · have hb : (k == q.1) = false := by simpa using h
        simp [List.lookup, hb, ih]

/-- A key that occurs in `L` has a lookup in `L`. -/
theorem lookup_ne_none_of_mem {β : Type*} (L : List (BitString × β)) (k : BitString) (v : β)
    (hmem : (k, v) ∈ L) : L.lookup k ≠ none := by
  induction L with
  | nil => simp at hmem
  | cons q L ih =>
      by_cases h : k = q.1
      · simp [List.lookup, h]
      · have hb : (k == q.1) = false := by simpa using h
        simp only [List.lookup, hb]
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd (congrArg Prod.fst h') h
        · exact ih h'

/-- If `(k, v) ∈ L` and every entry of `L` with key `k` carries `v`, the lookup of `k` in
`L ++ M` returns `v`. -/
theorem lookup_getD_append_left {β : Type*} (L M : List (BitString × β)) (k : BitString)
    (v d : β) (hmem : (k, v) ∈ L) (huniq : ∀ q ∈ L, q.1 = k → q.2 = v) :
    ((L ++ M).lookup k).getD d = v := by
  have h := lookup_getD_eq L k v d hmem huniq
  rw [lookup_append]
  cases hL : L.lookup k with
  | none => exact absurd hL (lookup_ne_none_of_mem L k v hmem)
  | some x => rw [hL] at h; simpa using h

/-- A key that occurs in no entry of `M` has no lookup in `M`. -/
theorem lookup_eq_none_of_forall {β : Type*} (M : List (BitString × β)) (k : BitString)
    (h : ∀ p ∈ M, p.1 ≠ k) : M.lookup k = none := by
  induction M with
  | nil => rfl
  | cons q M ih =>
      have hb : (k == q.1) = false := by
        have := h q (by simp); simpa using fun hh => this hh.symm
      simp only [List.lookup, hb]
      exact ih (fun r hr => h r (by simp [hr]))

/-- A key absent from `M` is looked up in `L ++ M` as in `L`. -/
theorem lookup_getD_append_right_none {β : Type*} (L M : List (BitString × β)) (k : BitString)
    (d : β) (h : ∀ p ∈ M, p.1 ≠ k) : ((L ++ M).lookup k).getD d = (L.lookup k).getD d := by
  rw [lookup_append, lookup_eq_none_of_forall M k h]
  cases L.lookup k <;> simp

/-- Scaling an optional value by `c` scales its default-`0` reading by `c`. -/
theorem getD_map_mul (o : Option ℕ) (c : ℕ) : (o.map (fun v => v * c)).getD 0 = o.getD 0 * c := by
  cases o <;> simp

/-- The list `binStrings d` of the strings of length `d` has no duplicates. -/
theorem binStrings_nodup (d : ℕ) : (binStrings d).Nodup := by
  induction d with
  | zero => simp [binStrings]
  | succ d ih =>
      rw [binStrings]
      refine List.nodup_flatMap.mpr ⟨fun w _ => ?_, ?_⟩
      · simp
      · refine List.Pairwise.imp_of_mem ?_ ih
        intro a b ha hb hne
        have hlen : a.length = b.length := by
          rw [length_of_mem_binStrings d a ha, length_of_mem_binStrings d b hb]
        simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl) <;> rintro (hx | hx) <;>
          exact (hne (List.append_inj_left hx hlen)).elim

/-- The sum of a `flatMap` is the sum of the sums of the pieces. -/
theorem sum_flatMap {α : Type*} (L : List α) (F : α → List ℕ) :
    (L.flatMap F).sum = (L.map (fun x => (F x).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Dropping the zero entries does not change the total of the recorded values. -/
theorem sum_filterMap_nonzero (u : BitString) (F : BitString → ℕ) (l : List BitString) :
    ((l.filterMap (fun w => if F w = 0 then none else some (u ++ w, F w))).map Prod.snd).sum
      = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons w l ih => by_cases hF : F w = 0 <;> simp [hF, ih]

/-- The keys kept after dropping the zero entries are the extensions `u ++ w` with
`F w ≠ 0`. -/
theorem filterMap_map_fst (u : BitString) (F : BitString → ℕ) (l : List BitString) :
    ((l.filterMap (fun w => if F w = 0 then none else some (u ++ w, F w))).map Prod.fst)
      = (l.filter (fun w => !(F w == 0))).map (fun w => u ++ w) := by
  induction l with
  | nil => simp
  | cons w l ih => by_cases hF : F w = 0 <;> simp [hF, ih]

/-- Lookup commutes with scaling all values by `c`. -/
theorem lookup_map_scale {β : Type*} [Mul β] (L : List (BitString × β)) (c : β) (k : BitString) :
    ((L.map (fun p => (p.1, p.2 * c))).lookup k) = (L.lookup k).map (fun v => v * c) := by
  induction L with
  | nil => simp
  | cons q L ih =>
      by_cases h : k = q.1
      · simp [List.lookup, h]
      · have hb : (k == q.1) = false := by simpa using h
        simp [List.lookup, hb, ih]

section Transition

variable {R : ℕ} {g : Gen} {qa : ℕ → BitString → BitString → ℕ} {s : ℕ}

/-- The front vertices after a transition: the extensions `u ++ w` of the old front vertices
at relative depth `s - start + 1` with nonzero completed flow. -/
theorem mem_transition_front_iff {q : BitString × ℕ} :
    q ∈ (transition qa g s).front ↔ ∃ p ∈ g.front, ∃ w ∈ binStrings (s - g.start + 1),
      transFlow qa (s - g.start) p w ≠ 0 ∧
        q = (p.1 ++ w, transFlow qa (s - g.start) p w) := by
  rw [transition_front]
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, w, hw, hq⟩
    by_cases hv : transFlow qa (s - g.start) p w = 0
    · simp [hv] at hq
    · simp only [hv, ite_false, Option.some.injEq] at hq
      exact ⟨p, hp, w, hw, hv, hq.symm⟩
  · rintro ⟨p, hp, w, hw, hv, rfl⟩
    exact ⟨p, hp, w, hw, by simp [hv]⟩

/-- The frozen entries after a transition: the rescaled old frozen entries and the completed
flows above the new front. -/
theorem mem_transition_frozen_iff {q : BitString × ℕ} :
    q ∈ (transition qa g s).frozen ↔
      (∃ p ∈ g.frozen, q = (p.1, p.2 * 2 ^ (s - g.start + 1))) ∨
      (∃ p ∈ g.front, ∃ w ∈ binStringsUpTo (s - g.start),
        q = (p.1 ++ w, transFlow qa (s - g.start) p w)) := by
  rw [transition_frozen]
  simp only [List.mem_append, List.mem_map, List.mem_flatMap]
  constructor
  · rintro (⟨p, hp, hq⟩ | ⟨p, hp, w, hw, hq⟩)
    · exact Or.inl ⟨p, hp, hq.symm⟩
    · exact Or.inr ⟨p, hp, w, hw, hq.symm⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, w, hw, rfl⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, w, hw, rfl⟩

variable (h : GenInv R g)
include h

/-- Under the invariant, all front vertices after a transition lie at the new level. -/
theorem transition_front_len {q : BitString × ℕ} (hq : q ∈ (transition qa g s).front) :
    q.1.length = (transition qa g s).level := by
  obtain ⟨p, hp, w, hw, _, rfl⟩ := mem_transition_front_iff.mp hq
  simp only [transition, List.length_append, h.front_len p hp,
    length_of_mem_binStrings _ _ hw]
  omega

/-- Under the invariant, all frozen entries after a transition lie strictly above the new
level. -/
theorem transition_frozen_len {q : BitString × ℕ} (hq : q ∈ (transition qa g s).frozen) :
    q.1.length < (transition qa g s).level := by
  rcases mem_transition_frozen_iff.mp hq with ⟨p, hp, rfl⟩ | ⟨p, hp, w, hw, rfl⟩
  · have := h.frozen_len p hp; simp only [transition]; omega
  · have h1 := h.front_len p hp
    have h2 := length_of_mem_binStringsUpTo hw
    simp only [transition, List.length_append]; omega

/-- Nothing in the new generation is recorded at a vertex without a front vertex above it,
except above the front. -/
theorem transition_value_of_no_front {z : BitString} (hz1 : g.level ≤ z.length)
    (hz2 : ∀ p ∈ g.front, ¬ (p.1 <+: z)) : (transition qa g s).value z = 0 := by
  refine lookup_getD_eq_default _ _ _ ?_
  intro q hq hk
  rcases List.mem_append.mp hq with hq' | hq'
  · obtain ⟨p, hp, w, _, _, rfl⟩ := mem_transition_front_iff.mp hq'
    exact hz2 p hp (hk ▸ (List.prefix_append p.1 w))
  · rcases mem_transition_frozen_iff.mp hq' with ⟨p, hp, rfl⟩ | ⟨p, hp, w, _, rfl⟩
    · have := h.frozen_len p hp; rw [hk] at this; omega
    · exact hz2 p hp (hk ▸ (List.prefix_append p.1 w))

/-- Above the front of the old generation the values are simply rescaled. -/
theorem transition_value_lt_level {z : BitString} (hz : z.length < g.level) :
    (transition qa g s).value z = g.value z * 2 ^ (s - g.start + 1) := by
  have hnf : ∀ q ∈ (transition qa g s).front, q.1 ≠ z := by
    intro q hq hk
    have h1 := transition_front_len h hq
    rw [hk] at h1
    simp only [transition] at h1; omega
  have hz' : (List.lookup z (g.front ++ g.frozen)).getD (0 : ℕ)
      = (List.lookup z g.frozen).getD 0 :=
    lookup_append_left_none _ _ _ _
      (fun q hq hk => by have := h.front_len q hq; rw [hk] at this; omega)
  unfold Gen.value
  rw [lookup_append_left_none _ _ _ _ hnf, transition_frozen,
    lookup_getD_append_right_none, lookup_map_scale, getD_map_mul, hz']
  intro q hq hk
  simp only [List.mem_flatMap, List.mem_map] at hq
  obtain ⟨p, hp, w, hw, rfl⟩ := hq
  have hplen := h.front_len p hp
  have hk2 : p.1 ++ w = z := hk
  have hll : (p.1 ++ w).length = z.length := by rw [hk2]
  simp only [List.length_append] at hll
  omega

/-- Under a front vertex the new generation records the completed flow. -/
theorem transition_value_front {p : BitString × ℕ} (hp : p ∈ g.front) {w : BitString}
    (hw : w.length ≤ s - g.start + 1) :
    (transition qa g s).value (p.1 ++ w) = transFlow qa (s - g.start) p w := by
  have hplen := h.front_len p hp
  have hlen : (p.1 ++ w).length = g.level + w.length := by
    simp [hplen]
  -- entries of `frozen` never reach length `g.level + (t+1)`, and entries of the mapped
  -- old frozen region never reach length `g.level`
  have hfrozen_ne : ∀ q ∈ (transition qa g s).frozen, w.length = s - g.start + 1 →
      q.1 ≠ p.1 ++ w := by
    intro q hq hwt hk
    rcases mem_transition_frozen_iff.mp hq with ⟨p', hp', rfl⟩ | ⟨p', hp', w', hw', rfl⟩
    · have := h.frozen_len p' hp'
      have hk2 : p'.1 = p.1 ++ w := hk
      have h2 : p'.1.length = (p.1 ++ w).length := by rw [hk2]
      omega
    · have h1 := h.front_len p' hp'
      have h2 := length_of_mem_binStringsUpTo hw'
      have hk2 : p'.1 ++ w' = p.1 ++ w := hk
      have h3 : (p'.1 ++ w').length = (p.1 ++ w).length := by rw [hk2]
      simp only [List.length_append] at h3
      omega
  have hfront_key : ∀ q ∈ (transition qa g s).front, q.1 = p.1 ++ w →
      q.2 = transFlow qa (s - g.start) p w := by
    intro q hq hk
    obtain ⟨p', hp', w', hw', hv', rfl⟩ := mem_transition_front_iff.mp hq
    have hl : p'.1.length = p.1.length := by rw [h.front_len p' hp', hplen]
    obtain ⟨he1, he2⟩ := List.append_inj hk hl
    have : p' = p := eq_of_key_nodup h.front_nodup hp' hp he1
    subst this; subst he2; rfl
  by_cases hwt : w.length = s - g.start + 1
  · by_cases hv : transFlow qa (s - g.start) p w = 0
    · rw [hv]
      refine lookup_getD_eq_default _ _ _ ?_
      intro q hq hk
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨p', hp', w', hw', hv', rfl⟩ := mem_transition_front_iff.mp hq'
        exact hv' ((hfront_key _ hq' hk).trans hv)
      · exact hfrozen_ne q hq' hwt hk
    · refine lookup_getD_eq _ _ _ _ ?_ ?_
      · refine List.mem_append.mpr (Or.inl (mem_transition_front_iff.mpr
          ⟨p, hp, w, ?_, hv, rfl⟩))
        exact hwt ▸ mem_binStrings w
      · intro q hq hk
        rcases List.mem_append.mp hq with hq' | hq'
        · exact hfront_key q hq' hk
        · exact absurd hk (hfrozen_ne q hq' hwt)
  · have hwt' : w.length ≤ s - g.start := by omega
    refine lookup_getD_eq _ _ _ _ ?_ ?_
    · exact List.mem_append.mpr (Or.inr (mem_transition_frozen_iff.mpr
        (Or.inr ⟨p, hp, w, mem_binStringsUpTo hwt', rfl⟩)))
    · intro q hq hk
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨p', hp', w', hw', _, rfl⟩ := mem_transition_front_iff.mp hq'
        exfalso
        have h1 := h.front_len p' hp'
        have h2 := length_of_mem_binStrings _ _ hw'
        have hk2 : p'.1 ++ w' = p.1 ++ w := hk
        have h3 : (p'.1 ++ w').length = (p.1 ++ w).length := by rw [hk2]
        simp only [List.length_append] at h3
        omega
      · rcases mem_transition_frozen_iff.mp hq' with ⟨p', hp', rfl⟩ | ⟨p', hp', w', hw', rfl⟩
        · exfalso
          have := h.frozen_len p' hp'
          have hk2 : p'.1 = p.1 ++ w := hk
          have h2 : p'.1.length = (p.1 ++ w).length := by rw [hk2]
          omega
        · have hl : p'.1.length = p.1.length := by rw [h.front_len p' hp', hplen]
          obtain ⟨he1, he2⟩ := List.append_inj hk hl
          have : p' = p := eq_of_key_nodup h.front_nodup hp' hp he1
          subst this; subst he2; rfl


/-- Above the front of the old generation (front vertices included) the values are simply
rescaled by `2^{t+1}`. -/
theorem transition_value_le_level {z : BitString} (hz : z.length ≤ g.level) :
    (transition qa g s).value z = g.value z * 2 ^ (s - g.start + 1) := by
  rcases Nat.lt_or_ge z.length g.level with hlt | hge
  · exact transition_value_lt_level h hlt
  · have heq : z.length = g.level := le_antisymm hz hge
    by_cases hf : ∃ p ∈ g.front, p.1 = z
    · obtain ⟨p, hp, hpz⟩ := hf
      subst hpz
      have hv := transition_value_front (qa := qa) (s := s) h hp (w := []) (by simp)
      simp only [List.append_nil] at hv
      rw [hv, transFlow_nil, value_of_mem_front h.front_len h.front_nodup h.frozen_len hp]
    · push Not at hf
      have hgv : g.value z = 0 := by
        refine lookup_getD_eq_default _ _ _ ?_
        intro q hq hk
        rcases List.mem_append.mp hq with hq' | hq'
        · exact hf q hq' hk
        · have := h.frozen_len q hq'; rw [hk] at this; omega
      rw [hgv, Nat.zero_mul]
      refine lookup_getD_eq_default _ _ _ ?_
      intro q hq hk
      rcases List.mem_append.mp hq with hq' | hq'
      · have hl := transition_front_len h hq'
        rw [hk] at hl; simp only [transition] at hl; omega
      · rcases mem_transition_frozen_iff.mp hq' with ⟨p', hp', rfl⟩ | ⟨p', hp', w', hw', rfl⟩
        · have hfl := h.frozen_len p' hp'
          have hk2 : p'.1 = z := hk
          rw [hk2] at hfl; omega
        · have h1 := h.front_len p' hp'
          have hk2 : p'.1 ++ w' = z := hk
          have h3 : (p'.1 ++ w').length = z.length := by rw [hk2]
          simp only [List.length_append] at h3
          have hw'nil : w' = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hw'nil
          exact hf p' hp' (by simpa using hk2)

/-- **A3.6 (`transition_inv`).**  The invariant is preserved by a transition. -/
theorem genInv_transition
    (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
    (hs : g.start ≤ s) : GenInv R (transition qa g s) := by
  have hstart := h.start_ge
  have hlevel := h.level_ge
  -- a front vertex of the old generation, used for nonemptiness
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil _ h.front_ne
  have hfront_ne : (transition qa g s).front ≠ [] := by
    have hsum := transFlow_level_sum (qa := qa) (t := s - g.start) (p := p₀) hcoh
      (s - g.start + 1)
    have hpos : 0 < p₀.2 * 2 ^ (s - g.start + 1) :=
      Nat.mul_pos (h.front_pos p₀ hp₀) (Nat.two_pow_pos _)
    have hex : ∃ w ∈ binStrings (s - g.start + 1), transFlow qa (s - g.start) p₀ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [List.sum_eq_zero (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact hcon w hw)] at hsum
      omega
    obtain ⟨w, hw, hv⟩ := hex
    intro hnil
    have hmem : (p₀.1 ++ w, transFlow qa (s - g.start) p₀ w) ∈ (transition qa g s).front :=
      mem_transition_front_iff.mpr ⟨p₀, hp₀, w, hw, hv, rfl⟩
    rw [hnil] at hmem
    simp at hmem
  have hbudget : ((transition qa g s).front.map Prod.snd).sum
      = 2 ^ ((transition qa g s).start - (R + 1)) := by
    have hinner : ∀ q ∈ g.front, (((binStrings (s - g.start + 1)).filterMap (fun w =>
          if transFlow qa (s - g.start) q w = 0 then none
          else some (q.1 ++ w, transFlow qa (s - g.start) q w))).map Prod.snd).sum
        = q.2 * 2 ^ (s - g.start + 1) := by
      intro q _
      rw [sum_filterMap_nonzero]
      exact transFlow_level_sum hcoh _
    rw [transition_front, List.map_flatMap, sum_flatMap, List.map_congr_left hinner,
      List.sum_map_mul_right g.front Prod.snd (2 ^ (s - g.start + 1)), h.budget_sum,
      ← pow_add]
    simp only [transition]
    congr 1
    omega
  have hvalroot : (transition qa g s).value (pLabel R)
      = 2 ^ ((transition qa g s).start - (R + 1)) := by
    rw [transition_value_le_level h (by rw [pLabel_length]; omega), h.value_root, ← pow_add]
    simp only [transition]
    congr 1
    omega
  refine genInv_of_core (by simp only [transition]; omega) (by simp only [transition]; omega)
    hfront_ne (fun q hq => transition_front_len h hq) ?_ ?_ ?_ hbudget
    (fun q hq => transition_frozen_len h hq) ?_ hvalroot ?_
  · intro q hq
    obtain ⟨q', hq', w, _, _, rfl⟩ := mem_transition_front_iff.mp hq
    exact (h.front_ext q' hq').trans (List.prefix_append _ _)
  · intro q hq
    obtain ⟨q', hq', w, _, hv, rfl⟩ := mem_transition_front_iff.mp hq
    exact Nat.pos_of_ne_zero hv
  · -- the new front is a set of distinct level-`level'` vertices
    rw [transition_front, List.map_flatMap]
    simp only [filterMap_map_fst]
    have hfn : g.front.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp h.front_nodup
    refine List.nodup_flatMap.mpr ⟨fun q _ => ?_, ?_⟩
    · exact List.Nodup.map (fun a b hab => List.append_cancel_left hab)
        (List.Nodup.filter _ (binStrings_nodup _))
    · refine List.Pairwise.imp_of_mem ?_ hfn
      intro a b ha hb hne
      have hlen : a.1.length = b.1.length := by
        rw [h.front_len a ha, h.front_len b hb]
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro x ⟨y₁, _, rfl⟩ ⟨y₂, _, hx⟩
      exact hne (List.append_inj_left hx hlen.symm).symm
  · intro q hq
    rcases mem_transition_frozen_iff.mp hq with ⟨q', hq', rfl⟩ | ⟨q', hq', w, _, rfl⟩
    · exact h.frozen_ext q' hq'
    · exact (h.front_ext q' hq').trans (List.prefix_append _ _)
  · -- exact splitting of the new frozen region
    intro z hzext hzlt
    simp only [transition] at hzlt
    rcases Nat.lt_or_ge z.length g.level with hlt | hge
    · rw [transition_value_le_level h (by simp; omega),
        transition_value_le_level h (by simp; omega),
        transition_value_lt_level h hlt, ← Nat.add_mul, h.value_split z hzext hlt]
    · by_cases hfp : ∃ p ∈ g.front, p.1 <+: z
      · obtain ⟨p, hp, hpre⟩ := hfp
        obtain ⟨w, rfl⟩ := hpre
        have hplen := h.front_len p hp
        have hwlen : w.length ≤ s - g.start := by
          simp only [List.length_append, hplen] at hzlt; omega
        rw [show p.1 ++ w ++ [false] = p.1 ++ (w ++ [false]) by simp,
          show p.1 ++ w ++ [true] = p.1 ++ (w ++ [true]) by simp,
          transition_value_front h hp (w := w ++ [false]) (by simp; omega),
          transition_value_front h hp (w := w ++ [true]) (by simp; omega),
          transition_value_front h hp (w := w) (by omega),
          transFlow_split hcoh]
      · push Not at hfp
        have hchild : ∀ b : Bool, ∀ q ∈ g.front, ¬ (q.1 <+: z ++ [b]) := by
          intro b q hq hpre
          exact hfp q hq ((List.isPrefix_append_of_length
            (by rw [h.front_len q hq]; omega)).mp hpre)
        rw [transition_value_of_no_front h hge hfp,
          transition_value_of_no_front h (by simp; omega) (hchild false),
          transition_value_of_no_front h (by simp; omega) (hchild true)]

end Transition

/-- **A3.6 + A3.9.**  The invariant along the evolution of a component.

The hypothesis `hcoh` (each sanitized stage `Q̂_t(· | u)` is a semimeasure) is genuinely
needed: it is what makes the completed flows `flowVal` exact, hence what conserves the
total budget.  For a *coherent* family of stages this is `qHat_coherent hQ hqsup`. -/
theorem genInv_genAt' (qa ma : ℕ → BitString → BitString → ℕ)
    (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
    (R n : ℕ) : GenInv R (genAt qa ma R n) := by
  induction n with
  | zero => exact genInv_initGen R
  | succ n ih =>
      rw [genAt]
      split
      · exact genInv_transition ih hcoh (genAt_start_le qa ma R n)
      · exact ih

/-- The coherence hypothesis of `genInv_genAt'` for the sanitized stages of a genuine
conditional continuous semimeasure. -/
theorem qHat_coh (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa : ℕ → BitString → BitString → ℕ}
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u) :
    ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y :=
  fun u t y => qHat_coherent hQ hqsup u t y

/-! #### Why `genInv_genAt'` needs `hcoh`: a machine-checked refutation of the
unconditional statement

Dropping the coherence hypothesis makes the invariant FALSE.  `GenInv.budget_sum` asserts
that the front budgets of `genAt qa ma R n` sum to `2 ^ (start - (R+1))`.  For an
*arbitrary* `qa : ℕ → BitString → BitString → ℕ` the sanitized stages `qHat qa u t ·` need
not be semimeasures, the snapshots handed to `flowVal` are then incoherent, `flowVal` no
longer splits exactly (ℕ-subtraction truncates) and the level sums of the completion
*exceed* the root budget; the budget then grows without control across a transition.

Concretely: `R = 0`, the trigger fails at stage `1` and fires at stage `2` (so the local
time is `t = 1`), and the raw stage `qa 1 y u = 100` for `|y| = 1` is far too large to be a
semimeasure.  The completion of the incoherent snapshot then carries the mass `200` instead
of `4 = 2 ^ (start - (R+1))`.
 -/

private def qaBad : ℕ → BitString → BitString → ℕ :=
  fun s y _ => if s = 1 ∧ y.length = 1 then 100 else 0

private def maBad : ℕ → BitString → BitString → ℕ :=
  fun s _ _ => if s = 2 then 100 else 0

example :
    ¬ (∀ (qa ma : ℕ → BitString → BitString → ℕ) (R n : ℕ), GenInv R (genAt qa ma R n)) := by
  intro hall
  have h := (hall qaBad maBad 0 2).budget_sum
  have e1 : ((genAt qaBad maBad 0 2).front.map Prod.snd).sum = 200 := by decide
  have e2 : (2 : ℕ) ^ ((genAt qaBad maBad 0 2).start - (0 + 1)) = 4 := by decide
  rw [e1, e2] at h
  exact absurd h (by decide)

/-! ### Leading ones: the component index -/

/-- A leading `1` increments the number of leading ones. -/
theorem compIdx_cons_true (x : BitString) : compIdx (true :: x) = compIdx x + 1 := by
  simp [compIdx, List.takeWhile]

/-- A string starting with `0` has no leading ones. -/
theorem compIdx_cons_false (x : BitString) : compIdx (false :: x) = 0 := by
  simp [compIdx, List.takeWhile]

/-- The number of leading ones is at most the length. -/
theorem compIdx_le (z : BitString) : compIdx z ≤ z.length := by
  simpa [compIdx] using (List.takeWhile_sublist (l := z) (p := id)).length_le

/-- The all-ones string `1^n` has `n` leading ones. -/
theorem compIdx_replicate_true (n : ℕ) : compIdx (List.replicate n true) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, compIdx_cons_true, ih]

/-- The label `p_R = 1^R 0` lies in component `R`. -/
@[simp] theorem compIdx_pLabel (R : ℕ) : compIdx (pLabel R) = R := by
  unfold pLabel
  induction R with
  | zero => simp [compIdx]
  | succ R ih => rw [List.replicate_succ, List.cons_append, compIdx_cons_true, ih]



/-- A string consisting of leading ones only is the all-ones string (a spine vertex). -/
theorem eq_replicate_of_full {x : BitString} (h : x.length = compIdx x) :
    x = List.replicate x.length true := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      cases a
      · rw [compIdx_cons_false] at h; simp at h
      · rw [compIdx_cons_true] at h
        simp only [List.length_cons] at h ⊢
        rw [List.replicate_succ, ← ih (by omega)]

/-- Appending `0` to the spine vertex `1^n` gives the label `p_n`. -/
theorem eq_pLabel_of_full {x : BitString} (h : x.length = compIdx x) :
    x ++ [false] = pLabel x.length := by
  rw [pLabel, ← eq_replicate_of_full h]

/-- Appending `1` to a spine vertex gives a spine vertex. -/
theorem full_append_true {x : BitString} (h : x.length = compIdx x) :
    (x ++ [true]).length = compIdx (x ++ [true]) := by
  have : x ++ [true] = List.replicate (x.length + 1) true := by
    rw [List.replicate_succ', ← eq_replicate_of_full h]
  rw [this, compIdx_replicate_true]
  simp

/-- Off the spine, appending a bit does not change the component index. -/
theorem compIdx_append_of_not_full {x : BitString} (h : x.length ≠ compIdx x) (b : Bool) :
    compIdx (x ++ [b]) = compIdx x := by
  induction x with
  | nil => simp [compIdx] at h
  | cons a x ih =>
      cases a
      · simp [compIdx_cons_false]
      · rw [List.cons_append, compIdx_cons_true, compIdx_cons_true] at *
        simp only [List.length_cons] at h
        rw [ih (by omega)]

/-- Off the spine, a string extends the label `p_R` of its component `R = compIdx x`. -/
theorem pLabel_prefix {x : BitString} (h : x.length ≠ compIdx x) : pLabel (compIdx x) <+: x := by
  induction x with
  | nil => simp [compIdx] at h
  | cons a x ih =>
      cases a
      · rw [compIdx_cons_false]; exact ⟨x, rfl⟩
      · rw [compIdx_cons_true]
        simp only [List.length_cons, compIdx_cons_true] at h
        obtain ⟨t, ht⟩ := ih (by omega)
        refine ⟨t, ?_⟩
        rw [pLabel, List.replicate_succ, List.cons_append, List.cons_append,
          show List.replicate (compIdx x) true ++ [false] = pLabel (compIdx x) from rfl, ht]

/-! ### Unfolding `nuStage` -/

/-- On the spine `1^j`, the stage numerator is `2^{s-j}` once `j ≤ s`, and `0` before. -/
theorem nuStage_spine (qa ma : ℕ → BitString → BitString → ℕ) (s : ℕ) {x : BitString}
    (h : x.length = compIdx x) :
    nuStage qa ma s x = if x.length ≤ s then 2 ^ (s - x.length) else 0 := by
  rw [nuStage, ite_eq_left h]

/-- Off the spine, the stage numerator is the stage value of the current generation of the
component, and `0` while the component is dormant. -/
theorem nuStage_comp (qa ma : ℕ → BitString → BitString → ℕ) (s : ℕ) {z : BitString}
    (h : z.length ≠ compIdx z) :
    nuStage qa ma s z =
      if compIdx z < s then
        compVal qa (genAt qa ma (compIdx z) (s - compIdx z - 1)) s z
      else 0 := by
  rw [nuStage, ite_eq_right h]

/-! ### Coherence of a single component -/

/-- **A3.11.**  The stage value of one generation is a semimeasure on the cone of `p_R`. -/
theorem compVal_coherent {R : ℕ} {g : Gen} (h : GenInv R g)
    {qa : ℕ → BitString → BitString → ℕ}
    (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
    (s : ℕ) {x : BitString} (hx : pLabel R <+: x) :
    compVal qa g s (x ++ [false]) + compVal qa g s (x ++ [true]) ≤ compVal qa g s x := by
  by_cases hf : ∃ p ∈ g.front, p.1 <+: x
  · -- below (or at) a front vertex: this is coherence of the sanitized stages
    obtain ⟨p, hp, hpre⟩ := hf
    have hlen : p.1.length ≤ x.length := hpre.length_le
    have e0 := find?_front h.front_len h.front_nodup hp hpre
    have e1 := find?_front h.front_len h.front_nodup hp
      (hpre.trans (List.prefix_append x [false]))
    have e2 := find?_front h.front_len h.front_nodup hp
      (hpre.trans (List.prefix_append x [true]))
    rw [compVal_of_find_some qa s e0, compVal_of_find_some qa s e1,
      compVal_of_find_some qa s e2, List.drop_append_of_le_length hlen,
      List.drop_append_of_le_length hlen, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hcoh _ _ _)
  · -- above the front: the frozen values split exactly
    push Not at hf
    have hchild : ∀ b : Bool,
        compVal qa g s (x ++ [b]) = g.value (x ++ [b]) * 2 ^ (s - g.start) := by
      intro b
      by_cases hfb : ∃ p ∈ g.front, p.1 <+: x ++ [b]
      · obtain ⟨p, hp, hpre⟩ := hfb
        have hnle : ¬ (p.1.length ≤ x.length) := fun hh =>
          hf p hp ((List.isPrefix_append_of_length hh).mp hpre)
        have hle := hpre.length_le
        simp only [List.length_append, List.length_singleton] at hle
        have heq : p.1 = x ++ [b] := hpre.eq_of_length (by simp; omega)
        rw [compVal_of_find_some qa s (find?_front h.front_len h.front_nodup hp hpre),
          ← heq, List.drop_length, qHat_root,
          value_of_mem_front h.front_len h.front_nodup h.frozen_len hp]
      · push Not at hfb
        rw [compVal_of_find_none qa s (find?_front_none hfb),
          value_of_not_front (fun q hq hk => hfb q hq (hk ▸ List.prefix_refl _))]
    have hxv : compVal qa g s x = g.value x * 2 ^ (s - g.start) := by
      rw [compVal_of_find_none qa s (find?_front_none hf),
        value_of_not_front (fun q hq hk => hf q hq (hk ▸ List.prefix_refl _))]
    rw [hchild false, hchild true, hxv, ← Nat.add_mul]
    refine Nat.mul_le_mul_right _ ?_
    rcases Nat.lt_or_ge x.length g.level with hlt | hge
    · exact le_of_eq (h.value_split x hx hlt)
    · have c0 : g.value (x ++ [false]) = 0 :=
        value_eq_zero_of_gt h.front_len h.frozen_len (by simp; omega)
      have c1 : g.value (x ++ [true]) = 0 :=
        value_eq_zero_of_gt h.front_len h.frozen_len (by simp; omega)
      simp [c0, c1]

/-! ### Stage monotonicity of a component -/

/-- At its own start stage a generation contributes exactly its recorded values (the local
clock is `t = 0`, where `Q̂_0` is the point mass at the root). -/
theorem compVal_at_start {R : ℕ} {g : Gen} (h : GenInv R g)
    (qa : ℕ → BitString → BitString → ℕ) (z : BitString) :
    compVal qa g g.start z = g.value z := by
  cases hf : g.front.find? (fun q => q.1.isPrefixOf z) with
  | none =>
      rw [compVal_of_find_none qa g.start hf]
      simp only [Nat.sub_self, pow_zero, Nat.mul_one]
      exact (value_of_not_front (fun q hq hk =>
        (List.find?_eq_none.mp hf q hq)
          (List.isPrefixOf_iff_prefix.mpr (hk ▸ List.prefix_refl _)))).symm
  | some p =>
      have hp : p ∈ g.front := List.mem_of_find?_eq_some hf
      have hpre : p.1 <+: z :=
        List.isPrefixOf_iff_prefix.mp (by simpa using List.find?_some hf)
      rw [compVal_of_find_some qa g.start hf]
      simp only [Nat.sub_self]
      by_cases hzp : z = p.1
      · subst hzp
        rw [List.drop_length, qHat_root, pow_zero, Nat.mul_one,
          value_of_mem_front h.front_len h.front_nodup h.frozen_len hp]
      · have hlt : p.1.length < z.length :=
          lt_of_le_of_ne hpre.length_le (fun he => hzp (hpre.eq_of_length he).symm)
        rw [qHat_vanishes qa p.1 0 _ (by simp only [List.length_drop]; omega), Nat.mul_zero]
        refine (value_eq_zero_of_gt h.front_len h.frozen_len ?_).symm
        rw [← h.front_len p hp]; omega

/-- **A3.8 (`stay_mono`).**  Without a trigger the value only grows, by stage monotonicity
of the sanitized stages. -/
theorem compVal_stay {g : Gen} {qa : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (s : ℕ) (hs : g.start ≤ s) (z : BitString) :
    2 * compVal qa g s z ≤ compVal qa g (s + 1) z := by
  have hstep : s + 1 - g.start = (s - g.start) + 1 := by omega
  cases hf : g.front.find? (fun q => q.1.isPrefixOf z) with
  | none =>
      rw [compVal_of_find_none qa s hf, compVal_of_find_none qa (s + 1) hf, hstep, pow_succ]
      exact le_of_eq (by ring)
  | some p =>
      rw [compVal_of_find_some qa s hf, compVal_of_find_some qa (s + 1) hf, hstep]
      have hstep2 := two_mul_le_of_dyadic
        (qHat_stage_mono hqmono p.1 (s - g.start) (z.drop p.1.length))
      calc 2 * (p.2 * qHat qa p.1 (s - g.start) (z.drop p.1.length))
          = p.2 * (2 * qHat qa p.1 (s - g.start) (z.drop p.1.length)) := by ring
        _ ≤ p.2 * qHat qa p.1 (s - g.start + 1) (z.drop p.1.length) :=
            Nat.mul_le_mul_left _ hstep2
        _ = _ := rfl

/-- **A3.7 (`transition_mono`).**  At a trigger the value only grows: the snapshot is
exactly twice the old numerator and the completion dominates it. -/
theorem compVal_trigger {R : ℕ} {g : Gen} (h : GenInv R g)
    {qa : ℕ → BitString → BitString → ℕ}
    (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
    (s : ℕ) (hs : g.start ≤ s) (z : BitString) :
    2 * compVal qa g s z ≤ compVal qa (transition qa g s) (s + 1) z := by
  have hginv' : GenInv R (transition qa g s) := genInv_transition h hcoh hs
  have hval : compVal qa (transition qa g s) (s + 1) z = (transition qa g s).value z :=
    compVal_at_start hginv' qa z
  rw [hval]
  cases hf : g.front.find? (fun q => q.1.isPrefixOf z) with
  | none =>
      have hnf : ∀ q ∈ g.front, ¬ (q.1 <+: z) := fun q hq hpre =>
        (List.find?_eq_none.mp hf q hq) (List.isPrefixOf_iff_prefix.mpr hpre)
      have hgz : g.value z = (List.lookup z g.frozen).getD 0 :=
        value_of_not_front (fun q hq hk => hnf q hq (hk ▸ List.prefix_refl _))
      rw [compVal_of_find_none qa s hf]
      rcases Nat.lt_or_ge z.length g.level with hlt | hge
      · rw [transition_value_lt_level h hlt, hgz, pow_succ]
        exact le_of_eq (by ring)
      · rw [transition_value_of_no_front h hge hnf]
        have hzero : (List.lookup z g.frozen).getD (0 : ℕ) = 0 :=
          lookup_getD_eq_default _ _ _ (fun q hq hk => by
            have := h.frozen_len q hq; rw [hk] at this; omega)
        rw [hzero]
        simp
  | some p =>
      have hp : p ∈ g.front := List.mem_of_find?_eq_some hf
      have hpre : p.1 <+: z :=
        List.isPrefixOf_iff_prefix.mp (by simpa using List.find?_some hf)
      rw [compVal_of_find_some qa s hf]
      obtain ⟨w, rfl⟩ := hpre
      rw [List.drop_left]
      rcases Nat.lt_or_ge (s - g.start + 1) w.length with hw | hw
      · rw [qHat_vanishes qa p.1 (s - g.start) w (by omega)]
        simp
      · rw [transition_value_front h hp hw]
        calc 2 * (p.2 * qHat qa p.1 (s - g.start) w)
            = 2 * p.2 * qHat qa p.1 (s - g.start) w := by ring
          _ ≤ transFlow qa (s - g.start) p w := transFlow_ge hcoh w

/-- One step of the evolution of component `R` increases the stage numerator by a factor
of at least `2` (i.e. does not decrease the dyadic value). -/
theorem compVal_genAt_succ {qa ma : ℕ → BitString → BitString → ℕ}
    (hcoh : ∀ u t y, qHat qa u t (y ++ [false]) + qHat qa u t (y ++ [true]) ≤ qHat qa u t y)
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (R n : ℕ) (z : BitString) :
    2 * compVal qa (genAt qa ma R n) (R + 1 + n) z
      ≤ compVal qa (genAt qa ma R (n + 1)) (R + 1 + n + 1) z := by
  have hinv := genInv_genAt' qa ma hcoh R n
  have hs := genAt_start_le qa ma R n
  rw [genAt]
  split
  · exact compVal_trigger hinv hcoh (R + 1 + n) hs z
  · exact compVal_stay hqmono (R + 1 + n) hs z
/-! ### The three obligations of `isLowerSemicomputableContinuousSemimeasure_iSup_of_stage` -/

/-- **Root.**  `ν_s([]) = 2^s`.  Difficulty **E**. -/
@[simp] theorem nuStage_root (qa ma : ℕ → BitString → BitString → ℕ) (s : ℕ) :
    nuStage qa ma s [] = 2 ^ s := by
  simp [nuStage, compIdx]

/-- **A3.12 (coherence).**  Each stage numerator is a tree semimeasure.

Proof sketch.  Three regimes.
* Spine `z = 1^j`, `j < s`: children are `1^{j+1}` (value `2^{s-j-1}`) and `p_j` (value
  `2^{s-j-1}` by `GenInv.root`), summing to `2^{s-j}` exactly.  For `j ≥ s` the children
  are `0`.
* Inside a component, above the front: exact flow splits, `flowVal_split`.
* At and below a front vertex: `b_u · qHat` splits by `qHat_coherent`; the value at the
  front vertex equals the budget by `qHat_root`, matching the frozen flow above it.
Difficulty **H**, ~150 lines (the bookkeeping is the bulk of WP3/WP4). -/
theorem nuStage_coherent (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa ma : ℕ → BitString → BitString → ℕ}
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u) (s : ℕ) (x : BitString) :
    nuStage qa ma s (x ++ [false]) + nuStage qa ma s (x ++ [true]) ≤ nuStage qa ma s x := by
  have hcoh := qHat_coh hQ hqsup
  by_cases hx : x.length = compIdx x
  · -- spine vertex `x = 1^j`: the two children split it exactly
    have hT : (x ++ [true]).length = compIdx (x ++ [true]) := full_append_true hx
    have hFeq : x ++ [false] = pLabel x.length := eq_pLabel_of_full hx
    have hFne : (x ++ [false]).length ≠ compIdx (x ++ [false]) := by
      rw [hFeq, pLabel_length, compIdx_pLabel]; omega
    have hFidx : compIdx (x ++ [false]) = x.length := by rw [hFeq, compIdx_pLabel]
    rw [nuStage_spine qa ma s hx, nuStage_spine qa ma s hT, nuStage_comp qa ma s hFne, hFidx]
    simp only [List.length_append, List.length_singleton]
    rcases Nat.lt_or_ge x.length s with hjs | hjs
    · rw [ite_eq_left hjs, ite_eq_left (by omega : x.length + 1 ≤ s),
        ite_eq_left (by omega : x.length ≤ s)]
      have hginv := genInv_genAt' qa ma hcoh x.length (s - x.length - 1)
      have hstart : (genAt qa ma x.length (s - x.length - 1)).start ≤ s := by
        have := genAt_start_le qa ma x.length (s - x.length - 1); omega
      rw [hFeq, hginv.root qa s hstart]
      obtain ⟨k, hk⟩ : ∃ k, s - x.length = k + 1 := ⟨s - x.length - 1, by omega⟩
      have h1 : s - (x.length + 1) = k := by omega
      rw [hk, h1, pow_succ]
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  · -- inside a component: one and the same generation governs `x` and its children
    have hR : compIdx (x ++ [false]) = compIdx x := compIdx_append_of_not_full hx false
    have hR' : compIdx (x ++ [true]) = compIdx x := compIdx_append_of_not_full hx true
    have hle := compIdx_le x
    have hne0 : (x ++ [false]).length ≠ compIdx (x ++ [false]) := by
      rw [hR]; simp only [List.length_append, List.length_singleton]; omega
    have hne1 : (x ++ [true]).length ≠ compIdx (x ++ [true]) := by
      rw [hR']; simp only [List.length_append, List.length_singleton]; omega
    rw [nuStage_comp qa ma s hx, nuStage_comp qa ma s hne0, nuStage_comp qa ma s hne1, hR, hR']
    by_cases hRs : compIdx x < s
    · rw [ite_eq_left hRs, ite_eq_left hRs, ite_eq_left hRs]
      exact compVal_coherent (genInv_genAt' qa ma hcoh _ _) hcoh s (pLabel_prefix hx)
    · simp only [ite_eq_right hRs, Nat.add_zero, le_refl]

/-- **A3.13 + A3.7 + A3.8 (stage monotonicity).**

Proof sketch.  Spine: `2^{-j}` at both stages once `j ≤ s`, and `0 ≤ 2^{-j}` at the
activation stage.  Component `R` at stage `s < R+1`: value `0`.  Otherwise compare
`genAt R n` with `genAt R (n+1)`:
* no trigger — same generation, and `dyadicValue (b · qHat u t y) (start+t)` is
  nondecreasing in `t` by `qHat_stage_mono` (the factor `b/2^{start}` is constant);
* trigger — the new value at a node `z = u ++ w` is `flowVal (snapshot ..) .. w / 2^{s+1}`,
  and `snapshot .. w = 2 · b · qHat u t w` is exactly twice the old numerator, so
  `flowVal_ge` gives the inequality; below relative depth `t+1` the old numerator is `0`
  by `qHat_vanishes`; above the front the frozen values are rescaled exactly.
Difficulty **H**, ~180 lines. -/
theorem nuStage_mono (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa ma : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u) (s : ℕ) (z : BitString) :
    dyadicValue (nuStage qa ma s z) s ≤ dyadicValue (nuStage qa ma (s + 1) z) (s + 1) := by
  have hcoh := qHat_coh hQ hqsup
  refine dyadicValue_le_succ_of_two_mul_le s ?_
  by_cases hz : z.length = compIdx z
  · rw [nuStage_spine qa ma s hz, nuStage_spine qa ma (s + 1) hz]
    rcases Nat.lt_or_ge s z.length with h1 | h1
    · rw [ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left h1, ite_eq_left (by omega : z.length ≤ s + 1),
        show s + 1 - z.length = (s - z.length) + 1 from by omega, pow_succ]
      exact le_of_eq (by ring)
  · rw [nuStage_comp qa ma s hz, nuStage_comp qa ma (s + 1) hz]
    by_cases hR : compIdx z < s
    · obtain ⟨n, rfl⟩ : ∃ n, s = compIdx z + 1 + n := ⟨s - compIdx z - 1, by omega⟩
      rw [ite_eq_left (by omega), ite_eq_left (by omega),
        show compIdx z + 1 + n - compIdx z - 1 = n from by omega,
        show compIdx z + 1 + n + 1 - compIdx z - 1 = n + 1 from by omega]
      exact compVal_genAt_succ hcoh hqmono (compIdx z) n z
    · rw [ite_eq_right hR]
      simp

/-! ### Effectivity toolkit for `nuStage` (WP5)

Everything between here and `nuStage_computable` is bookkeeping: a `Primcodable`
structure for `Gen`, primitive-recursive reformulations of the list utilities
(`binStrings`, `flowVal`, `List.find?`, `List.all`) and the `Computable`
combinators these need. -/

section Effectivity

/-- `Gen` as a product. -/
def Gen.toProd (g : Gen) : ℕ × ℕ × List (BitString × ℕ) × List (BitString × ℕ) :=
  (g.start, g.level, g.front, g.frozen)

/-- A product as a `Gen`. -/
def Gen.ofProd (p : ℕ × ℕ × List (BitString × ℕ) × List (BitString × ℕ)) : Gen :=
  { start := p.1, level := p.2.1, front := p.2.2.1, frozen := p.2.2.2 }

/-- `Gen` is equivalent to a product of `ℕ`s and lists. -/
def genEquiv : Gen ≃ (ℕ × ℕ × List (BitString × ℕ) × List (BitString × ℕ)) where
  toFun := Gen.toProd
  invFun := Gen.ofProd
  left_inv g := by cases g; rfl
  right_inv p := by rcases p with ⟨a, b, c, d⟩; rfl

instance genPrimcodable : Primcodable Gen := Primcodable.ofEquiv _ genEquiv

private theorem primrec_genToProd : Primrec Gen.toProd := Primrec.of_equiv

private theorem primrec_genOfProd : Primrec Gen.ofProd := Primrec.of_equiv_symm

private theorem primrec_gen_start : Primrec Gen.start :=
  Primrec.fst.comp primrec_genToProd
private theorem primrec_gen_level : Primrec Gen.level :=
  (Primrec.fst.comp Primrec.snd).comp primrec_genToProd
private theorem primrec_gen_front : Primrec Gen.front :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp primrec_genToProd
private theorem primrec_gen_frozen : Primrec Gen.frozen :=
  (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp primrec_genToProd

private theorem initGen_eq (R : ℕ) :
    initGen R = Gen.ofProd (R + 1, R + 1, [(pLabel R, 1)], []) := rfl

private theorem transition_eq (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ) :
    transition qa g s = Gen.ofProd
      (s + 1, g.level + (s - g.start) + 1,
        g.front.flatMap (fun p =>
          (binStrings (s - g.start + 1)).filterMap (fun w =>
            if flowVal (snapshot qa p.1 p.2 (s - g.start))
                (p.2 * 2 ^ ((s - g.start) + 1)) w = 0 then none
              else some (p.1 ++ w,
                flowVal (snapshot qa p.1 p.2 (s - g.start))
                  (p.2 * 2 ^ ((s - g.start) + 1)) w))),
        g.frozen.map (fun p => (p.1, p.2 * 2 ^ ((s - g.start) + 1))) ++
          g.front.flatMap (fun p =>
            (binStringsUpTo (s - g.start)).map (fun w =>
              (p.1 ++ w,
                flowVal (snapshot qa p.1 p.2 (s - g.start))
                  (p.2 * 2 ^ ((s - g.start) + 1)) w)))) := rfl

attribute [local irreducible] genPrimcodable genEquiv Gen.toProd Gen.ofProd initGen transition

/-! #### Generic `Computable` list combinators -/

private theorem computable_list_flatMap {α β σ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable σ] {f : α → List β} {g : α → β → List σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) :=
  (Primrec.list_flatten.to_comp.comp (Computable.list_map hf hg)).of_eq
    (fun _ => (List.flatMap_def).symm)

private theorem computable_listFilterMap {α β σ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable σ] {f : α → List β} {g : α → β → Option σ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).filterMap (g a)) :=
  have hg' : Computable₂ (fun (a : α) (b : β) => (g a b).toList) :=
    Primrec.optionToList.to_comp.comp hg
  (computable_list_flatMap hf hg').of_eq
    (fun _ => (List.filterMap_eq_flatMap_toList _ _).symm)

/-! #### `binStrings` -/

private theorem binStrings_rec (d : ℕ) :
    binStrings d = Nat.rec (motive := fun _ => List BitString) [[]]
      (fun _ ih => ih.flatMap (fun w => [w ++ [false], w ++ [true]])) d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [binStrings, ih]

private theorem primrec_binStrings : Primrec binStrings := by
  have hg : Primrec₂ (fun (_ : ℕ × (ℕ × List BitString)) (w : BitString) =>
      [w ++ [false], w ++ [true]]) := by
    have h0 : Primrec (fun q : (ℕ × (ℕ × List BitString)) × BitString => q.2 ++ [false]) :=
      Primrec.list_append.comp Primrec.snd (Primrec.const [false])
    have h1 : Primrec (fun q : (ℕ × (ℕ × List BitString)) × BitString => q.2 ++ [true]) :=
      Primrec.list_append.comp Primrec.snd (Primrec.const [true])
    exact Primrec.list_cons.comp h0 (Primrec.list_cons.comp h1 (Primrec.const []))
  have hstep : Primrec₂ (fun (_ : ℕ) (q : ℕ × List BitString) =>
      q.2.flatMap (fun w => [w ++ [false], w ++ [true]])) :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) hg
  have h := Primrec.nat_rec' (Primrec.id (α := ℕ)) (Primrec.const [([] : BitString)]) hstep
  exact h.of_eq (fun d => (binStrings_rec d).symm)

private theorem primrec_binStringsUpTo : Primrec binStringsUpTo := by
  have hg : Primrec₂ (fun (_ : ℕ) (d : ℕ) => binStrings d) :=
    primrec_binStrings.comp Primrec.snd
  exact (Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ) hg).of_eq (fun _ => rfl)

attribute [local irreducible] binStrings binStringsUpTo

/-! #### `pLabel` and `compIdx` -/

private theorem primrec_pLabel : Primrec pLabel :=
  Primrec.list_append.comp
    (Primrec.list_replicate.comp Primrec.id (Primrec.const true)) (Primrec.const [false])

private theorem primrec_compIdx : Primrec compIdx :=
  Primrec.list_length.comp (Primrec.list_takeWhile (p := (id : Bool → Bool)) Primrec.id)

attribute [local irreducible] pLabel compIdx

/-! #### `flowVal` as a left fold -/

private theorem flowVal_foldl (A : BitString → ℕ) (q0 : ℕ) (w : BitString) :
    w.foldl (fun (st : BitString × ℕ) (c : Bool) =>
        (st.1 ++ [c], bif c then A (st.1 ++ [true]) else st.2 - A (st.1 ++ [true])))
      (([] : BitString), q0) = (w, flowVal A q0 w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w c ih =>
      rw [List.foldl_append, ih]
      cases c <;> simp

attribute [local irreducible] flowVal flowValR

private theorem snapshot_eq (qa : ℕ → BitString → BitString → ℕ) (u : BitString) (b t : ℕ)
    (w : BitString) : snapshot qa u b t w = 2 * b * qHat qa u t w := rfl

attribute [local irreducible] snapshot

/-! #### `List.find?` and `List.all` reformulations -/

private theorem list_find?_eq_head?_filter {α : Type*} (p : α → Bool) (l : List α) :
    l.find? p = (l.filter p).head? := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : p a = true
      · rw [List.find?_cons_of_pos h, List.filter_cons_of_pos h, List.head?_cons]
      · rw [List.find?_cons_of_neg h, List.filter_cons_of_neg h, ih]

private theorem list_all_foldr {α : Type*} (p : α → Bool) (l : List α) :
    l.all p = l.foldr (fun a acc => p a && acc) true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

private theorem lookup_eq_head?_filter (z : BitString) (l : List (BitString × ℕ)) :
    List.lookup z l = ((l.filter (fun p => decide (p.1 = z))).head?).map Prod.snd := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨k, b⟩ := a
      cases hb : (z == k) with
      | true =>
          have hk : z = k := eq_of_beq hb
          subst hk
          simp [List.lookup]
      | false =>
          have hk : ¬ k = z := by
            intro h; subst h; simp at hb
          simp [List.lookup, hb, hk, ih]

/-! #### `List.isPrefixOf` -/

private theorem isPrefixOf_eq_decide (u z : BitString) :
    u.isPrefixOf z = decide (z.take u.length = u) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  exact eq_comm

private theorem primrec_isPrefixOf : Primrec₂ (fun (u z : BitString) => u.isPrefixOf z) := by
  have h : Primrec (fun q : BitString × BitString => decide (q.2.take q.1.length = q.1)) :=
    (PrimrecRel.decide (Primrec.eq (α := BitString))).comp
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd) Primrec.fst
  exact h.of_eq (fun q => (isPrefixOf_eq_decide q.1 q.2).symm)

/-! #### The computable pieces of the construction -/

section Pieces

variable {qa ma : ℕ → BitString → BitString → ℕ}

attribute [local irreducible] qHat

/-- The exact flow completing a snapshot, computable in all of its parameters. -/
private theorem computable_flowSnap
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : (BitString × ℕ × ℕ) × BitString =>
      flowVal (snapshot qa a.1.1 a.1.2.1 a.1.2.2) (a.1.2.1 * 2 ^ (a.1.2.2 + 1)) a.2) := by
  have hqh : Computable (fun p : ℕ × BitString × BitString => qHat qa p.2.2 p.1 p.2.1) :=
    qHat_computable hq
  -- the fold step
  have hu : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.1.1.1) := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hb : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.1.1.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ht : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.1.1.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hst1 : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.2.1.1) := Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hst2 : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.2.1.2) := Computable.snd.comp (Computable.fst.comp Computable.snd)
  have hbit : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      q.2.2) := Computable.snd.comp Computable.snd
  have hA : Computable (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
      snapshot qa q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2.1.1 ++ [true])) := by
    have hw : Computable
        (fun q : ((BitString × ℕ × ℕ) × BitString) × ((BitString × ℕ) × Bool) =>
          q.2.1.1 ++ [true]) :=
      Computable.list_append.comp hst1 (Computable.const [true])
    exact (Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) hb)
      (hqh.comp (Computable.pair ht (Computable.pair hw hu)))).of_eq
      (fun q => (snapshot_eq qa q.1.1.1 q.1.1.2.1 q.1.1.2.2 (q.2.1.1 ++ [true])).symm)
  have hh : Computable₂ (fun (a : (BitString × ℕ × ℕ) × BitString)
      (p : (BitString × ℕ) × Bool) =>
        (p.1.1 ++ [p.2], bif p.2 then snapshot qa a.1.1 a.1.2.1 a.1.2.2 (p.1.1 ++ [true])
          else p.1.2 - snapshot qa a.1.1 a.1.2.1 a.1.2.2 (p.1.1 ++ [true]))) :=
    Computable.pair
      (Computable.list_append.comp hst1 (Primrec.list_cons.to_comp.comp hbit (Computable.const [])))
      (Computable.cond hbit hA (Primrec.nat_sub.to_comp.comp hst2 hA))
  have hg : Computable (fun a : (BitString × ℕ × ℕ) × BitString =>
      (([] : BitString), a.1.2.1 * 2 ^ (a.1.2.2 + 1))) :=
    Computable.pair (Computable.const [])
      (Primrec.nat_mul.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (primrec_two_pow_aux.to_comp.comp
          (Computable.succ.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
  have hfold : Computable (fun a : (BitString × ℕ × ℕ) × BitString =>
      a.2.foldl (fun (st : BitString × ℕ) (c : Bool) =>
          (st.1 ++ [c], bif c then snapshot qa a.1.1 a.1.2.1 a.1.2.2 (st.1 ++ [true])
            else st.2 - snapshot qa a.1.1 a.1.2.1 a.1.2.2 (st.1 ++ [true])))
        (([] : BitString), a.1.2.1 * 2 ^ (a.1.2.2 + 1))) :=
    (Computable.list_foldl Computable.snd hg hh).of_eq fun _ => rfl
  exact (Computable.snd.comp hfold).of_eq (fun a => by rw [flowVal_foldl])

/-- `compVal` rewritten with `Option.casesOn` over `head? ∘ filter`. -/
private theorem compVal_eq (qa : ℕ → BitString → BitString → ℕ) (g : Gen) (s : ℕ)
    (z : BitString) :
    compVal qa g s z =
      Option.casesOn ((g.front.filter (fun p => p.1.isPrefixOf z)).head?)
        ((List.lookup z g.frozen).getD 0 * 2 ^ (s - g.start))
        (fun p => p.2 * qHat qa p.1 (s - g.start) (z.drop p.1.length)) := by
  rw [compVal, list_find?_eq_head?_filter]
  generalize (g.front.filter (fun p => p.1.isPrefixOf z)).head? = o
  cases o <;> rfl

attribute [local irreducible] compVal

private theorem computable_compVal
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : Gen × ℕ × BitString => compVal qa a.1 a.2.1 a.2.2) := by
  have hqh : Computable (fun p : ℕ × BitString × BitString => qHat qa p.2.2 p.1 p.2.1) :=
    qHat_computable hq
  have hz : Primrec (fun a : Gen × ℕ × BitString => a.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec (fun a : Gen × ℕ × BitString => a.2.1) := Primrec.fst.comp Primrec.snd
  have hstart : Primrec (fun a : Gen × ℕ × BitString => a.1.start) :=
    primrec_gen_start.comp Primrec.fst
  have ht : Primrec (fun a : Gen × ℕ × BitString => a.2.1 - a.1.start) :=
    Primrec.nat_sub.comp hs hstart
  have hfilter : Primrec (fun a : Gen × ℕ × BitString =>
      a.1.front.filter (fun p => p.1.isPrefixOf a.2.2)) :=
    Primrec.list_filter (primrec_gen_front.comp Primrec.fst)
      (primrec_isPrefixOf.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hhead : Computable (fun a : Gen × ℕ × BitString =>
      (a.1.front.filter (fun p => p.1.isPrefixOf a.2.2)).head?) :=
    (Primrec.list_head?.comp hfilter).to_comp
  have hlookup : Primrec (fun a : Gen × ℕ × BitString => List.lookup a.2.2 a.1.frozen) := by
    have hf : Primrec (fun a : Gen × ℕ × BitString =>
        a.1.frozen.filter (fun p => decide (p.1 = a.2.2))) :=
      Primrec.list_filter (primrec_gen_frozen.comp Primrec.fst)
        ((PrimrecRel.decide (Primrec.eq (α := BitString))).comp
          (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact (Primrec.option_map (Primrec.list_head?.comp hf)
      (Primrec.snd.comp Primrec.snd).to₂).of_eq
      (fun a => (lookup_eq_head?_filter a.2.2 a.1.frozen).symm)
  have hnone : Computable (fun a : Gen × ℕ × BitString =>
      (List.lookup a.2.2 a.1.frozen).getD 0 * 2 ^ (a.2.1 - a.1.start)) :=
    Primrec.nat_mul.to_comp.comp
      (Computable.option_getD hlookup.to_comp (Computable.const 0))
      (primrec_two_pow_aux.to_comp.comp ht.to_comp)
  have hsome : Computable₂ (fun (a : Gen × ℕ × BitString) (p : BitString × ℕ) =>
      p.2 * qHat qa p.1 (a.2.1 - a.1.start) (a.2.2.drop p.1.length)) := by
    have hp1 : Computable (fun q : (Gen × ℕ × BitString) × (BitString × ℕ) => q.2.1) :=
      Computable.fst.comp Computable.snd
    have hp2 : Computable (fun q : (Gen × ℕ × BitString) × (BitString × ℕ) => q.2.2) :=
      Computable.snd.comp Computable.snd
    have hdrop : Computable (fun q : (Gen × ℕ × BitString) × (BitString × ℕ) =>
        q.1.2.2.drop q.2.1.length) :=
      Primrec.list_drop.to_comp.comp (Computable.list_length.comp hp1)
        (hz.to_comp.comp Computable.fst)
    exact Primrec.nat_mul.to_comp.comp hp2
      (hqh.comp (Computable.pair (ht.to_comp.comp Computable.fst)
        (Computable.pair hdrop hp1)))
  exact (Computable.option_casesOn hhead hnone hsome).of_eq
    (fun a => (compVal_eq qa a.1 a.2.1 a.2.2).symm)

private theorem computable_trig
    (hm : Computable (fun p : ℕ × BitString × BitString => ma p.1 p.2.1 p.2.2)) :
    Computable (fun a : ℕ × Gen × ℕ => trig ma a.1 a.2.1 a.2.2) := by
  have hfront : Computable (fun a : ℕ × Gen × ℕ => a.2.1.front) :=
    (primrec_gen_front.comp (Primrec.fst.comp Primrec.snd)).to_comp
  have hh : Computable₂ (fun (a : ℕ × Gen × ℕ) (q : (BitString × ℕ) × Bool) =>
      decide (q.1.2 * 2 ^ (a.2.2 - a.2.1.start) < ma a.2.2 q.1.1 [] * (a.1 + 1)) && q.2) := by
    have hR : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) => w.1.1) :=
      Computable.fst.comp Computable.fst
    have hs : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) => w.1.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have hstart : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) =>
        w.1.2.1.start) :=
      (primrec_gen_start.comp (Primrec.fst.comp Primrec.snd)).to_comp.comp Computable.fst
    have hp1 : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) => w.2.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.snd)
    have hp2 : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) => w.2.1.2) :=
      Computable.snd.comp (Computable.fst.comp Computable.snd)
    have hacc : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) => w.2.2) :=
      Computable.snd.comp Computable.snd
    have hlhs : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) =>
        w.2.1.2 * 2 ^ (w.1.2.2 - w.1.2.1.start)) :=
      Primrec.nat_mul.to_comp.comp hp2
        (primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp hs hstart))
    have hrhs : Computable (fun w : (ℕ × Gen × ℕ) × ((BitString × ℕ) × Bool) =>
        ma w.1.2.2 w.2.1.1 [] * (w.1.1 + 1)) :=
      Primrec.nat_mul.to_comp.comp
        (hm.comp (Computable.pair hs (Computable.pair hp1 (Computable.const []))))
        (Computable.succ.comp hR)
    exact (Primrec.dom_bool₂ (fun b c : Bool => b && c)).to_comp.comp
      ((PrimrecRel.decide Primrec.nat_lt).to_comp.comp hlhs hrhs) hacc
  have hfold := Computable.list_foldr hfront (Computable.const true) hh
  exact hfold.of_eq (fun a => by rw [trig, list_all_foldr])

attribute [local irreducible] trig

private def transDepth (a : Gen × ℕ) : ℕ := a.2 - a.1.start

private theorem computable_transDepth : Computable transDepth :=
  (Primrec.nat_sub.comp Primrec.snd (primrec_gen_start.comp Primrec.fst)).to_comp

private theorem computable_flowPair
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString =>
      (r.1.2.1 ++ r.2,
        flowVal (snapshot qa r.1.2.1 r.1.2.2 (r.1.1.2 - r.1.1.1.start))
          (r.1.2.2 * 2 ^ ((r.1.1.2 - r.1.1.1.start) + 1)) r.2)) := by
  have hflow := computable_flowSnap (qa := qa) hq
  have huA : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString => r.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hbA : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString => r.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have htA : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString =>
      r.1.1.2 - r.1.1.1.start) :=
    (computable_transDepth.comp (Computable.fst.comp Computable.fst)).of_eq (fun _ => rfl)
  have hvA : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString =>
      flowVal (snapshot qa r.1.2.1 r.1.2.2 (r.1.1.2 - r.1.1.1.start))
        (r.1.2.2 * 2 ^ ((r.1.1.2 - r.1.1.1.start) + 1)) r.2) :=
    hflow.comp (Computable.pair (Computable.pair huA (Computable.pair hbA htA)) Computable.snd)
  exact Computable.pair (Computable.list_append.comp huA Computable.snd) hvA

private theorem computable_transFront
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : Gen × ℕ =>
      a.1.front.flatMap (fun p =>
        (binStrings (a.2 - a.1.start + 1)).filterMap (fun w =>
          if flowVal (snapshot qa p.1 p.2 (a.2 - a.1.start))
              (p.2 * 2 ^ ((a.2 - a.1.start) + 1)) w = 0 then none
            else some (p.1 ++ w,
              flowVal (snapshot qa p.1 p.2 (a.2 - a.1.start))
                (p.2 * 2 ^ ((a.2 - a.1.start) + 1)) w)))) := by
  have hpairA := computable_flowPair (qa := qa) hq
  have hvA : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString =>
      flowVal (snapshot qa r.1.2.1 r.1.2.2 (r.1.1.2 - r.1.1.1.start))
        (r.1.2.2 * 2 ^ ((r.1.1.2 - r.1.1.1.start) + 1)) r.2) :=
    Computable.snd.comp hpairA
  have htQ : Computable (fun q : (Gen × ℕ) × (BitString × ℕ) => q.1.2 - q.1.1.start) :=
    (computable_transDepth.comp Computable.fst).of_eq (fun _ => rfl)
  have hfront : Computable (fun a : Gen × ℕ => a.1.front) :=
    (primrec_gen_front.comp Primrec.fst).to_comp
  have hinner : Computable₂ (fun (q : (Gen × ℕ) × (BitString × ℕ)) (w : BitString) =>
      if flowVal (snapshot qa q.2.1 q.2.2 (q.1.2 - q.1.1.start))
          (q.2.2 * 2 ^ ((q.1.2 - q.1.1.start) + 1)) w = 0 then none
        else some (q.2.1 ++ w,
          flowVal (snapshot qa q.2.1 q.2.2 (q.1.2 - q.1.1.start))
            (q.2.2 * 2 ^ ((q.1.2 - q.1.1.start) + 1)) w)) := by
    have hzero : Computable (fun r : ((Gen × ℕ) × (BitString × ℕ)) × BitString =>
        decide (flowVal (snapshot qa r.1.2.1 r.1.2.2 (r.1.1.2 - r.1.1.1.start))
          (r.1.2.2 * 2 ^ ((r.1.1.2 - r.1.1.1.start) + 1)) r.2 = 0)) :=
      (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp hvA (Computable.const 0)
    exact (Computable.cond hzero (Computable.const none)
      (Primrec.option_some.to_comp.comp hpairA)).of_eq (fun _ => by simp only [Bool.cond_decide])
  exact computable_list_flatMap hfront
    (computable_listFilterMap
      (primrec_binStrings.to_comp.comp (Computable.succ.comp htQ)) hinner)

private theorem computable_transFrozen
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : Gen × ℕ =>
      a.1.frozen.map (fun p => (p.1, p.2 * 2 ^ ((a.2 - a.1.start) + 1))) ++
        a.1.front.flatMap (fun p =>
          (binStringsUpTo (a.2 - a.1.start)).map (fun w =>
            (p.1 ++ w,
              flowVal (snapshot qa p.1 p.2 (a.2 - a.1.start))
                (p.2 * 2 ^ ((a.2 - a.1.start) + 1)) w)))) := by
  have hpairA := computable_flowPair (qa := qa) hq
  have htQ : Computable (fun q : (Gen × ℕ) × (BitString × ℕ) => q.1.2 - q.1.1.start) :=
    (computable_transDepth.comp Computable.fst).of_eq (fun _ => rfl)
  have hfront : Computable (fun a : Gen × ℕ => a.1.front) :=
    (primrec_gen_front.comp Primrec.fst).to_comp
  have hfrozen : Computable (fun a : Gen × ℕ => a.1.frozen) :=
    (primrec_gen_frozen.comp Primrec.fst).to_comp
  have hrescale : Computable (fun a : Gen × ℕ =>
      a.1.frozen.map (fun p => (p.1, p.2 * 2 ^ ((a.2 - a.1.start) + 1)))) :=
    Computable.list_map hfrozen
      (Computable.pair (Computable.fst.comp Computable.snd)
        (Primrec.nat_mul.to_comp.comp (Computable.snd.comp Computable.snd)
          (primrec_two_pow_aux.to_comp.comp (Computable.succ.comp htQ))))
  have hnewFrozen : Computable (fun a : Gen × ℕ =>
      a.1.front.flatMap (fun p =>
        (binStringsUpTo (a.2 - a.1.start)).map (fun w =>
          (p.1 ++ w,
            flowVal (snapshot qa p.1 p.2 (a.2 - a.1.start))
              (p.2 * 2 ^ ((a.2 - a.1.start) + 1)) w)))) :=
    computable_list_flatMap hfront
      (Computable.list_map (primrec_binStringsUpTo.to_comp.comp htQ) hpairA)
  exact Computable.list_append.comp hrescale hnewFrozen

private theorem computable_transition
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2)) :
    Computable (fun a : Gen × ℕ => transition qa a.1 a.2) := by
  have hstart : Computable (fun a : Gen × ℕ => a.1.start) :=
    (primrec_gen_start.comp Primrec.fst).to_comp
  have hlevel : Computable (fun a : Gen × ℕ => a.1.level) :=
    (primrec_gen_level.comp Primrec.fst).to_comp
  have hsub : Computable (fun a : Gen × ℕ => a.2 - a.1.start) :=
    Primrec.nat_sub.to_comp.comp Computable.snd hstart
  have hres := primrec_genOfProd.to_comp.comp
    (Computable.pair (Computable.succ.comp (Computable.snd (α := Gen) (β := ℕ)))
      (Computable.pair
        (Computable.succ.comp (Primrec.nat_add.to_comp.comp hlevel hsub))
        (Computable.pair (computable_transFront (qa := qa) hq)
          (computable_transFrozen (qa := qa) hq))))
  exact hres.of_eq (fun a => (transition_eq qa a.1 a.2).symm)

private theorem computable_initGen : Computable initGen :=
  (primrec_genOfProd.comp
    (Primrec.pair Primrec.succ
      (Primrec.pair Primrec.succ
        (Primrec.pair
          (Primrec.list_cons.comp (Primrec.pair primrec_pLabel (Primrec.const 1))
            (Primrec.const []))
          (Primrec.const []))))).to_comp.of_eq (fun R => (initGen_eq R).symm)

private theorem genAt_rec (qa ma : ℕ → BitString → BitString → ℕ) (R n : ℕ) :
    genAt qa ma R n = Nat.rec (motive := fun _ => Gen) (initGen R)
      (fun k ih => if trig ma R ih (R + 1 + k) then transition qa ih (R + 1 + k) else ih) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [genAt, ih]

attribute [local irreducible] genAt

private theorem computable_genAt
    (hq : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2))
    (hm : Computable (fun p : ℕ × BitString × BitString => ma p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × ℕ => genAt qa ma p.1 p.2) := by
  have hbase : Computable (fun p : ℕ × ℕ => initGen p.1) :=
    computable_initGen.comp Computable.fst
  have hstep : Computable₂ (fun (p : ℕ × ℕ) (q : ℕ × Gen) =>
      if trig ma p.1 q.2 (p.1 + 1 + q.1) then transition qa q.2 (p.1 + 1 + q.1) else q.2) := by
    have hR : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) => w.1.1) :=
      Computable.fst.comp Computable.fst
    have hk : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) => w.2.1) :=
      Computable.fst.comp Computable.snd
    have hgen : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) => w.2.2) :=
      Computable.snd.comp Computable.snd
    have hs : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) => w.1.1 + 1 + w.2.1) :=
      Primrec.nat_add.to_comp.comp (Computable.succ.comp hR) hk
    have htr : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) =>
        trig ma w.1.1 w.2.2 (w.1.1 + 1 + w.2.1)) :=
      (computable_trig hm).comp (Computable.pair hR (Computable.pair hgen hs))
    have hts : Computable (fun w : (ℕ × ℕ) × (ℕ × Gen) =>
        transition qa w.2.2 (w.1.1 + 1 + w.2.1)) :=
      (computable_transition hq).comp (Computable.pair hgen hs)
    exact (Computable.cond htr hts hgen).of_eq (fun w => by
      cases h : trig ma w.1.1 w.2.2 (w.1.1 + 1 + w.2.1) <;> simp [h])
  exact (Computable.nat_rec Computable.snd hbase hstep).of_eq
    (fun p => (genAt_rec qa ma p.1 p.2).symm)

private theorem nuStage_eq_cond (s : ℕ) (z : BitString) :
    nuStage qa ma s z =
      cond (decide (z.length = compIdx z))
        (cond (decide (z.length ≤ s)) (2 ^ (s - z.length)) 0)
        (cond (decide (compIdx z < s))
          (compVal qa (genAt qa ma (compIdx z) (s - compIdx z - 1)) s z) 0) := by
  simp only [Bool.cond_decide, nuStage]

end Pieces

end Effectivity

-- Without these local attributes the `Computable` combinators below unfold the definitions
-- of the construction while unifying, which exhausts the default heartbeat budget.
attribute [local irreducible] genPrimcodable genEquiv Gen.toProd Gen.ofProd initGen transition
  binStrings binStringsUpTo pLabel compIdx flowVal flowValR snapshot qHat compVal trig genAt in
/-- **A3.15 (effectivity).**  The stage function is computable.

Proof sketch (blueprint B3, template `GacsDayRequestFamily`).  `Gen` is `Primcodable`
(a product of `ℕ`, `ℕ` and two `List (BitString × ℕ)`); `binStrings`, `binStringsUpTo`,
`flowVal`, `snapshot`, `compVal`, `trig` and `transition` are `Primrec`/`Computable`
compositions of `Primrec.list_*`, `Primrec.nat_*` and `qHat_computable`; `genAt` is
`Computable.nat_rec` over `n` with that step; `nuStage` is a `Computable.cond` of decidable
integer tests.  Difficulty **H** (dominant risk, WP5), ~600 lines. -/
theorem nuStage_computable {qa ma : ℕ → BitString → BitString → ℕ}
    (hqcomp : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2))
    (hmcomp : Computable (fun p : ℕ × BitString × BitString => ma p.1 p.2.1 p.2.2)) :
    Computable (fun p : ℕ × BitString => nuStage qa ma p.1 p.2) := by
  have hci : Computable (fun p : ℕ × BitString => compIdx p.2) :=
    primrec_compIdx.to_comp.comp Computable.snd
  have hlen : Computable (fun p : ℕ × BitString => p.2.length) :=
    Computable.list_length.comp Computable.snd
  have hgen : Computable (fun p : ℕ × BitString =>
      genAt qa ma (compIdx p.2) (p.1 - compIdx p.2 - 1)) :=
    (computable_genAt hqcomp hmcomp).comp (Computable.pair hci
      (Primrec.nat_sub.to_comp.comp
        (Primrec.nat_sub.to_comp.comp Computable.fst hci) (Computable.const 1)))
  have hcv : Computable (fun p : ℕ × BitString =>
      compVal qa (genAt qa ma (compIdx p.2) (p.1 - compIdx p.2 - 1)) p.1 p.2) :=
    (computable_compVal hqcomp).comp
      (Computable.pair hgen (Computable.pair Computable.fst Computable.snd))
  have hc1 : Computable (fun p : ℕ × BitString => decide (p.2.length = compIdx p.2)) :=
    (PrimrecRel.decide (Primrec.eq (α := ℕ))).to_comp.comp hlen hci
  have hc2 : Computable (fun p : ℕ × BitString => decide (p.2.length ≤ p.1)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hlen Computable.fst
  have hc3 : Computable (fun p : ℕ × BitString => decide (compIdx p.2 < p.1)) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp.comp hci Computable.fst
  have hpow : Computable (fun p : ℕ × BitString => 2 ^ (p.1 - p.2.length)) :=
    primrec_two_pow_aux.to_comp.comp (Primrec.nat_sub.to_comp.comp Computable.fst hlen)
  exact (Computable.cond hc1 (Computable.cond hc2 hpow (Computable.const 0))
    (Computable.cond hc3 hcv (Computable.const 0))).of_eq
    (fun p => (nuStage_eq_cond (qa := qa) (ma := ma) p.1 p.2).symm)

/-- **A3.14 + A3.15.**  `ν` is a lower semicomputable continuous semimeasure. -/
theorem nu_isLowerSemicomputableContinuousSemimeasure
    (hQ : IsConditionalContinuousTreeSemimeasure Q)
    {qa ma : ℕ → BitString → BitString → ℕ}
    (hqmono : ∀ s y u, dyadicValue (qa s y u) s ≤ dyadicValue (qa (s + 1) y u) (s + 1))
    (hqsup : ∀ y u, ⨆ s, dyadicValue (qa s y u) s = Q y u)
    (hqcomp : Computable (fun p : ℕ × BitString × BitString => qa p.1 p.2.1 p.2.2))
    (hmcomp : Computable (fun p : ℕ × BitString × BitString => ma p.1 p.2.1 p.2.2)) :
    IsLowerSemicomputableContinuousSemimeasure (nu qa ma) :=
  isLowerSemicomputableContinuousSemimeasure_iSup_of_stage
    (nuStage_root qa ma) (nuStage_coherent hQ hqsup)
    (nuStage_mono hQ hqmono hqsup) (nuStage_computable hqcomp hmcomp)

end Shen
end Kolmogorov
