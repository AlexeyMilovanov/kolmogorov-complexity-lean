import KolmogorovMathlib.StoppingComplexity.Words
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.MonotoneComplexity.REClosure

/-!
# Operational randomized stopping machines

Blueprint 03 §2 and F4 of the stopping-complexity blueprint. A stopping machine is a
*controller*: a partial recursive function `R : BitString × BitString →. StopAction` returning
the next request (read an input bit, read a random bit, halt) after the machine has consumed
exactly the input prefix `x` and the random prefix `q`; `Part.none` is an internal computation
that never makes another request. `Reaches R z p x q` is the chain of consumed pairs of the run
on finite buffers `(z, p)`, and `Witness R z p` is a halting run with exact consumption.

The module states the replay lemma M2, the incompatibility lemma M3 with its two corollaries,
the computable enumeration `stoppingMachine e` of all controllers (via `Nat.Partrec.Code`), the
bounded simulation `witnessWithin` and the finite witness enumeration M1.
-/

namespace Kolmogorov

/-- The request a stopping controller makes after finishing an internal computation: read one
input bit, read one random bit, or halt. Blueprint 03 §2 (03-2-DEF-ACTION). -/
inductive StopAction where
  | readInput
  | readRandom
  | halt
  deriving DecidableEq, Repr

/-- The three stop actions in bijection with `Fin 3` (used for the `Primcodable` instance).
Blueprint 03 §2 (03-2-DEF-ACTION). -/
def StopAction.equivFin : StopAction ≃ Fin 3 where
  toFun a := match a with
    | .readInput => 0
    | .readRandom => 1
    | .halt => 2
  invFun i := if i = 0 then .readInput else if i = 1 then .readRandom else .halt
  left_inv a := by cases a <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Stop actions are primitively codable, through `StopAction.equivFin`.
Blueprint 03 §2 (03-2-DEF-ACTION). -/
instance : Primcodable StopAction := Primcodable.ofEquiv (Fin 3) StopAction.equivFin

/-- An operational randomized stopping machine, indexed by its consumed input/random prefixes:
`R (x, q)` is the next action after consuming exactly `x` and `q`; `Part.none` is an internal
computation that never makes another request. The consumed pair plays the role of the
controller's state (deviation 03-2-DEF-ACTION). Blueprint 03 §2 (03-2-DEF-ACTION). -/
abbrev StoppingController := BitString × BitString →. StopAction

/-- The run of `R` on the finite buffers `(z, p)` passes through the consumed pair `(x, q)`:
the chain starts at `([], [])`, and each step extends the tape the current action asked for by
the next bit of `z` or `p`. A request past the end of a buffer is not a step.
Blueprint 03 §2 (03-2-DEF-REACHES). -/
inductive Reaches (R : StoppingController) (z p : BitString) : BitString → BitString → Prop
  | nil : Reaches R z p [] []
  | readInput {x q : BitString} (h : Reaches R z p x q) (hx : x.length < z.length)
      (ha : StopAction.readInput ∈ R (x, q)) : Reaches R z p (x ++ [z[x.length]'hx]) q
  | readRandom {x q : BitString} (h : Reaches R z p x q) (hq : q.length < p.length)
      (ha : StopAction.readRandom ∈ R (x, q)) : Reaches R z p x (q ++ [p[q.length]'hq])

/-- `Witness R z p`: the machine halts after consuming exactly the input `z` and exactly the
random prefix `p` (it cannot read an extra bit and pretend to have stopped earlier).
Blueprint 03 §2 and F4 (03-2-DEF-WITNESS). -/
def Witness (R : StoppingController) (z p : BitString) : Prop :=
  Reaches R z p z p ∧ StopAction.halt ∈ R (z, p)

/-- Extending a prefix `x` of a buffer `z` by the next bit of `z` gives a prefix of `z`.
Blueprint 03 Lemma M2 (03-M2). -/
private theorem append_getElem_prefix {x z : BitString} (h : x <+: z)
    (hx : x.length < z.length) : x ++ [z[x.length]'hx] <+: z := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hx
  | cons b t => simp

/-- Every reached consumed pair consists of prefixes of the buffers.
Blueprint 03 Lemma M2 (03-M2). -/
theorem Reaches.prefix {R : StoppingController} {z p x q : BitString}
    (h : Reaches R z p x q) : x <+: z ∧ q <+: p := by
  induction h with
  | nil => exact ⟨List.nil_prefix, List.nil_prefix⟩
  | readInput _ hx _ ih => exact ⟨append_getElem_prefix ih.1 hx, ih.2⟩
  | readRandom _ hq _ ih => exact ⟨ih.1, append_getElem_prefix ih.2 hq⟩

/-- Replay on extensions: a consumed pair reached on the buffers `(z, p)` is reached on every
pair of longer buffers `(z', p')` extending them. Blueprint 03 Lemma M2 (03-M2). -/
theorem Reaches.mono {R : StoppingController} {z p z' p' x q : BitString}
    (h : Reaches R z p x q) (hz : z <+: z') (hp : p <+: p') : Reaches R z' p' x q := by
  induction h with
  | nil => exact .nil
  | @readInput x q _ hx ha ih =>
    have hx' : x.length < z'.length := lt_of_lt_of_le hx hz.length_le
    rw [hz.getElem hx]
    exact ih.readInput hx' ha
  | @readRandom x q _ hq ha ih =>
    have hq' : q.length < p'.length := lt_of_lt_of_le hq hp.length_le
    rw [hp.getElem hq]
    exact ih.readRandom hq' ha

/-- Determinism of a run: it reaches at most one consumed pair of each total length
`|x| + |q|`. Blueprint 03 Lemma M2 (03-M2). -/
private theorem Reaches.eq_of_length_add_eq {R : StoppingController} {z p x q x' q' : BitString}
    (h : Reaches R z p x q) (h' : Reaches R z p x' q')
    (hlen : x.length + q.length = x'.length + q'.length) : x = x' ∧ q = q' := by
  induction h generalizing x' q' with
  | nil =>
    simp only [List.length_nil] at hlen
    exact ⟨(List.eq_nil_of_length_eq_zero (by omega)).symm,
      (List.eq_nil_of_length_eq_zero (by omega)).symm⟩
  | @readInput x q _ hx ha ih =>
    cases h' with
    | nil => simp at hlen
    | readInput h₀ _ _ =>
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨rfl, rfl⟩ := ih h₀ (by omega)
      exact ⟨rfl, rfl⟩
    | readRandom h₀ _ ha₀ =>
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨rfl, rfl⟩ := ih h₀ (by omega)
      exact absurd (Part.mem_unique ha ha₀) (by decide)
  | @readRandom x q _ hq ha ih =>
    cases h' with
    | nil => simp at hlen
    | readInput h₀ _ ha₀ =>
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨rfl, rfl⟩ := ih h₀ (by omega)
      exact absurd (Part.mem_unique ha ha₀) (by decide)
    | readRandom h₀ _ _ =>
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨rfl, rfl⟩ := ih h₀ (by omega)
      exact ⟨rfl, rfl⟩

/-- A run passes through every intermediate total length: below a reached pair of total length
`n` there is, for each `k ≤ n`, a reached pair of total length `k` that is a prefix of it in both
coordinates. Blueprint 03 Lemma M2 (03-M2). -/
private theorem Reaches.exists_prefix_length_add_eq {R : StoppingController}
    {z p x q : BitString} (h : Reaches R z p x q) {k : ℕ} (hk : k ≤ x.length + q.length) :
    ∃ x' q', Reaches R z p x' q' ∧ x' <+: x ∧ q' <+: q ∧ x'.length + q'.length = k := by
  induction h generalizing k with
  | nil => exact ⟨[], [], .nil, List.nil_prefix, List.nil_prefix, by simp at hk ⊢; omega⟩
  | @readInput x q h hx ha ih =>
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k (x.length + 1 + q.length) with hlt | hge
    · obtain ⟨x', q', h', hx', hq', hlen⟩ := ih (k := k) (by omega)
      exact ⟨x', q', h', hx'.trans (List.prefix_append _ _), hq', hlen⟩
    · exact ⟨_, _, h.readInput hx ha, List.prefix_rfl, List.prefix_rfl, by simp; omega⟩
  | @readRandom x q h hq ha ih =>
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k (x.length + (q.length + 1)) with hlt | hge
    · obtain ⟨x', q', h', hx', hq', hlen⟩ := ih (k := k) (by omega)
      exact ⟨x', q', h', hx', hq'.trans (List.prefix_append _ _), hlen⟩
    · exact ⟨_, _, h.readRandom hq ha, List.prefix_rfl, List.prefix_rfl, by simp; omega⟩

/-- The consumed pairs of one run form a chain: two reached pairs are comparable in both
coordinates, in the same direction. Blueprint 03 Lemma M2 (03-M2). -/
theorem Reaches.chain {R : StoppingController} {z p x q x' q' : BitString}
    (h : Reaches R z p x q) (h' : Reaches R z p x' q') :
    (x <+: x' ∧ q <+: q') ∨ (x' <+: x ∧ q' <+: q) := by
  rcases le_total (x.length + q.length) (x'.length + q'.length) with hle | hle
  · obtain ⟨x'', q'', h'', hx'', hq'', hlen⟩ := h'.exists_prefix_length_add_eq hle
    obtain ⟨rfl, rfl⟩ := h.eq_of_length_add_eq h'' hlen.symm
    exact Or.inl ⟨hx'', hq''⟩
  · obtain ⟨x'', q'', h'', hx'', hq'', hlen⟩ := h.exists_prefix_length_add_eq hle
    obtain ⟨rfl, rfl⟩ := h'.eq_of_length_add_eq h'' hlen.symm
    exact Or.inr ⟨hx'', hq''⟩

/-- A halting consumed pair bounds every reached pair of the same run: after a halt no further
bit is consumed. Blueprint 03 Lemma M2 (03-M2). -/
theorem Reaches.length_le_of_halt {R : StoppingController} {z p x q x' q' : BitString}
    (h : Reaches R z p x q) (hh : StopAction.halt ∈ R (x, q)) (h' : Reaches R z p x' q') :
    x'.length + q'.length ≤ x.length + q.length := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨x'', q'', h'', -, -, hlen⟩ :=
    h'.exists_prefix_length_add_eq (k := x.length + q.length + 1) hlt
  cases h'' with
  | nil => simp at hlen
  | readInput h₀ _ ha₀ =>
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨rfl, rfl⟩ := h.eq_of_length_add_eq h₀ (by omega)
    exact absurd (Part.mem_unique hh ha₀) (by decide)
  | readRandom h₀ _ ha₀ =>
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨rfl, rfl⟩ := h.eq_of_length_add_eq h₀ (by omega)
    exact absurd (Part.mem_unique hh ha₀) (by decide)

/-- Incompatible witnesses along a path: two witnesses whose input strings are comparable and
whose random strings are comparable are the same pair. Blueprint 03 Lemma M3 (03-M3). -/
theorem Witness.eq_of_isComparable {R : StoppingController} {z q z' q' : BitString}
    (h : Witness R z q) (h' : Witness R z' q') (hz : IsComparable z z') (hq : IsComparable q q') :
    z = z' ∧ q = q' := by
  obtain ⟨Z, hzZ, hz'Z⟩ : ∃ Z, z <+: Z ∧ z' <+: Z := by
    rcases hz with hz | hz
    · exact ⟨z', hz, List.prefix_rfl⟩
    · exact ⟨z, List.prefix_rfl, hz⟩
  obtain ⟨P, hqP, hq'P⟩ : ∃ P, q <+: P ∧ q' <+: P := by
    rcases hq with hq | hq
    · exact ⟨q', hq, List.prefix_rfl⟩
    · exact ⟨q, List.prefix_rfl, hq⟩
  have h₁ := h.1.mono hzZ hqP
  have h₂ := h'.1.mono hz'Z hq'P
  exact h₁.eq_of_length_add_eq h₂
    (le_antisymm (h₂.length_le_of_halt h'.2 h₁) (h₁.length_le_of_halt h.2 h₂))

/-- For a fixed input `z` the random witnesses form a prefix-free set.
Blueprint 03 Lemma M3, first consequence (03-M3-a). -/
theorem isPrefixFree_witness (R : StoppingController) (z : BitString) :
    IsPrefixFree {q | Witness R z q} := by
  intro q hq q' hq' hqq'
  exact (Witness.eq_of_isComparable hq hq' (Or.inl List.prefix_rfl) (Or.inl hqq')).2

/-- Witnesses of two distinct comparable inputs have incomparable random strings.
Blueprint 03 Lemma M3, second consequence (03-M3-b). -/
theorem Witness.isIncomparable_of_ne {R : StoppingController} {z q z' q' : BitString}
    (h : Witness R z q) (h' : Witness R z' q') (hz : IsComparable z z') (hne : z ≠ z') :
    IsIncomparable q q' := by
  exact ⟨fun hqq' => hne (h.eq_of_isComparable h' hz (Or.inl hqq')).1,
    fun hq'q => hne (h.eq_of_isComparable h' hz (Or.inr hq'q)).1⟩

/-- The `e`-th stopping controller: evaluate the `e`-th Mathlib partial recursive code on the
encoded consumed pair and decode the result as a stop action (an undecodable result is an
internal divergence). Blueprint 03 §2 (03-2-ENUM). -/
def stoppingMachine (e : ℕ) : StoppingController := fun xq =>
  ((Denumerable.ofNat Nat.Partrec.Code e).eval (Encodable.encode xq)).bind fun r =>
    Part.ofOption (Encodable.decode (α := StopAction) r)

/-- The enumeration of controllers is partial recursive, uniformly in the index.
Blueprint 03 §2 (03-2-ENUM). -/
theorem stoppingMachine_partrec :
    Partrec fun a : ℕ × (BitString × BitString) => stoppingMachine a.1 a.2 := by
  have hcode : Computable fun a : ℕ × (BitString × BitString) =>
      Denumerable.ofNat Nat.Partrec.Code a.1 :=
    ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst).to_comp
  exact (Nat.Partrec.Code.eval_part.comp hcode (Computable.encode.comp Computable.snd)).bind
    (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂

/-- Every partial recursive controller has an index in the enumeration.
Blueprint 03 §2 (03-2-ENUM). -/
theorem exists_stoppingMachine_eq {R : StoppingController} (hR : Partrec R) :
    ∃ e, stoppingMachine e = R := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hR
  refine ⟨Encodable.encode c, funext fun xq => ?_⟩
  simp only [stoppingMachine, Denumerable.ofNat_encode, hc]
  ext a
  simp [Encodable.encodek]

/-- One controller step of the `e`-th machine with time budget `t` (via
`Nat.Partrec.Code.evaln`): `none` when the internal computation has not finished within `t`
steps. Blueprint 03 Lemma M1 (03-M1). -/
def stepWithin (e t : ℕ) (xq : BitString × BitString) : Option StopAction :=
  (Nat.Partrec.Code.evaln t (Denumerable.ofNat Nat.Partrec.Code e) (Encodable.encode xq)).bind
    (Encodable.decode (α := StopAction))

/-- One replayed step of the bounded simulation on the buffers `(z, p)`: from the consumed
lengths `(i, j)`, ask the `e`-th machine (budget `t`) for its action at `(z.take i, p.take j)`
and advance the requested tape when a bit is available; otherwise the simulation suspends
(`none`). Blueprint 03 Lemma M1 (03-M1). -/
def consumeStep (e t : ℕ) (z p : BitString) (ij : ℕ × ℕ) : Option (ℕ × ℕ) :=
  match stepWithin e t (z.take ij.1, p.take ij.2) with
  | some StopAction.readInput => if ij.1 < z.length then some (ij.1 + 1, ij.2) else none
  | some StopAction.readRandom => if ij.2 < p.length then some (ij.1, ij.2 + 1) else none
  | _ => none

/-- Bounded exact-consumption simulation: replay the chain of consumed pairs from `([], [])`
for `|z| + |p|` steps, each internal computation within budget `t`, and accept exactly when the
run consumed all of `z` and `p` and then halts at `(z, p)` within budget `t`.
Blueprint 03 Lemma M1 (03-M1). -/
def witnessWithin (e t : ℕ) (z p : BitString) : Bool :=
  match (List.range (z.length + p.length)).foldl
      (fun st _ => st.bind (consumeStep e t z p)) (some (0, 0)) with
  | some ij =>
      decide (ij = (z.length, p.length)) && decide (stepWithin e t (z, p) = some StopAction.halt)
  | none => false

/-- The bounded step computes the controller exactly: `a` is the next action of the `e`-th
machine at `xq` iff some finite budget produces it (`Nat.Partrec.Code.evaln_sound`,
`Nat.Partrec.Code.evaln_complete`). Blueprint 03 Lemma M1 (03-M1). -/
private theorem mem_stoppingMachine_iff_exists_stepWithin {e : ℕ} {xq : BitString × BitString}
    {a : StopAction} : a ∈ stoppingMachine e xq ↔ ∃ t, stepWithin e t xq = some a := by
  constructor
  · intro h
    obtain ⟨r, hr, hra⟩ := Part.mem_bind_iff.1 h
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hr
    exact ⟨k, Option.bind_eq_some_iff.2 ⟨r, hk, Part.mem_ofOption.1 hra⟩⟩
  · rintro ⟨t, h⟩
    obtain ⟨r, hr, hra⟩ := Option.bind_eq_some_iff.1 h
    exact Part.mem_bind_iff.2 ⟨r, Nat.Partrec.Code.evaln_sound hr, Part.mem_ofOption.2 hra⟩

/-- A controller step found within budget `t` is found, with the same action, within every
larger budget (`Nat.Partrec.Code.evaln_mono`). Blueprint 03 Lemma M1 (03-M1). -/
private theorem stepWithin_mono {e t t' : ℕ} (h : t ≤ t') {xq : BitString × BitString}
    {a : StopAction} (ha : stepWithin e t xq = some a) : stepWithin e t' xq = some a := by
  obtain ⟨r, hr, hra⟩ := Option.bind_eq_some_iff.1 ha
  exact Option.bind_eq_some_iff.2 ⟨r, Nat.Partrec.Code.evaln_mono h hr, hra⟩

/-- A successful replayed step advances exactly one tape by one bit, in the direction requested
by the action of the `e`-th machine (budget `t`) at the current consumed pair.
Blueprint 03 Lemma M1 (03-M1). -/
private theorem consumeStep_eq_some {e t : ℕ} {z p : BitString} {i j : ℕ} {s : ℕ × ℕ}
    (h : consumeStep e t z p (i, j) = some s) :
    (stepWithin e t (z.take i, p.take j) = some .readInput ∧ i < z.length ∧ s = (i + 1, j)) ∨
      (stepWithin e t (z.take i, p.take j) = some .readRandom ∧ j < p.length ∧
        s = (i, j + 1)) := by
  unfold consumeStep at h
  rcases hst : stepWithin e t (z.take i, p.take j) with _ | a
  · simp [hst] at h
  · cases a with
    | readInput =>
      simp only [hst] at h
      split_ifs at h with hi
      exact Or.inl ⟨rfl, hi, (Option.some.inj h).symm⟩
    | readRandom =>
      simp only [hst] at h
      split_ifs at h with hj
      exact Or.inr ⟨rfl, hj, (Option.some.inj h).symm⟩
    | halt => simp [hst] at h

/-- A left fold whose step ignores the list entries iterates the step once per entry.
Blueprint 03 Lemma M1 (03-M1). -/
private theorem foldl_const_eq_iterate {α β : Type*} (f : β → β) (L : List α) (b : β) :
    L.foldl (fun s _ => f s) b = f^[L.length] b := by
  induction L generalizing b with
  | nil => rfl
  | cons a L ih => simp only [List.foldl_cons, List.length_cons, Function.iterate_succ_apply, ih]

/-- The replay is monotone in the budget: a state reached after `n` steps within budget `t`
is reached after `n` steps within every larger budget. Blueprint 03 Lemma M1 (03-M1). -/
private theorem iterate_consumeStep_mono {e t t' : ℕ} (h : t ≤ t') {z p : BitString} :
    ∀ {n : ℕ} {s : ℕ × ℕ},
      (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p))^[n] (some (0, 0)) = some s →
      (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t' z p))^[n] (some (0, 0)) = some s
  | 0, _, hs => hs
  | n + 1, s, hs => by
    rw [Function.iterate_succ_apply'] at hs ⊢
    obtain ⟨⟨i, j⟩, hij, hs'⟩ := Option.bind_eq_some_iff.1 hs
    rw [iterate_consumeStep_mono h hij, Option.bind_some]
    unfold consumeStep at hs' ⊢
    rcases hst : stepWithin e t (z.take i, p.take j) with _ | a
    · simp [hst] at hs'
    · rw [hst] at hs'
      rw [stepWithin_mono h hst]
      exact hs'

/-- Soundness of the replay: after `n` steps within any budget the state `(i, j)` satisfies
`i + j = n`, and the run of the `e`-th machine on `(z, p)` reaches `(z.take i, p.take j)`.
Blueprint 03 Lemma M1 (03-M1). -/
private theorem reaches_of_iterate_consumeStep {e t : ℕ} {z p : BitString} :
    ∀ {n i j : ℕ},
      (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p))^[n] (some (0, 0)) =
        some (i, j) → i + j = n ∧ Reaches (stoppingMachine e) z p (z.take i) (p.take j)
  | 0, i, j, h => by
    simp only [Function.iterate_zero, id_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simpa using (Reaches.nil : Reaches (stoppingMachine e) z p [] [])⟩
  | n + 1, i, j, h => by
    rw [Function.iterate_succ_apply'] at h
    obtain ⟨⟨i₀, j₀⟩, h₀, hstep⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hsum, hreach⟩ := reaches_of_iterate_consumeStep h₀
    rcases consumeStep_eq_some hstep with ⟨ha, hi, hs⟩ | ⟨ha, hj, hs⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs.symm
      have hlen : (z.take i₀).length < z.length := by simp; omega
      have hnext := hreach.readInput hlen
        ((mem_stoppingMachine_iff_exists_stepWithin).2 ⟨t, ha⟩)
      have heq : z.take i₀ ++ [z[(z.take i₀).length]'hlen] = z.take (i₀ + 1) := by
        simp [Nat.min_eq_left hi.le]
      rw [heq] at hnext
      exact ⟨by omega, hnext⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs.symm
      have hlen : (p.take j₀).length < p.length := by simp; omega
      have hnext := hreach.readRandom hlen
        ((mem_stoppingMachine_iff_exists_stepWithin).2 ⟨t, ha⟩)
      have heq : p.take j₀ ++ [p[(p.take j₀).length]'hlen] = p.take (j₀ + 1) := by
        simp [Nat.min_eq_left hj.le]
      rw [heq] at hnext
      exact ⟨by omega, hnext⟩

/-- Completeness of the replay: a consumed pair `(x, q)` reached by the run of the `e`-th
machine on `(z, p)` is the state of the replay after `|x| + |q|` steps, for every large enough
budget. Blueprint 03 Lemma M1 (03-M1). -/
private theorem exists_iterate_consumeStep_of_reaches {e : ℕ} {z p x q : BitString}
    (h : Reaches (stoppingMachine e) z p x q) : ∃ t₀, ∀ t, t₀ ≤ t →
      (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p))^[x.length + q.length]
        (some (0, 0)) = some (x.length, q.length) := by
  induction h with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | @readInput x q h hx ha ih =>
    obtain ⟨t₀, ht₀⟩ := ih
    obtain ⟨k, hk⟩ := mem_stoppingMachine_iff_exists_stepWithin.1 ha
    refine ⟨max t₀ k, fun t ht => ?_⟩
    have hxz : z.take x.length = x := (List.prefix_iff_eq_take.1 h.prefix.1).symm
    have hqp : p.take q.length = q := (List.prefix_iff_eq_take.1 h.prefix.2).symm
    have hlen : (x ++ [z[x.length]'hx]).length + q.length = x.length + q.length + 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hlen, Function.iterate_succ_apply', ht₀ t (le_of_max_le_left ht), Option.bind_some]
    unfold consumeStep
    rw [hxz, hqp, stepWithin_mono (le_of_max_le_right ht) hk]
    simp [hx]
  | @readRandom x q h hq ha ih =>
    obtain ⟨t₀, ht₀⟩ := ih
    obtain ⟨k, hk⟩ := mem_stoppingMachine_iff_exists_stepWithin.1 ha
    refine ⟨max t₀ k, fun t ht => ?_⟩
    have hxz : z.take x.length = x := (List.prefix_iff_eq_take.1 h.prefix.1).symm
    have hqp : p.take q.length = q := (List.prefix_iff_eq_take.1 h.prefix.2).symm
    have hlen : x.length + (q ++ [p[q.length]'hq]).length = x.length + q.length + 1 := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hlen, Function.iterate_succ_apply', ht₀ t (le_of_max_le_left ht), Option.bind_some]
    unfold consumeStep
    rw [hxz, hqp, stepWithin_mono (le_of_max_le_right ht) hk]
    simp [hq]

/-- The acceptance test of the bounded simulation: `witnessWithin` accepts exactly when the
replay reaches `(|z|, |p|)` after `|z| + |p|` steps and the machine then halts within the budget.
Blueprint 03 Lemma M1 (03-M1). -/
private theorem witnessWithin_eq_true_iff {e t : ℕ} {z p : BitString} :
    witnessWithin e t z p = true ↔
      (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p))^[z.length + p.length]
          (some (0, 0)) = some (z.length, p.length) ∧
        stepWithin e t (z, p) = some StopAction.halt := by
  unfold witnessWithin
  rw [foldl_const_eq_iterate (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p)),
    List.length_range]
  rcases (fun st : Option (ℕ × ℕ) => st.bind (consumeStep e t z p))^[z.length + p.length]
    (some (0, 0)) with _ | ij
  · simp
  · simp

/-- The bounded simulation is monotone in the time budget.
Blueprint 03 Lemma M1 (03-M1). -/
theorem witnessWithin_mono {e t t' : ℕ} (h : t ≤ t') {z p : BitString}
    (hw : witnessWithin e t z p = true) : witnessWithin e t' z p = true := by
  obtain ⟨hrun, hhalt⟩ := witnessWithin_eq_true_iff.1 hw
  exact witnessWithin_eq_true_iff.2 ⟨iterate_consumeStep_mono h hrun, stepWithin_mono h hhalt⟩

/-- The bounded controller step is primitive recursive in the index, the budget and the
consumed pair (`Nat.Partrec.Code.primrec_evaln`). Blueprint 03 Lemma M1 (03-M1). -/
private theorem primrec_stepWithin :
    Primrec fun a : (ℕ × ℕ) × (BitString × BitString) => stepWithin a.1.1 a.1.2 a.2 := by
  have hev : Primrec fun a : (ℕ × ℕ) × (BitString × BitString) =>
      Nat.Partrec.Code.evaln a.1.2 (Denumerable.ofNat Nat.Partrec.Code a.1.1)
        (Encodable.encode a.2) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.encode.comp Primrec.snd))
  have hdec : Primrec₂ fun (_ : (ℕ × ℕ) × (BitString × BitString)) (r : ℕ) =>
      Encodable.decode (α := StopAction) r :=
    (Primrec.decode.comp Primrec.snd).to₂
  exact Primrec.option_bind hev hdec

/-- The transition of the replay on the action `a` at the consumed lengths `(i, j)` of buffers
of lengths `(lz, lp)` is primitive recursive: advance the requested tape when a bit is left.
Blueprint 03 Lemma M1 (03-M1). -/
private theorem primrec_replayTransition :
    Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) =>
      if x.1.1 = StopAction.readInput then
        (if x.1.2.1 < x.2.1 then some (x.1.2.1 + 1, x.1.2.2) else none)
      else if x.1.1 = StopAction.readRandom then
        (if x.1.2.2 < x.2.2 then some (x.1.2.1, x.1.2.2 + 1) else none)
      else none := by
  have ha : Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) => x.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hi : Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) => x.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hj : Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) => x.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hlz : Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) => x.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hlp : Primrec fun x : (StopAction × (ℕ × ℕ)) × (ℕ × ℕ) => x.2.2 :=
    Primrec.snd.comp Primrec.snd
  refine Primrec.ite (Primrec.eq.comp ha (Primrec.const _)) ?_ ?_
  · exact Primrec.ite (Primrec.nat_lt.comp hi hlz)
      (Primrec.option_some.comp (Primrec.pair (Primrec.succ.comp hi) hj)) (Primrec.const none)
  · exact Primrec.ite (Primrec.eq.comp ha (Primrec.const _))
      (Primrec.ite (Primrec.nat_lt.comp hj hlp)
        (Primrec.option_some.comp (Primrec.pair hi (Primrec.succ.comp hj))) (Primrec.const none))
      (Primrec.const none)

/-- The replayed step is primitive recursive in the index, the budget, the buffers and the
consumed lengths. Blueprint 03 Lemma M1 (03-M1). -/
private theorem primrec_consumeStep :
    Primrec fun b : ((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ) =>
      consumeStep b.1.1.1 b.1.1.2 b.1.2.1 b.1.2.2 b.2 := by
  have hZ : Primrec fun b : ((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ) => b.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hP : Primrec fun b : ((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ) => b.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hact : Primrec fun b : ((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ) =>
      stepWithin b.1.1.1 b.1.1.2 (b.1.2.1.take b.2.1, b.1.2.2.take b.2.2) :=
    primrec_stepWithin.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.list_take.comp hZ (Primrec.fst.comp Primrec.snd))
        (Primrec.list_take.comp hP (Primrec.snd.comp Primrec.snd))))
  have hnext : Primrec₂ fun (b : ((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ))
      (a : StopAction) =>
      if a = StopAction.readInput then
        (if b.2.1 < b.1.2.1.length then some (b.2.1 + 1, b.2.2) else none)
      else if a = StopAction.readRandom then
        (if b.2.2 < b.1.2.2.length then some (b.2.1, b.2.2 + 1) else none)
      else none := by
    have hg : Primrec fun p : (((ℕ × ℕ) × (BitString × BitString)) × (ℕ × ℕ)) × StopAction =>
        ((p.2, p.1.2), (p.1.1.2.1.length, p.1.1.2.2.length)) :=
      Primrec.pair (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.list_length.comp (hZ.comp Primrec.fst))
          (Primrec.list_length.comp (hP.comp Primrec.fst)))
    exact (primrec_replayTransition.comp hg).of_eq fun p => rfl
  refine (Primrec.option_bind hact hnext).of_eq fun b => ?_
  unfold consumeStep
  rcases stepWithin b.1.1.1 b.1.1.2 (b.1.2.1.take b.2.1, b.1.2.2.take b.2.2) with _ | a
  · rfl
  · cases a <;> simp

/-- The bounded simulation is primitive recursive in the index, the budget and both buffers.
Blueprint 03 Lemma M1 (03-M1). -/
theorem primrec_witnessWithin :
    Primrec fun a : (ℕ × ℕ) × BitString × BitString => witnessWithin a.1.1 a.1.2 a.2.1 a.2.2 := by
  have hZ : Primrec fun a : (ℕ × ℕ) × BitString × BitString => a.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hP : Primrec fun a : (ℕ × ℕ) × BitString × BitString => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hcons : Primrec₂ fun (x : ((ℕ × ℕ) × BitString × BitString) × (Option (ℕ × ℕ) × ℕ))
      (ij : ℕ × ℕ) => consumeStep x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 ij :=
    (primrec_consumeStep.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq
      fun _ => rfl
  have hstep : Primrec₂ fun (a : (ℕ × ℕ) × BitString × BitString)
      (sb : Option (ℕ × ℕ) × ℕ) => sb.1.bind (consumeStep a.1.1 a.1.2 a.2.1 a.2.2) :=
    (Primrec.option_bind (Primrec.fst.comp Primrec.snd) hcons).of_eq fun _ => rfl
  have hrun : Primrec fun a : (ℕ × ℕ) × BitString × BitString =>
      (List.range (a.2.1.length + a.2.2.length)).foldl
        (fun st _ => st.bind (consumeStep a.1.1 a.1.2 a.2.1 a.2.2)) (some (0, 0)) :=
    (Primrec.list_foldl (Primrec.list_range.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hZ) (Primrec.list_length.comp hP)))
      (Primrec.const (some ((0 : ℕ), (0 : ℕ)))) hstep).of_eq fun _ => rfl
  have hhalt : Primrec fun a : (ℕ × ℕ) × BitString × BitString =>
      stepWithin a.1.1 a.1.2 (a.2.1, a.2.2) :=
    (primrec_stepWithin.comp (Primrec.pair Primrec.fst (Primrec.pair hZ hP))).of_eq fun _ => rfl
  have hlen : Primrec fun p : ((ℕ × ℕ) × BitString × BitString) × (ℕ × ℕ) =>
      (p.1.2.1.length, p.1.2.2.length) :=
    Primrec.pair (Primrec.list_length.comp (hZ.comp Primrec.fst))
      (Primrec.list_length.comp (hP.comp Primrec.fst))
  have hacc : Primrec₂ fun (a : (ℕ × ℕ) × BitString × BitString) (ij : ℕ × ℕ) =>
      decide (ij = (a.2.1.length, a.2.2.length)) &&
        decide (stepWithin a.1.1 a.1.2 (a.2.1, a.2.2) = some StopAction.halt) :=
    (Primrec.and.comp (Primrec.eq.comp Primrec.snd hlen).decide
      (Primrec.eq.comp (hhalt.comp Primrec.fst) (Primrec.const _)).decide).of_eq fun _ => rfl
  refine (Primrec.option_casesOn hrun (Primrec.const false) hacc).of_eq fun a => ?_
  unfold witnessWithin
  split
  · next ij h => rw [h]
  · next h => rw [h]

/-- Finite witness enumeration: `(z, p)` is a witness of the `e`-th machine iff the bounded
simulation accepts it for some budget. Blueprint 03 Lemma M1 (03-M1). -/
theorem witness_iff_exists_witnessWithin (e : ℕ) (z p : BitString) :
    Witness (stoppingMachine e) z p ↔ ∃ t, witnessWithin e t z p = true := by
  constructor
  · rintro ⟨hreach, hhalt⟩
    obtain ⟨t₀, ht₀⟩ := exists_iterate_consumeStep_of_reaches hreach
    obtain ⟨k, hk⟩ := mem_stoppingMachine_iff_exists_stepWithin.1 hhalt
    exact ⟨max t₀ k, witnessWithin_eq_true_iff.2
      ⟨ht₀ _ (le_max_left _ _), stepWithin_mono (le_max_right _ _) hk⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨hrun, hhalt⟩ := witnessWithin_eq_true_iff.1 ht
    have hreach := (reaches_of_iterate_consumeStep hrun).2
    rw [List.take_length, List.take_length] at hreach
    exact ⟨hreach, mem_stoppingMachine_iff_exists_stepWithin.2 ⟨t, hhalt⟩⟩

/-- The witness relation is computably enumerable, uniformly in the machine index.
Blueprint 03 Lemma M1 and F4 `witness_re` (03-M1). -/
theorem isRE_witness :
    IsRE fun a : ℕ × BitString × BitString => Witness (stoppingMachine a.1) a.2.1 a.2.2 := by
  have hdec : IsRE fun b : (ℕ × BitString × BitString) × ℕ =>
      witnessWithin b.1.1 b.2 b.1.2.1 b.1.2.2 = true :=
    isRE_of_computable_bool _ (fun b => witnessWithin b.1.1 b.2 b.1.2.1 b.1.2.2)
      (fun _ => Iff.rfl)
      (primrec_witnessWithin.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp Primrec.fst))).to_comp
  exact (IsRE.exists_encodable
    (R := fun (a : ℕ × BitString × BitString) (t : ℕ) => witnessWithin a.1 t a.2.1 a.2.2 = true)
    hdec).of_iff fun a => (witness_iff_exists_witnessWithin a.1 a.2.1 a.2.2).symm

end Kolmogorov
