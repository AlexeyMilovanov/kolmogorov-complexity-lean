import KolmogorovMathlib.StoppingComplexity.StopProbability

/-!
# The fixed universal stopping machine

Blueprint 03 §3 and F5 of the stopping-complexity blueprint. The universal machine
`univStopping` is one closed definition: it reads a unary tag `natCode e = 1^e 0` from the
random tape and then runs the `e`-th controller `stoppingMachine e` on the remaining random
tape and the original input tape. Lemma M5 (`witness_univStopping_iff`) is the exact
simulation of witnesses, the domination `univStopProb_ge_stoppingMachine` is the one direction
of universal probability comparison the blueprint needs, `univStopProb` and
`univStopComplexity` are the `M_stop` and `K_stop` of F0 (the random prefix counts the tag),
and the geometric machine gives finiteness of `K_stop`, positivity of `M_stop` and the
`ℕ`-valued shadow `univStopComplexityNat` (F5).
-/

namespace Kolmogorov

open scoped ENNReal

/-- The fixed universal stopping machine `V`: with `k` the number of leading `true` bits of the
consumed random prefix, if the tag `natCode k = 1^k 0` is complete then act as the `k`-th
controller on the input and the random bits after the tag, otherwise request one more random
bit. Blueprint 03 §3 (03-3-DEF-V). -/
def univStopping : StoppingController := fun xq =>
  let k := (xq.2.takeWhile id).length
  if k < xq.2.length then stoppingMachine k (xq.1, xq.2.drop (k + 1))
  else Part.some StopAction.readRandom

/-- The universal machine is a partial recursive controller. Blueprint 03 §3 (03-3-DEF-V). -/
theorem univStopping_partrec : Partrec univStopping := by
  have hk : Primrec fun xq : BitString × BitString => (xq.2.takeWhile id).length :=
    Primrec.list_length.comp ((Primrec.list_takeWhile Primrec.id).comp Primrec.snd)
  have hc : Primrec fun xq : BitString × BitString =>
      decide ((xq.2.takeWhile id).length < xq.2.length) :=
    (Primrec.nat_lt.comp hk (Primrec.list_length.comp Primrec.snd)).decide
  have hf : Partrec fun xq : BitString × BitString =>
      stoppingMachine (xq.2.takeWhile id).length
        (xq.1, xq.2.drop ((xq.2.takeWhile id).length + 1)) :=
    stoppingMachine_partrec.comp (hk.to_comp.pair (Computable.fst.pair
      (Primrec.list_drop.comp Primrec.snd (Primrec.succ.comp hk)).to_comp))
  refine (Partrec.cond hc.to_comp hf (Partrec.const' (Part.some StopAction.readRandom))).of_eq ?_
  intro xq
  simp only [univStopping]
  split_ifs with h <;> simp [h]

/-- The unary tag is read back by counting leading ones: the leading `true` run of
`natCode e ++ r` has length exactly `e`, whatever follows the tag.
Blueprint 03 Lemma M5 (03-M5). -/
private theorem length_takeWhile_natCode_append (e : ℕ) (r : BitString) :
    ((natCode e ++ r).takeWhile id).length = e := by
  simp [natCode]

/-- Tag parsing: if the leading `true` run of `p` (of length `k`) stops before the end of `p`,
then `p` is the complete tag `natCode k` followed by the bits after it.
Blueprint 03 Lemma M5 (03-M5). -/
private theorem natCode_append_drop_of_lt {p : BitString}
    (h : (p.takeWhile id).length < p.length) :
    natCode (p.takeWhile id).length ++ p.drop ((p.takeWhile id).length + 1) = p := by
  induction p with
  | nil => simp at h
  | cons b p ih =>
    cases b with
    | false => simp [natCode]
    | true =>
      simp only [List.takeWhile_cons, id, if_true, List.length_cons] at h ih ⊢
      simp only [natCode, List.replicate_succ, List.cons_append, List.drop_succ_cons] at ih ⊢
      rw [ih (by omega)]

/-- Interpreter step after a complete tag: on the random prefix `natCode e ++ r` the universal
machine acts as the `e`-th controller on the random bits `r` after the tag.
Blueprint 03 §3 (03-3-DEF-V). -/
private theorem univStopping_natCode_append (e : ℕ) (x r : BitString) :
    univStopping (x, natCode e ++ r) = stoppingMachine e (x, r) := by
  simp only [univStopping, length_takeWhile_natCode_append, List.length_append, length_natCode]
  rw [if_pos (by omega), List.drop_left' (length_natCode e)]

/-- Interpreter step inside the tag: while the consumed random prefix is all ones the tag is
incomplete, and the universal machine requests one more random bit.
Blueprint 03 §3 (03-3-DEF-V). -/
private theorem univStopping_replicate (x : BitString) (j : ℕ) :
    univStopping (x, List.replicate j true) = Part.some StopAction.readRandom := by
  simp [univStopping]

/-- The tag phase: on a random buffer beginning with `natCode e`, the universal machine reads
the whole tag, one random bit at a time, without touching the input tape.
Blueprint 03 Lemma M5 (03-M5). -/
private theorem reaches_univStopping_natCode (z : BitString) (e : ℕ) (q : BitString) :
    Reaches univStopping z (natCode e ++ q) [] (natCode e) := by
  have hrep : ∀ j ≤ e, Reaches univStopping z (natCode e ++ q) [] (List.replicate j true) := by
    intro j hj
    induction j with
    | zero => exact Reaches.nil
    | succ j ih =>
      have hlt : (List.replicate j true).length < (natCode e ++ q).length := by simp; omega
      have hstep := Reaches.readRandom (ih (by omega)) hlt
        (by rw [univStopping_replicate]; exact Part.mem_some _)
      have hb : (natCode e ++ q)[(List.replicate j true).length]'hlt = true := by
        simp [natCode, show j < e by omega]
      rw [hb, ← List.replicate_succ'] at hstep
      exact hstep
  have hlt : (List.replicate e true).length < (natCode e ++ q).length := by simp; omega
  have hstep := Reaches.readRandom (hrep e le_rfl) hlt
    (by rw [univStopping_replicate]; exact Part.mem_some _)
  have hb : (natCode e ++ q)[(List.replicate e true).length]'hlt = false := by simp [natCode]
  rw [hb] at hstep
  exact hstep

/-- Forward replay: every consumed pair `(x, r)` of the `e`-th machine on the random buffer `q`
is reached by the universal machine on `natCode e ++ q` as `(x, natCode e ++ r)`; the simulation
reads no bits except those requested by the `e`-th machine. Blueprint 03 Lemma M5 (03-M5). -/
private theorem Reaches.univStopping_of_stoppingMachine {e : ℕ} {z q x r : BitString}
    (h : Reaches (stoppingMachine e) z q x r) :
    Reaches univStopping z (natCode e ++ q) x (natCode e ++ r) := by
  induction h with
  | nil => simpa using reaches_univStopping_natCode z e q
  | readInput _ hx ha ih =>
    exact Reaches.readInput ih hx (by rwa [univStopping_natCode_append])
  | @readRandom x r _ hr ha ih =>
    have hlt : (natCode e ++ r).length < (natCode e ++ q).length := by simp; omega
    have hstep := Reaches.readRandom ih hlt (by rwa [univStopping_natCode_append])
    have hb : (natCode e ++ q)[(natCode e ++ r).length]'hlt = q[r.length]'hr := by
      simp [List.getElem_append_right]
    rwa [hb, List.append_assoc] at hstep

/-- Backward replay, the tag-phase invariant: a consumed pair `(x, q)` of the universal machine
on the random buffer `p` is either in the tag phase (no input read, only ones read, a prefix of
`p`), or lies after a complete tag `natCode e` at the head of `p`, where `q = natCode e ++ r`
and `(x, r)` is a consumed pair of the `e`-th machine on the rest of `p`.
Blueprint 03 Lemma M5 (03-M5). -/
private theorem Reaches.of_univStopping {z p x q : BitString}
    (h : Reaches univStopping z p x q) :
    (x = [] ∧ q = List.replicate q.length true ∧ q <+: p) ∨
      ∃ e r, q = natCode e ++ r ∧ natCode e ++ p.drop (e + 1) = p ∧
        Reaches (stoppingMachine e) z (p.drop (e + 1)) x r := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl, List.nil_prefix⟩
  | @readInput x q _ hx ha ih =>
    rcases ih with ⟨rfl, hq, -⟩ | ⟨e, r, rfl, hp, hr⟩
    · rw [hq, univStopping_replicate] at ha
      exact absurd (Part.mem_some_iff.mp ha) (by decide)
    · rw [univStopping_natCode_append] at ha
      exact Or.inr ⟨e, r, rfl, hp, Reaches.readInput hr hx ha⟩
  | @readRandom x q _ hq ha ih =>
    rcases ih with ⟨rfl, hrep, hpre⟩ | ⟨e, r, rfl, hp, hr⟩
    · have hpre' : q ++ [p[q.length]] <+: p := by
        have key : p.take q.length ++ [p[q.length]] <+: p := by
          rw [List.take_append_getElem]; exact List.take_prefix _ _
        rwa [← List.prefix_iff_eq_take.mp hpre] at key
      cases hb : p[q.length] with
      | true =>
        rw [hb] at hpre'
        refine Or.inl ⟨rfl, ?_, hpre'⟩
        simp only [List.length_append, List.length_singleton, List.replicate_succ']
        rw [← hrep]
      | false =>
        rw [hb] at hpre'
        have hnat : natCode q.length = q ++ [false] := by rw [natCode, ← hrep]
        refine Or.inr ⟨q.length, [], by rw [List.append_nil, hnat], ?_, Reaches.nil⟩
        obtain ⟨t, ht⟩ := hpre'
        rw [hnat, ← ht, List.drop_left' (by simp)]
    · rw [univStopping_natCode_append] at ha
      have hr' : r.length < (p.drop (e + 1)).length := by simp at hq ⊢; omega
      have hb : p[(natCode e ++ r).length]'hq = (p.drop (e + 1))[r.length]'hr' := by simp
      refine Or.inr ⟨e, r ++ [(p.drop (e + 1))[r.length]'hr'], ?_, hp,
        Reaches.readRandom hr hr' ha⟩
      rw [List.append_assoc, hb]

/-- Exact universal simulation: `(z, p)` is a witness of `V` iff `p` is a tag `natCode e`
followed by a witness `q` of the `e`-th machine at `z`; the decomposition is unique because the
tags are prefix-free. Blueprint 03 Lemma M5, F4 `universal_simulation_witness` (03-M5). -/
theorem witness_univStopping_iff (z p : BitString) :
    Witness univStopping z p ↔
      ∃ e q, p = natCode e ++ q ∧ Witness (stoppingMachine e) z q := by
  constructor
  · rintro ⟨hreach, hhalt⟩
    rcases hreach.of_univStopping with ⟨-, hrep, -⟩ | ⟨e, r, hpr, -, hr⟩
    · rw [hrep, univStopping_replicate] at hhalt
      exact absurd (Part.mem_some_iff.mp hhalt) (by decide)
    · have hdrop : p.drop (e + 1) = r := by rw [hpr]; exact List.drop_left' (length_natCode e)
      rw [hdrop] at hr
      rw [hpr, univStopping_natCode_append] at hhalt
      exact ⟨e, r, hpr, hr, hhalt⟩
  · rintro ⟨e, q, rfl, hreach, hhalt⟩
    exact ⟨hreach.univStopping_of_stoppingMachine, by rwa [univStopping_natCode_append]⟩

/-- Bounded witness search for the universal machine: parse the unary tag of `p` and run the
bounded simulation of the tagged machine on the rest of `p`. Blueprint 03 Lemma M5 (03-M5). -/
def univWitnessWithin (t : ℕ) (z p : BitString) : Bool :=
  let k := (p.takeWhile id).length
  decide (k < p.length) && witnessWithin k t z (p.drop (k + 1))

/-- `(z, p)` is a witness of `V` iff the bounded universal search accepts it for some budget.
Blueprint 03 Lemma M5 with Lemma M1 (03-M5). -/
theorem univWitness_iff_exists_univWitnessWithin (z p : BitString) :
    Witness univStopping z p ↔ ∃ t, univWitnessWithin t z p = true := by
  rw [witness_univStopping_iff]
  constructor
  · rintro ⟨e, q, rfl, hq⟩
    obtain ⟨t, ht⟩ := (witness_iff_exists_witnessWithin e z q).mp hq
    refine ⟨t, ?_⟩
    simp only [univWitnessWithin, length_takeWhile_natCode_append, List.length_append,
      length_natCode, List.drop_left' (length_natCode e), ht, Bool.and_true, decide_eq_true_eq]
    omega
  · rintro ⟨t, ht⟩
    simp only [univWitnessWithin, Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ⟨_, _, (natCode_append_drop_of_lt ht.1).symm,
      (witness_iff_exists_witnessWithin _ z _).mpr ⟨t, ht.2⟩⟩

/-- The bounded universal search is primitive recursive. Blueprint 03 Lemma M5 (03-M5). -/
theorem primrec_univWitnessWithin :
    Primrec fun a : ℕ × BitString × BitString => univWitnessWithin a.1 a.2.1 a.2.2 := by
  have hk : Primrec fun a : ℕ × BitString × BitString => (a.2.2.takeWhile id).length :=
    Primrec.list_length.comp
      ((Primrec.list_takeWhile Primrec.id).comp (Primrec.snd.comp Primrec.snd))
  have hlt : Primrec fun a : ℕ × BitString × BitString =>
      decide ((a.2.2.takeWhile id).length < a.2.2.length) :=
    (Primrec.nat_lt.comp hk (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))).decide
  have hw : Primrec fun a : ℕ × BitString × BitString =>
      witnessWithin (a.2.2.takeWhile id).length a.1 a.2.1
        (a.2.2.drop ((a.2.2.takeWhile id).length + 1)) :=
    primrec_witnessWithin.comp ((hk.pair Primrec.fst).pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.list_drop.comp (Primrec.snd.comp Primrec.snd) (Primrec.succ.comp hk))))
  exact (Primrec.and.comp hlt hw).of_eq fun a => rfl

/-- The bounded universal search is monotone in the time budget: a larger budget accepts
every pair a smaller one accepts. Blueprint 03 Lemma M5 with Lemma M1 (03-M5). -/
theorem univWitnessWithin_mono {t t' : ℕ} (h : t ≤ t') {z p : BitString}
    (hw : univWitnessWithin t z p = true) : univWitnessWithin t' z p = true := by
  simp only [univWitnessWithin, Bool.and_eq_true] at hw ⊢
  exact ⟨hw.1, witnessWithin_mono h hw.2⟩

/-- `M_stop(z)`: the stopping probability of the fixed universal machine at exactly `z` (F0).
Blueprint 03 §3 (03-3-DEF-MK). -/
noncomputable def univStopProb (z : BitString) : ℝ≥0∞ := stopProb univStopping z

/-- Machine complexity `K_R(z) ∈ ℕ∞`: the least length of a random witness for `z`, `⊤` when
there is none. Blueprint 03 §3 and F5 (03-3-DEF-MK). -/
noncomputable def stopComplexity (R : StoppingController) (z : BitString) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ p, Witness R z p ∧ (p.length : ℕ∞) = n}

/-- `K_stop(z)`: the stopping complexity with respect to the fixed universal machine; the
witness length counts the whole consumed random prefix, tag included (F0).
Blueprint 03 §3 (03-3-DEF-MK). -/
noncomputable def univStopComplexity (z : BitString) : ℕ∞ := stopComplexity univStopping z

/-- A witness bounds the machine complexity by its length. Blueprint 03 §3 (03-3-DEF-MK). -/
theorem stopComplexity_le_of_witness {R : StoppingController} {z p : BitString}
    (h : Witness R z p) : stopComplexity R z ≤ p.length := by
  exact sInf_le ⟨p, h, rfl⟩

/-- A finite machine complexity is attained by a witness. Blueprint 03 §3 (03-3-DEF-MK). -/
theorem exists_witness_of_stopComplexity_ne_top {R : StoppingController} {z : BitString}
    (h : stopComplexity R z ≠ ⊤) : ∃ p, Witness R z p ∧ (p.length : ℕ∞) = stopComplexity R z := by
  have hne : {n : ℕ∞ | ∃ p, Witness R z p ∧ (p.length : ℕ∞) = n}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact h (by rw [stopComplexity, hemp, sInf_empty])
  obtain ⟨p, hp, hlen⟩ := csInf_mem hne
  exact ⟨p, hp, hlen⟩

/-- The universal stopping probability is the weighted sum of the stopping probabilities of
all enumerated machines: `M_stop(z) = Σ_e 2^{-(e+1)} τ_{R_e}(z)`. Blueprint 03 §3 (03-3-DOM). -/
theorem univStopProb_eq_tsum_stoppingMachine (z : BitString) :
    univStopProb z = ∑' e, (2 : ℝ≥0∞)⁻¹ ^ (e + 1) * stopProb (stoppingMachine e) z := by
  let f : (Σ e, {q : BitString // Witness (stoppingMachine e) z q}) →
      {p : BitString // Witness univStopping z p} := fun s =>
    ⟨natCode s.1 ++ s.2, (witness_univStopping_iff z _).mpr ⟨s.1, s.2, rfl, s.2.2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨e, q, hq⟩ ⟨e', q', hq'⟩ hs
      obtain ⟨rfl, rfl⟩ := natCode_append_inj (congrArg Subtype.val hs)
      rfl
    · rintro ⟨p, hp⟩
      obtain ⟨e, q, rfl, hq⟩ := (witness_univStopping_iff z p).mp hp
      exact ⟨⟨e, q, hq⟩, rfl⟩
  rw [univStopProb, stopProb_eq_tsum, ← (Equiv.ofBijective f hf).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun e => ?_
  rw [stopProb_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  simp only [Equiv.ofBijective_apply, f, List.length_append, length_natCode, pow_add]

/-- Universal domination, the one direction needed: `M_stop(z) ≥ 2^{-(e+1)} τ_{R_e}(z)` for every
index `e`, with the constant `|natCode e| = e + 1` independent of `z`.
Blueprint 03 Lemma M5, F4 `universal_simulation_probability` (03-3-DOM). -/
theorem univStopProb_ge_stoppingMachine (e : ℕ) (z : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ (e + 1) * stopProb (stoppingMachine e) z ≤ univStopProb z := by
  rw [univStopProb_eq_tsum_stoppingMachine]
  exact ENNReal.le_tsum e

/-- `K_stop(z) ≤ K_{R_e}(z) + (e + 1)`: simulating the `e`-th machine costs the tag length.
Blueprint 03 §3 (03-3-DOM). -/
theorem univStopComplexity_le_stoppingMachine (e : ℕ) (z : BitString) :
    univStopComplexity z ≤ stopComplexity (stoppingMachine e) z + (e + 1 : ℕ) := by
  by_cases h : stopComplexity (stoppingMachine e) z = ⊤
  · rw [h, top_add]
    exact le_top
  · obtain ⟨q, hq, hlen⟩ := exists_witness_of_stopComplexity_ne_top h
    have hw : Witness univStopping z (natCode e ++ q) :=
      (witness_univStopping_iff z _).mpr ⟨e, q, rfl, hq⟩
    calc univStopComplexity z ≤ ((natCode e ++ q).length : ℕ∞) := stopComplexity_le_of_witness hw
      _ = stopComplexity (stoppingMachine e) z + (e + 1 : ℕ) := by
        rw [← hlen, List.length_append, length_natCode]
        push_cast
        ring

/-- The geometric machine: request a random bit; halt if it is `1`, otherwise read one input
bit and repeat (if no random bit beyond the input length has been read yet, request one).
Blueprint F5 (F5-GEO). -/
def geometricController : StoppingController := fun xq =>
  Part.some
    (if xq.2.length ≤ xq.1.length then StopAction.readRandom
    else if xq.2.getLast? = some true then StopAction.halt else StopAction.readInput)

/-- At input `x` the geometric machine has the witness `0^{|x|} 1`. Blueprint F5 (F5-GEO). -/
theorem witness_geometricController (x : BitString) :
    Witness geometricController x (List.replicate x.length false ++ [true]) := by
  have hphase : ∀ i ≤ x.length, Reaches geometricController x
      (List.replicate x.length false ++ [true]) (x.take i) (List.replicate i false) := by
    intro i hi
    induction i with
    | zero => simpa using (Reaches.nil : Reaches geometricController x _ [] [])
    | succ i ih =>
      have hlt1 : (List.replicate i false).length <
          (List.replicate x.length false ++ [true]).length := by simp; omega
      have h2 := Reaches.readRandom (ih (by omega)) hlt1 (by
        simp only [geometricController, List.length_replicate, List.length_take]
        rw [if_pos (by omega)]
        exact Part.mem_some _)
      have hb1 : (List.replicate x.length false ++ [true])[(List.replicate i false).length]'hlt1
          = false := by simp [show i < x.length by omega]
      rw [hb1, ← List.replicate_succ'] at h2
      have hlt2 : (x.take i).length < x.length := by simp; omega
      have h3 := Reaches.readInput h2 hlt2 (by
        simp only [geometricController, List.length_replicate, List.length_take]
        rw [if_neg (by omega)]
        simp [List.getLast?_replicate])
      have hb2 : x[(x.take i).length]'hlt2 = x[i]'(by omega) := by
        simp only [List.length_take, Nat.min_eq_left (show i ≤ x.length by omega)]
      rwa [hb2, List.take_append_getElem] at h3
  have h1 := hphase x.length le_rfl
  rw [List.take_length] at h1
  have hlt : (List.replicate x.length false).length <
      (List.replicate x.length false ++ [true]).length := by simp
  have h2 := Reaches.readRandom h1 hlt (by simp [geometricController])
  have hb : (List.replicate x.length false ++ [true])[(List.replicate x.length false).length]'hlt
      = true := by simp
  rw [hb] at h2
  exact ⟨h2, by simp [geometricController]⟩

/-- `K_stop(x) ≤ |x| + 1 + a` for one natural constant `a` (the tag length of the geometric
machine), quantified before `x`. Blueprint F5 (F5-GEO). -/
theorem univStopComplexity_le_length :
    ∃ a : ℕ, ∀ x : BitString, univStopComplexity x ≤ (x.length + 1 + a : ℕ) := by
  have hlast : Primrec fun xq : BitString × BitString => xq.2.getLast? :=
    (Primrec.list_head?.comp (Primrec.list_reverse.comp Primrec.snd)).of_eq fun xq => by simp
  have hc : Primrec fun xq : BitString × BitString =>
      if xq.2.length ≤ xq.1.length then StopAction.readRandom
      else if xq.2.getLast? = some true then StopAction.halt else StopAction.readInput :=
    Primrec.ite (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_length.comp Primrec.fst)) (Primrec.const _)
      (Primrec.ite (Primrec.eq.comp hlast (Primrec.const _)) (Primrec.const _) (Primrec.const _))
  obtain ⟨e, he⟩ := exists_stoppingMachine_eq (hc.to_comp.partrec.of_eq fun _ => rfl :
    Partrec geometricController)
  refine ⟨e + 1, fun x => ?_⟩
  calc univStopComplexity x ≤ stopComplexity (stoppingMachine e) x + (e + 1 : ℕ) :=
        univStopComplexity_le_stoppingMachine e x
    _ ≤ ((x.length + 1 : ℕ) : ℕ∞) + (e + 1 : ℕ) := by
        gcongr
        rw [he]
        simpa using stopComplexity_le_of_witness (witness_geometricController x)
    _ = (x.length + 1 + (e + 1) : ℕ) := by push_cast; ring

/-- The universal stopping complexity is finite on every word. Blueprint F5 (F5-FIN). -/
theorem univStopComplexity_ne_top (z : BitString) : univStopComplexity z ≠ ⊤ := by
  obtain ⟨a, ha⟩ := univStopComplexity_le_length
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (ha z)

/-- The universal stopping probability is positive on every word. Blueprint F5 (F5-FIN). -/
theorem univStopProb_pos (z : BitString) : 0 < univStopProb z := by
  obtain ⟨p, hp, -⟩ := exists_witness_of_stopComplexity_ne_top (univStopComplexity_ne_top z)
  exact lt_of_lt_of_le (ENNReal.pow_pos (by simp) _) (two_pow_neg_le_stopProb_of_witness hp)

/-- The universal stopping probability is at most one. Blueprint F5 (F5-FIN). -/
theorem univStopProb_le_one (z : BitString) : univStopProb z ≤ 1 := by
  exact stopProb_le_one univStopping z

/-- The `ℕ`-valued shadow of `K_stop` (exposed only after finiteness, per the ENat/Nat-shadow
convention). Blueprint F5 (F5-FIN). -/
noncomputable def univStopComplexityNat (z : BitString) : ℕ := (univStopComplexity z).toNat

/-- The shadow casts back to `K_stop`. Blueprint F5 (F5-FIN). -/
theorem univStopComplexityNat_eq_coe (z : BitString) :
    (univStopComplexityNat z : ℕ∞) = univStopComplexity z := by
  exact ENat.coe_toNat (univStopComplexity_ne_top z)

/-- A shortest witness contributes its weight: `2^{-K_stop(z)} ≤ M_stop(z)`.
Blueprint F5 (F5-FIN). -/
theorem two_pow_neg_univStopComplexityNat_le (z : BitString) :
    (2 : ℝ≥0∞)⁻¹ ^ univStopComplexityNat z ≤ univStopProb z := by
  obtain ⟨p, hp, hlen⟩ := exists_witness_of_stopComplexity_ne_top (univStopComplexity_ne_top z)
  have hK : univStopComplexityNat z = p.length := by
    rw [univStopComplexityNat, univStopComplexity, ← hlen, ENat.toNat_coe]
  rw [hK]
  exact two_pow_neg_le_stopProb_of_witness hp

end Kolmogorov
