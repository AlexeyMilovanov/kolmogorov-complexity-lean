import KolmogorovMathlib.StoppingComplexity.AllocatorLimit
import KolmogorovMathlib.StoppingComplexity.Universal

/-!
# Realization of an effective time semimeasure by a stopping machine

Blueprint 03 §5 (Lemmas R1, R2), F4 `timeSemimeasure_realization` and the characterization at the
end of 03 §5.  The two-certificate controller `realizeController ρ`, at the consumed pair `(x, q)`,
uses `|q|` as its round counter and scans the allocator tables of all stages `≤ |q|`: an atom label
of `x` that is a prefix of `q` is an `A_x^∞` certificate (halt); an atom label of a strict extension
of `x` that is a prefix of `q` is a `D_x` certificate (read one input bit); otherwise it requests
one more random bit.  Lemma R1 says a certificate is eventually discovered when the random tape
lies in the corresponding event; Lemma R2 says the halting event at `z` is exactly the seed event
`A_z^∞`, so the stopping probability is the limit mass `requestLimit ρ z`.

The realization asserts equality of stopping events and probabilities only, never a witness of a
given length (F4, "crucial limitation"): the controller may read more random bits than the depth of
the certifying cylinder.
-/

namespace Kolmogorov

open scoped ENNReal

/-- Stage-`s` certificate of `A_x^∞` on the consumed random prefix `q`: some atom label of `x` at
stage `s` is a prefix of `q`. Blueprint 03 §5 (certificates). -/
def hasSeedCertificate (ρ : RequestStream) (s : ℕ) (x q : BitString) : Bool :=
  (seedLabels ρ s x).any fun p => decide (p <+: q)

/-- Stage-`s` certificate of `D_x` on the consumed random prefix `q`: some atom label of a strict
extension of `x` at stage `s` is a prefix of `q`. Blueprint 03 §5 (certificates). -/
def hasDescendantCertificate (ρ : RequestStream) (s : ℕ) (x q : BitString) : Bool :=
  ((allocRun ρ s).table.map Prod.fst).any fun y =>
    decide (x <+: y ∧ x ≠ y) && hasSeedCertificate ρ s y q

/-- The two-certificate controller `R_ν` of the stream `ρ`: at the consumed pair `(x, q)`, with
round counter `|q|`, scan the stages `s ≤ |q|`; an `A_x^∞` certificate halts, otherwise a `D_x`
certificate reads one input bit, otherwise one more random bit is requested.  Total (never
`Part.none`).
Blueprint 03 §5 (construction of `R_ν`). -/
def realizeController (ρ : RequestStream) : StoppingController := fun xq =>
  Part.some <|
    if (List.range (xq.2.length + 1)).any fun s => hasSeedCertificate ρ s xq.1 xq.2 then
      StopAction.halt
    else if (List.range (xq.2.length + 1)).any fun s => hasDescendantCertificate ρ s xq.1 xq.2 then
      StopAction.readInput
    else StopAction.readRandom

/-! ### Compiling the controller (Lemma R2, last paragraph) -/

/-- The prefix test on bit strings is primitive recursive (`v <+: w` iff `w.take |v| = v`). -/
private theorem primrec_decide_prefix : Primrec₂ fun v w : BitString => decide (v <+: w) := by
  have h : Primrec fun p : BitString × BitString => decide (p.2.take p.1.length = p.1) :=
    (PrimrecRel.comp Primrec.eq (Primrec.list_take.comp Primrec.snd
      (Primrec.list_length.comp Primrec.fst)) Primrec.fst).decide
  exact h.of_eq fun p => decide_eq_decide.mpr (eq_comm.trans List.prefix_iff_eq_take.symm)

/-- The occupied strings (the keys of the allocation table) are primitive recursive in the
state. -/
private theorem primrec_tableKeys : Primrec fun st : AllocState => st.table.map Prod.fst := by
  have ht : Primrec AllocState.table :=
    (Primrec.snd.comp (Primrec.of_equiv (e := AllocState.equivProd))).of_eq fun _ => rfl
  exact Primrec.list_map ht (Primrec.fst.comp Primrec.snd).to₂

/-- `List.any` of a computable list under a computable predicate is computable. -/
private theorem computable_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).any (p a) := by
  have hstep : Computable₂ fun (a : α) (q : β × Bool) => p a q.1 || q.2 :=
    (Primrec.or.to_comp.comp (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hf (Computable.const false) hstep).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b t ih => simp [List.any_cons, ih]

/-- The seed-certificate test is computable in the stage, the input prefix and the random prefix.
Blueprint 03 §5 (certificates are found by finite enumeration steps). -/
private theorem computable_hasSeedCertificate {ρ : RequestStream} (hρ : Computable ρ) :
    Computable fun a : ℕ × BitString × BitString => hasSeedCertificate ρ a.1 a.2.1 a.2.2 := by
  have hg : Computable fun a : ℕ × BitString × BitString => (a.1, a.2.1) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hl := Computable.comp (seedLabels_computable hρ) hg
  have hq : Computable fun b : (ℕ × BitString × BitString) × BitString => (b.2, b.1.2.2) :=
    Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hd : Computable fun p : BitString × BitString => decide (p.1 <+: p.2) :=
    primrec_decide_prefix.to_comp
  have hp := (Computable.comp hd hq).to₂
  exact (computable_list_any hl hp).of_eq fun _ => rfl

/-- The descendant-certificate test is computable in the stage, the input prefix and the random
prefix. Blueprint 03 §5 (certificates are found by finite enumeration steps). -/
private theorem computable_hasDescendantCertificate {ρ : RequestStream} (hρ : Computable ρ) :
    Computable fun a : ℕ × BitString × BitString =>
      hasDescendantCertificate ρ a.1 a.2.1 a.2.2 := by
  have hrun := Computable.comp (allocRun_computable hρ)
    (Computable.fst : Computable fun a : ℕ × BitString × BitString => a.1)
  have hkeys := Computable.comp primrec_tableKeys.to_comp hrun
  have hne : Primrec fun p : BitString × BitString => decide (p.1 <+: p.2 ∧ p.1 ≠ p.2) := by
    have h : Primrec fun p : BitString × BitString =>
        decide (p.1 <+: p.2) && !decide (p.1 = p.2) :=
      Primrec.and.comp primrec_decide_prefix (Primrec.not.comp Primrec.eq.decide)
    exact h.of_eq fun p => by simp
  have hpair : Computable fun b : (ℕ × BitString × BitString) × BitString => (b.1.2.1, b.2) :=
    (Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd
  have hsub : Computable fun b : (ℕ × BitString × BitString) × BitString =>
      (b.1.1, b.2, b.1.2.2) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hand : Computable fun p : Bool × Bool => p.1 && p.2 := Primrec.and.to_comp
  have hp := (Computable.comp hand (Computable.pair (Computable.comp hne.to_comp hpair)
    (Computable.comp (computable_hasSeedCertificate hρ) hsub))).to₂
  exact (computable_list_any hkeys hp).of_eq fun _ => rfl

/-- The controller of a computable stream is partial recursive (in fact total computable); the
compilation into the controller representation is this theorem, not an assumption.
Blueprint 03 §5 (Lemma R2, "compile this controller"). -/
theorem realizeController_partrec {ρ : RequestStream} (hρ : Computable ρ) :
    Partrec (realizeController ρ) := by
  have hrange : Computable fun xq : BitString × BitString => List.range (xq.2.length + 1) :=
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd))).to_comp
  have hargs : Computable fun a : (BitString × BitString) × ℕ => (a.2, a.1.1, a.1.2) :=
    Computable.snd.pair ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp Computable.fst))
  have hseed : Computable fun xq : BitString × BitString =>
      (List.range (xq.2.length + 1)).any fun s => hasSeedCertificate ρ s xq.1 xq.2 :=
    (computable_list_any hrange
      (Computable.comp (computable_hasSeedCertificate hρ) hargs).to₂).of_eq fun _ => rfl
  have hdesc : Computable fun xq : BitString × BitString =>
      (List.range (xq.2.length + 1)).any fun s => hasDescendantCertificate ρ s xq.1 xq.2 :=
    (computable_list_any hrange
      (Computable.comp (computable_hasDescendantCertificate hρ) hargs).to₂).of_eq fun _ => rfl
  have hf := Computable.cond hseed (Computable.const StopAction.halt) (Computable.cond hdesc
    (Computable.const StopAction.readInput) (Computable.const StopAction.readRandom))
  exact hf.partrec.of_eq fun xq => by simp only [realizeController, cond_eq_ite, PFun.coe_val]

/-! ### Certificates and the events they certify -/

/-- Two finite prefixes of one tape are nested by their lengths. -/
private theorem prefix_of_isCantorPrefix {u q : BitString} {w : CantorSeq}
    (hu : IsCantorPrefix u w) (hq : IsCantorPrefix q w) (h : u.length ≤ q.length) : u <+: q := by
  rw [isCantorPrefix_iff_cantorPrefix_eq] at hu hq
  have h1 := cantorPrefix_mono w h
  rwa [hu, hq] at h1

/-- A finite prefix of the tape `w` is a Cantor prefix of `w`. -/
private theorem isCantorPrefix_cantorPrefix (w : CantorSeq) (n : ℕ) :
    IsCantorPrefix (cantorPrefix w n) w := by
  rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]

/-- The prefix of length `j + 1` of a tape appends its bit number `j`. -/
private theorem cantorPrefix_succ (w : CantorSeq) (j : ℕ) :
    cantorPrefix w (j + 1) = cantorPrefix w j ++ [w j] := by
  unfold cantorPrefix
  rw [List.ofFn_succ_last]
  simp

/-- A string with an allocated atom is a key of the allocation table. -/
private theorem mem_keys_of_mem_atoms {st : AllocState} {y : BitString} {i : ℕ}
    (hi : i ∈ st.atoms y) : y ∈ st.table.map Prod.fst := by
  unfold AllocState.atoms at hi
  cases h : st.table.lookup y with
  | none => simp [h] at hi
  | some l =>
    obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.1 h
    rw [heq]
    simp

/-- A seed certificate is sound: a stage-`s` certificate of `x` on a prefix `q` of the tape `w`
puts `w` in the seed event `A_x^∞` (the certifying label is a prefix of `q`, hence of `w`).
Blueprint 03 §5 (certificates), R2 forward direction. -/
private theorem mem_seedEvent_of_hasSeedCertificate {ρ : RequestStream} {s : ℕ}
    {x q : BitString} {w : CantorSeq} (hq : IsCantorPrefix q w)
    (h : hasSeedCertificate ρ s x q = true) : w ∈ seedEvent ρ x := by
  obtain ⟨u, hu, huq⟩ := List.any_eq_true.1 h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
  have hpre : bitsOfNatBE (allocRun ρ s).prec i <+: q := of_decide_eq_true huq
  refine Set.mem_iUnion.2 ⟨s, Set.mem_iUnion₂.2 ⟨i, hi, fun j hj => ?_⟩⟩
  rw [hq j (lt_of_lt_of_le hj hpre.length_le)]
  exact (hpre.getElem hj).symm

/-- A descendant certificate is sound: a stage-`s` certificate of `x` on a prefix `q` of the tape
`w` puts `w` in the event `D_x`. Blueprint 03 §5 (certificates). -/
private theorem mem_descendantEvent_of_hasDescendantCertificate {ρ : RequestStream} {s : ℕ}
    {x q : BitString} {w : CantorSeq} (hq : IsCantorPrefix q w)
    (h : hasDescendantCertificate ρ s x q = true) : w ∈ descendantEvent ρ x := by
  obtain ⟨y, -, hy⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, decide_eq_true_iff] at hy
  exact Set.mem_iUnion₂.2 ⟨y, hy.1, mem_seedEvent_of_hasSeedCertificate hq hy.2⟩

/-- R1 at one stage: if the tape `w` lies in the cylinder of an atom `i` of `x` at stage `s`, then
every prefix `q` of `w` at least as long as the grid precision carries the stage-`s` seed
certificate of `x`. Blueprint 03 Lemma R1. -/
private theorem hasSeedCertificate_of_mem_atoms {ρ : RequestStream} {s i : ℕ} {x q : BitString}
    {w : CantorSeq} (hi : i ∈ (allocRun ρ s).atoms x)
    (hw : IsCantorPrefix (bitsOfNatBE (allocRun ρ s).prec i) w) (hq : IsCantorPrefix q w)
    (hlen : (allocRun ρ s).prec ≤ q.length) : hasSeedCertificate ρ s x q = true := by
  refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, decide_eq_true ?_⟩
  exact prefix_of_isCantorPrefix hw hq (by rw [length_bitsOfNatBE]; exact hlen)

/-- Lemma R1 (certificate discovery, seed event): if the random tape `w` lies in `A_x^∞`, then from
some round on every consumed prefix `q` of `w` carries an `A_x^∞` certificate at a stage `≤ |q|`.
Blueprint 03 Lemma R1. -/
theorem exists_certificate_of_mem_seedEvent {ρ : RequestStream} {x : BitString} {w : CantorSeq}
    (hw : w ∈ seedEvent ρ x) :
    ∃ t, ∀ q, IsCantorPrefix q w → t ≤ q.length →
      ∃ s ≤ q.length, hasSeedCertificate ρ s x q = true := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hw
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 hs
  refine ⟨max s (allocRun ρ s).prec, fun q hq hlen => ⟨s, (le_max_left _ _).trans hlen, ?_⟩⟩
  exact hasSeedCertificate_of_mem_atoms hi hwi hq ((le_max_right _ _).trans hlen)

/-- Lemma R1 (certificate discovery, descendant event): if the random tape `w` lies in `D_x`, then
from some round on every consumed prefix `q` of `w` carries a `D_x` certificate at a stage `≤ |q|`.
Blueprint 03 Lemma R1. -/
theorem exists_certificate_of_mem_descendantEvent {ρ : RequestStream} {x : BitString}
    {w : CantorSeq} (hw : w ∈ descendantEvent ρ x) :
    ∃ t, ∀ q, IsCantorPrefix q w → t ≤ q.length →
      ∃ s ≤ q.length, hasDescendantCertificate ρ s x q = true := by
  obtain ⟨y, hxy, hwy⟩ := Set.mem_iUnion₂.1 hw
  obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hwy
  obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 hs
  refine ⟨max s (allocRun ρ s).prec, fun q hq hlen => ⟨s, (le_max_left _ _).trans hlen, ?_⟩⟩
  refine List.any_eq_true.2 ⟨y, mem_keys_of_mem_atoms hi, ?_⟩
  rw [Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨hxy, hasSeedCertificate_of_mem_atoms hi hwi hq ((le_max_right _ _).trans hlen)⟩

/-! ### The actions of the controller -/

/-- The controller halts only on a seed certificate. Blueprint 03 §5 (construction of `R_ν`). -/
private theorem exists_hasSeedCertificate_of_halt {ρ : RequestStream} {x q : BitString}
    (h : StopAction.halt ∈ realizeController ρ (x, q)) :
    ∃ s, hasSeedCertificate ρ s x q = true := by
  simp only [realizeController, Part.mem_some_iff] at h
  split_ifs at h with h1 h2
  all_goals first
    | exact absurd h (by decide)
    | (obtain ⟨s, -, hs⟩ := List.any_eq_true.1 h1; exact ⟨s, hs⟩)

/-- The controller reads an input bit only on a descendant certificate.
Blueprint 03 §5 (construction of `R_ν`). -/
private theorem exists_hasDescendantCertificate_of_readInput {ρ : RequestStream}
    {x q : BitString} (h : StopAction.readInput ∈ realizeController ρ (x, q)) :
    ∃ s, hasDescendantCertificate ρ s x q = true := by
  simp only [realizeController, Part.mem_some_iff] at h
  split_ifs at h with h1 h2
  all_goals first
    | exact absurd h (by decide)
    | (obtain ⟨s, -, hs⟩ := List.any_eq_true.1 h2; exact ⟨s, hs⟩)

/-- A certificate of either kind at a stage `≤ |q|` ends the random requests at `(x, q)`.
Blueprint 03 §5 (construction of `R_ν`). -/
private theorem readRandom_not_mem_realizeController {ρ : RequestStream} {x q : BitString}
    {s : ℕ} (hs : s ≤ q.length)
    (h : hasSeedCertificate ρ s x q = true ∨ hasDescendantCertificate ρ s x q = true) :
    StopAction.readRandom ∉ realizeController ρ (x, q) := by
  have hmem : s ∈ List.range (q.length + 1) := List.mem_range.2 (Nat.lt_succ_of_le hs)
  simp only [realizeController, Part.mem_some_iff]
  split_ifs with h1 h2
  · exact by decide
  · exact by decide
  · rcases h with h | h
    · exact absurd (List.any_eq_true.2 ⟨s, hmem, h⟩) h1
    · exact absurd (List.any_eq_true.2 ⟨s, hmem, h⟩) h2

/-! ### Runs along a random tape -/

/-- A run of random requests along the tape `w`: if the controller requests a random bit at the
input position `x` after every prefix `cantorPrefix w j` with `n ≤ j < m`, a run on the buffer
`cantorPrefix w M` (`m ≤ M`) through `(x, cantorPrefix w n)` passes through
`(x, cantorPrefix w m)`. Blueprint 03 Lemma R2 (waiting rounds). -/
private theorem Reaches.readRandom_run {R : StoppingController} {z x : BitString}
    {w : CantorSeq} {n m M : ℕ} (hnm : n ≤ m) (hmM : m ≤ M)
    (h : Reaches R z (cantorPrefix w M) x (cantorPrefix w n))
    (hr : ∀ j, n ≤ j → j < m → StopAction.readRandom ∈ R (x, cantorPrefix w j)) :
    Reaches R z (cantorPrefix w M) x (cantorPrefix w m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ j hnj ih =>
    have hj := ih (by omega) fun i hi hij => hr i hi (by omega)
    have hlt : (cantorPrefix w j).length < (cantorPrefix w M).length := by simp; omega
    have := hj.readRandom hlt (hr j hnj (by omega))
    simp only [cantorPrefix_getElem, cantorPrefix_length] at this
    rwa [← cantorPrefix_succ] at this

/-- The first round without a random request: if a run reaches `(x, cantorPrefix w n)` on every
long buffer and the controller stops requesting random bits at `x` at some round `≥ n`, then it
reaches `(x, cantorPrefix w m)` at the first such round `m`, on every buffer
`cantorPrefix w M` with `M ≥ m`. Blueprint 03 Lemma R2 (fair waiting, R1). -/
private theorem exists_reaches_first_nonrandom {R : StoppingController} {z x : BitString}
    {w : CantorSeq} {n : ℕ}
    (hreach : ∀ M ≥ n, Reaches R z (cantorPrefix w M) x (cantorPrefix w n))
    (hex : ∃ j, n ≤ j ∧ StopAction.readRandom ∉ R (x, cantorPrefix w j)) :
    ∃ m, n ≤ m ∧ StopAction.readRandom ∉ R (x, cantorPrefix w m) ∧
      ∀ M ≥ m, Reaches R z (cantorPrefix w M) x (cantorPrefix w m) := by
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun M hM => ?_⟩
  refine (hreach M ((Nat.find_spec hex).1.trans hM)).readRandom_run (Nat.find_spec hex).1 hM ?_
  intro j hnj hj
  by_contra hno
  exact Nat.find_min hex hj ⟨hnj, hno⟩

/-- Reading the next input bit at the position `z.take k` moves the run to `z.take (k + 1)`. -/
private theorem Reaches.readInput_take {R : StoppingController} {z p q : BitString} {k : ℕ}
    (h : Reaches R z p (z.take k) q) (hk : k < z.length)
    (ha : StopAction.readInput ∈ R (z.take k, q)) : Reaches R z p (z.take (k + 1)) q := by
  have hx : (z.take k).length < z.length := by simp; omega
  have e : z.take k ++ [z[(z.take k).length]'hx] = z.take (k + 1) := by
    simp only [List.length_take, Nat.min_eq_left hk.le]
    exact List.take_concat_get' z k hk
  rw [← e]
  exact h.readInput hx ha

/-- R2, the run through the strict prefixes: for a tape `w` in `A_z^∞`, the controller reads the
input bits of `z` one by one (at a strict prefix `x` of `z` the tape lies in `D_x` and not in
`A_x^∞`, so R1 eventually yields a `D_x` certificate and no halt occurs); for every `k ≤ |z|` some
round `n` has the run at `(z.take k, cantorPrefix w n)` on all long buffers.
Blueprint 03 Lemma R2 (reverse proof). -/
private theorem reaches_take_of_mem_seedEvent {ρ : RequestStream}
    (hb : IsBudgetedRequestStream ρ) {z : BitString} {w : CantorSeq} (hw : w ∈ seedEvent ρ z) :
    ∀ k ≤ z.length, ∃ n, ∀ M ≥ n,
      Reaches (realizeController ρ) z (cantorPrefix w M) (z.take k) (cantorPrefix w n) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, fun M _ => ?_⟩
    simpa [cantorPrefix] using (Reaches.nil : Reaches (realizeController ρ) z _ [] [])
  | succ k ih =>
    intro hk
    obtain ⟨n, hn⟩ := ih (by omega)
    have hxz : z.take k <+: z := List.take_prefix k z
    have hne : z.take k ≠ z := fun h => by
      have := congrArg List.length h
      simp at this
      omega
    have hD : w ∈ descendantEvent ρ (z.take k) := Set.mem_iUnion₂.2 ⟨z, ⟨hxz, hne⟩, hw⟩
    have hA : w ∉ seedEvent ρ (z.take k) := fun hx =>
      Set.disjoint_left.1 (seedEvent_disjoint hb (Or.inl hxz) hne) hx hw
    obtain ⟨t, ht⟩ := exists_certificate_of_mem_descendantEvent hD
    have hex : ∃ j, n ≤ j ∧
        StopAction.readRandom ∉ realizeController ρ (z.take k, cantorPrefix w j) := by
      obtain ⟨s, hs, hcert⟩ :=
        ht (cantorPrefix w (max n t)) (isCantorPrefix_cantorPrefix w _) (by simp)
      exact ⟨max n t, le_max_left _ _, readRandom_not_mem_realizeController hs (Or.inr hcert)⟩
    obtain ⟨m, -, hm, hreach⟩ := exists_reaches_first_nonrandom hn hex
    have hin : StopAction.readInput ∈ realizeController ρ (z.take k, cantorPrefix w m) := by
      obtain ⟨a, ha⟩ : ∃ a, a ∈ realizeController ρ (z.take k, cantorPrefix w m) :=
        ⟨_, Part.mem_some _⟩
      cases a with
      | readInput => exact ha
      | readRandom => exact absurd ha hm
      | halt =>
        obtain ⟨s, hs⟩ := exists_hasSeedCertificate_of_halt ha
        exact absurd (mem_seedEvent_of_hasSeedCertificate (isCantorPrefix_cantorPrefix w m) hs) hA
    exact ⟨m, fun M hM => (hreach M hM).readInput_take (by omega) hin⟩

/-- Lemma R2 (exact stopping event): along a budgeted stream, the controller halts after consuming
exactly the input `z` precisely on the random tapes of the seed event `A_z^∞`.
Blueprint 03 Lemma R2. -/
theorem haltEvent_realizeController {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ)
    (z : BitString) : haltEvent (realizeController ρ) z = seedEvent ρ z := by
  ext w
  constructor
  · rintro ⟨p, hp, -, hhalt⟩
    obtain ⟨s, hs⟩ := exists_hasSeedCertificate_of_halt hhalt
    exact mem_seedEvent_of_hasSeedCertificate hp hs
  · intro hw
    obtain ⟨n, hn⟩ := reaches_take_of_mem_seedEvent hb hw z.length le_rfl
    rw [List.take_length] at hn
    obtain ⟨t, ht⟩ := exists_certificate_of_mem_seedEvent hw
    have hex : ∃ j, n ≤ j ∧
        StopAction.readRandom ∉ realizeController ρ (z, cantorPrefix w j) := by
      obtain ⟨s, hs, hcert⟩ :=
        ht (cantorPrefix w (max n t)) (isCantorPrefix_cantorPrefix w _) (by simp)
      exact ⟨max n t, le_max_left _ _, readRandom_not_mem_realizeController hs (Or.inl hcert)⟩
    obtain ⟨m, -, hm, hreach⟩ := exists_reaches_first_nonrandom hn hex
    refine ⟨cantorPrefix w m, isCantorPrefix_cantorPrefix w m, hreach m le_rfl, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, a ∈ realizeController ρ (z, cantorPrefix w m) := ⟨_, Part.mem_some _⟩
    cases a with
    | halt => exact ha
    | readRandom => exact absurd ha hm
    | readInput =>
      obtain ⟨s, hs⟩ := exists_hasDescendantCertificate_of_readInput ha
      exact absurd (mem_descendantEvent_of_hasDescendantCertificate
        (isCantorPrefix_cantorPrefix w m) hs)
        (Set.disjoint_left.1 (seedEvent_disjoint_descendantEvent hb z) hw)

/-- Lemma R2 (probabilities): along a budgeted stream, the stopping probability of the controller at
`z` is the limit mass `requestLimit ρ z`; nothing is claimed about witness lengths.
Blueprint 03 Lemma R2 (`τ_{R_ν}(z) = ν(z)`). -/
theorem stopProb_realizeController {ρ : RequestStream} (hb : IsBudgetedRequestStream ρ)
    (z : BitString) : stopProb (realizeController ρ) z = requestLimit ρ z := by
  rw [stopProb, haltEvent_realizeController hb, uniformMeasure_seedEvent hb]

/-- F4 `timeSemimeasure_realization` (index form): a computable budgeted request stream is realized
by some stopping machine of the fixed enumeration, with the same stopping probabilities at every
string. Blueprint F4 (`timeSemimeasure_realization`), 03 §5. -/
theorem exists_stoppingMachine_realizing {ρ : RequestStream} (hρ : Computable ρ)
    (hb : IsBudgetedRequestStream ρ) :
    ∃ e : ℕ, ∀ z, stopProb (stoppingMachine e) z = requestLimit ρ z := by
  obtain ⟨e, he⟩ := exists_stoppingMachine_eq (realizeController_partrec hρ)
  exact ⟨e, fun z => by rw [he]; exact stopProb_realizeController hb z⟩

/-- Effective characterization: `ν` is a lower semicomputable time semimeasure if and only if it is
the stopping-probability function of some stopping machine of the enumeration.
Blueprint 03 §5 (end: "Combining Sections 2 and 4–5"). -/
theorem isLowerSemicomputableTimeSemimeasure_iff_exists_stoppingMachine (ν : BitString → ℝ≥0∞) :
    IsLowerSemicomputableTimeSemimeasure ν ↔
      ∃ e : ℕ, ∀ z, stopProb (stoppingMachine e) z = ν z := by
  constructor
  · intro hν
    obtain ⟨ρ, hρ, hb, hlim⟩ := exists_requestStream_of_isLowerSemicomputableTimeSemimeasure hν
    obtain ⟨e, he⟩ := exists_stoppingMachine_realizing hρ hb
    exact ⟨e, fun z => (he z).trans (hlim z)⟩
  · rintro ⟨e, he⟩
    have hν : ν = stopProb (stoppingMachine e) := funext fun z => (he z).symm
    rw [hν]
    exact stopProb_stoppingMachine_isLSC e

end Kolmogorov
