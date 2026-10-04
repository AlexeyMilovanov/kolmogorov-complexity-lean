import KolmogorovMathlib.StoppingComplexity.WordGame
import KolmogorovMathlib.StoppingComplexity.Realization

/-!
# The global enumerator and the generic diagonalization theorem

Blueprint part 03, §7 (the global enumerator: no negative halting test; D1–D4) and the generic
diagonalization theorem. A computable family of winning word strategies, one per tag `c`, is
played simultaneously against the fixed universal machine by one fair enumerator: the global
stage `s` serves the tag `(Nat.unpair s).1`; a tag either *declares* the next request of its
strategy — the dyadic request `(1^c 0 ++ x, 2^{-n})` is emitted **before** any search — or
advances by one budget unit the bounded search for a witness of the universal machine on the
tagged string among the programs of length at most `b c n`. A witness, once found, is Bob's
answer and the tag's transcript grows; the absence of a witness is never decided. The requests
form one effective time semimeasure (D2), whose realization (`Realization`) is dominated by the
universal machine with one constant `a` for all tags (D4). Since every play is finite, each tag
has a request that is never answered (D3): a string `1^c 0 ++ x` with universal mass at least
`2^{-n-a}` and no witness of length `≤ b c n`, which is the generic diagonalization theorem.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The per-tag state and the enumerator (03 §7) -/

/-- The state of one tag: the answered transcript and, if a request has been declared and not
yet answered, that request with the current search budget. Blueprint 03 §7. -/
abbrev TagState := WordHistory × Option (Request × ℕ)

/-- The global state: the tag states, indexed by the tag (a missing entry is `([], none)`).
Blueprint 03 §7. -/
abbrev DiagState := List TagState

/-- The state of the tag `c`. Blueprint 03 §7. -/
def diagStateGet (st : DiagState) (c : ℕ) : TagState := st.getD c ([], none)

/-- Replace the state of the tag `c`, extending the list with default states if needed.
Blueprint 03 §7. -/
def diagStateSet (st : DiagState) (c : ℕ) (ts : TagState) : DiagState :=
  (List.range (max st.length (c + 1))).map fun i => if i = c then ts else diagStateGet st i

/-- One step of the tag `c`: with no pending request, declare the next request `(x, n)` of the
strategy — the emitted dyadic request `(1^c 0 ++ x, 1, n)` has weight `2^{-n}` and is output
before any search; with a pending request of budget `t`, run the witness search of the universal
machine on `1^c 0 ++ x` over the programs of length `≤ b c n` for `t + 1` steps: the first
program found is Bob's answer, otherwise the budget grows. Blueprint 03 §7. -/
def diagTagStep (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (c : ℕ) (st : TagState) :
    TagState × Option DyadicRequest :=
  match st.2 with
  | none =>
    let r := σ c st.1
    ((st.1, some (r, 0)), some (natCode c ++ r.1, 1, r.2))
  | some (r, t) =>
    match (boundedPrograms (b c r.2)).find?
        (fun p => univWitnessWithin (t + 1) (natCode c ++ r.1) p) with
    | some p => ((st.1 ++ [(r, p)], none), none)
    | none => ((st.1, some (r, t + 1)), none)

/-- The global stage `s` serves the tag `(Nat.unpair s).1`, so every tag is served at
infinitely many stages (fair dovetailing). Blueprint 03 §7. -/
def diagStep (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (s : ℕ) (st : DiagState) :
    DiagState × Option DyadicRequest :=
  let c := (Nat.unpair s).1
  let r := diagTagStep b σ c (diagStateGet st c)
  (diagStateSet st c r.1, r.2)

/-- The global state before the stage `s`. Blueprint 03 §7. -/
def diagState (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) : ℕ → DiagState
  | 0 => []
  | s + 1 => (diagStep b σ s (diagState b σ s)).1

/-- The global enumerator: the request stream emitted by the fair dovetailing of all tags.
Blueprint 03 §7. -/
def globalEnumerator (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) : RequestStream :=
  fun s => (diagStep b σ s (diagState b σ s)).2

/-! ### The state algebra of the enumerator -/

/-- Reading a tag after replacing one: the replaced tag has the new state, every other tag keeps
its state. Blueprint 03 §7. -/
private theorem diagStateGet_diagStateSet (st : DiagState) (c : ℕ) (ts : TagState) (c' : ℕ) :
    diagStateGet (diagStateSet st c ts) c' = if c' = c then ts else diagStateGet st c' := by
  simp only [diagStateSet, diagStateGet, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hc : c' < max st.length (c + 1)
  · rw [List.getElem?_range hc]
    rfl
  · simp only [not_lt, max_le_iff] at hc
    rw [ite_eq_right (by omega), List.getElem?_eq_none (l := List.range _) (by simp; omega),
      List.getElem?_eq_none (l := st) hc.1]
    rfl

/-- One stage of the enumerator changes only the served tag `(Nat.unpair s).1`, by one tag step.
Blueprint 03 §7 (fair dovetailing). -/
private theorem diagState_succ_get (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (s c : ℕ) :
    diagStateGet (diagState b σ (s + 1)) c =
      if c = (Nat.unpair s).1 then (diagTagStep b σ c (diagStateGet (diagState b σ s) c)).1
      else diagStateGet (diagState b σ s) c := by
  simp only [diagState, diagStep, diagStateGet_diagStateSet]
  split_ifs with h
  · subst h
    rfl
  · rfl

/-- A tag step emits a request exactly when nothing is pending, and the emitted request is the
tagged strategy move `(1^c 0 ++ x, 1, n)` at the current transcript (emit before search).
Blueprint 03 §7. -/
private theorem diagTagStep_snd_eq_some {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {c : ℕ}
    {ts : TagState} {r : DyadicRequest} (h : (diagTagStep b σ c ts).2 = some r) :
    ts.2 = none ∧ r = (natCode c ++ (σ c ts.1).1, 1, (σ c ts.1).2) := by
  obtain ⟨H, o⟩ := ts
  cases o with
  | none =>
    simp only [diagTagStep, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩
  | some rt =>
    simp only [diagTagStep] at h
    split at h <;> simp at h

/-- The request lifecycle in one tag step: a pending request stays pending with a larger search
budget, or it is answered by a word `p` appended to the transcript and nothing is pending.
Blueprint 03 §7 (steps 2–4). -/
private theorem diagTagStep_of_pending (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (c : ℕ)
    (H : WordHistory) (r : Request) (t : ℕ) :
    (diagTagStep b σ c (H, some (r, t))).1 = (H, some (r, t + 1)) ∨
      ∃ p, (diagTagStep b σ c (H, some (r, t))).1 = (H ++ [(r, p)], none) := by
  simp only [diagTagStep]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- The transcript of a tag only grows along one step. Blueprint 03 §7. -/
private theorem transcript_prefix_diagTagStep (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (c : ℕ)
    (ts : TagState) : ts.1 <+: (diagTagStep b σ c ts).1.1 := by
  obtain ⟨H, o⟩ := ts
  cases o with
  | none => exact List.prefix_rfl
  | some rt =>
    rcases diagTagStep_of_pending b σ c H rt.1 rt.2 with h | ⟨p, h⟩
    · rw [h]
    · rw [h]
      exact List.prefix_append _ _

/-- The transcripts of a tag are prefix-monotone in the stage. Blueprint 03 §7 (D2, D3). -/
private theorem diagState_transcript_mono (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (c : ℕ)
    {s s' : ℕ} (hss' : s ≤ s') :
    (diagStateGet (diagState b σ s) c).1 <+: (diagStateGet (diagState b σ s') c).1 := by
  induction s', hss' using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ j _ ih =>
    refine ih.trans ?_
    rw [diagState_succ_get]
    split_ifs with h
    · exact transcript_prefix_diagTagStep b σ c _
    · exact List.prefix_rfl

/-- A pending request stays pending, with the same transcript, until it is answered; once
answered, the answer extends the transcript at all later stages. Blueprint 03 §7 (request
lifecycle). -/
private theorem diagState_pending_lifecycle (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) {c s : ℕ}
    {H : WordHistory} {r : Request} {t : ℕ}
    (hs : diagStateGet (diagState b σ s) c = (H, some (r, t))) {s' : ℕ} (hss' : s ≤ s') :
    (∃ t' ≥ t, diagStateGet (diagState b σ s') c = (H, some (r, t'))) ∨
      ∃ p, H ++ [(r, p)] <+: (diagStateGet (diagState b σ s') c).1 := by
  induction s', hss' using Nat.le_induction with
  | base => exact Or.inl ⟨t, le_rfl, hs⟩
  | succ j hsj ih =>
    rcases ih with ⟨t', htt', ht'⟩ | ⟨p, hp⟩
    · rw [diagState_succ_get]
      split_ifs with h
      · rw [ht']
        rcases diagTagStep_of_pending b σ c H r t' with h1 | ⟨p, h1⟩
        · exact Or.inl ⟨t' + 1, by omega, h1⟩
        · rw [h1]
          exact Or.inr ⟨p, List.prefix_rfl⟩
      · exact Or.inl ⟨t', htt', ht'⟩
    · exact Or.inr ⟨p, hp.trans (diagState_transcript_mono b σ c (Nat.le_succ j))⟩

/-- The emission at a stage: the enumerator outputs a request exactly when the served tag has
nothing pending, and it is the tagged strategy move at the current transcript. Blueprint 03 §7. -/
private theorem globalEnumerator_eq_some_iff {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {s : ℕ}
    {r : DyadicRequest} (h : globalEnumerator b σ s = some r) :
    (diagStateGet (diagState b σ s) (Nat.unpair s).1).2 = none ∧
      r = (natCode (Nat.unpair s).1 ++
        (σ (Nat.unpair s).1 (diagStateGet (diagState b σ s) (Nat.unpair s).1).1).1, 1,
        (σ (Nat.unpair s).1 (diagStateGet (diagState b σ s) (Nat.unpair s).1).1).2) :=
  diagTagStep_snd_eq_some h

/-! ### The tag invariant (D1) -/

/-- The tag invariant of the enumerator: the transcript is a reachable history of the tag's
strategy, every recorded answer is a witness of the universal machine at the tagged vertex, and
a pending request is the strategy's move at the transcript. Blueprint 03 D1. -/
private def TagInvariant (b : ℕ → ℕ) (σ : WordStrategy) (c : ℕ) (ts : TagState) : Prop :=
  ReachableWordHistory b σ ts.1 ∧ (∀ e ∈ ts.1, Witness univStopping (natCode c ++ e.1.1) e.2) ∧
    ∀ r t, ts.2 = some (r, t) → r = σ ts.1

/-- One tag step preserves the tag invariant: a found answer has length `≤ b n`
(`boundedPrograms`), is a witness (`univWitness_iff_exists_univWitnessWithin`), and is
incomparable with the answers at distinct comparable vertices because the tagged strings are
distinct and comparable (M3, `Witness.isIncomparable_of_ne`). Blueprint 03 D1. -/
private theorem TagInvariant.diagTagStep {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {c : ℕ}
    {ts : TagState} (hts : TagInvariant (b c) (σ c) c ts) :
    TagInvariant (b c) (σ c) c (diagTagStep b σ c ts).1 := by
  obtain ⟨H, o⟩ := ts
  obtain ⟨hreach, hwit, hpend⟩ := hts
  cases o with
  | none =>
    refine ⟨hreach, hwit, fun r t hrt => ?_⟩
    simp only [Kolmogorov.diagTagStep, Option.some.injEq, Prod.mk.injEq] at hrt
    exact hrt.1.symm
  | some rt =>
    obtain ⟨r, t⟩ := rt
    have hr : r = σ c H := hpend r t rfl
    simp only [Kolmogorov.diagTagStep]
    split
    · next p hfind =>
      have hpmem := List.mem_of_find?_eq_some hfind
      have hW : Witness univStopping (natCode c ++ r.1) p :=
        (univWitness_iff_exists_univWitnessWithin _ _).2 ⟨_, List.find?_some hfind⟩
      refine ⟨?_, ?_, fun r' t' h' => by simp at h'⟩
      · subst hr
        refine hreach.snoc ⟨(mem_boundedPrograms_iff _ _).1 hpmem, fun e he hcomp hne => ?_⟩
        refine (hwit e he).isIncomparable_of_ne hW ?_ fun heq => hne (List.append_cancel_left heq)
        exact hcomp.imp (List.prefix_append_right_inj _).2 (List.prefix_append_right_inj _).2
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hwit e he
        · rw [List.mem_singleton] at he
          subst he
          exact hW
    · exact ⟨hreach, hwit, fun r' t' h' => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        exact h'.1 ▸ hr⟩

/-- Every tag state at every stage satisfies the tag invariant. Blueprint 03 D1. -/
private theorem diagState_tagInvariant (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (s c : ℕ) :
    TagInvariant (b c) (σ c) c (diagStateGet (diagState b σ s) c) := by
  induction s with
  | zero =>
    refine ⟨.nil, fun e he => ?_, fun r t h => ?_⟩
    · simp [diagState, diagStateGet] at he
    · simp [diagState, diagStateGet] at h
  | succ s ih =>
    rw [diagState_succ_get]
    split_ifs with h
    · exact ih.diagTagStep
    · exact ih

/-! ### Computability of the enumerator -/

/-- `List.find?` of a computable list under a computable predicate is computable. -/
private theorem computable_list_find? {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable fun a => (f a).find? (p a) := by
  have hstep : Computable₂ fun (a : α) (q : β × Option β) => bif p a q.1 then some q.1 else q.2 :=
    (Computable.cond (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.option_some.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hf (Computable.const none) hstep).of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b t ih =>
    simp at ih
    cases h : p a b <;> simp [h, ih]

/-- One tag step is computable in the tag and the tag state: the declaration evaluates the
strategy, the search is a `find?` over the finite list of programs of length `≤ b c n`.
Blueprint 03 §7. -/
private theorem computable_diagTagStep {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy}
    (hb : Computable₂ b) (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2) :
    Computable fun a : ℕ × TagState => diagTagStep b σ a.1 a.2 := by
  have hpair1 : Computable fun a : ℕ × TagState => (a.1, a.2.1) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hsig := Computable.comp hσ hpair1
  have hdecl : Computable fun a : ℕ × TagState =>
      (((a.2.1, some (σ a.1 a.2.1, 0)), some (natCode a.1 ++ (σ a.1 a.2.1).1, 1,
        (σ a.1 a.2.1).2)) : TagState × Option DyadicRequest) :=
    ((Computable.fst.comp Computable.snd).pair
      (Computable.option_some.comp (hsig.pair (Computable.const 0)))).pair
      (Computable.option_some.comp ((Primrec.list_append.to_comp.comp
        (primrec_natCode.to_comp.comp Computable.fst) (Computable.fst.comp hsig)).pair
        ((Computable.const 1).pair (Computable.snd.comp hsig))))
  have hl : Computable fun q : (ℕ × TagState) × (Request × ℕ) =>
      boundedPrograms (b q.1.1 q.2.1.2) :=
    Computable.boundedPrograms.comp (hb.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp (Computable.fst.comp Computable.snd)))
  have htup : Computable fun x : ((ℕ × TagState) × (Request × ℕ)) × BitString =>
      (x.1.2.2 + 1, natCode x.1.1.1 ++ x.1.2.1.1, x.2) :=
    (Computable.succ.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
      ((Primrec.list_append.to_comp.comp (primrec_natCode.to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst)))
        (Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.fst)))).pair
        Computable.snd)
  have hpred := Computable.comp primrec_univWitnessWithin.to_comp htup
  have hfind := computable_list_find? hl hpred.to₂
  have hwait : Computable fun q : (ℕ × TagState) × (Request × ℕ) =>
      (((q.1.2.1, some (q.2.1, q.2.2 + 1)), none) : TagState × Option DyadicRequest) :=
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.option_some.comp ((Computable.fst.comp Computable.snd).pair
        (Computable.succ.comp (Computable.snd.comp Computable.snd))))).pair
      (Computable.const none)
  have hans : Computable₂ fun (q : (ℕ × TagState) × (Request × ℕ)) (p : BitString) =>
      (((q.1.2.1 ++ [(q.2.1, p)], none), none) : TagState × Option DyadicRequest) :=
    (((Primrec.list_append.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
      (Computable.list_cons.comp ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        Computable.snd) (Computable.const []))).pair (Computable.const none)).pair
      (Computable.const none)).to₂
  have hsearch := Computable.option_casesOn hfind hwait hans
  have hall := Computable.option_casesOn (Computable.snd.comp Computable.snd) hdecl
    hsearch.to₂
  refine hall.of_eq fun a => ?_
  rcases a with ⟨c, H, _ | ⟨r, t⟩⟩
  · rfl
  · simp only [diagTagStep]
    cases (boundedPrograms (b c r.2)).find? fun p => univWitnessWithin (t + 1) (natCode c ++ r.1) p
      <;> rfl

/-- One global stage is computable in the stage and the global state: reading and replacing a
tag state are list operations. Blueprint 03 §7. -/
private theorem computable_diagStep {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy}
    (hb : Computable₂ b) (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2) :
    Computable fun p : ℕ × DiagState => diagStep b σ p.1 p.2 := by
  have hc : Computable fun p : ℕ × DiagState => (Nat.unpair p.1).1 :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.fst)
  have hget : Computable₂ diagStateGet :=
    (Primrec.list_getD (([], none) : TagState)).to_comp.of_eq fun _ => rfl
  have hts : Computable fun p : ℕ × DiagState => diagStateGet p.2 (Nat.unpair p.1).1 :=
    hget.comp Computable.snd hc
  have htag := Computable.comp (computable_diagTagStep hb hσ) (hc.pair hts)
  have hset : Computable fun a : DiagState × ℕ × TagState => diagStateSet a.1 a.2.1 a.2.2 := by
    have hlen : Computable fun a : DiagState × ℕ × TagState =>
        List.range (max a.1.length (a.2.1 + 1)) :=
      Primrec.list_range.to_comp.comp (Primrec.nat_max.to_comp.comp
        (Primrec.list_length.to_comp.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
    have heq : Computable fun x : (DiagState × ℕ × TagState) × ℕ => decide (x.2 = x.1.2.1) :=
      (Primrec.eq.decide : Primrec₂ fun m n : ℕ => decide (m = n)).to_comp.comp Computable.snd
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have hval : Computable fun x : (DiagState × ℕ × TagState) × ℕ =>
        bif decide (x.2 = x.1.2.1) then x.1.2.2 else diagStateGet x.1.1 x.2 :=
      Computable.cond heq (Computable.snd.comp (Computable.snd.comp Computable.fst))
        (hget.comp (Computable.fst.comp Computable.fst) Computable.snd)
    refine (Computable.list_map hlen hval.to₂).of_eq fun a => ?_
    simp only [diagStateSet, Bool.cond_decide]
  have hres := hset.comp (Computable.snd.pair (hc.pair (Computable.fst.comp htag)))
  exact (hres.pair (Computable.snd.comp htag)).of_eq fun _ => rfl

/-- The enumerator is computable when the length bounds and the strategy family are.
Blueprint 03 §7. -/
theorem globalEnumerator_computable {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} (hb : Computable₂ b)
    (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2) :
    Computable (globalEnumerator b σ) := by
  have hstep := computable_diagStep hb hσ
  have hrec : Computable fun s : ℕ => Nat.rec (motive := fun _ => DiagState) []
      (fun y IH => (diagStep b σ y IH).1) s :=
    Computable.nat_rec Computable.id (Computable.const ([] : DiagState))
      (Computable.fst.comp (Computable.comp hstep Computable.snd)).to₂
  have hstate : Computable (diagState b σ) := hrec.of_eq fun s => by
    induction s with
    | zero => rfl
    | succ s ih => simp only [diagState, ← ih]
  exact (Computable.snd.comp (Computable.comp hstep (Computable.id.pair hstate))).of_eq
    fun _ => rfl

/-! ### D1–D4 -/

/-- **D1** (generated answers are legal): the transcript of every tag at every stage is a
reachable history of that tag's strategy — every found witness has length `≤ b c n` and,
by the incomparability of witnesses of distinct comparable inputs (M3), is a legal word answer.
Blueprint 03 D1. -/
theorem diagState_reachable (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (s c : ℕ) :
    ReachableWordHistory (b c) (σ c) (diagStateGet (diagState b σ s) c).1 :=
  (diagState_tagInvariant b σ s c).1

/-- Every emitted request is a tagged string with the weight of its exponent.
Blueprint 03 §7. -/
theorem globalEnumerator_eq_some {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {s : ℕ}
    {r : DyadicRequest} (h : globalEnumerator b σ s = some r) :
    ∃ c x n, r = (natCode c ++ x, 1, n) :=
  ⟨_, _, _, (globalEnumerator_eq_some_iff h).2⟩

/-- For a winning family a string is requested at most once: two stages that emit requests at
the same word coincide. The winning hypothesis is needed: its fresh-vertex clause forbids a tag
to declare an already answered vertex again. Blueprint 03 §7 / D2. -/
theorem globalEnumerator_stage_unique {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hwin : IsWinningWordFamily b σ T) {s s' : ℕ} {z : BitString} {k n k' n' : ℕ}
    (h : globalEnumerator b σ s = some (z, k, n))
    (h' : globalEnumerator b σ s' = some (z, k', n')) : s = s' := by
  wlog hle : s ≤ s' generalizing s s' k n k' n'
  · exact (this h' h (le_of_not_ge hle)).symm
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  exfalso
  obtain ⟨hnone, hr⟩ := globalEnumerator_eq_some_iff h
  obtain ⟨hnone', hr'⟩ := globalEnumerator_eq_some_iff h'
  set c := (Nat.unpair s).1
  set H := (diagStateGet (diagState b σ s) c).1
  set H' := (diagStateGet (diagState b σ s') (Nat.unpair s').1).1
  have e1 := congrArg Prod.fst hr
  have e2 := congrArg Prod.fst hr'
  simp only at e1 e2
  have hz := e1.symm.trans e2
  obtain ⟨hc, hx⟩ := natCode_append_inj hz
  have hpend : diagStateGet (diagState b σ (s + 1)) c = (H, some (σ c H, 0)) := by
    rw [diagState_succ_get, ite_eq_left rfl, show diagStateGet (diagState b σ s) c = (H, none) from
      Prod.ext rfl hnone]
    rfl
  rw [← hc] at hnone' hx
  rcases diagState_pending_lifecycle b σ hpend hlt with ⟨t', -, ht'⟩ | ⟨p, hp⟩
  · rw [ht'] at hnone'
    exact Option.some_ne_none _ hnone'
  · have hmem : (σ c H).1 ∈ H'.map fun e => e.1.1 := by
      refine List.mem_map.2 ⟨(σ c H, p), ?_, rfl⟩
      rw [show H' = (diagStateGet (diagState b σ s') c).1 by rw [hc]]
      exact hp.subset (List.mem_append_right _ (List.mem_singleton_self _))
    have hfresh := (hwin c _ (diagState_reachable b σ s' c)).2.1
    rw [show (diagStateGet (diagState b σ s') c).1 = H' by rw [hc]] at hfresh
    rw [hx] at hmem
    exact hfresh hmem

/-! ### D2: the path budget of the enumerator -/

/-- The requests declared by the tag `c` before the stage `s`: the requests of its transcript
followed by the pending one. Blueprint 03 D2. -/
private def tagEmitted (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) (s c : ℕ) : List Request :=
  (diagStateGet (diagState b σ s) c).1.map Prod.fst ++
    ((diagStateGet (diagState b σ s) c).2.map Prod.fst).toList

/-- One more stage adds to the cumulative load along `u` the weight of the request of that
stage when its word is a prefix of `u` (the prefixes of `u` have distinct lengths).
Blueprint 01 F3 (F3-STREAM). -/
private theorem streamStageLoad_succ (ρ : RequestStream) (s : ℕ) (u : BitString) :
    streamStageLoad ρ (s + 1) u = streamStageLoad ρ s u +
      (((ρ s).toList.filter fun r => decide (r.1 <+: u)).map DyadicRequest.weight).sum := by
  have hmass : ∀ z, streamStageMass ρ (s + 1) z = streamStageMass ρ s z +
      (((ρ s).toList.filter fun r => decide (r.1 = z)).map DyadicRequest.weight).sum := by
    intro z
    simp only [streamStageMass, List.range_succ, List.filterMap_append, List.filter_append,
      List.map_append, List.sum_append]
    cases h : ρ s <;> simp [h]
  unfold streamStageLoad
  simp only [hmass, Finset.sum_add_distrib]
  congr 1
  cases h : ρ s with
  | none => simp
  | some r =>
    have key : ∀ k ∈ Finset.range (u.length + 1),
        ((([r].filter fun r' => decide (r'.1 = u.take k)).map DyadicRequest.weight).sum) =
          if r.1.length = k then (if r.1 <+: u then r.weight else 0) else 0 := by
      intro k hk
      have hk' : k ≤ u.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      by_cases h1 : r.1 = u.take k
      · have hlen : r.1.length = k := by rw [h1, List.length_take]; omega
        have hpre : r.1 <+: u := h1 ▸ List.take_prefix k u
        rw [ite_eq_left hlen, ite_eq_left hpre]
        simp [h1]
      · have : ¬ (r.1.length = k ∧ r.1 <+: u) := fun ⟨hl, hp⟩ =>
          h1 (hl ▸ List.prefix_iff_eq_take.1 hp)
        by_cases hl : r.1.length = k
        · simp [h1, hl, show ¬ r.1 <+: u from fun hp => this ⟨hl, hp⟩]
        · simp [h1, hl]
    simp only [Option.toList_some]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq]
    by_cases hr : r.1 <+: u
    · simp [hr, Nat.lt_succ_of_le hr.length_le]
    · simp [hr]

/-- A request of another tag never lies on a path below the tag `c`: the words `1^c' 0 ++ x'`
and `1^c 0 ++ v` are incomparable unless `c' = c`. Blueprint 03 D2 ("an input path enters at
most one tag subtree"). -/
private theorem not_prefix_natCode_append {c c' : ℕ} (hc : c' ≠ c) (x v : BitString) :
    ¬ natCode c' ++ x <+: natCode c ++ v := by
  intro h
  have h1 : natCode c' <+: natCode c ++ v := (List.prefix_append _ _).trans h
  rcases List.prefix_or_prefix_of_prefix h1 (List.prefix_append (natCode c) v) with h2 | h2
  · exact hc (natCode_prefix_iff.1 h2)
  · exact hc (natCode_prefix_iff.1 h2).symm

/-- The cumulative load of the enumerator along a path below the tag `c` is the load of the
requests declared by that tag so far (the pending one included). Blueprint 03 D2. -/
private theorem streamStageLoad_globalEnumerator (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy)
    (s c : ℕ) (v : BitString) :
    streamStageLoad (globalEnumerator b σ) s (natCode c ++ v) = load (tagEmitted b σ s c) v := by
  induction s with
  | zero => simp [streamStageLoad, streamStageMass, tagEmitted, diagState, diagStateGet, load]
  | succ s ih =>
    rw [streamStageLoad_succ, ih]
    have hglob : globalEnumerator b σ s = (diagTagStep b σ (Nat.unpair s).1
        (diagStateGet (diagState b σ s) (Nat.unpair s).1)).2 := rfl
    by_cases hc : c = (Nat.unpair s).1
    · subst hc
      rcases hts : diagStateGet (diagState b σ s) (Nat.unpair s).1 with ⟨H, _ | ⟨r, t⟩⟩
      · rw [hts] at hglob
        have hnext : diagStateGet (diagState b σ (s + 1)) (Nat.unpair s).1 =
            (H, some (σ (Nat.unpair s).1 H, 0)) := by
          rw [diagState_succ_get, ite_eq_left rfl, hts]
          rfl
        simp only [tagEmitted, hts, hnext, hglob, diagTagStep, Option.map_none,
          Option.toList_none, List.append_nil, Option.map_some, Option.toList_some, load_append,
          Option.toList_some, List.filter_cons, List.filter_nil, List.prefix_append_right_inj]
        congr 1
        by_cases hp : (σ (Nat.unpair s).1 H).1 <+: v
        · simp [hp, load, DyadicRequest.weight, requestWeight]
        · simp [hp, load]
      · have hnone : globalEnumerator b σ s = none := by
          rw [hglob, hts]
          simp only [diagTagStep]
          split <;> rfl
        have hsame : tagEmitted b σ (s + 1) (Nat.unpair s).1 =
            tagEmitted b σ s (Nat.unpair s).1 := by
          rw [tagEmitted, tagEmitted, diagState_succ_get, ite_eq_left rfl, hts]
          rcases diagTagStep_of_pending b σ (Nat.unpair s).1 H r t with h1 | ⟨p, h1⟩ <;>
            simp [h1]
        rw [hnone, hsame]
        simp
    · have hsame : tagEmitted b σ (s + 1) c = tagEmitted b σ s c := by
        simp only [tagEmitted, diagState_succ_get, ite_eq_right hc]
      rw [hsame]
      cases hρ : globalEnumerator b σ s with
      | none => simp
      | some r =>
        obtain ⟨-, hr⟩ := globalEnumerator_eq_some_iff hρ
        have hnp : ¬ r.1 <+: natCode c ++ v := by
          rw [hr]
          exact not_prefix_natCode_append (Ne.symm hc) _ _
        simp [hnp]

/-- **D2** (the generated requests form one effective time semimeasure): for a winning family
the enumerator is budgeted — the requests of one tag load every path by at most `1` (the
strategy's budget, including the pending request) and the tags live under the prefix-free
codes `1^c 0`. Blueprint 03 D2. -/
theorem globalEnumerator_budgeted {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hwin : IsWinningWordFamily b σ T) : IsBudgetedRequestStream (globalEnumerator b σ) := by
  refine isBudgetedRequestStream_of_tagged (fun s r hr => ?_) fun c s v => ?_
  · obtain ⟨c, x, n, rfl⟩ := globalEnumerator_eq_some hr
    exact ⟨c, x, rfl⟩
  · rw [streamStageLoad_globalEnumerator]
    obtain ⟨hreach, -, hpend⟩ := diagState_tagInvariant b σ s c
    set H := (diagStateGet (diagState b σ s) c).1
    have hbud := (hwin c H hreach).2.2.1 v
    refine le_trans ?_ hbud
    unfold tagEmitted
    rcases hts : (diagStateGet (diagState b σ s) c).2 with _ | ⟨r, t⟩
    · simp only [Option.map_none, Option.toList_none, List.append_nil, load_append]
      exact le_add_of_nonneg_right (load_nonneg _ _)
    · rw [hpend r t hts]
      rfl

/-! ### D3: the eventually pending request of a tag -/

/-- For a winning family the transcript of a tag stabilizes: it is prefix-monotone in the stage
and its length stays below the request bound `T c` of the reachable histories (D1). -/
private theorem exists_transcript_stable {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hwin : IsWinningWordFamily b σ T) (c : ℕ) :
    ∃ s₀, ∀ s ≥ s₀,
      (diagStateGet (diagState b σ s) c).1 = (diagStateGet (diagState b σ s₀) c).1 := by
  let L : ℕ → ℕ := fun s => (diagStateGet (diagState b σ s) c).1.length
  have hbdd : BddAbove (Set.range L) := by
    refine ⟨T c, ?_⟩
    rintro _ ⟨s, rfl⟩
    have := (hwin c _ (diagState_reachable b σ s c)).2.2.2
    simp only [L]
    omega
  obtain ⟨s₀, hs₀⟩ := Nat.sSup_mem (Set.range_nonempty L) hbdd
  refine ⟨s₀, fun s hs => ?_⟩
  have hpre := diagState_transcript_mono b σ c hs
  have hle : L s ≤ L s₀ := hs₀ ▸ le_csSup hbdd ⟨s, rfl⟩
  exact (hpre.eq_of_length (le_antisymm hpre.length_le hle)).symm

/-- A served pending request whose transcript does not grow is not answered: its search
budget grows by one, and no program of length `≤ b c n` passes the bounded search at the
current budget. Blueprint 03 §7 (step 4), D3. -/
private theorem served_pending_step {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {s c : ℕ}
    {H : WordHistory} {r : Request} {t : ℕ} (hc : (Nat.unpair s).1 = c)
    (hs : diagStateGet (diagState b σ s) c = (H, some (r, t)))
    (hstab : (diagStateGet (diagState b σ (s + 1)) c).1 = H) :
    diagStateGet (diagState b σ (s + 1)) c = (H, some (r, t + 1)) ∧
      ∀ p ∈ boundedPrograms (b c r.2), univWitnessWithin (t + 1) (natCode c ++ r.1) p ≠ true := by
  rw [diagState_succ_get, ite_eq_left hc.symm, hs] at hstab ⊢
  cases hfind : (boundedPrograms (b c r.2)).find?
      (fun p => univWitnessWithin (t + 1) (natCode c ++ r.1) p) with
  | some p =>
    simp only [diagTagStep, hfind] at hstab
    have := congrArg List.length hstab
    simp at this
  | none =>
    simp only [diagTagStep, hfind]
    exact ⟨by trivial, fun p hp => List.find?_eq_none.1 hfind p hp⟩

/-- A pending request was emitted at an earlier stage, as the tagged dyadic request
`(1^c 0 ++ x, 1, n)`. Blueprint 03 §7 (step 1), D3. -/
private theorem exists_emission_of_pending (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) {s c : ℕ}
    {H : WordHistory} {r : Request} {t : ℕ}
    (hs : diagStateGet (diagState b σ s) c = (H, some (r, t))) :
    ∃ s' < s, globalEnumerator b σ s' = some (natCode c ++ r.1, 1, r.2) := by
  induction s generalizing H r t with
  | zero => simp [diagState, diagStateGet] at hs
  | succ s ih =>
    rw [diagState_succ_get] at hs
    split_ifs at hs with hc
    · have hglob : globalEnumerator b σ s =
          (diagTagStep b σ c (diagStateGet (diagState b σ s) c)).2 := by
        rw [hc]
        rfl
      rcases hts : diagStateGet (diagState b σ s) c with ⟨H0, _ | ⟨r0, t0⟩⟩
      · rw [hts] at hs hglob
        simp only [diagTagStep, Prod.mk.injEq, Option.some.injEq] at hs hglob
        refine ⟨s, Nat.lt_succ_self s, ?_⟩
        rw [hglob, ← hs.2.1]
      · rw [hts] at hs
        rcases diagTagStep_of_pending b σ c H0 r0 t0 with h1 | ⟨p, h1⟩
        · rw [h1] at hs
          simp only [Prod.mk.injEq, Option.some.injEq] at hs
          obtain ⟨rfl, rfl, -⟩ := hs
          obtain ⟨s', hs', he⟩ := ih hts
          exact ⟨s', Nat.lt_succ_of_lt hs', he⟩
        · rw [h1] at hs
          simp at hs
    · obtain ⟨s', hs', he⟩ := ih hs
      exact ⟨s', Nat.lt_succ_of_lt hs', he⟩

/-- Once the transcript of a tag is stable, a pending request stays pending with a search
budget that does not decrease. Blueprint 03 §7 (request lifecycle), D3. -/
private theorem pending_of_stable (b : ℕ → ℕ → ℕ) (σ : ℕ → WordStrategy) {c s s' : ℕ}
    {H : WordHistory} {r : Request} {t : ℕ}
    (hs : diagStateGet (diagState b σ s) c = (H, some (r, t))) (hss' : s ≤ s')
    (hstab : (diagStateGet (diagState b σ s') c).1 = H) :
    ∃ t' ≥ t, diagStateGet (diagState b σ s') c = (H, some (r, t')) := by
  rcases diagState_pending_lifecycle b σ hs hss' with h | ⟨p, hp⟩
  · exact h
  · have := hp.length_le
    rw [hstab] at this
    simp at this

/-- **D3** (a forever-unanswered request exists at every tag): since every play of a winning
family is finite, some declared request `(x, n)` of the tag `c` — reached by the strategy, with
`n ≥ 1` — is never answered: the tagged string `1^c 0 ++ x` has limit mass exactly `2^{-n}` in
the enumerator and no witness of the universal machine of length `≤ b c n`.
Blueprint 03 D3. -/
theorem exists_forever_pending {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hwin : IsWinningWordFamily b σ T) (c : ℕ) :
    ∃ (x : BitString) (n : ℕ), 1 ≤ n ∧
      (∃ h, ReachableWordHistory (b c) (σ c) h ∧ σ c h = (x, n)) ∧
      requestLimit (globalEnumerator b σ) (natCode c ++ x) = (2 : ℝ≥0∞)⁻¹ ^ n ∧
      ∀ p : BitString, p.length ≤ b c n → ¬ Witness univStopping (natCode c ++ x) p := by
  obtain ⟨s₀, hs₀⟩ := exists_transcript_stable hwin c
  set H := (diagStateGet (diagState b σ s₀) c).1 with hH
  have hreach : ReachableWordHistory (b c) (σ c) H := diagState_reachable b σ s₀ c
  have hserve : ∀ s, (Nat.unpair (Nat.pair c s)).1 = c := fun s => by rw [Nat.unpair_pair]
  have hge : ∀ s, s ≤ Nat.pair c s := fun s => Nat.right_le_pair c s
  -- after the service stage `pair c s₀` the tag is pending with the move at `H`
  obtain ⟨t₁, hp₁⟩ : ∃ t₁,
      diagStateGet (diagState b σ (Nat.pair c s₀ + 1)) c = (H, some (σ c H, t₁)) := by
    have hstab := hs₀ (Nat.pair c s₀ + 1) (by have := hge s₀; omega)
    have hinv := diagState_tagInvariant b σ (Nat.pair c s₀) c
    rcases hts : diagStateGet (diagState b σ (Nat.pair c s₀)) c with ⟨H2, _ | ⟨r2, t2⟩⟩
    · have hH2 : H2 = H := by
        rw [← hs₀ (Nat.pair c s₀) (hge s₀), hts]
      refine ⟨0, ?_⟩
      rw [diagState_succ_get, ite_eq_left (hserve s₀).symm, hts, hH2]
      rfl
    · have hH2 : H2 = H := by
        rw [← hs₀ (Nat.pair c s₀) (hge s₀), hts]
      rw [hts] at hinv
      have hr2 : r2 = σ c H2 := hinv.2.2 r2 t2 rfl
      subst hH2 hr2
      exact ⟨t2 + 1, (served_pending_step (hserve s₀) hts hstab).1⟩
  have hs₁ : s₀ ≤ Nat.pair c s₀ + 1 := by have := hge s₀; omega
  -- the search budget of the pending request grows without bound
  have hgrow : ∀ k, ∃ s ≥ s₀, ∃ t ≥ k,
      diagStateGet (diagState b σ s) c = (H, some (σ c H, t)) := by
    intro k
    induction k with
    | zero => exact ⟨_, hs₁, t₁, Nat.zero_le _, hp₁⟩
    | succ k ih =>
      obtain ⟨s, hs, t, htk, hst⟩ := ih
      obtain ⟨t', htt', hst'⟩ := pending_of_stable b σ hst (hge s)
        (hs₀ _ (hs.trans (hge s)))
      have := served_pending_step (hserve s) hst' (hs₀ _ (by have := hge s; omega))
      exact ⟨_, by have := hge s; omega, t' + 1, by omega, this.1⟩
  refine ⟨(σ c H).1, (σ c H).2, (hwin c H hreach).1, ⟨H, hreach, rfl⟩, ?_, ?_⟩
  · obtain ⟨se, -, hse⟩ := exists_emission_of_pending b σ hp₁
    refine requestLimit_eq_of_single_request hse fun s' r hr hr1 => ?_
    obtain ⟨z', k', n'⟩ := r
    simp only at hr1
    subst hr1
    exact globalEnumerator_stage_unique hwin hr hse
  · intro p hp hW
    obtain ⟨t₀, ht₀⟩ := (univWitness_iff_exists_univWitnessWithin _ _).1 hW
    obtain ⟨s, hs, t, ht, hst⟩ := hgrow t₀
    obtain ⟨t', htt', hst'⟩ := pending_of_stable b σ hst (hge s) (hs₀ _ (hs.trans (hge s)))
    have hstep := served_pending_step (hserve s) hst' (hs₀ _ (by have := hge s; omega))
    exact hstep.2 p ((mem_boundedPrograms_iff _ _).2 hp) (univWitnessWithin_mono (by omega) ht₀)

/-- **D4** (realization of the enumerator): for a winning family with computable length bounds
and computable strategies, one stopping machine `e` of the fixed enumeration realizes the
enumerator's time semimeasure: its stopping probability equals the limit mass
`requestLimit (globalEnumerator b σ)` at every string (Sections 4–5 applied to the single global
request stream). Blueprint 03 Lemma D4. -/
theorem globalEnumerator_realized {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hb : Computable₂ b) (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2)
    (hwin : IsWinningWordFamily b σ T) :
    ∃ e : ℕ, ∀ z, stopProb (stoppingMachine e) z = requestLimit (globalEnumerator b σ) z :=
  exists_stoppingMachine_realizing (globalEnumerator_computable hb hσ)
    (globalEnumerator_budgeted hwin)

/-- **D4** (one constant for all tags): for a winning family with computable length bounds and
computable strategies there is one natural `a` (the tag length `e + 1` of a realizing machine
`e`) such that `2^{-a} φ(z) ≤ M_stop(z)` for every string `z`, where `φ` is the limit mass of
the enumerator; `a` depends on the family, not on the tag or the string.
Blueprint 03 Lemma D4. -/
theorem univStopProb_ge_requestLimit {b : ℕ → ℕ → ℕ} {σ : ℕ → WordStrategy} {T : ℕ → ℕ}
    (hb : Computable₂ b) (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2)
    (hwin : IsWinningWordFamily b σ T) :
    ∃ a : ℕ, ∀ z,
      (2 : ℝ≥0∞)⁻¹ ^ a * requestLimit (globalEnumerator b σ) z ≤ univStopProb z := by
  obtain ⟨e, he⟩ := globalEnumerator_realized hb hσ hwin
  refine ⟨e + 1, fun z => ?_⟩
  rw [← he z]
  exact univStopProb_ge_stoppingMachine e z

/-- **D4 and the generic diagonalization theorem.** For a computable family of winning word
strategies with computable length bounds there is ONE constant `a` (the universal simulation
overhead of the realization of the enumerator's time semimeasure, independent of the tag)
such that every tag `c` has a request `(x, n)` reached by its strategy whose tagged string
`1^c 0 ++ x` has stopping complexity `> b c n` and universal stopping probability
`≥ 2^{-n-a}`. Blueprint 03 §7 (D4, generic diagonalization theorem). -/
theorem diagonalization (b : ℕ → ℕ → ℕ) (hb : Computable₂ b) (σ : ℕ → WordStrategy)
    (hσ : Computable fun a : ℕ × WordHistory => σ a.1 a.2) (T : ℕ → ℕ)
    (hwin : IsWinningWordFamily b σ T) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ (x : BitString) (n : ℕ),
      (∃ h, ReachableWordHistory (b c) (σ c) h ∧ σ c h = (x, n)) ∧
      (b c n : ℕ∞) < univStopComplexity (natCode c ++ x) ∧
      (2 : ℝ≥0∞)⁻¹ ^ (n + a) ≤ univStopProb (natCode c ++ x) := by
  obtain ⟨a, ha⟩ := univStopProb_ge_requestLimit hb hσ hwin
  refine ⟨a, fun c => ?_⟩
  obtain ⟨x, n, -, hreach, hmass, hnowit⟩ := exists_forever_pending hwin c
  refine ⟨x, n, hreach, ?_, ?_⟩
  · have hle : ((b c n : ℕ) : ℕ∞) + 1 ≤ univStopComplexity (natCode c ++ x) := by
      unfold univStopComplexity stopComplexity
      refine le_sInf fun m hm => ?_
      obtain ⟨p, hp, rfl⟩ := hm
      have hlt : b c n < p.length := lt_of_not_ge fun hle => hnowit p hle hp
      exact_mod_cast Nat.succ_le_of_lt hlt
    exact (ENat.add_one_le_iff (ENat.natCast_ne_top _)).1 hle
  · calc (2 : ℝ≥0∞)⁻¹ ^ (n + a) = (2 : ℝ≥0∞)⁻¹ ^ a * requestLimit (globalEnumerator b σ)
          (natCode c ++ x) := by rw [hmass, pow_add, mul_comm]
      _ ≤ univStopProb (natCode c ++ x) := ha _

end Kolmogorov
