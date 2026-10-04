import KolmogorovMathlib.MonotoneComplexity.RobustMachine

/-!
# Converse direction of Theorem 82: every computable stream map is a robust machine

`RobustMachine.lean` proves the forward half of Theorem 82: the denotation of a
robust machine (a computable, prefix-monotone, rate-limited `step` function on
timing histories whose behaviour does not depend on the schedule) is a
computable map on streams.

This file proves the converse: for every `f : BitStream → BitStream` with
`IsComputableStreamMap f` there is a `step` function satisfying all the robust
machine laws whose denotation `robustDenotation step` is exactly `f`.

The machine is a *bounded enumerator*.  A timing history `h` provides both the
delivered input `h.filterMap id` and a time budget `h.length`.  Running on `h`
the machine performs `h.length` rounds; in round `j` it uses the input delivered
after `j+1` ticks and the enumeration stage `j+1`, and appends one further bit
to its current output whenever this bounded search confirms that the extended
string is still below `f` of the delivered input.  Growth by at most one bit per
round makes the machine rate-limited, and the bounded search is monotone both in
the stage and in the delivered input, which makes the machine prefix-monotone
and schedule-independent.
-/

namespace Kolmogorov

/-- Two strings with a common prefix agree on any initial segment inside that prefix. -/
lemma take_eq_take_of_prefix {α : Type*} {l l' : List α} (hp : l <+: l') {j : ℕ}
    (hj : j ≤ l.length) : l.take j = l'.take j := by
  obtain ⟨t, rfl⟩ := hp
  exact (List.take_append_of_le_length hj).symm

/-! ## Bounded confirmation search -/

/-- `confirmBelow A inp y s n` is the disjunction of `A (inp.take k, y) s` over `k < n`. -/
def confirmBelow (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k b => A (inp.take k, y) s || b) n

/-- The bounded lower-graph search: `y` is confirmed at stage `s` for the delivered
input `inp` if some prefix `inp.take k` with `k ≤ min s inp.length` already
enumerates `y` within `s` stages. -/
def confirmStage (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s : ℕ) : Bool :=
  confirmBelow A inp y s (min s inp.length + 1)

/-- The bounded confirmation search is empty at bound zero. -/
lemma confirmBelow_zero (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s : ℕ) :
    confirmBelow A inp y s 0 = false := rfl

/-- One step of the bounded confirmation search adds the next truncation of the input. -/
lemma confirmBelow_succ (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s n : ℕ) :
    confirmBelow A inp y s (n + 1) =
      (A (inp.take n, y) s || confirmBelow A inp y s n) := rfl

/-- The bounded confirmation search fires exactly when some truncation below the bound is
confirmed. -/
lemma confirmBelow_true_iff (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s n : ℕ) :
    confirmBelow A inp y s n = true ↔ ∃ k, k < n ∧ A (inp.take k, y) s = true := by
  induction n with
  | zero => simp [confirmBelow_zero]
  | succ n ih =>
    rw [confirmBelow_succ, Bool.or_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · obtain ⟨k, hk, hk'⟩ := ih.mp h
        exact ⟨k, Nat.lt_succ_of_lt hk, hk'⟩
    · rintro ⟨k, hk, hk'⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact Or.inr (ih.mpr ⟨k, h, hk'⟩)
      · exact Or.inl hk'

/-- The stage confirmation fires exactly when some truncation of the input, of length at most the
stage, is confirmed at that stage. -/
lemma confirmStage_true_iff (A : BitString × BitString → ℕ → Bool) (inp y : BitString) (s : ℕ) :
    confirmStage A inp y s = true ↔
      ∃ k, k ≤ min s inp.length ∧ A (inp.take k, y) s = true := by
  rw [confirmStage, confirmBelow_true_iff]
  constructor
  · rintro ⟨k, hk, hk'⟩; exact ⟨k, Nat.lt_succ_iff.mp hk, hk'⟩
  · rintro ⟨k, hk, hk'⟩; exact ⟨k, Nat.lt_succ_iff.mpr hk, hk'⟩

/-- Confirmation is monotone in the delivered input. -/
lemma confirmStage_mono_input {A : BitString × BitString → ℕ → Bool} {inp inp' y : BitString}
    {s : ℕ} (hp : inp <+: inp') (h : confirmStage A inp y s = true) :
    confirmStage A inp' y s = true := by
  rw [confirmStage_true_iff] at h ⊢
  obtain ⟨k, hk, hk'⟩ := h
  have hlen : inp.length ≤ inp'.length := hp.length_le
  have hkk : k ≤ inp.length := le_trans hk (min_le_right _ _)
  have htake : inp.take k = inp'.take k := take_eq_take_of_prefix hp hkk
  refine ⟨k, ?_, ?_⟩
  · exact le_min (le_trans hk (min_le_left _ _)) (le_trans hkk hlen)
  · rwa [← htake]

/-- Confirmation is monotone in the stage, given a stage-monotone approximation. -/
lemma confirmStage_mono_stage {A : BitString × BitString → ℕ → Bool}
    (hAmono : ∀ p s t, s ≤ t → A p s = true → A p t = true)
    {inp y : BitString} {s t : ℕ} (hst : s ≤ t) (h : confirmStage A inp y s = true) :
    confirmStage A inp y t = true := by
  rw [confirmStage_true_iff] at h ⊢
  obtain ⟨k, hk, hk'⟩ := h
  exact ⟨k, le_min (le_trans (le_trans hk (min_le_left _ _)) hst)
    (le_trans hk (min_le_right _ _)), hAmono _ _ _ hst hk'⟩

/-! ## The bounded enumerator machine -/

/-- One round of the enumerator: extend the current output `y` by one bit if the
bounded search at stage `j+1`, with the input delivered after `j+1` ticks,
confirms the extension. -/
def enumeratorAdvance (A : BitString × BitString → ℕ → Bool) (h : TimingHistory) (j : ℕ)
    (y : BitString) : BitString :=
  cond (confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [false]) (j + 1)) (y ++ [false])
    (cond (confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [true]) (j + 1)) (y ++ [true]) y)

/-- The output after `k` rounds of the enumerator on the timing history `h`. -/
def enumeratorRun (A : BitString × BitString → ℕ → Bool) (h : TimingHistory) (k : ℕ) :
    BitString :=
  Nat.rec (motive := fun _ => BitString) [] (fun j y => enumeratorAdvance A h j y) k

/-- The step function of the bounded enumerator machine: run for as many rounds
as the timing history is long. -/
def enumeratorStep (A : BitString × BitString → ℕ → Bool) (h : TimingHistory) : BitString :=
  enumeratorRun A h h.length

/-- The enumerator has produced nothing before its first round. -/
lemma enumeratorRun_zero (A : BitString × BitString → ℕ → Bool) (h : TimingHistory) :
    enumeratorRun A h 0 = [] := rfl

/-- Each round of the enumerator advances the output produced so far. -/
lemma enumeratorRun_succ (A : BitString × BitString → ℕ → Bool) (h : TimingHistory) (k : ℕ) :
    enumeratorRun A h (k + 1) = enumeratorAdvance A h k (enumeratorRun A h k) := rfl

/-! ### Operational laws -/

/-- Advancing the enumerator only extends the current output. -/
lemma enumeratorAdvance_prefix (A : BitString × BitString → ℕ → Bool) (h : TimingHistory)
    (j : ℕ) (y : BitString) : y <+: enumeratorAdvance A h j y := by
  unfold enumeratorAdvance
  cases confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [false]) (j + 1) <;>
    cases confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [true]) (j + 1) <;>
    simp

/-- Advancing the enumerator appends at most one bit. -/
lemma enumeratorAdvance_length_le (A : BitString × BitString → ℕ → Bool) (h : TimingHistory)
    (j : ℕ) (y : BitString) : (enumeratorAdvance A h j y).length ≤ y.length + 1 := by
  unfold enumeratorAdvance
  cases confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [false]) (j + 1) <;>
    cases confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [true]) (j + 1) <;>
    simp

/-- The output of the enumerator grows with the number of rounds. -/
lemma enumeratorRun_prefix_of_le (A : BitString × BitString → ℕ → Bool) (h : TimingHistory)
    {k m : ℕ} (hkm : k ≤ m) : enumeratorRun A h k <+: enumeratorRun A h m := by
  induction m with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hkm
    subst this
    exact List.prefix_rfl
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hkm) with hk | hk
    · exact (ih (Nat.lt_succ_iff.mp hk)).trans
        (by rw [enumeratorRun_succ]; exact enumeratorAdvance_prefix _ _ _ _)
    · subst hk
      exact List.prefix_rfl

/-- The first `k` rounds only look at the first `k` ticks of the history. -/
lemma enumeratorRun_eq_of_prefix (A : BitString × BitString → ℕ → Bool) {h h' : TimingHistory}
    (hp : h <+: h') {k : ℕ} (hk : k ≤ h.length) :
    enumeratorRun A h k = enumeratorRun A h' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ h.length := Nat.le_of_succ_le hk
    rw [enumeratorRun_succ, enumeratorRun_succ, ih hk']
    unfold enumeratorAdvance
    rw [take_eq_take_of_prefix hp hk]

/-- Prefix monotonicity of the machine. -/
lemma enumeratorStep_prefix_of_prefix (A : BitString × BitString → ℕ → Bool)
    {h h' : TimingHistory} (hp : h <+: h') :
    enumeratorStep A h <+: enumeratorStep A h' := by
  have h1 : enumeratorRun A h h.length = enumeratorRun A h' h.length :=
    enumeratorRun_eq_of_prefix A hp le_rfl
  rw [enumeratorStep, enumeratorStep, h1]
  exact enumeratorRun_prefix_of_le A h' hp.length_le

/-- The machine outputs at most one further bit per tick. -/
lemma enumeratorStep_length_le_succ (A : BitString × BitString → ℕ → Bool) (h : TimingHistory)
    (o : Option Bool) :
    (enumeratorStep A (h ++ [o])).length ≤ (enumeratorStep A h).length + 1 := by
  have hp : h <+: h ++ [o] := ⟨[o], rfl⟩
  have hlen : (h ++ [o]).length = h.length + 1 := by simp
  have h1 : enumeratorRun A (h ++ [o]) h.length = enumeratorStep A h :=
    (enumeratorRun_eq_of_prefix A hp le_rfl).symm
  rw [enumeratorStep, hlen, enumeratorRun_succ, h1]
  exact enumeratorAdvance_length_le _ _ _ _

/-! ### Computability -/

/-- The stage confirmation of a computable enumeration is computable. -/
lemma computable_confirmStage {A : BitString × BitString → ℕ → Bool} (hA : Computable₂ A) :
    Computable fun q : (BitString × BitString) × ℕ => confirmStage A q.1.1 q.1.2 q.2 := by
  have hbound : Computable fun q : (BitString × BitString) × ℕ =>
      min q.2 q.1.1.length + 1 :=
    Primrec.to_comp (Primrec.succ.comp
      (Primrec.nat_min.comp Primrec.snd
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))))
  have hstep : Computable₂ fun (q : (BitString × BitString) × ℕ) (p : ℕ × Bool) =>
      A (q.1.1.take p.1, q.1.2) q.2 || p.2 := by
    have htakeBase : Computable₂ (fun (w : BitString) (n : ℕ) => w.take n) :=
      (Primrec.list_take.comp Primrec.snd Primrec.fst).to_comp
    have hword : Computable fun r : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
        r.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hn : Computable fun r : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
        r.2.1 :=
      Computable.fst.comp Computable.snd
    have htake : Computable fun r : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
        (r.1.1.1.take r.2.1, r.1.1.2) :=
      Computable.pair (htakeBase.comp hword hn)
        (Computable.snd.comp (Computable.fst.comp Computable.fst))
    have hA' : Computable fun r : ((BitString × BitString) × ℕ) × (ℕ × Bool) =>
        A (r.1.1.1.take r.2.1, r.1.1.2) r.1.2 :=
      hA.comp htake (Computable.snd.comp Computable.fst)
    exact Primrec.or.to_comp.comp hA' (Computable.snd.comp Computable.snd)
  have := Computable.nat_rec (σ := Bool) (f := fun q : (BitString × BitString) × ℕ =>
      min q.2 q.1.1.length + 1) (g := fun _ => false)
    (h := fun q p => A (q.1.1.take p.1, q.1.2) q.2 || p.2) hbound (Computable.const false) hstep
  exact this.of_eq (fun q => rfl)

/-- The step function of the enumerator machine is computable. -/
lemma computable_enumeratorStep {A : BitString × BitString → ℕ → Bool} (hA : Computable₂ A) :
    Computable (enumeratorStep A) := by
  have hfilter : Computable (fun h : TimingHistory => h.filterMap id) :=
    (Primrec.listFilterMap Primrec.id Primrec₂.right).to_comp
  have hadv : Computable₂ fun (h : TimingHistory) (p : ℕ × BitString) =>
      enumeratorAdvance A h p.1 p.2 := by
    have hinp : Computable fun r : TimingHistory × (ℕ × BitString) =>
        ((r.1.take (r.2.1 + 1)).filterMap id) :=
      hfilter.comp (Primrec.to_comp (Primrec.list_take.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst))
    have hstage : Computable fun r : TimingHistory × (ℕ × BitString) => r.2.1 + 1 :=
      Primrec.to_comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
    have hy : Computable fun r : TimingHistory × (ℕ × BitString) => r.2.2 :=
      Computable.snd.comp Computable.snd
    have hfalse : Computable fun r : TimingHistory × (ℕ × BitString) => r.2.2 ++ [false] :=
      Computable.list_append.comp hy (Computable.const [false])
    have htrue : Computable fun r : TimingHistory × (ℕ × BitString) => r.2.2 ++ [true] :=
      Computable.list_append.comp hy (Computable.const [true])
    have hpf : Computable fun r : TimingHistory × (ℕ × BitString) =>
        (((r.1.take (r.2.1 + 1)).filterMap id, r.2.2 ++ [false]), r.2.1 + 1) :=
      Computable.pair (Computable.pair hinp hfalse) hstage
    have hpt : Computable fun r : TimingHistory × (ℕ × BitString) =>
        (((r.1.take (r.2.1 + 1)).filterMap id, r.2.2 ++ [true]), r.2.1 + 1) :=
      Computable.pair (Computable.pair hinp htrue) hstage
    have hcf : Computable fun r : TimingHistory × (ℕ × BitString) =>
        confirmStage A ((r.1.take (r.2.1 + 1)).filterMap id) (r.2.2 ++ [false]) (r.2.1 + 1) := by
      have h := Computable.comp (computable_confirmStage hA) hpf
      exact h
    have hct : Computable fun r : TimingHistory × (ℕ × BitString) =>
        confirmStage A ((r.1.take (r.2.1 + 1)).filterMap id) (r.2.2 ++ [true]) (r.2.1 + 1) := by
      have h := Computable.comp (computable_confirmStage hA) hpt
      exact h
    exact Computable.cond hcf hfalse (Computable.cond hct htrue hy)
  have := Computable.nat_rec (σ := BitString) (f := fun h : TimingHistory => h.length)
    (g := fun _ => ([] : BitString))
    (h := fun (h : TimingHistory) (p : ℕ × BitString) => enumeratorAdvance A h p.1 p.2)
    Computable.list_length (Computable.const []) hadv
  exact this.of_eq (fun h => rfl)


/-! ## Semantics: the enumerator computes the given stream map -/

/-- Two finite strings below a common stream are prefix-comparable. -/
lemma prefix_or_prefix_of_finite_le {sigma : BitStream} {a b : BitString}
    (ha : BitStream.finite a ≤ sigma) (hb : BitStream.finite b ≤ sigma) :
    a <+: b ∨ b <+: a := by
  cases sigma with
  | finite z => exact isPrefix_or_isPrefix_of_isPrefix ha hb
  | infinite w =>
    have ha1 : a <+: cantorPrefix w (max a.length b.length) := by
      have h : cantorPrefix w a.length = a := (isCantorPrefix_iff_cantorPrefix_eq a w).1 ha
      nth_rw 1 [← h]
      exact cantorPrefix_mono w (le_max_left a.length b.length)
    have hb1 : b <+: cantorPrefix w (max a.length b.length) := by
      have h : cantorPrefix w b.length = b := (isCantorPrefix_iff_cantorPrefix_eq b w).1 hb
      nth_rw 1 [← h]
      exact cantorPrefix_mono w (le_max_right a.length b.length)
    exact isPrefix_or_isPrefix_of_isPrefix ha1 hb1

section Semantics

variable {f : BitStream → BitStream} {A : BitString × BitString → ℕ → Bool}

/-- A confirmed string really is below `f` of the delivered input. -/
lemma confirmStage_lowerGraph (hfm : Monotone f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2)
    {inp y : BitString} {s : ℕ} (h : confirmStage A inp y s = true) :
    streamLowerGraph f inp y := by
  obtain ⟨k, _, hk⟩ := (confirmStage_true_iff A inp y s).mp h
  have h1 : streamLowerGraph f (inp.take k) y := hAsound (inp.take k, y) s hk
  exact le_trans h1 (hfm (show BitStream.finite (inp.take k) ≤ BitStream.finite inp from
    List.take_prefix k inp))

/-- Anything below `f` of the delivered input is eventually confirmed. -/
lemma exists_confirmStage
    (hAmono : ∀ p s t, s ≤ t → A p s = true → A p t = true)
    (hAcomplete : ∀ p, streamLowerGraph f p.1 p.2 → ∃ s, A p s = true)
    {inp y : BitString} (h : streamLowerGraph f inp y) :
    ∃ s₀, ∀ s, s₀ ≤ s → confirmStage A inp y s = true := by
  obtain ⟨s₁, hs₁⟩ := hAcomplete (inp, y) h
  refine ⟨max s₁ inp.length, fun s hs => ?_⟩
  rw [confirmStage_true_iff]
  refine ⟨inp.length, le_min (le_trans (le_max_right s₁ inp.length) hs) le_rfl, ?_⟩
  rw [List.take_length]
  exact hAmono (inp, y) s₁ s (le_trans (le_max_left s₁ inp.length) hs) hs₁

/-- Soundness of the enumerator run. -/
lemma enumeratorRun_lowerGraph (hfm : Monotone f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2)
    (h : TimingHistory) (k : ℕ) :
    streamLowerGraph f ((h.take k).filterMap id) (enumeratorRun A h k) := by
  induction k with
  | zero =>
    change BitStream.finite [] ≤ _
    exact BitStream.nil_le _
  | succ k ih =>
    rw [enumeratorRun_succ]
    have hpre : h.take k <+: h.take (k + 1) := List.take_prefix_take_left (Nat.le_succ k)
    have hin : ((h.take k).filterMap id) <+: ((h.take (k + 1)).filterMap id) :=
      hpre.filterMap id
    have ih' : streamLowerGraph f ((h.take (k + 1)).filterMap id) (enumeratorRun A h k) :=
      le_trans ih (hfm (show BitStream.finite ((h.take k).filterMap id) ≤
        BitStream.finite ((h.take (k + 1)).filterMap id) from hin))
    unfold enumeratorAdvance
    by_cases hcf : confirmStage A ((h.take (k + 1)).filterMap id)
        (enumeratorRun A h k ++ [false]) (k + 1) = true
    · rw [hcf]
      exact confirmStage_lowerGraph hfm hAsound hcf
    · rw [Bool.eq_false_iff.mpr hcf]
      by_cases hct : confirmStage A ((h.take (k + 1)).filterMap id)
          (enumeratorRun A h k ++ [true]) (k + 1) = true
      · rw [hct]
        exact confirmStage_lowerGraph hfm hAsound hct
      · rw [Bool.eq_false_iff.mpr hct]
        exact ih'

/-- Everything the enumerator outputs on a history is in the lower graph of the map it enumerates.
-/
lemma enumeratorStep_lowerGraph (hfm : Monotone f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2) (h : TimingHistory) :
    streamLowerGraph f (h.filterMap id) (enumeratorStep A h) := by
  have := enumeratorRun_lowerGraph hfm hAsound h h.length
  rwa [List.take_length] at this

/-- Growth in one round, whenever the one-bit extension is confirmed. -/
lemma enumeratorAdvance_length_succ_of_confirm {h : TimingHistory} {j : ℕ} {y : BitString}
    {b : Bool} (hb : confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [b]) (j + 1) = true) :
    (enumeratorAdvance A h j y).length = y.length + 1 := by
  unfold enumeratorAdvance
  by_cases hcf : confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [false]) (j + 1) = true
  · rw [hcf]; simp
  · have hct : confirmStage A ((h.take (j + 1)).filterMap id) (y ++ [true]) (j + 1) = true := by
      cases b with
      | false => exact absurd hb hcf
      | true => exact hb
    rw [Bool.eq_false_iff.mpr hcf, hct]
    simp

/-! ### Running along a schedule -/

/-- The history of `n` ticks has length `n`. -/
lemma schedule_history_length (sch : Schedule) (n : ℕ) : (sch.history n).length = n := by
  simp [Schedule.history]

/-- The bits delivered by a schedule grow with the number of ticks. -/
lemma schedule_delivered_prefix (sch : Schedule) {n m : ℕ} (hnm : n ≤ m) :
    (sch.history n).filterMap id <+: (sch.history m).filterMap id :=
  (history_prefix sch n m hnm).filterMap id

/-- The enumerator output after `n` ticks of a schedule is the `n`-th stage of the
run along any longer history. -/
lemma enumeratorStep_history_eq_run (sch : Schedule) {n m : ℕ} (hnm : n ≤ m) :
    enumeratorStep A (sch.history n) = enumeratorRun A (sch.history m) n := by
  rw [enumeratorStep, schedule_history_length]
  exact enumeratorRun_eq_of_prefix A (history_prefix sch n m hnm)
    (by rw [schedule_history_length])

/-- The output of the enumerator machine grows along the histories of a schedule. -/
lemma enumeratorStep_history_prefix (sch : Schedule) {n m : ℕ} (hnm : n ≤ m) :
    enumeratorStep A (sch.history n) <+: enumeratorStep A (sch.history m) :=
  enumeratorStep_prefix_of_prefix A (history_prefix sch n m hnm)

/-- On a schedule realising the input, the enumerator machine never outputs beyond the value of
the map it enumerates. -/
lemma enumeratorStep_history_le (hfm : Monotone f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2)
    {x : BitStream} {sch : Schedule} (hreal : sch.realizes x) (n : ℕ) :
    BitStream.finite (enumeratorStep A (sch.history n)) ≤ f x :=
  le_trans (enumeratorStep_lowerGraph hfm hAsound (sch.history n)) (hfm (hreal n))

/-- Fairness makes every string below `f x` eventually visible to the machine. -/
lemma exists_index_lowerGraph (hf : IsContinuousStreamMap f)
    {x : BitStream} {sch : Schedule} (hreal : sch.realizes x) (hfair : sch.fairFor x)
    {z : BitString} (hz : BitStream.finite z ≤ f x) :
    ∃ N, ∀ n, N ≤ n → streamLowerGraph f ((sch.history n).filterMap id) z := by
  cases x with
  | finite u =>
    obtain ⟨N, hN⟩ := hfair u (le_refl (BitStream.finite u))
    refine ⟨N, fun n hn => ?_⟩
    have h2 : u <+: (sch.history n).filterMap id :=
      hN.trans (schedule_delivered_prefix sch hn)
    have h3 : (sch.history n).filterMap id <+: u := hreal n
    have heq : (sch.history n).filterMap id = u :=
      h3.eq_of_length (le_antisymm h3.length_le h2.length_le)
    rw [heq]
    exact hz
  | infinite w =>
    obtain ⟨k, hk⟩ := (continuousStreamMap_finite_le_infinite_iff f hf w z).mp hz
    have hpre : BitStream.finite (cantorPrefix w k) ≤ BitStream.infinite w :=
      (isCantorPrefix_iff_cantorPrefix_eq _ _).mpr (by simp [cantorPrefix_length])
    obtain ⟨N, hN⟩ := hfair (cantorPrefix w k) hpre
    refine ⟨N, fun n hn => ?_⟩
    have h1 : cantorPrefix w k <+: (sch.history n).filterMap id :=
      hN.trans (schedule_delivered_prefix sch hn)
    exact le_trans hk (hf.1 (show BitStream.finite (cantorPrefix w k) ≤
      BitStream.finite ((sch.history n).filterMap id) from h1))

/-- The key growth estimate: the enumerator eventually outputs at least `m` bits
for every `m` not exceeding the length of a string below `f x`.

The hypotheses `hAsound`, `hAmono` and `hAcomplete` are the interface of an arbitrary
stage predicate `A`: it is sound and complete for the lower graph of `f`, and monotone
in the stage. -/
lemma enumeratorStep_exists_length_ge (hf : IsContinuousStreamMap f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2)
    (hAmono : ∀ p s t, s ≤ t → A p s = true → A p t = true)
    (hAcomplete : ∀ p, streamLowerGraph f p.1 p.2 → ∃ s, A p s = true)
    {x : BitStream} {sch : Schedule} (hreal : sch.realizes x) (hfair : sch.fairFor x)
    {y : BitString} (hy : BitStream.finite y ≤ f x) :
    ∀ m, m ≤ y.length → ∃ n, m ≤ (enumeratorStep A (sch.history n)).length := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨0, Nat.zero_le _⟩
  | succ m ih =>
    intro hm
    obtain ⟨n, hn⟩ := ih (Nat.le_of_succ_le hm)
    have hmy : m < y.length := hm
    -- the string we want to reach next
    set z := y.take (m + 1) with hz_def
    have hzy : z <+: y := List.take_prefix _ _
    have hz : BitStream.finite z ≤ f x :=
      le_trans (show BitStream.finite z ≤ BitStream.finite y from hzy) hy
    obtain ⟨N, hN⟩ := exists_index_lowerGraph hf hreal hfair hz
    obtain ⟨s₀, hs₀⟩ := exists_confirmStage hAmono hAcomplete (hN N le_rfl)
    set t := max (max n N) s₀ with ht_def
    have hnt : n ≤ t := le_trans (le_max_left n N) (le_max_left _ _)
    have hNt : N ≤ t := le_trans (le_max_right n N) (le_max_left _ _)
    have hs₀t : s₀ ≤ t := le_max_right _ _
    by_cases hgrow : m + 1 ≤ (enumeratorStep A (sch.history t)).length
    · exact ⟨t, hgrow⟩
    · -- the output at time `t` has length exactly `m`
      have hge : m ≤ (enumeratorStep A (sch.history t)).length :=
        le_trans hn (enumeratorStep_history_prefix sch hnt).length_le
      have hlen : (enumeratorStep A (sch.history t)).length = m := by omega
      have hout_le : BitStream.finite (enumeratorStep A (sch.history t)) ≤ f x :=
        enumeratorStep_history_le hf.1 hAsound hreal t
      have hcmp := prefix_or_prefix_of_finite_le hout_le hy
      have hout_pre : enumeratorStep A (sch.history t) <+: y := by
        rcases hcmp with h | h
        · exact h
        · exact absurd h.length_le (by omega)
      have hout_take : y.take m = enumeratorStep A (sch.history t) := by
        have := isPrefix_of_isPrefix_take hout_pre
        rwa [hlen] at this
      -- the delivered input at time `t+1` confirms `z`
      have hconf₀ : confirmStage A ((sch.history N).filterMap id) z (t + 1) = true :=
        hs₀ (t + 1) (le_trans hs₀t (Nat.le_succ t))
      have hconf : confirmStage A ((sch.history (t + 1)).filterMap id) z (t + 1) = true :=
        confirmStage_mono_input
          (schedule_delivered_prefix sch (le_trans hNt (Nat.le_succ t))) hconf₀
      -- `z` extends the current output by one bit
      have hz_eq : z = enumeratorStep A (sch.history t) ++ [y[m]] := by
        rw [hz_def, List.take_add_one, ← hout_take]
        congr 1
        rw [List.getElem?_eq_getElem hmy]
        rfl
      -- unfold one round of the run at time `t+1`
      have hstep_t : enumeratorRun A (sch.history (t + 1)) t =
          enumeratorStep A (sch.history t) :=
        (enumeratorStep_history_eq_run sch (Nat.le_succ t)).symm
      have htake : (sch.history (t + 1)).take (t + 1) = sch.history (t + 1) := by
        rw [List.take_of_length_le (by rw [schedule_history_length])]
      have hconf' : confirmStage A (((sch.history (t + 1)).take (t + 1)).filterMap id)
          (enumeratorStep A (sch.history t) ++ [y[m]]) (t + 1) = true := by
        rw [htake, ← hz_eq]; exact hconf
      refine ⟨t + 1, ?_⟩
      have hrun : enumeratorStep A (sch.history (t + 1)) =
          enumeratorAdvance A (sch.history (t + 1)) t (enumeratorStep A (sch.history t)) := by
        rw [enumeratorStep, schedule_history_length, enumeratorRun_succ, hstep_t]
      rw [hrun, enumeratorAdvance_length_succ_of_confirm hconf', hlen]

/-- **Semantic completeness of the bounded enumerator.**  Along any realizing and
fair schedule, the strings ever produced by the enumerator are exactly the finite
approximations of `f x`.

The hypotheses `hAsound`, `hAmono` and `hAcomplete` are the interface of an arbitrary
stage predicate `A`: it is sound and complete for the lower graph of `f`, and monotone
in the stage. -/
theorem enumeratorRun_finite_le_iff_lowerGraph (hf : IsContinuousStreamMap f)
    (hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2)
    (hAmono : ∀ p s t, s ≤ t → A p s = true → A p t = true)
    (hAcomplete : ∀ p, streamLowerGraph f p.1 p.2 → ∃ s, A p s = true)
    {x : BitStream} {sch : Schedule} (hreal : sch.realizes x) (hfair : sch.fairFor x)
    (y : BitString) :
    (∃ n, y <+: enumeratorStep A (sch.history n)) ↔ BitStream.finite y ≤ f x := by
  constructor
  · rintro ⟨n, hn⟩
    exact le_trans (show BitStream.finite y ≤
      BitStream.finite (enumeratorStep A (sch.history n)) from hn)
      (enumeratorStep_history_le hf.1 hAsound hreal n)
  · intro hy
    obtain ⟨n, hn⟩ := enumeratorStep_exists_length_ge hf hAsound hAmono hAcomplete hreal hfair hy
      y.length le_rfl
    refine ⟨n, ?_⟩
    have hout_le : BitStream.finite (enumeratorStep A (sch.history n)) ≤ f x :=
      enumeratorStep_history_le hf.1 hAsound hreal n
    rcases prefix_or_prefix_of_finite_le hy hout_le with h | h
    · exact h
    · rw [h.eq_of_length (le_antisymm h.length_le hn)]

end Semantics

/-! ## Theorem 82, converse direction -/

/-- **Theorem 82 (converse).**  Every computable map on streams is the denotation
of a robust machine: there is a computable, prefix-monotone and rate-limited step
function on timing histories whose output does not depend on the schedule and
whose robust denotation is the given map. -/
theorem exists_robustMachine_of_isComputableStreamMap {f : BitStream → BitStream}
    (hf : IsComputableStreamMap f) :
    ∃ step : TimingHistory → BitString, Computable step ∧
      (∀ h h', h <+: h' → step h <+: step h') ∧
      (∀ h o, (step (h ++ [o])).length ≤ (step h).length + 1) ∧
      (∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
        Schedule.realizes s2 x → Schedule.fairFor s2 x →
        ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) ∧
      robustDenotation step = f := by
  obtain ⟨A, hAcomp, hAmono, hAiff⟩ := hf.2.exists_stageApprox
  have hAsound : ∀ p s, A p s = true → streamLowerGraph f p.1 p.2 :=
    fun p s hs => (hAiff p).mpr ⟨s, hs⟩
  have hAcomplete : ∀ p, streamLowerGraph f p.1 p.2 → ∃ s, A p s = true :=
    fun p hp => (hAiff p).mp hp
  have hmono : ∀ h h', h <+: h' → enumeratorStep A h <+: enumeratorStep A h' :=
    fun _ _ hp => enumeratorStep_prefix_of_prefix A hp
  have hchar : ∀ (x : BitStream) (sch : Schedule), sch.realizes x → sch.fairFor x →
      ∀ y, (∃ n, y <+: enumeratorStep A (sch.history n)) ↔ BitStream.finite y ≤ f x :=
    fun x sch hreal hfair y =>
      enumeratorRun_finite_le_iff_lowerGraph hf.1 hAsound hAmono hAcomplete hreal hfair y
  refine ⟨enumeratorStep A, computable_enumeratorStep hAcomp, hmono,
    enumeratorStep_length_le_succ A, ?_, ?_⟩
  · intro x s1 s2 hr1 hf1 hr2 hf2 y
    rw [hchar x s1 hr1 hf1 y, hchar x s2 hr2 hf2 y]
  · funext x
    apply BitStream.eq_of_forall_finite_le_iff
    intro y
    rw [robustDenotation, dite_eq_left hmono, BitStream.finite_le_ofPrefixSet_iff]
    exact hchar x (canonicalTiming x) (canonicalTiming_realizes x).1
      (canonicalTiming_realizes x).2 y

/-- **Theorem 82.**  A map on streams is computable if and only if it is the
denotation of a robust machine. -/
theorem isComputableStreamMap_iff_exists_robustMachine {f : BitStream → BitStream} :
    IsComputableStreamMap f ↔
      ∃ step : TimingHistory → BitString, Computable step ∧
        (∀ h h', h <+: h' → step h <+: step h') ∧
        (∀ h o, (step (h ++ [o])).length ≤ (step h).length + 1) ∧
        (∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
          Schedule.realizes s2 x → Schedule.fairFor s2 x →
          ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) ∧
        robustDenotation step = f := by
  constructor
  · exact exists_robustMachine_of_isComputableStreamMap
  · rintro ⟨step, hc, hmono, hslow, hrobust, hden⟩
    rw [← hden]
    exact robustMachine_denotation_isComputableStreamMap hc hmono hslow hrobust

end Kolmogorov
