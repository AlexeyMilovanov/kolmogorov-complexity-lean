import KolmogorovMathlib.MonotoneComplexity.ContinuousStreamMap
import KolmogorovMathlib.MonotoneComplexity.REClosure
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# Machines that are insensitive to the timing of their input

A monotone machine reading a stream bit by bit should not depend on *when* the bits arrive. A
`TimingHistory` records what has been read after finitely many ticks, a `Schedule` is an infinite
timing, and `Schedule.realizes` / `Schedule.fairFor` say it delivers exactly the bits of a stream,
each of them eventually. A machine is robust when its output does not depend on the schedule; the
results are that the lower graph of its denotation is recursively enumerable
(`robustDenotation_lowerGraph_isRE`) and hence
`robustMachine_denotation_isComputableStreamMap`: a computable, monotone, robust machine denotes
a computable stream map. This makes the operational and the relational descriptions of monotone
machines interchangeable.
-/

namespace Kolmogorov

/-- A finite record of what the machine has read so far: at each tick either a bit or nothing. -/
abbrev TimingHistory := List (Option Bool)

/-- The history reads the bits of the stream `x` in order, with idle ticks in between. -/
def TimingHistory.realizes (h : TimingHistory) (x : BitStream) : Prop :=
  BitStream.finite (h.filterMap id) ≤ x

/-- An infinite timing: at each tick either a bit arrives or the machine idles. -/
abbrev Schedule := ℕ → Option Bool

/-- The history of the first `n` ticks of a schedule. -/
def Schedule.history (s : Schedule) (n : ℕ) : TimingHistory :=
  List.ofFn (fun (i : Fin n) => s i.val)

/-- The schedule delivers exactly the bits of the stream `x`. -/
def Schedule.realizes (s : Schedule) (x : BitStream) : Prop :=
  ∀ n, (s.history n).realizes x

/-- The schedule is fair for `x`: every bit of `x` is eventually delivered. -/
def Schedule.fairFor (s : Schedule) (x : BitStream) : Prop :=
  ∀ y : BitString, BitStream.finite y ≤ x → ∃ n, y <+: (s.history n).filterMap id

/-- The schedule that delivers the bits of `x` one per tick, idling after the end of a finite
stream. -/
def canonicalTiming (x : BitStream) : Schedule :=
  fun n =>
    match x with
    | .finite u => if h : n < u.length then some (u.get ⟨n, h⟩) else none
    | .infinite w => some (w n)

/-- Wrapping the entries of a list in `some` and then discarding the wrappers returns the list. -/
lemma filterMap_id_map_some {α} (l : List α) : (l.map some).filterMap id = l := by
  induction l <;> simp [*]

/-- Listing a function into options is the option wrapping of listing it. -/
lemma ofFn_map_some {α} (n : ℕ) (f : Fin n → α) :
    List.ofFn (fun i => some (f i)) = (List.ofFn f).map some := by
  apply List.ext_getElem <;> simp

/-- The bits delivered by the canonical schedule of an infinite stream in `n` ticks are its first
`n` bits. -/
lemma history_filterMap_infinite (w : CantorSeq) (n : ℕ) :
    ((canonicalTiming (.infinite w)).history n).filterMap id = cantorPrefix w n := by
  dsimp [canonicalTiming, Schedule.history, cantorPrefix]
  rw [ofFn_map_some, filterMap_id_map_some]

/-- The bits delivered by the canonical schedule of a finite stream in `n` ticks are its first
`n` bits. -/
lemma history_filterMap_finite (u : BitString) (n : ℕ) :
    ((canonicalTiming (.finite u)).history n).filterMap id = u.take n := by
  dsimp [Schedule.history]
  have h_ofFn : List.ofFn (fun i : Fin n => canonicalTiming (.finite u) i.val) =
    (u.take n).map some ++ List.replicate (n - u.length) none := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hi1 hi2
      simp only [List.getElem_ofFn]
      dsimp [canonicalTiming]
      have h_len : ((u.take n).map some).length = min n u.length := by simp
      have h_i_n : i < n := by simpa using hi1
      split_ifs with h
      · have hi_left : i < ((u.take n).map some).length := by omega
        rw [List.getElem_append_left hi_left]
        simp
      · have hi_right : ((u.take n).map some).length ≤ i := by omega
        rw [List.getElem_append_right hi_right]
        simp
  rw [h_ofFn]
  rw [List.filterMap_append]
  have h1 : ((u.take n).map some).filterMap id = u.take n := filterMap_id_map_some _
  have h2 : (List.replicate (n - u.length) (none : Option Bool)).filterMap id = [] := by
    induction n - u.length <;> simp [*]
  rw [h1, h2, List.append_nil]

/-- The canonical schedule of a stream both realises it and is fair for it. -/
lemma canonicalTiming_realizes (x : BitStream) :
    (canonicalTiming x).realizes x ∧ (canonicalTiming x).fairFor x := by
  constructor
  · intro n
    dsimp [Schedule.realizes, TimingHistory.realizes]
    cases x with
    | finite u =>
      rw [history_filterMap_finite]
      change u.take n <+: u
      exact List.take_prefix _ _
    | infinite w =>
      rw [history_filterMap_infinite]
      change IsCantorPrefix (cantorPrefix w n) w
      apply (isCantorPrefix_iff_cantorPrefix_eq _ _).mpr
      simp [cantorPrefix_length]
  · intro y hy
    cases x with
    | finite u =>
      change y <+: u at hy
      use u.length
      rw [history_filterMap_finite]
      have h_take : u.take u.length = u := by simp
      rw [h_take]
      exact hy
    | infinite w =>
      change IsCantorPrefix y w at hy
      use y.length
      rw [history_filterMap_infinite]
      have h_eq : cantorPrefix w y.length = y := (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hy
      rw [h_eq]

/-- The strings the machine outputs on `x` under some history realising `x`. -/
def robustDenotationSet (step : TimingHistory → BitString) (x : BitStream) : Set BitString :=
  { y | ∃ n, y <+: step ((canonicalTiming x).history n) }

/-- The history of a schedule grows with the number of ticks. -/
lemma history_prefix (s : Schedule) (n m : ℕ) (h : n ≤ m) :
    s.history n <+: s.history m := by
  dsimp [Schedule.history]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [h]
  · intro i hi1 hi2
    simp

private def appendHistorySchedule (h : TimingHistory) (s : Schedule) : Schedule :=
  fun n => if hn : n < h.length then h[n] else s (n - h.length)

private lemma appendHistorySchedule_history_add (h : TimingHistory) (s : Schedule) (n : ℕ) :
    (appendHistorySchedule h s).history (h.length + n) = h ++ s.history n := by
  apply List.ext_getElem
  · simp [Schedule.history]
  · intro i hi₁ hi₂
    simp only [Schedule.history, List.getElem_ofFn]
    by_cases hi : i < h.length
    · rw [List.getElem_append_left hi]
      simp [appendHistorySchedule, hi]
    · rw [List.getElem_append_right (Nat.le_of_not_gt hi)]
      simp [appendHistorySchedule, hi]

private lemma append_cantorPrefix_shift_eq {v : BitString} {w : CantorSeq}
    (hv : IsCantorPrefix v w) (n : ℕ) :
    v ++ cantorPrefix (fun i => w (v.length + i)) n = cantorPrefix w (v.length + n) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    by_cases hi : i < v.length
    · rw [List.getElem_append_left hi, cantorPrefix_getElem]
      exact (hv i hi).symm
    · rw [List.getElem_append_right (Nat.le_of_not_gt hi), cantorPrefix_getElem,
        cantorPrefix_getElem]
      congr 1
      omega

private lemma exists_fair_schedule_extending_history {h : TimingHistory} {x : BitStream}
    (hx : h.realizes x) :
    ∃ s : Schedule, s.realizes x ∧ s.fairFor x ∧ h <+: s.history h.length := by
  cases x with
  | finite u =>
      change h.filterMap id <+: u at hx
      rcases hx with ⟨rest, hrest⟩
      let s := appendHistorySchedule h (canonicalTiming (.finite rest))
      refine ⟨s, ?_, ?_, ?_⟩
      · intro m
        change (s.history m).filterMap id <+: u
        rcases le_total m h.length with hm | hm
        · have hp : s.history m <+: s.history h.length := history_prefix s m h.length hm
          have hp' := hp.filterMap id
          have hs0 : s.history h.length = h := by
            simpa [s, Schedule.history] using appendHistorySchedule_history_add h
              (canonicalTiming (.finite rest)) 0
          rw [hs0] at hp'
          exact List.IsPrefix.trans hp' ⟨rest, hrest⟩
        · have hadd : h.length + (m - h.length) = m := Nat.add_sub_of_le hm
          rw [← hadd]
          simp only [s]
          rw [appendHistorySchedule_history_add, List.filterMap_append,
            history_filterMap_finite]
          exact ⟨rest.drop (m - h.length), by
            rw [List.append_assoc, List.take_append_drop, hrest]⟩
      · intro y hy
        use h.length + rest.length
        simp only [s]
        rw [appendHistorySchedule_history_add, List.filterMap_append,
          history_filterMap_finite]
        have hy' : y <+: u := BitStream.finite_le_finite_iff.mp hy
        rw [List.take_length]
        change y <+: h.filterMap id ++ rest
        rw [hrest]
        exact hy'
      · have hs0 : s.history h.length = h := by
          simpa [s, Schedule.history] using appendHistorySchedule_history_add h
            (canonicalTiming (.finite rest)) 0
        rw [hs0]
  | infinite w =>
      change IsCantorPrefix (h.filterMap id) w at hx
      let tail : CantorSeq := fun i => w ((h.filterMap id).length + i)
      let s := appendHistorySchedule h (canonicalTiming (.infinite tail))
      refine ⟨s, ?_, ?_, ?_⟩
      · intro m
        change IsCantorPrefix ((s.history m).filterMap id) w
        rcases le_total m h.length with hm | hm
        · have hp : s.history m <+: s.history h.length := history_prefix s m h.length hm
          have hp' := hp.filterMap id
          have hs0 : s.history h.length = h := by
            simpa [s, Schedule.history] using appendHistorySchedule_history_add h
              (canonicalTiming (.infinite tail)) 0
          rw [hs0] at hp'
          exact BitStream.IsCantorPrefix.of_prefix hp' hx
        · have hadd : h.length + (m - h.length) = m := Nat.add_sub_of_le hm
          rw [← hadd]
          simp only [s]
          rw [appendHistorySchedule_history_add, List.filterMap_append,
            history_filterMap_infinite]
          rw [append_cantorPrefix_shift_eq hx]
          apply (isCantorPrefix_iff_cantorPrefix_eq _ _).mpr
          simp
      · intro y hy
        use h.length + y.length
        simp only [s]
        rw [appendHistorySchedule_history_add, List.filterMap_append,
          history_filterMap_infinite, append_cantorPrefix_shift_eq hx]
        have hy_eq : cantorPrefix w y.length = y :=
          (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hy
        rw [← hy_eq]
        simpa using cantorPrefix_mono w
          (show y.length ≤ (h.filterMap id).length + y.length by omega)
      · have hs0 : s.history h.length = h := by
          simpa [s, Schedule.history] using appendHistorySchedule_history_add h
            (canonicalTiming (.infinite tail)) 0
        rw [hs0]

/-- For a monotone step function the outputs on a stream form a prefix set, hence describe a
stream. -/
lemma isStreamPrefixSet_robustDenotationSet (step : TimingHistory → BitString)
    (hmono : ∀ h h', h <+: h' → step h <+: step h') (x : BitStream) :
    IsStreamPrefixSet (robustDenotationSet step x) := by
  dsimp [IsStreamPrefixSet, robustDenotationSet]
  refine ⟨?_, ?_, ?_⟩
  · use 0
    exact List.nil_prefix
  · intro y z hyz hz
    rcases hz with ⟨n, hn⟩
    exact ⟨n, List.IsPrefix.trans hyz hn⟩
  · intro y z hy hz
    rcases hy with ⟨n, hn⟩
    rcases hz with ⟨m, hm⟩
    cases le_total n m with
    | inl hnm =>
      have h_hist : (canonicalTiming x).history n <+: (canonicalTiming x).history m :=
        history_prefix _ _ _ hnm
      have h_step := hmono _ _ h_hist
      have hn_ext : y <+: step ((canonicalTiming x).history m) := List.IsPrefix.trans hn h_step
      exact List.prefix_or_prefix_of_prefix hn_ext hm
    | inr hmn =>
      have h_hist : (canonicalTiming x).history m <+: (canonicalTiming x).history n :=
        history_prefix _ _ _ hmn
      have h_step := hmono _ _ h_hist
      have hm_ext : z <+: step ((canonicalTiming x).history n) := List.IsPrefix.trans hm h_step
      have H := List.prefix_or_prefix_of_prefix hm_ext hn
      rcases H with H1 | H2
      · exact Or.inr H1
      · exact Or.inl H2

open Classical in
/-- The stream the machine outputs on `x`, independently of the timing. -/
noncomputable def robustDenotation (step : TimingHistory → BitString) (x : BitStream) : BitStream :=
  if hmono : (∀ h h', h <+: h' → step h <+: step h') then
    BitStream.ofPrefixSet (robustDenotationSet step x) (isStreamPrefixSet_robustDenotationSet
      step hmono x)
  else
    .finite []

/-- Restatement of the monotonicity hypothesis on the step function. -/
lemma step_prefix_of_prefix_history {step : TimingHistory → BitString}
    (hmono : ∀ h h', h <+: h' → step h <+: step h') :
    ∀ h h' : TimingHistory, h <+: h' → step h <+: step h' :=
  hmono

/-- For a robust machine, a string is output exactly when some history realising the input
produces it. -/
lemma robustDenotation_finite_le_iff_exists_history {step : TimingHistory → BitString}
    (hmono : ∀ h h', h <+: h' → step h <+: step h')
    (hrobust : ∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
                 Schedule.realizes s2 x → Schedule.fairFor s2 x →
                 ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n)))
    (x : BitStream) (y : BitString) :
    BitStream.finite y ≤ robustDenotation step x ↔
      ∃ h : TimingHistory, h.realizes x ∧ y <+: step h := by
  rw [robustDenotation, dite_eq_left hmono,
    BitStream.finite_le_ofPrefixSet_iff]
  constructor
  · rintro ⟨n, hyn⟩
    exact ⟨(canonicalTiming x).history n, (canonicalTiming_realizes x).1 n, hyn⟩
  · rintro ⟨h, hhx, hyh⟩
    obtain ⟨s, hsx, hsfair, hh⟩ := exists_fair_schedule_extending_history hhx
    have hsout : ∃ n, y <+: step (s.history n) :=
      ⟨h.length, List.IsPrefix.trans hyh (hmono h (s.history h.length) hh)⟩
    exact (hrobust x s (canonicalTiming x) hsx hsfair
      (canonicalTiming_realizes x).1 (canonicalTiming_realizes x).2 y).mp hsout

/-- The denotation of a robust machine is monotone in the input stream. -/
lemma robustDenotation_mono {step : TimingHistory → BitString}
    (hmono : ∀ h h', h <+: h' → step h <+: step h')
    (hrobust : ∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
                 Schedule.realizes s2 x → Schedule.fairFor s2 x →
                 ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) :
    Monotone (robustDenotation step) := by
  intro x x' hxx'
  rw [BitStream.le_iff_forall_finite_le]
  intro y hy
  rw [robustDenotation_finite_le_iff_exists_history hmono hrobust] at hy ⊢
  rcases hy with ⟨h, hhx, hyh⟩
  exact ⟨h, le_trans hhx hxx', hyh⟩

/-- The denotation on an infinite input is the least upper bound of the denotations on its finite
prefixes. -/
lemma robustDenotation_infinite_lub {step : TimingHistory → BitString}
    (hmono : ∀ h h', h <+: h' → step h <+: step h')
    (hrobust : ∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
                 Schedule.realizes s2 x → Schedule.fairFor s2 x →
                 ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) :
    ∀ w : CantorSeq, ∀ y : BitStream,
      (∀ n, robustDenotation step (.finite (cantorPrefix w n)) ≤ y) →
      robustDenotation step (.infinite w) ≤ y := by
  intro w z hz
  rw [BitStream.le_iff_forall_finite_le]
  intro y hy
  rw [robustDenotation_finite_le_iff_exists_history hmono hrobust] at hy
  rcases hy with ⟨h, hhw, hyh⟩
  let n := (h.filterMap id).length
  have hfinite : h.realizes (.finite (cantorPrefix w n)) := by
    change h.filterMap id <+: cantorPrefix w n
    change IsCantorPrefix (h.filterMap id) w at hhw
    have heq : cantorPrefix w n = h.filterMap id :=
      (isCantorPrefix_iff_cantorPrefix_eq _ _).mp hhw
    rw [heq]
  have hyfinite : BitStream.finite y ≤
      robustDenotation step (.finite (cantorPrefix w n)) :=
    (robustDenotation_finite_le_iff_exists_history hmono hrobust _ _).mpr
      ⟨h, hfinite, hyh⟩
  exact le_trans hyfinite (hz n)

private def robustPrefixCheck (q : BitString × BitString) : Bool :=
  decide (q.2 = q.1.take q.2.length)

private lemma computable_robustPrefixCheck : Computable robustPrefixCheck := by
  obtain ⟨_, hp⟩ : PrimrecPred fun q : BitString × BitString =>
      q.2 = q.1.take q.2.length :=
    Primrec.eq.comp Primrec.snd
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst)
  exact (hp.of_eq fun q => by simp [robustPrefixCheck]).to_comp

private lemma computable_timingHistory_filterMap_id :
    Computable (fun h : TimingHistory => h.filterMap id) :=
  (Primrec.listFilterMap Primrec.id Primrec₂.right).to_comp

private def robustHistoryCheck (step : TimingHistory → BitString)
    (q : (BitString × BitString) × TimingHistory) : Bool :=
  robustPrefixCheck (q.1.1, q.2.filterMap id) &&
    robustPrefixCheck (step q.2, q.1.2)

private lemma robustHistoryCheck_eq_true_iff (step : TimingHistory → BitString)
    (q : (BitString × BitString) × TimingHistory) :
    robustHistoryCheck step q = true ↔
      q.2.realizes (.finite q.1.1) ∧ q.1.2 <+: step q.2 := by
  change (decide (q.2.filterMap id = q.1.1.take (q.2.filterMap id).length) &&
      decide (q.1.2 = (step q.2).take q.1.2.length)) = true ↔
    q.2.filterMap id <+: q.1.1 ∧ q.1.2 <+: step q.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.prefix_iff_eq_take]

private lemma computable_robustHistoryCheck {step : TimingHistory → BitString}
    (hc : Computable step) : Computable (robustHistoryCheck step) := by
  have hdelivered : Computable
      (fun q : (BitString × BitString) × TimingHistory => q.2.filterMap id) :=
    computable_timingHistory_filterMap_id.comp Computable.snd
  have hinput : Computable
      (fun q : (BitString × BitString) × TimingHistory => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hfirst : Computable
      (fun q : (BitString × BitString) × TimingHistory =>
        robustPrefixCheck (q.1.1, q.2.filterMap id)) :=
    computable_robustPrefixCheck.comp (Computable.pair hinput hdelivered)
  have houtput : Computable
      (fun q : (BitString × BitString) × TimingHistory => step q.2) :=
    hc.comp Computable.snd
  have hy : Computable
      (fun q : (BitString × BitString) × TimingHistory => q.1.2) :=
    Computable.snd.comp Computable.fst
  have hsecond : Computable
      (fun q : (BitString × BitString) × TimingHistory =>
        robustPrefixCheck (step q.2, q.1.2)) :=
    computable_robustPrefixCheck.comp (Computable.pair houtput hy)
  exact Primrec.and.to_comp.comp hfirst hsecond

/-- The lower graph of the denotation of a computable robust machine is recursively enumerable. -/
lemma robustDenotation_lowerGraph_isRE {step : TimingHistory → BitString}
    (hc : Computable step)
    (hmono : ∀ h h', h <+: h' → step h <+: step h')
    (hrobust : ∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
                 Schedule.realizes s2 x → Schedule.fairFor s2 x →
                 ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) :
    IsRE fun p : BitString × BitString => streamLowerGraph (robustDenotation step) p.1 p.2 := by
  have hhistory : IsRE fun q : (BitString × BitString) × TimingHistory =>
      q.2.realizes (.finite q.1.1) ∧ q.1.2 <+: step q.2 :=
    isRE_of_computable_bool _ (robustHistoryCheck step)
      (robustHistoryCheck_eq_true_iff step) (computable_robustHistoryCheck hc)
  have hhistory' : IsRE fun q : (BitString × BitString) × TimingHistory =>
      (fun p h => h.realizes (.finite p.1) ∧ p.2 <+: step h) q.1 q.2 :=
    hhistory
  have hexists : IsRE fun p : BitString × BitString =>
      ∃ h : TimingHistory, h.realizes (.finite p.1) ∧ p.2 <+: step h :=
    IsRE.exists_encodable (α := BitString × BitString) (β := TimingHistory)
      (R := fun p h => h.realizes (.finite p.1) ∧ p.2 <+: step h) hhistory'
  apply hexists.of_iff
  intro p
  exact (robustDenotation_finite_le_iff_exists_history hmono hrobust
    (.finite p.1) p.2).symm

/-- The denotation of a computable, monotone, robust machine is a computable stream map. -/
theorem robustMachine_denotation_isComputableStreamMap
    {step : List (Option Bool) → BitString}
    (hc : Computable step)
    (hmono : ∀ h h', h <+: h' → step h <+: step h')
    (_hslow : ∀ h o, (step (h ++ [o])).length ≤ (step h).length + 1)
    (hrobust : ∀ x s1 s2, Schedule.realizes s1 x → Schedule.fairFor s1 x →
                 Schedule.realizes s2 x → Schedule.fairFor s2 x →
                 ∀ y, (∃ n, y <+: step (s1.history n)) ↔ (∃ n, y <+: step (s2.history n))) :
    IsComputableStreamMap (robustDenotation step) := by
  refine ⟨⟨robustDenotation_mono hmono hrobust,
    robustDenotation_infinite_lub hmono hrobust⟩, ?_⟩
  exact robustDenotation_lowerGraph_isRE hc hmono hrobust

end Kolmogorov
