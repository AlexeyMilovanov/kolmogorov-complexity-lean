import KolmogorovMathlib.StrongMerging.Upper.Orientation

/-!
# H01: capped extraction

Blueprint node H01: the capped extraction step, its forward iteration on sets, the
code-level step and its simulation.

Part of `KolmogorovMathlib.StrongMerging.Upper.Hierarchy`, which imports it.
-/

namespace Kolmogorov.StrongMerging.Upper

/-! ### H01: capped extraction -/

section Extract

variable (elig : Finset BitString → Prop) [DecidablePred elig]

/-- The first eligible subset of `rem` in a fixed computable order: the first sublist (in
`List.sublists` order) of the canonical sorted list `canonicalFinsetList rem` whose underlying set
is eligible. -/
def firstEligible (rem : Finset BitString) : Option (Finset BitString) :=
  ((canonicalFinsetList rem).sublists.find? fun s => decide (elig s.toFinset)).map List.toFinset

/-- Extraction with explicit fuel: select the first eligible subset, record it, remove it and
repeat; stop when no eligible subset remains (or the fuel is exhausted). -/
def extractAux : ℕ → Finset BitString → List (Finset BitString) × Finset BitString
  | 0, rem => ([], rem)
  | fuel + 1, rem =>
    match firstEligible elig rem with
    | none => ([], rem)
    | some T => (T :: (extractAux fuel (rem \ T)).1, (extractAux fuel (rem \ T)).2)

/-- **Capped extraction (blueprint H01).**  The list of children and the residual of a parent
`F`; the fuel `|F| + 1` suffices because each selected child is nonempty. -/
def extract (F : Finset BitString) : List (Finset BitString) × Finset BitString :=
  extractAux elig (F.card + 1) F

variable {elig}

/-- A selected subset is eligible and lies in the remainder.

Proof sketch: unfold `firstEligible`; `Option.map_eq_some_iff` gives a sublist `s` with
`find? = some s` and `T = s.toFinset`; `List.find?_some` gives eligibility and
`List.mem_of_find?_eq_some`, `List.mem_sublists`, `List.Sublist.subset` give `T ⊆ rem` (via
`mem_canonicalFinsetList`). -/
theorem firstEligible_some {rem T : Finset BitString} (h : firstEligible elig rem = some T) :
    elig T ∧ T ⊆ rem := by
  unfold firstEligible at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := List.find?_some hs
  have h2 := List.mem_of_find?_eq_some hs
  refine ⟨by simpa using h1, ?_⟩
  intro z hz
  rw [List.mem_toFinset] at hz
  have := (List.mem_sublists.mp h2).subset hz
  simpa using this

/-- If no subset is selected, no subset of the remainder is eligible.

Proof sketch: for `T ⊆ rem` put `s = (canonicalFinsetList rem).filter (· ∈ T)`; it is a sublist
(`List.filter_sublist`, hence in `sublists`) with `s.toFinset = T` (use `T ⊆ rem` and
`mem_canonicalFinsetList`).  `List.find?_eq_none` then says `¬ elig T`. -/
theorem firstEligible_none {rem : Finset BitString} (h : firstEligible elig rem = none) :
    ∀ T ⊆ rem, ¬ elig T := by
  intro T hT hel
  unfold firstEligible at h
  rw [Option.map_eq_none_iff] at h
  have hsub : (canonicalFinsetList rem).filter (fun z => decide (z ∈ T)) ∈
      (canonicalFinsetList rem).sublists :=
    List.mem_sublists.mpr List.filter_sublist
  have hset : ((canonicalFinsetList rem).filter (fun z => decide (z ∈ T))).toFinset = T := by
    ext z
    simp only [List.mem_toFinset, List.mem_filter, mem_canonicalFinsetList, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  have := List.find?_eq_none.mp h _ hsub
  simp only [hset, decide_eq_true_eq] at this
  exact this hel

/-- Children of `extractAux` are eligible subsets of the remainder.

Proof sketch: induction on `fuel` generalizing `rem`; in the `some T` branch use
`firstEligible_some` for `T` and the induction hypothesis on `rem \ T ⊆ rem`. -/
theorem extractAux_children (fuel : ℕ) (rem : Finset BitString) :
    ∀ T ∈ (extractAux elig fuel rem).1, elig T ∧ T ⊆ rem := by
  induction fuel generalizing rem with
  | zero => simp [extractAux]
  | succ fuel ih =>
    simp only [extractAux]
    split
    · simp
    · rename_i T hT
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact firstEligible_some hT
      · obtain ⟨h1, h2⟩ := ih (rem \ T) T' hT'
        exact ⟨h1, h2.trans Finset.sdiff_subset⟩

/-- `extractAux` partitions the remainder: the children are pairwise disjoint and disjoint from
the residual, the residual is a subset, and every element lies in the residual or in a child.

Proof sketch: induction on `fuel` generalizing `rem`.  In the `some T` branch the recursive call
works inside `rem \ T`, so its children and residual are disjoint from `T` and
(`List.pairwise_cons`) the new list stays pairwise disjoint; an element of `rem` is in `T` or in
`rem \ T`. -/
theorem extractAux_partition (fuel : ℕ) (rem : Finset BitString) :
    (extractAux elig fuel rem).1.Pairwise Disjoint ∧
      (∀ T ∈ (extractAux elig fuel rem).1, Disjoint T (extractAux elig fuel rem).2) ∧
      (extractAux elig fuel rem).2 ⊆ rem ∧
      ∀ z ∈ rem, z ∈ (extractAux elig fuel rem).2 ∨ ∃ T ∈ (extractAux elig fuel rem).1, z ∈ T := by
  induction fuel generalizing rem with
  | zero => simp [extractAux]
  | succ fuel ih =>
    simp only [extractAux]
    split
    · simp
    · rename_i T hT
      obtain ⟨h1, h2, h3, h4⟩ := ih (rem \ T)
      have hchild := extractAux_children (elig := elig) fuel (rem \ T)
      refine ⟨List.pairwise_cons.mpr ⟨fun T' hT' => ?_, h1⟩, ?_, h3.trans Finset.sdiff_subset, ?_⟩
      · exact Finset.disjoint_of_subset_right (hchild T' hT').2 Finset.disjoint_sdiff
      · intro T' hT'
        rcases List.mem_cons.mp hT' with rfl | hT'
        · exact Finset.disjoint_of_subset_right h3 Finset.disjoint_sdiff
        · exact h2 T' hT'
      · intro z hz
        by_cases hzT : z ∈ T
        · exact Or.inr ⟨T, List.mem_cons_self, hzT⟩
        · rcases h4 z (Finset.mem_sdiff.mpr ⟨hz, hzT⟩) with h | ⟨T', hT', hzT'⟩
          · exact Or.inl h
          · exact Or.inr ⟨T', List.mem_cons_of_mem _ hT', hzT'⟩

/-- With enough fuel the residual has no eligible subset.

Proof sketch: induction on `fuel` generalizing `rem`.  Fuel `0` is impossible (`rem.card < 0`).
In the `none` branch use `firstEligible_none`.  In the `some T` branch `T` is nonempty
(`hne` and `firstEligible_some`) and `T ⊆ rem`, so `(rem \ T).card < rem.card < fuel + 1`
(`Finset.card_sdiff_lt` style), and the induction hypothesis applies. -/
theorem extractAux_residual (hne : ∀ T, elig T → T.Nonempty) (fuel : ℕ) (rem : Finset BitString)
    (hfuel : rem.card < fuel) : ∀ T ⊆ (extractAux elig fuel rem).2, ¬ elig T := by
  induction fuel generalizing rem with
  | zero => omega
  | succ fuel ih =>
    simp only [extractAux]
    split
    · rename_i h
      exact firstEligible_none h
    · rename_i T hT
      obtain ⟨hel, hsub⟩ := firstEligible_some hT
      apply ih (rem \ T)
      have hlt : (rem \ T).card < rem.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hsub (hne T hel))
      omega

/-- **Capped extraction (blueprint H01, `UpperExtract`).**  For an eligibility predicate that
implies nonemptiness, `extract elig F` returns eligible, pairwise disjoint children inside `F`,
disjoint from the residual; children and residual cover `F`; and no subset of the residual is
eligible. -/
theorem upperExtract (hne : ∀ T, elig T → T.Nonempty) (F : Finset BitString) :
    (∀ T ∈ (extract elig F).1, elig T ∧ T ⊆ F) ∧ (extract elig F).1.Pairwise Disjoint ∧
      (∀ T ∈ (extract elig F).1, Disjoint T (extract elig F).2) ∧ (extract elig F).2 ⊆ F ∧
      (∀ z ∈ F, z ∈ (extract elig F).2 ∨ ∃ T ∈ (extract elig F).1, z ∈ T) ∧
      ∀ T ⊆ (extract elig F).2, ¬ elig T := by
  obtain ⟨h1, h2, h3, h4⟩ := extractAux_partition (elig := elig) (F.card + 1) F
  exact ⟨extractAux_children (F.card + 1) F, h1, h2, h3, h4,
    extractAux_residual hne (F.card + 1) F (Nat.lt_succ_self _)⟩

/-- `List.sublists` of a primitive recursive list is primitive recursive: `List.sublists` is the
`List.foldr` of `acc ↦ acc.flatMap fun s => [s, a :: s]` starting from `[[]]`. -/
theorem extractPR_sublists_primrec {α β} [Primcodable α] [Primcodable β]
    {f : α → List β} (hf : Primrec f) : Primrec (fun a => (f a).sublists) := by
  have hstep : Primrec₂ (fun (a : α) (p : β × List (List β)) =>
      List.flatMap (fun s => [s, p.1 :: s]) p.2) := by
    have hf' : Primrec (fun q : α × (β × List (List β)) => q.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hg' : Primrec₂ (fun (q : α × (β × List (List β))) (s : List β) =>
        [s, q.2.1 :: s]) := by
      have h2 : Primrec (fun r : (α × (β × List (List β))) × List β => r.1.2.1 :: r.2) :=
        Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
      exact (Primrec.list_cons.comp Primrec.snd
        (Primrec.list_cons.comp h2 (Primrec.const []))).to₂
    exact (Primrec.list_flatMap hf' hg').to₂
  exact Primrec.list_foldr hf (Primrec.const ([[]] : List (List β))) hstep

/-! ### Forward iteration on sets -/

/-- One forward step of capped extraction on the state (children so far, remainder): select the
first eligible subset of the remainder, append it to the children and remove it; if nothing is
eligible, the state is unchanged. -/
def extractPRSetStep (el : Finset BitString → Prop) [DecidablePred el]
    (st : List (Finset BitString) × Finset BitString) :
    List (Finset BitString) × Finset BitString :=
  match firstEligible el st.2 with
  | none => st
  | some T => (st.1 ++ [T], st.2 \ T)

/-- If nothing is eligible in `rem`, `extractAux` stops immediately, whatever the fuel. -/
theorem extractPR_extractAux_none (el : Finset BitString → Prop) [DecidablePred el]
    {rem : Finset BitString} (h : firstEligible el rem = none) (n : ℕ) :
    extractAux el n rem = ([], rem) := by
  cases n with
  | zero => simp only [extractAux]
  | succ n => simp only [extractAux, h]

/-- Iterating the forward step `n` times from `(cs, rem)` appends the children of
`extractAux el n rem` to `cs` and returns its residual.

Proof: induction on `n` generalizing the state; `Function.iterate_succ_apply` peels the first
step; in the `none` case the state is a fixed point (`Function.iterate_fixed`). -/
theorem extractPR_iterate_eq (el : Finset BitString → Prop) [DecidablePred el] (n : ℕ) :
    ∀ (cs : List (Finset BitString)) (rem : Finset BitString),
      (extractPRSetStep el)^[n] (cs, rem) =
        (cs ++ (extractAux el n rem).1, (extractAux el n rem).2) := by
  induction n with
  | zero =>
    intro cs rem
    simp only [Function.iterate_zero, id_eq, extractAux, List.append_nil]
  | succ n ih =>
    intro cs rem
    rw [Function.iterate_succ_apply]
    cases hT : firstEligible el rem with
    | none =>
      have hfix : extractPRSetStep el (cs, rem) = (cs, rem) := by
        simp only [extractPRSetStep, hT]
      rw [hfix, Function.iterate_fixed hfix, extractPR_extractAux_none el hT, List.append_nil]
    | some T =>
      have hstep : extractPRSetStep el (cs, rem) = (cs ++ [T], rem \ T) := by
        simp only [extractPRSetStep, hT]
      rw [hstep, ih]
      simp only [extractAux, hT, List.append_assoc, List.singleton_append]

/-! ### The code-level step -/

/-- One forward step of capped extraction on codes.  The state is (codes of the children so far,
a list enumerating the remainder) and `test` is the eligibility test on set codes: the first
sublist `s` of the canonical listing of the remainder whose set code passes the test is recorded
(as the code of `s.toFinset`) and filtered out of the list. -/
noncomputable def extractPRStep (test : BitString → Bool) (st : List BitString × List BitString) :
    List BitString × List BitString :=
  match (canonicalFinsetList st.2.toFinset).sublists.find?
      (fun s => test (canonicalFiniteSetCode s.toFinset)) with
  | none => st
  | some s => (st.1 ++ [canonicalFiniteSetCode s.toFinset], st.2.filter fun x => !decide (x ∈ s))

/-- The code-level step is primitive recursive, uniformly in a primitive recursive test.

Proof: `Primrec.option_casesOn` over `list_find?_primrec` of `extractPR_sublists_primrec`; the
`some` branch is a list append and a `primrec_list_filter` with `bitString_mem_primrec`. -/
theorem extractPRStep_primrec {β : Type} [Primcodable β] {t : β → BitString → Bool}
    (ht : Primrec₂ t) :
    Primrec₂ fun (p : β) (st : List BitString × List BitString) => extractPRStep (t p) st := by
  have hsub : Primrec fun q : β × (List BitString × List BitString) =>
      (canonicalFinsetList q.2.2.toFinset).sublists :=
    extractPR_sublists_primrec (canonicalFinsetList_toFinset_primrec.comp
      (Primrec.snd.comp Primrec.snd))
  have hpred : Primrec₂ fun (q : β × (List BitString × List BitString)) (s : List BitString) =>
      t q.1 (canonicalFiniteSetCode s.toFinset) :=
    (ht.comp (Primrec.fst.comp Primrec.fst)
      (canonicalFiniteSetCode_toFinset_primrec.comp Primrec.snd)).to₂
  have hfind : Primrec fun q : β × (List BitString × List BitString) =>
      (canonicalFinsetList q.2.2.toFinset).sublists.find?
        (fun s => t q.1 (canonicalFiniteSetCode s.toFinset)) :=
    list_find?_primrec hsub hpred
  have hcodes : Primrec fun r : (β × (List BitString × List BitString)) × List BitString =>
      r.1.2.1 ++ [canonicalFiniteSetCode r.2.toFinset] :=
    Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (canonicalFiniteSetCode_toFinset_primrec.comp Primrec.snd)
        (Primrec.const []))
  have hnotmem : Primrec₂ fun (r : (β × (List BitString × List BitString)) × List BitString)
      (x : BitString) => !decide (x ∈ r.2) :=
    (Primrec.not.comp (bitString_mem_primrec.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst))).to₂
  have hrest : Primrec fun r : (β × (List BitString × List BitString)) × List BitString =>
      r.1.2.2.filter fun x => !decide (x ∈ r.2) :=
    primrec_list_filter (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hnotmem
  have hsome : Primrec₂ fun (q : β × (List BitString × List BitString)) (s : List BitString) =>
      (q.2.1 ++ [canonicalFiniteSetCode s.toFinset], q.2.2.filter fun x => !decide (x ∈ s)) :=
    (Primrec.pair hcodes hrest).to₂
  have h : Primrec fun q : β × (List BitString × List BitString) => extractPRStep (t q.1) q.2 := by
    refine (Primrec.option_casesOn hfind Primrec.snd hsome).of_eq fun q => ?_
    rcases hq : (canonicalFinsetList q.2.2.toFinset).sublists.find?
        (fun s => t q.1 (canonicalFiniteSetCode s.toFinset)) with _ | s
    · simp only [extractPRStep, hq]
    · simp only [extractPRStep, hq]
  exact h.to₂

/-! ### Simulation -/

/-- The code-level state `st'` represents the set-level state `st`: its codes are the canonical
codes of the children and its list enumerates the remainder. -/
def extractPRRel (st : List (Finset BitString) × Finset BitString)
    (st' : List BitString × List BitString) : Prop :=
  st'.1 = st.1.map canonicalFiniteSetCode ∧ st'.2.toFinset = st.2

/-- One code-level step simulates one set-level step, for a test that agrees with `el` on
canonical codes.

Proof: the two `find?` predicates agree (`htest`), so `firstEligible` is the `find?` result mapped
by `List.toFinset`; in the `some s` case the new code is that of `s.toFinset` and the filtered list
enumerates `rem \ s.toFinset`. -/
theorem extractPRStep_rel (el : Finset BitString → Prop) [DecidablePred el]
    (test : BitString → Bool) (htest : ∀ S, test (canonicalFiniteSetCode S) = decide (el S))
    {st : List (Finset BitString) × Finset BitString} {st' : List BitString × List BitString}
    (h : extractPRRel st st') : extractPRRel (extractPRSetStep el st) (extractPRStep test st') := by
  obtain ⟨cs, rem⟩ := st
  obtain ⟨cs', r⟩ := st'
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h1 h2
  have hfe : firstEligible el r.toFinset = ((canonicalFinsetList r.toFinset).sublists.find?
      (fun s => test (canonicalFiniteSetCode s.toFinset))).map List.toFinset := by
    simp only [firstEligible, htest]
  rcases hf : (canonicalFinsetList r.toFinset).sublists.find?
      (fun s => test (canonicalFiniteSetCode s.toFinset)) with _ | s
  · rw [hf] at hfe
    simp only [extractPRSetStep, extractPRStep, extractPRRel, hfe, hf, Option.map_none, and_self]
  · rw [hf] at hfe
    simp only [extractPRSetStep, extractPRStep, extractPRRel, hfe, hf, Option.map_some]
    refine ⟨by simp, ?_⟩
    ext x
    simp

/-- `n` code-level steps simulate `n` set-level steps (induction with
`Function.iterate_succ_apply'` and `extractPRStep_rel`). -/
theorem extractPR_rel_iterate (el : Finset BitString → Prop) [DecidablePred el]
    (test : BitString → Bool) (htest : ∀ S, test (canonicalFiniteSetCode S) = decide (el S))
    (n : ℕ) {st : List (Finset BitString) × Finset BitString}
    {st' : List BitString × List BitString} (h : extractPRRel st st') :
    extractPRRel ((extractPRSetStep el)^[n] st) ((extractPRStep test)^[n] st') := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact extractPRStep_rel el test htest ih

/-- The code-level extraction run on a parent code `w`: `|parent| + 1` code-level steps from (no
children, the canonical listing of the parent). -/
noncomputable def extractPRRun (test : BitString → Bool) (w : BitString) :
    List BitString × List BitString :=
  (extractPRStep test)^[(canonicalPointListOfCode w).length + 1] ([], canonicalPointListOfCode w)

/-- The code-level run represents `extract el (parseModel w)`.

Proof: the canonical listing is duplicate-free, so its length is `|parseModel w|`; combine
`extractPR_rel_iterate` with `extractPR_iterate_eq`. -/
theorem extractPRRun_rel (el : Finset BitString → Prop) [DecidablePred el]
    (test : BitString → Bool) (htest : ∀ S, test (canonicalFiniteSetCode S) = decide (el S))
    (w : BitString) : extractPRRel (extract el (parseModel w)) (extractPRRun test w) := by
  have hnd : (canonicalPointListOfCode w).Nodup := by
    unfold canonicalPointListOfCode
    exact canonicalFinsetList_nodup _
  have hlen : (canonicalPointListOfCode w).length = (parseModel w).card := by
    rw [parseModel, List.toFinset_card_of_nodup hnd]
  have h0 : extractPRRel ([], parseModel w) ([], canonicalPointListOfCode w) := by
    unfold extractPRRel
    exact ⟨rfl, rfl⟩
  have hR := extractPR_rel_iterate el test htest ((parseModel w).card + 1) h0
  rw [extractPR_iterate_eq, List.nil_append, Prod.mk.eta] at hR
  unfold extractPRRun
  rw [hlen, extract]
  exact hR

/-- **Extraction is a total computable finite search (blueprint H01, totality).**  If the
eligibility test of a set is primitive recursive on canonical codes, uniformly in a parameter
`p : β`, then the codes of the children and of the residual are primitive recursive (hence
computable, `Primrec.to_comp`) in `p` and the code of the parent.

Proof: `Primrec.nat_iterate` runs the primitive recursive code-level step `extractPRStep`
(`extractPRStep_primrec`) `|F| + 1` times from the canonical listing of the parent
(`extractPRRun`); `extractPRRun_rel` identifies the result with the codes of `extract`. -/
theorem extract_code_primrec {β : Type} [Primcodable β]
    (eligP : β → Finset BitString → Prop) [∀ p, DecidablePred (eligP p)]
    (htest : Primrec₂ fun (p : β) (w : BitString) => decide (eligP p (parseModel w))) :
    Primrec fun q : β × BitString =>
      (((extract (eligP q.1) (parseModel q.2)).1.map canonicalFiniteSetCode),
        canonicalFiniteSetCode (extract (eligP q.1) (parseModel q.2)).2) := by
  have hstep : Primrec₂ fun (p : β) (st : List BitString × List BitString) =>
      extractPRStep (fun w => decide (eligP p (parseModel w))) st :=
    extractPRStep_primrec htest
  have hfuel : Primrec fun q : β × BitString => (canonicalPointListOfCode q.2).length + 1 :=
    Primrec.succ.comp
      (Primrec.list_length.comp (canonicalPointListOfCode_primrec.comp Primrec.snd))
  have hinit : Primrec fun q : β × BitString =>
      (([] : List BitString), canonicalPointListOfCode q.2) :=
    Primrec.pair (Primrec.const []) (canonicalPointListOfCode_primrec.comp Primrec.snd)
  have hh : Primrec₂ fun (q : β × BitString) (st : List BitString × List BitString) =>
      extractPRStep (fun w => decide (eligP q.1 (parseModel w))) st :=
    (hstep.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hiter : Primrec fun q : β × BitString =>
      extractPRRun (fun w => decide (eligP q.1 (parseModel w))) q.2 :=
    (Primrec.nat_iterate hfuel hinit hh).of_eq fun q => by rw [extractPRRun]
  have hout : Primrec fun q : β × BitString =>
      ((extractPRRun (fun w => decide (eligP q.1 (parseModel w))) q.2).1,
        canonicalFiniteSetCode
          (extractPRRun (fun w => decide (eligP q.1 (parseModel w))) q.2).2.toFinset) :=
    Primrec.pair (Primrec.fst.comp hiter)
      (canonicalFiniteSetCode_toFinset_primrec.comp (Primrec.snd.comp hiter))
  refine hout.of_eq fun q => ?_
  obtain ⟨h1, h2⟩ := extractPRRun_rel (eligP q.1)
    (fun w => decide (eligP q.1 (parseModel w)))
    (fun S => by simp only [parseModel_canonicalFiniteSetCode]) q.2
  rw [h1, h2]

end Extract

end Kolmogorov.StrongMerging.Upper
