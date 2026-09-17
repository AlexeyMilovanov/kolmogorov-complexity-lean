import KolmogorovMathlib.Restricted.Improving
import KolmogorovMathlib.Restricted.GapCountingIn
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Deficiencies
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems
import KolmogorovMathlib.Restricted.DeficiencyEquiv.ProgrammedFamilies

/-!
# Marked-code selectors driven by a family program

The selection of high-multiplicity model codes, run from a program enumerating the family rather
than from the family itself. `progMarkedCodeSelectorFn` is the program-indexed selector built on
the program-indexed code stream, and `progMarkedCodeSelectorFn_eq_family` identifies it with the
selector of the family the program enumerates; `univMarkedCodeSelectorFn` reads the family
program from the first component of its argument, so one machine serves all families. The
computability lemmas for the candidate and stage code slices
(`progCandidateModelCodesList_computable`, `progStageModelCodesList_computable`,
`progMarkedCodeStream_computable`) are what make that uniform version legitimate. The
consequences are the uniform complexity bound `uniform_familyComplexityRefinedSet` and the
uniform description count `uniform_description_count_of_conditional_complexity_gap_ofEnum`.
-/

namespace Kolmogorov
open scoped ENNReal
open Kolmogorov.CodedFiniteDistribution
open Nat.Partrec (Code)

/-- Joint computability of the program-indexed candidate model-code slice. -/
theorem progCandidateModelCodesList_computable (c : Code) :
    Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have h1 : Primrec (fun q : (List BitString × List BitString × ℕ) × BitString =>
      decide (q.2 ∈ q.1.2.1)) :=
    bitString_mem_primrec.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have h2 : Primrec (fun q : (List BitString × List BitString × ℕ) × BitString =>
      isFamilyModelCodeBool q.1.2.2 q.2) :=
    (isFamilyModelCodeBool_primrec_uniform.comp
      (Primrec.pair Primrec.snd
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).of_eq fun q => rfl
  have hpred : Primrec₂ (fun (p : List BitString × List BitString × ℕ) (w : BitString) =>
      decide (w ∈ p.2.1) && isFamilyModelCodeBool p.2.2 w) := Primrec.and.comp h1 h2
  have h_filter : Computable (fun (p : List BitString × List BitString × ℕ) =>
      p.1.filter (fun w => decide (w ∈ p.2.1) && isFamilyModelCodeBool p.2.2 w)) :=
    (list_filter_primrec (f := fun p : List BitString × List BitString × ℕ => p.1)
      Primrec.fst hpred).to_comp
  have hcand : Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      (programmedEnum q.1.1.2 q.2, snapshotCodes c q.1.1.1 q.2, q.1.2)) := by
    apply Computable.pair;
    · convert programmedEnum_computable.comp ( Computable.pair _ _ ) using 1;
      · exact Computable.snd.comp ( Computable.fst.comp ( Computable.fst ) );
      · exact Computable.snd;
    · apply Computable.pair;
      · apply Computable.comp ( snapshotCodes_primrec c |> Primrec.to_comp )
          ( Computable.pair ( Computable.fst.comp ( Computable.fst.comp Computable.fst ) )
            ( Computable.snd ) );
      · exact Computable.snd.comp ( Computable.fst );
  refine (h_filter.comp hcand).of_eq ?_
  intro q
  rfl

/-
Joint computability of the program-indexed staged model-code list.
-/
theorem progStageModelCodesList_computable (c : Code) :
    Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      progStageModelCodesList c q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  have h_eraseDups : Computable (fun l : List BitString => l.eraseDups) := by
    exact eraseDups_bitstring_primrec.to_comp;
  have hg : Computable (fun q : ((ℕ × BitString) × ℕ) × ℕ =>
      (progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 0).eraseDups) := by
    refine (h_eraseDups.comp ((progCandidateModelCodesList_computable c).comp
      (Computable.pair Computable.fst (Computable.const 0)))).of_eq ?_
    intro q
    rfl
  have hh : Computable₂ (fun (q : ((ℕ × BitString) × ℕ) × ℕ) (r : ℕ × List BitString) =>
      (r.2 ++ progCandidateModelCodesList c q.1.1.1 q.1.1.2 q.1.2 (r.1 + 1)).eraseDups) := by
    refine (h_eraseDups.comp (Computable.list_append.comp
      (Computable.snd.comp Computable.snd)
      ((progCandidateModelCodesList_computable c).comp
        (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.succ.comp (Computable.fst.comp Computable.snd)))))).of_eq ?_
    intro q
    rfl
  convert Computable.nat_rec (f := fun q => q.2) Computable.snd hg hh using 1;
  exact funext fun q => by induction q.2 <;> simp +decide [ *, progStageModelCodesList ] ;

/-
Joint computability of the program-indexed marked-code stream.
-/
theorem progMarkedCodeStream_computable (c : Code) :
    Computable (fun q : (((((ℕ × BitString) × ℕ) × ℕ) × ℕ) × ℕ) =>
      progMarkedCodeStream c q.1.1.1.1.1 q.1.1.1.1.2 q.1.1.1.2 q.1.1.2 q.1.2 q.2) := by
  revert c;
  intro c
  unfold progMarkedCodeStream
  apply ( selectionStrategyOnline_primrec_uniform.to_comp.comp ?_ ).of_eq ?_;
  · exact fun n =>
      ( ( n.1.1.1.2, n.1.1.1.1.1, n.1.1.2, n.1.2 ),
        progStageModelCodesList c n.1.1.1.1.1 n.1.1.1.1.2 n.1.1.2 n.2 );
  · refine Computable.pair ?_ ?_;
    · apply Computable.pair;
      · exact Computable.snd.comp ( Computable.fst.comp ( Computable.fst.comp ( Computable.fst
          ) ) );
      · apply Computable.pair;
        · exact Computable.fst.comp ( Computable.fst.comp ( Computable.fst.comp (
            Computable.fst.comp Computable.fst ) ) );
        · exact Computable.pair ( Computable.snd.comp ( Computable.fst.comp ( Computable.fst )
            ) ) ( Computable.snd.comp ( Computable.fst ) );
    · convert progStageModelCodesList_computable c |> Computable.comp
        <| Computable.pair _ _ using 1;
      rotate_left;
      · exact fun n => ( n.1.1.1.1, n.1.1.2 );
      · exact fun n => n.2;
      · exact Computable.pair ( Computable.fst.comp ( Computable.fst.comp (
          Computable.fst.comp ( Computable.fst ) ) ) ) ( Computable.snd.comp (
            Computable.fst.comp ( Computable.fst ) ) );
      · exact Computable.snd;
      · rfl;
  · grind

/-- Program-indexed marked-code selector, using `progMarkedCodeStream`. -/
noncomputable def progMarkedCodeSelectorFn (c : Code) (p : BitString) : BitString →. BitString :=
  fun s =>
    let n := selN s
    let i := selI s
    let j := selJ s
    let k := selK s
    let r := selR s
    (Nat.rfind (fun t =>
        Part.some (decide (r < (progMarkedCodeStream c i p n j k t).eraseDups.length)))).bind
      (fun t =>
        let stream := (progMarkedCodeStream c i p n j k t).eraseDups
        Part.some (stream.getD r []))

/-- The selector computed from a program agrees with that of the family it enumerates. -/
theorem progMarkedCodeSelectorFn_eq_family (c : Code) (p : BitString)
    (mem : Finset BitString → Prop) (hp : IsProgramForFamily p mem) (s : BitString) :
    progMarkedCodeSelectorFn c p s = familyMarkedCodeSelectorFn c (programmedFamily p mem hp)
        s := by
  simp only [progMarkedCodeSelectorFn, familyMarkedCodeSelectorFn,
    progMarkedCodeStream_eq_family c (selI s) p mem hp (selN s) (selJ s) (selK s)]

/-- Universal marked-code selector: reads the family program `p` from the first
component of its input and the marked-selector word from the second. -/
noncomputable def univMarkedCodeSelectorFn (c : Code) : BitString →. BitString :=
  fun s => progMarkedCodeSelectorFn c (decodeFirst s) (decodeSecond s)

section UnivMarkedSelectorPartrec
-- Mirror `familyMarkedCodeSelectorFn_partrec`: sealing these `def`s prevents a
-- `whnf` blow-up when the final `of_eq` reconciles the composed function with the
-- unfolded selector.
attribute [local irreducible] progMarkedCodeStream selN selI selJ selK selR

/-- The universal marked-code selector is partial recursive. -/
theorem univMarkedCodeSelectorFn_partrec (c : Code) : Partrec (univMarkedCodeSelectorFn c) := by
  have dS : Computable (fun st : BitString × ℕ => decodeSecond st.1) :=
    decodeSecond_computable.comp Computable.fst
  have dF : Computable (fun st : BitString × ℕ => decodeFirst st.1) :=
    decodeFirst_computable.comp Computable.fst
  have h_stream : Computable (fun st : BitString × ℕ =>
      (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1)
          (selN (decodeSecond st.1))
        (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups) :=
    eraseDups_bitstring_primrec.to_comp.comp
      ((progMarkedCodeStream_computable c).comp
        (((((((selI_computable.comp dS).pair dF).pair (selN_computable.comp dS)).pair
          (selJ_computable.comp dS)).pair (selK_computable.comp dS)).pair Computable.snd)))
  have h_lt : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
    obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel (α := ℕ) (· < ·))
    convert h.to_comp
  have h_check : Computable (fun st : BitString × ℕ =>
      decide (selR (decodeSecond st.1) <
        (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1)
            (selN (decodeSecond st.1))
          (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups.length)) :=
    h_lt.comp ((selR_computable.comp dS).pair (Computable.list_length.comp h_stream))
  have h_post : Computable (fun st : BitString × ℕ =>
      (progMarkedCodeStream c (selI (decodeSecond st.1)) (decodeFirst st.1)
          (selN (decodeSecond st.1))
        (selJ (decodeSecond st.1)) (selK (decodeSecond st.1)) st.2).eraseDups.getD
        (selR (decodeSecond st.1)) []) :=
    ((Primrec.list_getD ([] : BitString)).to_comp).comp h_stream (selR_computable.comp dS)
  exact (Partrec.bind (Partrec.rfind h_check.to₂.partrec₂) h_post.to₂.partrec₂).of_eq
    (fun s => rfl)

end UnivMarkedSelectorPartrec

/-- Uniform (program-indexed) version of `selected_family_code_setComplexity_bound`,
charging `KPPlain U p` via the universal marked-code selector. -/
theorem uniform_selected_code_setComplexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : Code) :
    ∃ c_slack : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop)
      (hp : IsProgramForFamily p mem)
      (n i j k t : ℕ) (w : BitString) (S : Finset BitString) (hS : S.Nonempty),
      k ≤ i →
      w ∈ familyMarkedCodeStream c i (programmedFamily p mem hp) n j k t →
      w = (codedUniformOn S hS).code →
      setComplexity U S hS ≤ (i - k : ENat) + logSlack c_slack (n + i + j) + KPPlain U p := by
  obtain ⟨c_map, hc_map⟩ := KPPlain_partrec_map_le U hU (univMarkedCodeSelectorFn c)
    (univMarkedCodeSelectorFn_partrec c)
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_input, hc_input⟩ := familyMarkedInput_KPPlain_le_addr U hU (c_pair + c_map)
  obtain ⟨c_fold, hc_fold⟩ := logSlack_linear_bound c_input 5 10
  refine ⟨c_fold + 20, fun p mem hp n i j k t w S hS hk hw_stream hcode => ?_⟩
  set 𝒜 := programmedFamily p mem hp with h𝒜
  obtain ⟨r, hr_stage, hget_t⟩ :=
    exists_rank_getD_eraseDups (familyMarkedCodeStream c i 𝒜 n j k t) hw_stream
  have hr_bound : r < (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) := by
    exact lt_of_lt_of_le hr_stage
      (le_trans (eraseDups_bitString_length_le _)
        (familyMarkedCodeStream_length_bound c i 𝒜 n j k t))
  let M := n + i + j
  let P := 2 * ((i + 2) * (i + 1) * (n + 1))
  let q := (Nat.bits P).length
  let m := i - k + q
  have hpowP : P < 2 ^ q := by
    simpa [P, q] using lt_two_pow_length_natBits P
  have hexp : i + 1 - k = i - k + 1 := by omega
  have hbound_eq :
      (i + 2) * (i + 1) * (n + 1) * 2 ^ (i + 1 - k) =
        P * 2 ^ (i - k) := by
    simp [P, hexp, pow_succ]
    ring
  have hr_pow_m : r < 2 ^ (m + 1) := by
    have hlt : r < P * 2 ^ (i - k) := by
      simpa [hbound_eq] using hr_bound
    have hmul : P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hpowP)
    have hpow : 2 ^ q * 2 ^ (i - k) = 2 ^ m := by
      rw [show m = q + (i - k) by omega, pow_add]
    exact lt_of_lt_of_le hlt (by
      calc P * 2 ^ (i - k) ≤ 2 ^ q * 2 ^ (i - k) := hmul
        _ = 2 ^ m := hpow
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ m))
  let h_exists : ∃ u, r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length := ⟨t, hr_stage⟩
  let t0 := Nat.find h_exists
  have ht0_lt : r < (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.length :=
    Nat.find_spec h_exists
  have ht0_le_t : t0 ≤ t :=
    Nat.find_le (p := fun u => r < (familyMarkedCodeStream c i 𝒜 n j k u).eraseDups.length) hr_stage
  have hfirst : ∀ t' < t0, ¬(r < (familyMarkedCodeStream c i 𝒜 n j k t').eraseDups.length) := by
    intro t' ht'
    exact Nat.find_min h_exists ht'
  have hpre : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups <+:
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups :=
    familyMarkedCodeStream_eraseDups_prefix_of_le c i 𝒜 n j k ht0_le_t
  have hget_t0 : (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups.getD r [] = w := by
    have hget := StagedEnumeration.getD_eq_of_prefix
      (familyMarkedCodeStream c i 𝒜 n j k t0).eraseDups
      (familyMarkedCodeStream c i 𝒜 n j k t).eraseDups hpre r [] ht0_lt
    rw [← hget_t]
    exact hget.symm
  have hsel_eq := familyMarkedCodeSelectorFn_eq_of_rank c 𝒜 n i j k r t0 ht0_lt hfirst
  rw [hget_t0] at hsel_eq
  -- Bridge to the universal selector on the `p`-padded input.
  have huniv : univMarkedCodeSelectorFn c (pairCode p (familyMarkedInput n i j k r)) =
      Part.some w := by
    unfold univMarkedCodeSelectorFn
    rw [decodeFirst_pairCode, decodeSecond_pairCode, progMarkedCodeSelectorFn_eq_family c p mem hp]
    exact hsel_eq
  have hw_sel : w ∈ univMarkedCodeSelectorFn c (pairCode p (familyMarkedInput n i j k r)) :=
    Part.eq_some_iff.mp huniv
  have hcomp1 : KPPlain U w ≤ KPPlain U (pairCode p (familyMarkedInput n i j k r)) + (c_map :
      ENat) :=
    hc_map (pairCode p (familyMarkedInput n i j k r)) w hw_sel
  have hchain : KPPlain U w ≤
      KPPlain U p + (KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) : ENat)) := by
    calc KPPlain U w ≤ KPPlain U (pairCode p (familyMarkedInput n i j k r)) + (c_map : ENat)
        := hcomp1
      _ ≤ (KPPlain U p + KPPlain U (familyMarkedInput n i j k r) + (c_pair : ENat)) + (c_map :
          ENat) := by
            gcongr
            exact hc_pair p (familyMarkedInput n i j k r)
      _ = KPPlain U p + (KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) :
          ENat)) := by
            push_cast; ring
  have hcomp2 : KPPlain U (familyMarkedInput n i j k r) + ((c_pair + c_map : ℕ) : ENat) ≤
      ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) :=
    hc_input n i j k r m hr_pow_m
  have hq : q ≤ 3 * (Nat.bits M).length + 10 := by
    simpa [M, P, q] using markedStream_poly_bits_bound n i j
  have hbudget : n + i + j + k + m ≤ 5 * M + 10 := by
    have hWle : (Nat.bits M).length ≤ M := length_natBits_le M
    simp [M, m]
    omega
  have hfold : logSlack c_input (n + i + j + k + m) ≤ logSlack c_fold M := by
    exact (logSlack_mono (c := c_input) hbudget).trans (hc_fold M)
  have hqslack : 3 * (Nat.bits M).length + 11 + logSlack c_fold M ≤
      logSlack (c_fold + 20) M := by
    have e : logSlack (c_fold + 20) M
        = logSlack c_fold M + (20 * (Nat.bits M).length + 20) := by
      unfold logSlack; ring
    omega
  have htotal : ((m : ENat) + 1) + logSlack c_input (n + i + j + k + m) ≤
      (i - k : ENat) + logSlack (c_fold + 20) M := by
    have hm_le : m + 1 ≤ (i - k) + (3 * (Nat.bits M).length + 11) := by
      simp [m]
      omega
    have hnat : m + 1 + logSlack c_input (n + i + j + k + m) ≤
        (i - k) + logSlack (c_fold + 20) M := by
      have hnat1 : m + 1 + logSlack c_input (n + i + j + k + m) ≤
          (i - k) + (3 * (Nat.bits M).length + 11 + logSlack c_fold M) := by
        omega
      omega
    exact_mod_cast hnat
  have hfinal : KPPlain U w ≤ KPPlain U p + ((i - k : ENat) + logSlack (c_fold + 20) M) := by
    refine hchain.trans ?_
    exact add_le_add_right (hcomp2.trans htotal) (KPPlain U p)
  unfold setComplexity
  rw [← hcode]
  calc KPPlain U w ≤ KPPlain U p + ((i - k : ENat) + logSlack (c_fold + 20) M) := hfinal
    _ = (i - k : ENat) + logSlack (c_fold + 20) M + KPPlain U p := by ring

/-- Uniform selected-set complexity lemma. -/
theorem uniform_familyComplexityRefinedSet (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString) (mem : Finset BitString → Prop),
      IsProgramForFamily p mem →
      ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      ManyIJDescriptionsMem mem U x i j k →
      k ≤ i →
      ∃ (S : Finset BitString) (hS : S.Nonempty), mem S ∧ x ∈ S ∧
        setComplexity U S hS ≤ (i - k + logSlack c (n + i + j) + KPPlain U p : ENat) ∧
        S.card ≤ 2 ^ (j + logSlack c (n + i + j)) := by
  obtain ⟨c_opt, hc_opt⟩ : ∃ c_opt : Code, IsCodeFor c_opt U :=
    Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_slack, hc_slack⟩ := uniform_selected_code_setComplexity_bound U hU c_opt
  refine ⟨c_slack, ?_⟩
  intro p mem hp x n i j k hn hmany hk
  set 𝒜 := programmedFamily p mem hp with h𝒜
  have hmany_in : ManyIJDescriptionsIn 𝒜 U x i j k :=
    (manyIJDescriptionsMem_iff_in p mem programmedEnum programmedEnum_computable
      hp.mono hp.sound hp.complete U x i j k).mp hmany
  obtain ⟨t, ht⟩ := manyIJDescriptionsIn_visible_stage hc_opt 𝒜 x n i j k hn hmany_in
  obtain ⟨w, hw_stream, hw_desc⟩ := familyMarkedCodeStream_covers_many c_opt i 𝒜 n j k t x hn ht
  rcases hw_desc with ⟨S, hS, hmemS, hcode_eq, hcard, hxS⟩
  have hcomp := hc_slack p mem hp n i j k t w S hS hk hw_stream hcode_eq
  refine ⟨S, hS, hmemS.1, hxS, ?_, ?_⟩
  · calc setComplexity U S hS
        ≤ (i - k : ENat) + logSlack c_slack (n + i + j) + KPPlain U p := hcomp
      _ = (i - k + logSlack c_slack (n + i + j) + KPPlain U p : ENat) := by ring
  · refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact Nat.cast_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))

/-!
### `enum`-dependent forms of the two uniform leaves

The two uniform leaves above place `∃ c` *before* the family program `p`.  This is
sound precisely because the family is presented through the *fixed universal
interpreter* `programmedEnum` (so `c` is a single constant for that interpreter)
and the extra representation cost is paid by `KPPlain U p`.  With an *arbitrary*
host-language enumerator `enum` the same quantifier order would be unsound (an
adversarial `enum` could hide an arbitrarily complex family behind a trivial `p`),
so the lemmas below record the paper-faithful `enum`-relative statements, where the
constant is chosen after the enumerator.  They are proved by transporting the
fixed-family results (`restricted_description_count_of_conditional_complexity_gap_aux`,
`exists_familyComplexityRefinedSet`) along the `uniformPreFamily` bridge; no
`KPPlain U p` budget is needed once `c` may depend on `enum`. -/

/-- Sound form of `uniform_description_count_of_conditional_complexity_gap`:
the constant is chosen after the enumerator. -/
theorem uniform_description_count_of_conditional_complexity_gap_ofEnum
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (p : BitString) (mem : Finset BitString → Prop) (enum : BitString → ℕ → List BitString)
    (henum : Computable (fun p_t : BitString × ℕ => enum p_t.1 p_t.2))
    (hmono : ∀ t, enum p t <+: enum p (t + 1))
    (hsound : ∀ t, ∀ w ∈ enum p t, ∃ (S : Finset BitString) (hS : S.Nonempty),
      mem S ∧ w = (codedUniformOn S hS).code)
    (hcomplete : ∀ (S : Finset BitString) (hS : S.Nonempty), mem S →
      ∃ t, (codedUniformOn S hS).code ∈ enum p t) :
    ∃ c : ℕ, ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n i j m kx : ℕ),
      x.length = n →
      mem A →
      x ∈ A →
      setComplexity U A hA ≤ (i : ENat) →
      A.card ≤ 2 ^ j →
      HasPrefixComplexityValue U x kx →
      ¬ ManyIJDescriptionsMem mem U x i j m →
      KP U (codedUniformOn A hA).code (prefixComplexityContext x kx)
        ≤ (m + logSlack c (n + i + j) : ENat) := by
  obtain ⟨c, hc⟩ := restricted_description_count_of_conditional_complexity_gap_aux U hU
    (uniformPreFamily p mem enum henum hmono hsound hcomplete)
  refine ⟨c, fun A hA x n i j m kx hn hmem hx hi hj hkx hnm => ?_⟩
  refine hc A hA x n i j m kx hn ⟨hmem, hA⟩ hx hi hj hkx ?_
  intro hIn
  exact hnm ((manyIJDescriptionsMem_iff_in p mem enum henum hmono hsound hcomplete
    U x i j m).mpr hIn)

end Kolmogorov
