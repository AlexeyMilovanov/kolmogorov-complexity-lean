import KolmogorovMathlib.Restricted.Family
import KolmogorovMathlib.Restricted.CoverSearch
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.CurveRealization

/-!
# M2: basic properties of the restricted profile

This file records the restricted analogues of the elementary endpoint
properties of the unrestricted description profile.  The cover/shift statement
`inDescriptionProfileIn_cover_shift` is the first place where condition
(3), the family enumeration, and the enumeration-complexity layer interact.
-/

namespace Kolmogorov

/-- M2(a1): every restricted family contains the full cube, so every
length-`n` string has an `𝒜`-description at `(O(log n), n)`. -/
theorem inDescriptionProfileIn_fullCube_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (𝒜 : DescriptionFamily) (x : BitString) (n : ℕ),
      x.length = n →
      InDescriptionProfileIn 𝒜 U x (logSlack c n) n := by
  obtain ⟨c, hc⟩ := fullSetComplexityGate U hU
  refine ⟨c, fun 𝒜 x n hxlen => ?_⟩
  have hx : x ∈ stringsOfLength n := (memStringsOfLength n x).mpr hxlen
  have hcube_nonempty : (stringsOfLength n).Nonempty := ⟨x, hx⟩
  refine ⟨stringsOfLength n, hcube_nonempty, 𝒜.fullCube n, ?_⟩
  exact ⟨hx, hc n hcube_nonempty, le_of_eq (cardStringsOfLength n)⟩

/-- M2(a2): condition (2)+(3) gives every singleton, so every length-`n`
string has an `𝒜`-description at `(K(x)+O(log n), 0)`.  The paper states
`O(1)`; this gate-shaped version keeps the existing repository slack
convention from `SingletonSetComplexityGate`. -/
theorem inDescriptionProfileIn_singleton_of_optimal
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (𝒜 : DescriptionFamily) (x : BitString) (n kx : ℕ),
      x.length = n →
      KPPlain U x = (kx : ENat) →
      InDescriptionProfileIn 𝒜 U x (kx + logSlack c n) 0 := by
  obtain ⟨c, hc⟩ := singletonSetComplexityGate U hU
  refine ⟨c, fun 𝒜 x n kx hxlen hkx => ?_⟩
  refine ⟨{x}, Finset.singleton_nonempty x, 𝒜.singleton_mem x, ?_⟩
  exact ⟨by simp, hc x n kx hxlen hkx, by simp⟩

/-- **Combinatorial half of M2(a3).**  From a family member `A` with
`A.card ≤ 2^j`, condition (3) applied with covering size `c = max 1 (A.card / 2^k)`
produces a cover of the `n`-bit part of `A` by family members of card `≤ 2^(j-k)`,
using at most `overhead n · 2^(k+1)` sets.

This packages the size/membership/ordinal-count content of the restricted
description shift with no computability: every covering set is in `𝒜` and small
enough to give log-size `j - k`, `x` lies in one of them, and the number of
covering sets (hence the ordinal of the selected set) is bounded by
`overhead n · 2^(k+1)`.  The remaining content of `inDescriptionProfileIn_cover_shift`
is exactly the *complexity* bound on the selected covering set (see the note
there). -/
theorem exists_family_cover (𝒜 : DescriptionFamily) {A : Finset BitString}
    (hA : 𝒜.mem A) (n j k : ℕ) (hcard : A.card ≤ 2 ^ j) (hk : k ≤ j) :
    ∃ 𝒞 : List (Finset BitString),
      (∀ B ∈ 𝒞, 𝒜.mem B ∧ B.card ≤ 2 ^ (j - k)) ∧
      (∀ y ∈ A, y.length = n → ∃ B ∈ 𝒞, y ∈ B) ∧
      𝒞.length ≤ 𝒜.overhead n * 2 ^ (k + 1) := by
  have hAne : A.Nonempty := 𝒜.nonempty_of_mem hA
  set P : ℕ := 2 ^ k with hP
  have hPpos : 0 < P := by positivity
  set q : ℕ := A.card / P with hq
  set c : ℕ := max 1 q with hc
  have hqc : q ≤ c := le_max_right 1 q
  have h1c : 1 ≤ c := le_max_left 1 q
  have hcpos : 0 < c := h1c
  have hqA : q ≤ A.card := Nat.div_le_self _ _
  have h1A : 1 ≤ A.card := hAne.card_pos
  have hcA : c ≤ A.card := max_le h1A hqA
  have hsplit : (2 : ℕ) ^ j = 2 ^ (j - k) * P := by
    rw [hP, ← pow_add, Nat.sub_add_cancel hk]
  have hqle : q ≤ 2 ^ (j - k) := by
    have h : P * q ≤ P * 2 ^ (j - k) := by
      calc P * q ≤ A.card := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self A.card P
        _ ≤ 2 ^ j := hcard
        _ = 2 ^ (j - k) * P := hsplit
        _ = P * 2 ^ (j - k) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h hPpos
  have hcsize : c ≤ 2 ^ (j - k) := max_le (Nat.one_le_two_pow) hqle
  obtain ⟨𝒞, hsmall, hcover, hlen⟩ := 𝒜.cover hA n c hcpos hcA
  refine ⟨𝒞, ?_, hcover, ?_⟩
  · intro B hB
    obtain ⟨hBmem, hBcard⟩ := hsmall B hB
    exact ⟨hBmem, hBcard.trans hcsize⟩
  · have hmod : A.card % P < P := Nat.mod_lt _ hPpos
    have hdm : P * q + A.card % P = A.card := Nat.div_add_mod A.card P
    have hAlt : A.card < P * (q + 1) := by
      have hgoal : P * (q + 1) = P * q + P := by ring
      rw [hgoal, ← hdm]
      exact Nat.add_lt_add_left hmod (P * q)
    have hq1 : q + 1 ≤ 2 * c := by
      have := Nat.add_le_add hqc h1c
      omega
    have hA2 : A.card ≤ 2 * P * c := by
      calc A.card ≤ P * (q + 1) := Nat.le_of_lt hAlt
        _ ≤ P * (2 * c) := by gcongr
        _ = 2 * P * c := by ring
    have hstep : 𝒞.length * c ≤ (𝒜.overhead n * 2 ^ (k + 1)) * c := by
      calc 𝒞.length * c ≤ 𝒜.overhead n * A.card := hlen
        _ ≤ 𝒜.overhead n * (2 * P * c) := by gcongr
        _ = (𝒜.overhead n * 2 ^ (k + 1)) * c := by rw [hP, pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right hstep hcpos

/-
**Enumeration-stage refinement of `exists_family_cover`.**  A good cover of
the `n`-bit part of a family member `A` can be found whose members' canonical
codes all appear inside a *single* enumeration stage `𝒜.enumeration.enum T`.

This packages the completeness+monotonicity argument of the family enumeration:
take the combinatorial cover of `exists_family_cover`, use
`𝒜.enumeration.complete` to place each member's code in some stage, and take `T`
to be the maximum of those finitely many stages so that `mono` collects all
codes into `enum T`.  It is the pure (non-computability) core needed by the
canonical cover search in `exists_coverSelector`.
-/
theorem exists_cover_codes_in_stage (𝒜 : DescriptionFamily) {A : Finset BitString}
    (hA : 𝒜.mem A) (x : BitString) (n j k : ℕ) (hcard : A.card ≤ 2 ^ j) (hk : k ≤ j)
    (hxA : x ∈ A) (hxn : x.length = n) :
    ∃ (T : ℕ) (𝒞 : List (Finset BitString)),
      (∀ B ∈ 𝒞, 𝒜.mem B ∧ B.card ≤ 2 ^ (j - k)) ∧
      (∀ B ∈ 𝒞, ∃ (hB : B.Nonempty),
        (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum T) ∧
      (∃ B ∈ 𝒞, x ∈ B) ∧
      𝒞.length ≤ 𝒜.overhead n * 2 ^ (k + 1) := by
  obtain ⟨𝒞, h𝒞⟩ := exists_family_cover 𝒜 hA n j k hcard hk;
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ B ∈ 𝒞, ∃ hB : B.Nonempty,
      (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum T := by
    have hT : ∀ B ∈ 𝒞, ∃ t : ℕ, ∃ hB : B.Nonempty,
        (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum t := by
      intros B hB
      obtain ⟨hB_mem, hB_card⟩ := h𝒞.left B hB
      have hB_nonempty : B.Nonempty := 𝒜.nonempty_of_mem hB_mem
      exact ⟨_, hB_nonempty,
        𝒜.enumeration.complete B hB_nonempty hB_mem |> Classical.choose_spec⟩
    choose! t ht using hT;
    use Finset.sup (𝒞.toFinset) t;
    intro B hB
    obtain ⟨hB_nonempty, hB_mem⟩ := ht B hB
    use hB_nonempty;
    have h_mono : ∀ t1 t2 : ℕ, t1 ≤ t2 → 𝒜.enumeration.enum t1 <+: 𝒜.enumeration.enum t2 := by
      intro t1 t2 ht
      induction ht with
      | refl => exact List.prefix_rfl
      | step _ ih => exact ih.trans (𝒜.enumeration.mono _)
    exact h_mono _ _ ( Finset.le_sup ( f :=
        t ) ( List.mem_toFinset.mpr hB ) ) |> fun h => h.subset hB_mem;
  exact ⟨ T, 𝒞, h𝒞.1, hT, h𝒞.2.1 x hxA hxn, h𝒞.2.2 ⟩

/-
**Termination witness for the cover search.**  From the combinatorial cover
(`exists_family_cover` with covering size `c = max 1 (#A / 2^k)`, whose members
all appear in one enumeration stage) there is a valid address `p`: some
enumeration stage together with the list of the cover members' codes passes
`coverValidBool` for the target `{ y ∈ A | y.length = n }`.
-/
theorem exists_valid_coverAddress (𝒜 : DescriptionFamily) {A : Finset BitString}
    (hA : A.Nonempty) (hmemA : 𝒜.mem A) (n k : ℕ) :
    ∃ p, coverValidBool 𝒜 (codedUniformOn A hA).code n k (𝒜.overhead n) p = true := by
  obtain ⟨𝒞, h𝒞⟩ := 𝒜.cover hmemA n (max 1 (A.card / 2 ^ k)) (by
  positivity) (by
  exact max_le ( by linarith [ Finset.card_pos.mpr hA ] ) ( Nat.div_le_self _ _ ))
  generalize_proofs at *; (
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ∀ B ∈ 𝒞, ∃ (hB : B.Nonempty),
      (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum T := by
    have hT : ∀ B ∈ 𝒞, ∃ T : ℕ, ∃ (hB : B.Nonempty),
        (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum T := by
      intro B hB
      obtain ⟨hB_mem, hB_card⟩ := h𝒞.left B hB
      generalize_proofs at *; (
      exact ⟨ _, _,
          𝒜.enumeration.complete B ( 𝒜.nonempty_of_mem hB_mem ) hB_mem |> Classical.choose_spec ⟩)
    generalize_proofs at *; (
    have hT : ∀ B ∈ 𝒞, ∃ T : ℕ, ∀ t ≥ T, ∃ (hB : B.Nonempty),
        (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum t := by
      intro B hB
      obtain ⟨T, hT⟩ := hT B hB
      use T
      intro t ht
      obtain ⟨hB, hB_code⟩ := hT
      have hB_code_t : (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum t := by
        have hB_code_t : ∀ t ≥ T, (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum t := by
          intro t ht
          have hB_code_t : (codedUniformOn B hB).code ∈ 𝒜.enumeration.enum T := hB_code
          have hB_code_t_mono : ∀ t ≥ T, 𝒜.enumeration.enum T <+: 𝒜.enumeration.enum t := by
            exact fun t ht =>
                by induction ht <;> [ tauto; exact List.IsPrefix.trans ‹_› (
                    𝒜.enumeration.mono _ ) ] ;
          exact List.IsPrefix.subset ( hB_code_t_mono t ht ) hB_code_t
        generalize_proofs at *; (
        exact hB_code_t t ht)
      generalize_proofs at *; (
      exact ⟨ hB, hB_code_t ⟩)
    generalize_proofs at *; (
    choose! T hT using hT
    generalize_proofs at *; (
    exact ⟨ Finset.sup (𝒞.toFinset) T, fun B hB => hT B hB _ ( Finset.le_sup ( f :=
        T ) ( List.mem_toFinset.mpr hB ) ) ⟩)))
  generalize_proofs at *; (
  refine ⟨ Encodable.encode ( T, ( List.pmap ( fun B hB =>
      ( codedUniformOn B hB ).code ) 𝒞 ( fun B hB => hT B hB |> Classical.choose ) ) ), ?_ ⟩ ;
  simp +decide only [coverValidBool, Encodable.encode_prod_val, Encodable.encode_nat,
    le_sup_iff, Bool.decide_or, List.all_filter, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, List.any_eq_true] ;
  refine ⟨ ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩, ?_ ⟩ <;>
    simp +decide only [le_sup_iff, coverDecode, decodeCoverCodeList_code, mem_canonicalFinsetList,
      Encodable.decode_prod_val, Nat.unpair_pair, Encodable.decode_nat, Encodable.encodek,
      Option.map_some, Option.bind_some, Option.getD_some, List.mem_pmap, List.length_pmap,
      forall_exists_index, ↓existsAndEq, true_and, exists_prop] at *; (
  · grind +qlia);
  · have h_card_bound : A.card < 2 ^ k * (A.card / 2 ^ k + 1) ∧ A.card / 2 ^ k + 1 ≤ 2 * max 1
      (A.card / 2 ^ k) := by
      exact ⟨ by linarith [ Nat.div_add_mod A.card ( 2 ^ k ),
          Nat.mod_lt A.card ( pow_pos ( by decide : 0 < 2 ) k ) ],
              by cases max_cases 1 ( A.card / 2 ^ k ) <;> linarith ⟩
    generalize_proofs at *; (
    rw [ pow_succ' ] ; nlinarith [ Nat.zero_le ( 𝒜.overhead n ),
        Nat.zero_le ( A.card / 2 ^ k ), Nat.zero_le ( max 1 ( A.card / 2 ^ k ) ) ] ;);
  · intro x B hB hx; subst hx; simp +decide only [decodeCoverCodeList_code] ;
    rw [ List.dedup_eq_self.mpr, List.dedup_eq_self.mpr ] <;> norm_num [ h𝒞.1 B hB ];
    · exact Finset.sort_nodup _ _;
    · exact canonicalFinsetList_nodup B;
  · exact fun x hx => Classical.or_iff_not_imp_left.2 fun hx' =>
      h𝒞.2.1 x hx <| by simpa using hx';))

/-
**The computable cover-selector (M2(a3) computable core).**

The genuinely hard, computability-heavy content of the restricted description
shift, isolated as a single leaf so that the profile-level statement
`inDescriptionProfileIn_cover_shift` below is proved from it by pure accounting.

There is a fixed partial-recursive selector `f` (depending only on the family
`𝒜`) and a family constant `c₀` such that: for every family member `A`
containing a length-`n` string `x` with `A.card ≤ 2^j` and every `k ≤ j`, there
is a covering family member `B ∋ x` of card `≤ 2^(j-k)` whose canonical uniform
code `f` recovers from `pairCode A.code z`, where the address `z` is **short**:
`z.length ≤ k + c₀·(|bits n| + |bits k| + |bits (overhead n)| + 1)`
(coefficient **1** on `k`, matching the paper's `i + k + O(log n)` slack).

Construction:
* `exists_family_cover` gives, for `c := max 1 (A.card / 2^k)`, a cover `𝒞` of
  the `n`-bit part of `A` by `𝒜`-members of card `≤ 2^(j-k)`, with
  `𝒞.length ≤ overhead n · 2^(k+1)`; and `x` lies in some `B ∈ 𝒞`.
* By `𝒜.enumeration.complete` the codes of a good cover all appear in some stage
  `𝒜.enumeration.enum T`, so a canonical `Nat.rfind` search over
  `(stage, sublist-bitmask)` pairs — accepting a sublist iff its decoded sets
  are `𝒜`-members (automatic from `enumeration.sound`) of card `≤ c` that cover
  `{y ∈ A | y.length = n}`, and it has length `≤ overhead n · 2^(k+1)` —
  terminates.  The card bound `c = max 1 (A.card / 2^k)` and (via the passed
  value `q₀ := overhead n`) the length bound are computed by the decoder, so no
  `j` is transmitted and `overhead` need not be computable.
* `z` encodes `n, k, q₀ = overhead n` self-delimitingly (each `2·|bits ·|+1` via
  `pairCode`/`Nat.bits`) followed by the ordinal `idx < overhead n · 2^(k+1)` of
  the first cover set containing `x` in the found cover (its `|bits idx|` bits
  give the coefficient-1 `k` term).  `f` re-runs the same canonical search and
  returns the `idx`-th cover code, which is `(codedUniformOn B hB).code`.
-/
theorem exists_coverSelector (𝒜 : DescriptionFamily) :
    ∃ (f : BitString →. BitString), Partrec f ∧ ∃ c₀ : ℕ,
      ∀ (A : Finset BitString) (hA : A.Nonempty) (x : BitString) (n j k : ℕ),
        𝒜.mem A → A.card ≤ 2 ^ j → k ≤ j → x ∈ A → x.length = n →
        ∃ (B : Finset BitString) (hB : B.Nonempty) (z : BitString),
          𝒜.mem B ∧ x ∈ B ∧ B.card ≤ 2 ^ (j - k) ∧
          z.length ≤ k + c₀ * ((Nat.bits n).length + (Nat.bits k).length
            + (Nat.bits (𝒜.overhead n)).length + 1) ∧
          (codedUniformOn B hB).code ∈ f (pairCode (codedUniformOn A hA).code z) := by
  refine ⟨ ?_, ?_, 4, ?_ ⟩;
  · exact Kolmogorov.coverSelectorFun 𝒜;
  · exact coverSelectorFun_partrec 𝒜;
  · intro A hA x n j k hA_mem hA_card hk hxA hx_len
    obtain ⟨p, hp⟩ := exists_valid_coverAddress 𝒜 hA hA_mem n k
    set p' :=
        Nat.find (⟨p, hp⟩ : ∃ p,
            coverValidBool 𝒜 (codedUniformOn A hA).code n k (𝒜.overhead n) p) with hp'
    set stage := (coverDecode p').1 with hstage
    set cover := (coverDecode p').2 with hcover
    set idx := cover.findIdx (fun w => decide (x ∈ decodeCoverCodeList w)) with hidx
    set s := k + 1 + (Nat.bits (𝒜.overhead n)).length with hs
    set z := coverAddress n k (𝒜.overhead n) idx s with hz
    have hvalid : coverValidBool 𝒜 (codedUniformOn A hA).code n k
        (𝒜.overhead n) p' = true :=
      Nat.find_spec (⟨p, hp⟩ : ∃ p, coverValidBool 𝒜
        (codedUniformOn A hA).code n k (𝒜.overhead n) p = true)
    have hvalid_parts := hvalid
    simp only [coverValidBool, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hvalid_parts
    have hvalid_enum : ∀ w ∈ cover, w ∈ 𝒜.enumeration.enum stage := by
      simpa only [hcover, hstage] using hvalid_parts.1.1.1
    have hvalid_length : cover.length ≤ (𝒜.overhead n) * 2 ^ (k + 1) := by
      simpa only [hcover] using hvalid_parts.1.1.2
    have hvalid_card : ∀ w ∈ cover,
        (decodeCoverCodeList w).dedup.length ≤ max 1 (A.card / 2 ^ k) := by
      intro w hw
      have hw' := hvalid_parts.1.2 w (by simpa only [hcover] using hw)
      rw [decodeCoverCodeList_code,
        List.dedup_eq_self.mpr (canonicalFinsetList_nodup A),
        length_canonicalFinsetList] at hw'
      exact hw'
    have hx_cover : ∃ w ∈ cover, x ∈ decodeCoverCodeList w := by
      have hx' := hvalid_parts.2 x (by
        simp only [decodeCoverCodeList_code, List.mem_filter,
          decide_eq_true_eq, hx_len, and_true]
        exact mem_canonicalFinsetList.mpr hxA)
      simpa only [List.any_eq_true, decide_eq_true_eq, hcover] using hx'
    have hidx_lt : idx < cover.length := by
      rw [hidx]
      exact List.findIdx_lt_length_of_exists (by simpa using hx_cover)
    have hx_selected : x ∈ decodeCoverCodeList (cover.getD idx []) := by
      rw [hidx] at hidx_lt ⊢
      grind
    have hselected_mem : cover.getD idx [] ∈ cover := by
      rw [List.getD_eq_getElem cover [] hidx_lt]
      exact List.getElem_mem hidx_lt
    have hcover_members : ∀ w ∈ cover, ∃ S : Finset BitString,
        ∃ hS : S.Nonempty, 𝒜.mem S ∧ w = (codedUniformOn S hS).code :=
      fun w hw => 𝒜.enumeration.sound stage w (hvalid_enum w hw)
    use (decodeCoverCodeList (cover.getD idx [])).toFinset, by
      exact ⟨x, List.mem_toFinset.mpr hx_selected⟩, z
    generalize_proofs at *;
    refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    · obtain ⟨S, hS, hS_mem, hS_eq⟩ :=
        hcover_members (cover.getD idx []) hselected_mem
      rw [ hS_eq, decodeCoverCodeList_code ] ; aesop;
    · exact List.mem_toFinset.mpr hx_selected;
    · convert (hvalid_card (cover.getD idx []) hselected_mem).trans _ using 1;
      exact max_le ( Nat.one_le_pow _ _ ( by decide ) ) ( Nat.div_le_of_le_mul
          <| by rw [ ← pow_add, Nat.add_sub_of_le hk ] ; exact hA_card );
    · rw [ hz, coverAddress ];
      rw [ length_pairCode, length_pairCode, length_pairCode, chunkAddress_length ]
      · omega
      have hidx_lt_cover_length : (𝒜.overhead n) < 2 ^ (Nat.bits (𝒜.overhead n)).length := by
        exact lt_two_pow_length_natBits (𝒜.overhead n);
      rw [ hs, pow_add ];
      nlinarith [ hidx_lt, hvalid_length,
        pow_pos ( zero_lt_two' ℕ ) ( k + 1 ) ];
    · convert Kolmogorov.coverSelectorFun_getD_mem 𝒜 ( codedUniformOn A hA ).code n k (
        𝒜.overhead n ) idx s p' _ _ using 1
      all_goals generalize_proofs at *;
      · obtain ⟨S, hS, hS_mem, hS_eq⟩ :=
          hcover_members (cover.getD idx []) hselected_mem
        simp_all +decide [decodeCoverCodeList_code]
      · exact hvalid;
      · exact fun m mn =>
          by simpa using Nat.find_min ‹∃ p,
              coverValidBool 𝒜 ( codedUniformOn A hA ).code n k ( 𝒜.overhead n ) p = true› mn;

/-- **M2(a3): restricted description shift** (paper Prop. `prop:a-family`(a3);
analogue of `inDescriptionProfile_portion`).  If `(i, j) ∈ P_x^𝒜` and `k ≤ j`,
then `(i + k + O(log(n + k + overhead n)), j - k) ∈ P_x^𝒜`.  The family is fixed
before the slack constant, so the constant may depend on its enumeration, but is
uniform in the string and all profile parameters.

This is now *proved* from the isolated computable core `exists_coverSelector`
(the canonical cover search) by pure accounting:
* the selector supplies the covering member `B ∋ x` (family membership and
  log-size `j - k`) together with a fixed partial-recursive `f` and a **short**
  address `z` (`z.length ≤ k + O(log n + log k + log(overhead n))`, coefficient
  `1` on `k`) with `B.code ∈ f (pairCode A.code z)`;
* hence `setComplexity U B ≤ KPPlain U (pairCode A.code z) + O(1)`
  (`KPPlain_partrec_map_le`) `≤ setComplexity U A + KPPlain U z + O(1)`
  (`KPPair_le_KPPlain_add_KPPlain`) `≤ i + z.length + 2|bits z.length| + O(1)`
  (`KPPlain_le_length_add_log`), and the `z`-length bound folds the tail into
  `k + logSlack c (n + k + overhead n)` via `logSlack_linear_bound`.

On `fullFamily` (`overhead n = 2^n`) the slack degenerates to `O(n)` — weaker
than the unrestricted `inDescriptionProfile_portion` (`O(log k)`), but honest:
`fullFamily` covers by singletons, so its covering overhead is genuinely `2^n`. -/
theorem inDescriptionProfileIn_cover_shift
    (U : Map) (hU : IsOptimalPrefixConditional U) (𝒜 : DescriptionFamily) :
    ∃ c : ℕ, ∀ (x : BitString) (n i j k : ℕ),
      x.length = n →
      k ≤ j →
      InDescriptionProfileIn 𝒜 U x i j →
      InDescriptionProfileIn 𝒜 U x
        (i + k + logSlack c (n + k + 𝒜.overhead n))
        (j - k) := by
  obtain ⟨f, hf, c₀, hsel⟩ := exists_coverSelector 𝒜
  obtain ⟨c_map, hc_map⟩ := KPPlain_partrec_map_le U hU f hf
  obtain ⟨c_pair, hc_pair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨C₂, hC₂⟩ := logSlack_linear_bound 2 (1 + 3 * c₀) c₀
  refine ⟨4 * c₀ + C₂ + (c_map + c_pair + c_len), fun x n i j k hn hkj hprof => ?_⟩
  obtain ⟨S, hS, hmemS, hxS, hcompS, hcardS⟩ := hprof
  obtain ⟨B, hB, z, hmemB, hxB, hcardB, hzlen, hfB⟩ :=
    hsel S hS x n j k hmemS hcardS hkj hxS hn
  refine ⟨B, hB, hmemB, hxB, ?_, hcardB⟩
  set M : ℕ := n + k + 𝒜.overhead n with hM
  -- Coding chain (ENat): `B.code` is a computable image of `pairCode A.code z`.
  have hchain : setComplexity U B hB ≤
      ((i + (z.length + 2 * (Nat.bits z.length).length + c_len) + c_pair + c_map : ℕ) : ENat) := by
    have hstep : setComplexity U B hB
        ≤ (i : ENat) + (↑z.length + 2 * ↑((Nat.bits z.length).length) + (c_len : ENat))
            + (c_pair : ENat) + (c_map : ENat) := by
      calc setComplexity U B hB
          = KPPlain U (codedUniformOn B hB).code := rfl
        _ ≤ KPPlain U (pairCode (codedUniformOn S hS).code z) + (c_map : ENat) :=
            hc_map _ _ hfB
        _ = KPPair U (codedUniformOn S hS).code z + (c_map : ENat) := by
            rw [KPPlain_eq_KP, KPPair_eq_KP_pairCode]
        _ ≤ (KPPlain U (codedUniformOn S hS).code + KPPlain U z + (c_pair : ENat))
              + (c_map : ENat) := by
            gcongr
            exact hc_pair _ _
        _ ≤ ((i : ENat) + KPPlain U z + (c_pair : ENat)) + (c_map : ENat) := by
            gcongr
            exact hcompS
        _ ≤ ((i : ENat)
              + (↑z.length + 2 * ↑((Nat.bits z.length).length) + (c_len : ENat))
              + (c_pair : ENat)) + (c_map : ENat) := by
            gcongr
            exact hc_len z
    refine hstep.trans_eq ?_
    push_cast
    ring
  refine hchain.trans ?_
  -- Pure `ℕ` slack folding.
  have hn_le : (Nat.bits n).length ≤ (Nat.bits M).length :=
    length_natBits_mono (by omega)
  have hk_le : (Nat.bits k).length ≤ (Nat.bits M).length :=
    length_natBits_mono (by omega)
  have hov_le : (Nat.bits (𝒜.overhead n)).length ≤ (Nat.bits M).length :=
    length_natBits_mono (by omega)
  have hLM_le : (Nat.bits M).length ≤ M := length_natBits_le_self M
  -- `D := c₀·(...) ≤ logSlack (4 c₀) M`.
  have hD : c₀ * ((Nat.bits n).length + (Nat.bits k).length
        + (Nat.bits (𝒜.overhead n)).length + 1) ≤ logSlack (4 * c₀) M := by
    have hsum : (Nat.bits n).length + (Nat.bits k).length
        + (Nat.bits (𝒜.overhead n)).length + 1 ≤ 3 * (Nat.bits M).length + 1 := by omega
    calc c₀ * ((Nat.bits n).length + (Nat.bits k).length
            + (Nat.bits (𝒜.overhead n)).length + 1)
        ≤ c₀ * (3 * (Nat.bits M).length + 1) := Nat.mul_le_mul_left _ hsum
      _ ≤ logSlack (4 * c₀) M := by
          unfold logSlack
          nlinarith [Nat.zero_le (c₀ * (Nat.bits M).length), Nat.zero_le c₀]
  -- `z.length ≤ k + logSlack (4 c₀) M`.
  have hDz : z.length ≤ k + logSlack (4 * c₀) M :=
    le_trans hzlen (Nat.add_le_add_left hD k)
  -- `z.length ≤ (1+3 c₀) M + c₀`, feeding the `2·|bits z.length|` term.
  have hZM : z.length ≤ (1 + 3 * c₀) * M + c₀ := by
    have hsum : (Nat.bits n).length + (Nat.bits k).length
        + (Nat.bits (𝒜.overhead n)).length + 1 ≤ 3 * M + 1 := by omega
    have hmul : c₀ * ((Nat.bits n).length + (Nat.bits k).length
        + (Nat.bits (𝒜.overhead n)).length + 1) ≤ c₀ * (3 * M + 1) :=
      Nat.mul_le_mul_left _ hsum
    have hkM : k ≤ M := by omega
    nlinarith [hzlen, hmul, hkM]
  have hLZ : 2 * (Nat.bits z.length).length ≤ logSlack C₂ M := by
    have hmono : logSlack 2 z.length ≤ logSlack 2 ((1 + 3 * c₀) * M + c₀) :=
      logSlack_mono hZM
    have hlin : logSlack 2 ((1 + 3 * c₀) * M + c₀) ≤ logSlack C₂ M := hC₂ M
    have hz : logSlack 2 z.length = 2 * (Nat.bits z.length).length + 2 := by
      unfold logSlack; ring
    omega
  have hcomb : logSlack (4 * c₀) M + logSlack C₂ M = logSlack (4 * c₀ + C₂) M :=
    logSlack_add_const (4 * c₀) C₂ M
  have hcomb2 : logSlack (4 * c₀ + C₂) M + (c_map + c_pair + c_len)
      ≤ logSlack (4 * c₀ + C₂ + (c_map + c_pair + c_len)) M :=
    logSlack_add_nat_le (4 * c₀ + C₂) (c_map + c_pair + c_len) M
  have hgoal : i + (z.length + 2 * (Nat.bits z.length).length + c_len) + c_pair + c_map
      ≤ i + k + logSlack (4 * c₀ + C₂ + (c_map + c_pair + c_len)) M := by omega
  exact_mod_cast hgoal

end Kolmogorov
