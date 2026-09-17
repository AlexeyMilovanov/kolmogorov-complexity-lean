import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import KolmogorovMathlib.Restricted.Examples.HammingBalls
import KolmogorovMathlib.Restricted.BasicProfile
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Profile
import KolmogorovMathlib.Restricted.EffectiveSelection
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.Restricted.HammingGap.Part01

/-!
# Effective Hamming list decoding and the restricted-profile gap

This module turns the finite Hamming list-decoding set from `HammingGap.Part01` into a
computable search. It proves correctness of the searched set and supplies short descriptions for
the set, a high-complexity member, and intersections with Hamming balls.

The middle section constructs prefix machines that address an element from a coded finite set
or an intersection. Analytic lower bounds on Hamming volume and the final bit-budget estimate
then exclude simultaneous low-complexity descriptions.

`hamming_gap_exclusion` is the quantitative contradiction, and `prop_hamming_gap` packages it
as the Hamming-ball example separating restricted profile coordinates.
-/

namespace Kolmogorov
open Kolmogorov.CodedFiniteDistribution

private lemma primrec_decide_natEq {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => decide (f a = g a)) :=
  PrimrecPred.decide (PrimrecRel.comp Primrec.eq hf hg)

private lemma primrec_decide_natLe {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => decide (f a ≤ g a)) :=
  PrimrecPred.decide (PrimrecRel.comp Primrec.nat_le hf hg)

/-- The test that a list of strings is a list-decoding set for the given parameters is primitive
recursive. -/
lemma hammingListDecodingCheckBool_primrec :
    Primrec (fun p : ℕ × List BitString => hammingListDecodingCheckBool p.1 p.2) := by
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      List.all p.2 fun x => decide (x.length = p.1)) := by
    convert list_all_primrec _ _ using 1;
    all_goals try exact Primrec.snd;
    exact primrec_decide_natEq (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      decide (p.2.dedup.length = 2 ^ p.1 / hammingVol p.1 (p.1 / 64))) := by
    have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
        p.2.dedup.length) := by
      convert Primrec.list_length.comp ( dedup_primrec.comp ( Primrec.snd ) ) using 1;
    convert primrec_decide_natEq h_hammingListDecodingCheckBool
      (show Primrec (fun p : ℕ × List BitString =>
        2 ^ p.1 / hammingVol p.1 (p.1 / 64)) from ?_) using 1
    convert Primrec.nat_div.comp (primrec_two_pow_aux.comp Primrec.fst)
      (hammingVol_primrec₂.comp Primrec.fst
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 64))) using 1
  have h_hammingListDecodingCheckBool : Primrec (fun p : ℕ × List BitString =>
      List.all (List.range (p.1 / 64 + 1)) fun r' =>
        List.all (allStrings p.1) fun x =>
          p.2.dedup.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist x y ≤ r')) ≤ p.1) := by
    have h_countP : Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
        p.2.1.dedup.countP fun y =>
          decide (y.length = p.1) && decide (hammingDist p.2.2.2 y ≤ p.2.2.1)) := by
      have h_countP : Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
          List.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist p.2.2.2 y ≤ p.2.2.1)) p.2.1) := by
        convert list_countP_primrec
          (show Primrec fun p : ℕ × List BitString × ℕ × BitString =>
            p.2.1 from ?_) ?_ using 1
        · exact Primrec.fst.comp ( Primrec.snd );
        · apply Primrec.and.comp;
          · convert primrec_decide_natEq (Primrec.list_length.comp Primrec.snd)
              (Primrec.fst.comp Primrec.fst) using 1
          · convert primrec_decide_natLe
              (hammingDist_primrec.comp
                (show Primrec fun p :
                    (ℕ × List BitString × ℕ × BitString) × BitString =>
                  p.1.2.2.2 from ?_)
                (show Primrec fun p :
                    (ℕ × List BitString × ℕ × BitString) × BitString => p.2 from ?_))
              (show Primrec fun p :
                  (ℕ × List BitString × ℕ × BitString) × BitString =>
                p.1.2.2.1 from ?_) using 1
            · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) );
            · exact Primrec.snd;
            · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) );
      convert h_countP.comp
        (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
          (p.1, p.2.1.dedup, p.2.2.1, p.2.2.2)) from ?_) using 1
      convert Primrec.pair Primrec.fst
        (Primrec.pair (dedup_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) using 1
    have h_all : Primrec (fun p : ℕ × List BitString × ℕ =>
        List.all (allStrings p.1) fun x =>
          p.2.1.dedup.countP (fun y => decide (y.length = p.1) &&
            decide (hammingDist x y ≤ p.2.2)) ≤ p.1) := by
      convert list_all_primrec
        (show Primrec fun p : ℕ × List BitString × ℕ => allStrings p.1 from ?_) _ using 1
      · exact allStrings_primrec.comp ( Primrec.fst );
      · convert Primrec.comp
          (show Primrec (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) from ?_)
          (h_countP.pair Primrec.fst) using 1
        · constructor <;> intro h <;> simp_all +decide only [Primrec₂];
          · convert h.comp
              (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
                ((p.1, p.2.1, p.2.2.1), p.2.2.2)) from ?_) using 1
            exact Primrec.pair
              (Primrec.pair Primrec.fst
                (Primrec.pair (Primrec.fst.comp Primrec.snd)
                  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          · convert h.comp
              (show Primrec (fun p : ℕ × List BitString × ℕ × BitString =>
                (p.1, p.2.1, p.2.2.1, p.2.2.2)) from ?_) using 1
            · constructor <;> intro h <;> simp_all +decide only;
              convert h.comp
                (show Primrec (fun p : (ℕ × List BitString × ℕ) × BitString =>
                  (p.1.1, p.1.2.1, p.1.2.2, p.2)) from ?_) using 1
              exact Primrec.pair (Primrec.fst.comp Primrec.fst)
                (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                  (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
                    Primrec.snd))
            · exact Primrec.id;
        · exact PrimrecPred.decide
            (PrimrecRel.comp Primrec.nat_le Primrec.fst Primrec.snd)
    convert list_all_primrec _ _ using 1
    · exact inferInstance
    · convert Primrec.list_range.comp
        (Primrec.nat_div.comp Primrec.fst (Primrec.const 64) |>
          Primrec.comp Primrec.succ) using 1
    · exact (h_all.comp
        (Primrec.fst.comp Primrec.fst |> Primrec.pair <|
          Primrec.snd.comp Primrec.fst |> Primrec.pair <| Primrec.snd)).to₂.of_eq
        (fun _ _ => rfl)
  exact (Primrec.and.comp
    (Primrec.and.comp
      ‹Primrec fun p : ℕ × List BitString =>
        p.2.all fun x => decide (List.length x = p.1)›
      ‹Primrec fun p : ℕ × List BitString =>
        decide (p.2.dedup.length = 2 ^ p.1 / hammingVol p.1 (p.1 / 64))›)
    h_hammingListDecodingCheckBool).of_eq (fun _ => rfl)

/-- The exhaustive search for a list-decoding set is computable in `n`. -/
lemma hammingListDecodingSearchList_computable :
    Computable hammingListDecodingSearchList := by
  convert Primrec.to_comp _;
  convert Primrec.option_getD.comp
    (list_find?_primrec (primrec_sublists_gen allStrings_primrec)
      (show Primrec₂ (fun n L => hammingListDecodingCheckBool n L) from ?_))
    (Primrec.const []) using 1
  · ext n; unfold hammingListDecodingSearchList; simp +decide [ hammingListDecodingCheckBool_eq ] ;
  · -- Apply the lemma that states the function is primitive recursive.
    apply hammingListDecodingCheckBool_primrec

/-- The finite set found by the exhaustive search for a list-decoding set of parameters
`r = n / 64` and `N = 2 ^ n / hammingVol n r`. -/
noncomputable def hammingListDecodingSearchSet (n : ℕ) : Finset BitString :=
  (hammingListDecodingSearchList n).toFinset

/-- The canonical uniform code of the list-decoding set found for the length encoded in `w`. -/
noncomputable def hammingListDecodingSearchCode (w : BitString) : BitString :=
  let n := bitsToNat w
  canonicalUniformCodeOfList (canonicalFinsetList (hammingListDecodingSearchSet n))

/-- The code of the searched list-decoding set is computable in the encoded length. -/
lemma hammingListDecodingSearchCode_computable :
    Computable hammingListDecodingSearchCode := by
  have h := hammingListDecodingSearchList_computable
  have hc : Computable (fun w : BitString =>
      canonicalUniformCodeOfList (canonicalFinsetList
        (hammingListDecodingSearchList (bitsToNat w)).toFinset)) :=
    (canonicalUniformCodeOfList_primrec.to_comp).comp
      ((canonicalFinsetList_toFinset_primrec.to_comp).comp
        (h.comp bitsToNat_primrec.to_comp))
  exact hc.of_eq (fun w => rfl)

/-- If a list-decoding set of these parameters exists, the search finds one. -/
lemma hammingListDecodingSearchSet_correct (n : ℕ)
    (h_exists : ∃ E : Finset BitString,
      IsHammingListDecodingSet n (n / 64) (2 ^ n / hammingVol n (n / 64)) E) :
    ∃ _hE : (hammingListDecodingSearchSet n).Nonempty,
      IsHammingListDecodingSet n (n / 64) (2 ^ n / hammingVol n (n / 64))
        (hammingListDecodingSearchSet n) := by
  classical
  set r := n / 64
  set N := 2 ^ n / hammingVol n r
  let pred : List BitString → Bool :=
    fun L => @decide (IsHammingListDecodingSetFinite n r N L.toFinset)
      (IsHammingListDecodingSetFinite_decidable n r N L.toFinset)
  obtain ⟨E, hE⟩ := h_exists
  have hE_canon : IsHammingListDecodingSet n r N E := by
    simpa [r, N] using hE
  have hE_fin : IsHammingListDecodingSetFinite n r N E :=
    (IsHammingListDecodingSet_iff_finite n r N E).mp hE_canon
  let L : List BitString := (allStrings n).filter (fun x => decide (x ∈ E))
  have hL_mem : L ∈ (allStrings n).sublists := by
    exact List.mem_sublists.mpr List.filter_sublist
  have hL_set : L.toFinset = E := by
    ext x
    constructor
    · intro hx
      rw [List.mem_toFinset, List.mem_filter] at hx
      exact of_decide_eq_true hx.2
    · intro hx
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨(mem_allStrings n x).mpr (hE_canon.1 x hx), decide_eq_true hx⟩
  have hL_good : pred L = true := by
    unfold pred
    rw [hL_set]
    exact decide_eq_true hE_fin
  obtain ⟨L₀, hfind⟩ : ∃ L₀, (allStrings n).sublists.find? pred = some L₀ := by
    exact Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨L, hL_mem, hL_good⟩)
  have hL₀_good_bool : pred L₀ = true := List.find?_some hfind
  have hL₀_fin : IsHammingListDecodingSetFinite n r N L₀.toFinset := by
    unfold pred at hL₀_good_bool
    exact of_decide_eq_true hL₀_good_bool
  have hsearch_eq : hammingListDecodingSearchSet n = L₀.toFinset := by
    unfold hammingListDecodingSearchSet hammingListDecodingSearchList
    exact congrArg List.toFinset
      (congrArg (fun o : Option (List BitString) => o.getD []) hfind)
  have hN_pos : 0 < N := by
    have hV_pos : 0 < hammingVol n r := by
      have h1 : 1 ≤ hammingVol n r := by
        rw [← hammingVol_zero n]
        exact hammingVol_mono (n := n) (Nat.zero_le r)
      exact h1
    have hV_le : hammingVol n r ≤ 2 ^ n := hammingVol_le_two_pow n r
    exact Nat.div_pos hV_le hV_pos
  have hnonempty₀ : L₀.toFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [hL₀_fin.2.1]
    exact hN_pos
  refine ⟨hsearch_eq ▸ hnonempty₀, ?_⟩
  rw [hsearch_eq]
  exact (IsHammingListDecodingSet_iff_finite n r N L₀.toFinset).mpr hL₀_fin

/-- There is a computable map from `n` to the canonical uniform code of a list-decoding set of
parameters `r = n / 64` and `N = 2 ^ n / hammingVol n r`, whenever one exists. -/
lemma exists_computable_list_decoding_search :
    ∃ f : BitString → BitString, Computable f ∧
      ∀ n r N : ℕ, r = n / 64 → N = 2 ^ n / hammingVol n r →
      (∃ E : Finset BitString, IsHammingListDecodingSet n r N E) →
      ∃ E : Finset BitString, ∃ hE : E.Nonempty,
        IsHammingListDecodingSet n r N E ∧
        f (Nat.bits n) = (codedUniformOn E hE).code := by
  refine ⟨hammingListDecodingSearchCode, hammingListDecodingSearchCode_computable, ?_⟩
  intro n r N hr hN h_exists
  subst r
  subst N
  obtain ⟨hE, hprop⟩ := hammingListDecodingSearchSet_correct n h_exists
  refine ⟨hammingListDecodingSearchSet n, hE, hprop, ?_⟩
  unfold hammingListDecodingSearchCode
  rw [bitsToNat_bits]
  exact canonicalUniformCodeOfList_canonicalFinsetList (hammingListDecodingSearchSet n) hE

/--
The list-decoding set `E` can be chosen to have logarithmic complexity, by selecting the
lexicographically first witness of the exhaustive search.
-/
lemma exists_list_decoding_set_low_complexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n r N : ℕ,
    r = n / 64 →
    N = 2 ^ n / hammingVol n r →
    (∃ E : Finset BitString, IsHammingListDecodingSet n r N E) →
    ∃ E : Finset BitString, ∃ hE : E.Nonempty, IsHammingListDecodingSet n r N E ∧
      setComplexity U E hE ≤ (logSlack c n : ENat) := by
  obtain ⟨f, hf_comp, hf_spec⟩ := exists_computable_list_decoding_search
  obtain ⟨c_map, hc_map⟩ := KPPlain_map_le U hU f hf_comp
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_length_add_log U hU
  refine ⟨3 + c_len + c_map, fun n r N hr hN hE => ?_⟩
  obtain ⟨E, hE_nonempty, hE_prop, hf_eq⟩ := hf_spec n r N hr hN hE
  refine ⟨E, hE_nonempty, hE_prop, ?_⟩
  unfold setComplexity
  rw [← hf_eq]
  have hc1 := hc_map (Nat.bits n)
  have hc2 := hc_len (Nat.bits n)
  have hlen : (Nat.bits n).length.bits.length ≤ (Nat.bits n).length := by
    exact length_natBits_le _
  have h_bound :
      (Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len + c_map ≤
        logSlack (3 + c_len + c_map) n := by
    unfold logSlack
    nlinarith
  calc KPPlain U (f (Nat.bits n))
    ≤ KPPlain U (Nat.bits n) + (c_map : ENat) := hc1
    _ ≤ ((Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len : ℕ) +
        (c_map : ENat) := by exact add_le_add hc2 le_rfl
    _ = (((Nat.bits n).length + 2 * (Nat.bits (Nat.bits n).length).length + c_len +
        c_map : ℕ) : ENat) := by push_cast; ring
    _ ≤ logSlack (3 + c_len + c_map) n := by exact_mod_cast h_bound

/--
Any non-empty finite set contains an element whose complexity is at least the log-cardinality
of the set, up to an additive constant: an element incompressible inside the set.
-/
lemma exists_high_complexity_element_in_finset (U : Map) (_hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ E : Finset BitString, ∀ _hE : E.Nonempty,
    ∃ x ∈ E, (Nat.bits E.card).length ≤ KPPlain U x + (c : ENat) := by
  classical
  refine ⟨1, fun E hE => ?_⟩
  let L := (Nat.bits E.card).length
  by_cases hL_small : L ≤ 1
  · obtain ⟨x, hx⟩ := hE
    refine ⟨x, hx, ?_⟩
    calc
      (L : ENat) ≤ (1 : ENat) := by exact_mod_cast hL_small
      _ = (0 : ENat) + (1 : ENat) := by norm_num
      _ ≤ KPPlain U x + (1 : ENat) := by
        exact add_le_add bot_le le_rfl
  · have hL_ge2 : 2 ≤ L := by omega
    by_contra hno
    have hsubset : E ⊆ compressibleWords U [] (L - 2) := by
      intro x hx
      have hfail : ¬ ((L : ENat) ≤ KPPlain U x + (1 : ENat)) := by
        intro hgood
        exact hno ⟨x, hx, by simpa [L] using hgood⟩
      have hlt : KPPlain U x + (1 : ENat) < (L : ENat) :=
        lt_of_not_ge hfail
      have hne : KPPlain U x ≠ ⊤ := by
        intro htop
        have htop_add : KPPlain U x + (1 : ENat) = ⊤ := by
          rw [htop]
          simp
        rw [htop_add] at hlt
        exact not_top_lt hlt
      obtain ⟨kx, hkx_raw⟩ := ENat.ne_top_iff_exists.mp hne
      have hkx : KPPlain U x = (kx : ENat) := hkx_raw.symm
      have hKP : KP U x [] = (kx : ENat) := by
        simpa [KPPlain] using hkx
      have hkx_lt : kx + 1 < L := by
        have hcast : ((kx + 1 : ℕ) : ENat) < (L : ENat) := by
          simpa [hKP, Nat.cast_add] using hlt
        exact ENat.natCast_lt_natCast.mp hcast
      have hle : KPPlain U x ≤ ((L - 2 : ℕ) : ENat) := by
        rw [hkx]
        exact_mod_cast (by omega : kx ≤ L - 2)
      have hle_cond : condK U x [] ≤ ((L - 2 : ℕ) : ENat) := by
        simpa [KPPlain, KP, plainK] using hle
      rw [compressibleWords, Finset.mem_filter]
      refine ⟨?_, hle_cond⟩
      obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x [] (L - 2)).mp hle_cond
      rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
      exact ⟨p, mem_programsLe (L - 2) p hp_len, progToOut_eq_some.mpr hp_prod⟩
    have hcard_le : E.card ≤ (compressibleWords U [] (L - 2)).card :=
      Finset.card_le_card hsubset
    have hcard_lt : E.card < 2 ^ (L - 1) := by
      have hlt := lt_of_le_of_lt hcard_le (card_compressibleWordsLt U [] (L - 2))
      have hpow : 2 ^ ((L - 2) + 1) = 2 ^ (L - 1) := by
        congr
        omega
      simpa [hpow] using hlt
    have hE_card_pos : 0 < E.card := Finset.card_pos.mpr hE
    have hlower : 2 ^ (L - 1) ≤ E.card := by
      by_contra hnot
      have hltM : E.card < 2 ^ (L - 1) := Nat.lt_of_not_ge hnot
      have hsize_le : Nat.size E.card ≤ L - 1 := Nat.size_le.mpr hltM
      have hsize_eq : Nat.size E.card = L := by
        dsimp [L]
        exact (Nat.size_eq_bits_len E.card).symm
      omega
    omega

/-- Lemma 1: A ball of radius `R` can be covered by balls of radius `r`,
with the same radius-bracketing hypotheses used by `hammingBall_cover_centers`.
The bounds `c ≤ hammingVol n R` and `c ≤ hammingVol n (r+1)` are necessary:
without them, the `length * c` conclusion is false for tiny target balls. -/
lemma hammingBall_covered_by_smaller_balls (n : ℕ) (z : BitString) (R r c : ℕ)
    (hz : z.length = n) (hc : 0 < c)
    (h_R_bound : c ≤ hammingVol n R)
    (h_r_vol : hammingVol n r ≤ c)
    (h_r_next : c ≤ hammingVol n (r + 1))
    (h_c_le : c ≤ (n + 1) * hammingVol n r) :
    ∃ 𝒞 : List BitString,
      (∀ x ∈ 𝒞, x.length = n) ∧
      (∀ y ∈ hammingBall n z R, ∃ x ∈ 𝒞, hammingDist x y ≤ r) ∧
      𝒞.length * c ≤ (n + 1)^7 * (hammingBall n z R).card := by
  exact hammingBall_cover_centers n z R c r hz hc h_R_bound h_r_vol h_r_next h_c_le

/-- Lemma 2: Intersection bound for a list-decoding set and an arbitrary ball.
The `+ 1` is the ceiling/trivial-cover term needed when the target ball is
smaller than the decoding radius volume. -/
lemma hamming_list_decoding_intersection (n r N R : ℕ) (E : Finset BitString) (z : BitString)
    (h_list : IsHammingListDecodingSet n r N E) (hz : z.length = n) :
    (E ∩ hammingBall n z R).card ≤
      n * (((n + 1)^7 * (hammingBall n z R).card) / hammingVol n r + 1) := by
  classical
  set A := hammingBall n z R
  set V := hammingVol n r
  set M := (n + 1)^7 * A.card
  have hA_mem : hammingFamilyMem A := ⟨n, z, R, hz, rfl⟩
  have hV_pos : 0 < V := by
    have h1 : 1 ≤ hammingVol n r := by
      rw [← hammingVol_zero n]
      exact hammingVol_mono (n := n) (Nat.zero_le r)
    exact h1
  by_cases hsmall : A.card ≤ V
  · have hdirect : (A ∩ E).card ≤ n := h_list.2.2 A hA_mem (by simpa [V] using hsmall)
    rw [Finset.inter_comm]
    calc
      (A ∩ E).card ≤ n := hdirect
      _ ≤ n * (M / V + 1) := by
        have hone : 1 ≤ M / V + 1 := Nat.succ_le_succ (Nat.zero_le _)
        nlinarith
  · have hlarge : V ≤ A.card := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    obtain ⟨𝒞, h𝒞_small, h𝒞_cover, h𝒞_count⟩ :=
      hammingFamily_cover hA_mem n V hV_pos hlarge
    have hsub : E ∩ A ⊆ 𝒞.toFinset.biUnion (fun B => E ∩ B) := by
      intro y hy
      rw [Finset.mem_inter] at hy
      rcases hy with ⟨hyE, hyA⟩
      have hylen : y.length = n := by
        change y ∈ hammingBall n z R at hyA
        rw [hammingBall, Finset.mem_filter] at hyA
        exact (mem_stringsOfLength n y).mp hyA.1
      obtain ⟨B, hB𝒞, hyB⟩ := h𝒞_cover y hyA hylen
      rw [Finset.mem_biUnion]
      exact ⟨B, List.mem_toFinset.mpr hB𝒞, by rw [Finset.mem_inter]; exact ⟨hyE, hyB⟩⟩
    have h_each : ∀ B ∈ 𝒞.toFinset, (E ∩ B).card ≤ n := by
      intro B hB
      have hB_list : B ∈ 𝒞 := List.mem_toFinset.mp hB
      rcases h𝒞_small B hB_list with ⟨hB_mem, hB_card⟩
      rw [Finset.inter_comm]
      exact h_list.2.2 B hB_mem (by simpa [V] using hB_card)
    have h_inter_le : (E ∩ A).card ≤ 𝒞.length * n := by
      calc
        (E ∩ A).card ≤ (𝒞.toFinset.biUnion (fun B => E ∩ B)).card :=
          Finset.card_le_card hsub
        _ ≤ ∑ B ∈ 𝒞.toFinset, (E ∩ B).card := Finset.card_biUnion_le
        _ ≤ ∑ _B ∈ 𝒞.toFinset, n := Finset.sum_le_sum (fun B hB => h_each B hB)
        _ = 𝒞.toFinset.card * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 𝒞.length * n := by
          exact Nat.mul_le_mul_right n (List.toFinset_card_le 𝒞)
    have hlen_le : 𝒞.length ≤ M / V := by
      rw [Nat.le_div_iff_mul_le hV_pos]
      simpa [M, V, hammingOverhead] using h𝒞_count
    rw [show E ∩ hammingBall n z R = E ∩ A by rfl]
    calc
      (E ∩ A).card ≤ 𝒞.length * n := h_inter_le
      _ ≤ (M / V) * n := Nat.mul_le_mul_right n hlen_le
      _ ≤ n * (M / V + 1) := by nlinarith

/-- The computable decoder underlying `setComplexity_inter_le`: reading a pair of
canonical uniform codes, it recovers both point-lists, intersects them, and
re-encodes the intersection as a canonical uniform code. -/
noncomputable def interDecoder (w : BitString) : BitString :=
  let LE := (decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point
  let LB := (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point
  canonicalUniformCodeOfList
    (canonicalFinsetList (LE.filter (fun x => decide (x ∈ LB))).toFinset)

/-- Decoding two canonical uniform codes and re-encoding the intersection is computable. -/
theorem interDecoder_computable : Computable interDecoder := by
  have hLE : Primrec (fun w : BitString =>
      (decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp decodeFirst_primrec)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hLB : Primrec (fun w : BitString =>
      (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp decodeSecond_primrec)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hp : Primrec₂ (fun (w : BitString) (x : BitString) =>
      decide (x ∈ (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point)) :=
    bitString_mem_primrec.comp Primrec.snd (hLB.comp Primrec.fst)
  have hfilter : Primrec (fun w : BitString =>
      ((decodeDistributionData (decodeFirst w)).map CodedDistributionEntry.point).filter
        (fun x => decide (x ∈
          (decodeDistributionData (decodeSecond w)).map CodedDistributionEntry.point))) :=
    list_filter_primrec hLE hp
  exact (canonicalUniformCodeOfList_primrec.comp
    (canonicalFinsetList_toFinset_primrec.comp hfilter)).to_comp

/-- On the pair of the codes of `E` and `B` with non-empty intersection, the intersection decoder
returns the canonical uniform code of `E ∩ B`. -/
theorem interDecoder_eq (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty)
    (hI : (E ∩ B).Nonempty) :
    interDecoder (pairCode (codedUniformOn E hE).code (codedUniformOn B hB).code)
      = (codedUniformOn (E ∩ B) hI).code := by
  unfold interDecoder
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, dataPoints_codedUniformOn]
  have hset : ((canonicalFinsetList E).filter
      (fun x => decide (x ∈ canonicalFinsetList B))).toFinset = E ∩ B := by
    ext y
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_canonicalFinsetList,
      Finset.mem_inter]
  rw [hset]
  exact canonicalUniformCodeOfList_canonicalFinsetList (E ∩ B) hI

/-- Helper A for `KPPlain_le_intersection`: the canonical uniform code of an
intersection has complexity bounded by the sum of the two set complexities, up
to an additive constant.  Proved by a computable decoder that reads the two
uniform codes, recovers both point-lists (`dataPoints_codedUniformOn`),
intersects them, and re-encodes. -/
lemma setComplexity_inter_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty)
      (hI : (E ∩ B).Nonempty),
      setComplexity U (E ∩ B) hI ≤ setComplexity U E hE + setComplexity U B hB + (c : ENat) := by
  obtain ⟨c_map, hmap⟩ := KPPlain_map_le U hU interDecoder interDecoder_computable
  obtain ⟨c_pair, hpair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨c_map + c_pair, fun E B hE hB hI => ?_⟩
  have hcode := interDecoder_eq E B hE hB hI
  calc
    setComplexity U (E ∩ B) hI
        = KPPlain U (interDecoder (pairCode (codedUniformOn E hE).code
            (codedUniformOn B hB).code)) := by rw [hcode]; rfl
    _ ≤ KPPlain U (pairCode (codedUniformOn E hE).code (codedUniformOn B hB).code)
          + (c_map : ENat) := hmap _
    _ = KPPair U (codedUniformOn E hE).code (codedUniformOn B hB).code + (c_map : ENat) := by
          rw [KPPlain_eq_KP, KPPair_eq_KP_pairCode]
    _ ≤ (KPPlain U (codedUniformOn E hE).code + KPPlain U (codedUniformOn B hB).code
          + (c_pair : ENat)) + (c_map : ENat) := by
          gcongr; exact hpair _ _
    _ = setComplexity U E hE + setComplexity U B hB + ((c_map + c_pair : ℕ) : ENat) := by
          unfold setComplexity; push_cast; ring

/-- The option-valued core of the fixed-length set-index decompressor: given a
program `pr.1` (the fixed-length index bits) and a context `pr.2` (a canonical
uniform set code), it decodes the point-list, checks that the program length
matches `⌈log₂ card⌉`, and returns the indexed element. -/
def setIndexDecompressorOpt (pr : BitString × BitString) : Option BitString :=
  let L := (decodeDistributionData pr.2).map CodedDistributionEntry.point
  bif (pr.1.length == (Nat.bits L.length).length) then some (L.getD (bitsToNat pr.1) []) else none

/-- The fixed-length set-index conditional decompressor.  For each fixed context,
all halting programs share one length, so the halting domain is prefix-free. -/
noncomputable def setIndexDecompressor : Map := fun pr =>
  Part.ofOption (setIndexDecompressorOpt pr)

/-- The fixed-length set-index decompressor is a conditional decompressor. -/
theorem setIndexDecompressor_computable : isDecompressor setIndexDecompressor := by
  have hL : Primrec (fun pr : BitString × BitString =>
        (decodeDistributionData pr.2).map CodedDistributionEntry.point) :=
    Primrec.list_map (decodeDistributionData_primrec.comp Primrec.snd)
      (entry_point_primrec.comp Primrec.snd).to₂
  have hs : Primrec (fun pr : BitString × BitString =>
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) :=
    Primrec.list_length.comp (primrec_natBits.comp (Primrec.list_length.comp hL))
  have hlen : Primrec (fun pr : BitString × BitString => pr.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have h_beq : Primrec (fun pr : BitString × BitString =>
      (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length)) :=
    Primrec.beq.comp hlen hs
  have hcond : PrimrecPred (fun pr : BitString × BitString =>
      (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) =
            true) :=
    Primrec.eq.comp h_beq (Primrec.const true)
  have hidx : Primrec (fun pr : BitString × BitString => bitsToNat pr.1) :=
    bitsToNat_primrec.comp Primrec.fst
  have hout : Primrec (fun pr : BitString × BitString =>
        ((decodeDistributionData pr.2).map CodedDistributionEntry.point).getD
          (bitsToNat pr.1) []) :=
    (Primrec.list_getD []).comp hL hidx
  have h_opt : Primrec setIndexDecompressorOpt := by
    refine (Primrec.ite hcond (Primrec.option_some.comp hout)
      (Primrec.const none)).of_eq (fun pr => ?_)
    cases h : (pr.1.length ==
        (Nat.bits
          ((decodeDistributionData pr.2).map CodedDistributionEntry.point).length).length) <;>
      simp only [setIndexDecompressorOpt, h, cond_true, cond_false,
        Bool.false_eq_true, eq_self, if_true, if_false]
  exact Computable.ofOption h_opt.to_comp

/-- The set-index decompressor is a prefix machine: for each context all halting programs have
the same length. -/
theorem setIndexDecompressor_isPrefixMachine : IsPrefixMachine setIndexDecompressor := by
  have key : ∀ (y r : BitString), setIndexDecompressorOpt (r, y) ≠ none →
      r.length =
        (Nat.bits ((decodeDistributionData y).map CodedDistributionEntry.point).length).length := by
    intro y r hr
    by_cases h : (r.length ==
        (Nat.bits
          ((decodeDistributionData y).map CodedDistributionEntry.point).length).length) = true
    · exact beq_iff_eq.mp h
    · exfalso
      rw [Bool.not_eq_true] at h
      simp only [setIndexDecompressorOpt, h, cond_false, ne_eq, not_true_eq_false] at hr
  intro y p hp q hq hpre
  have hp' : setIndexDecompressorOpt (p, y) ≠ none := by
    intro h
    change (Part.ofOption (setIndexDecompressorOpt (p, y))).Dom at hp
    rw [h] at hp; exact hp
  have hq' : setIndexDecompressorOpt (q, y) ≠ none := by
    intro h
    change (Part.ofOption (setIndexDecompressorOpt (q, y))).Dom at hq
    rw [h] at hq; exact hq
  exact hpre.eq_of_length (by rw [key y p hp', key y q hq'])

/-- Given the code of a set as context, the fixed-width address of an element produces that
element. -/
theorem setIndexDecompressor_produces (S : Finset BitString) (hS : S.Nonempty) (x : BitString)
    (hx : x ∈ S) :
    produces setIndexDecompressor
      (chunkAddress ((canonicalFinsetList S).findIdx (· == x)) (Nat.bits S.card).length)
      (codedUniformOn S hS).code x := by
  set idx := (canonicalFinsetList S).findIdx (· == x) with hidx
  set s := (Nat.bits S.card).length with hs
  have hxL : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have hlt : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hxL, by simp⟩
  have hidx_lt : idx < S.card := by rw [hidx, ← length_canonicalFinsetList]; exact hlt
  have hcard_lt : S.card < 2 ^ s := by
    rw [hs, Nat.size_eq_bits_len]; exact Nat.lt_size_self S.card
  have hplen : (chunkAddress idx s).length = s :=
    chunkAddress_length idx s (lt_trans hidx_lt hcard_lt)
  have hgetD : (canonicalFinsetList S).getD idx [] = x := by
    rw [hidx, List.getD_eq_getElem _ _ hlt]
    have hpred := List.findIdx_getElem (w := hlt) (p := (· == x)) (xs := canonicalFinsetList S)
    simpa using hpred
  change x ∈ Part.ofOption (setIndexDecompressorOpt
    (chunkAddress idx s, (codedUniformOn S hS).code))
  rw [Part.mem_ofOption]
  unfold setIndexDecompressorOpt
  simp only [dataPoints_codedUniformOn S hS, length_canonicalFinsetList, hplen, ← hs,
    beq_self_eq_true, cond_true, Option.mem_def, Option.some.injEq]
  rw [bitsToNat_chunkAddress]
  exact hgetD

/-- Helper B for `KPPlain_le_intersection`: given the canonical uniform code of a
finite set `S` as the conditioning string, any element of `S` can be described by
its (fixed-length) index within `S`, so its conditional complexity is bounded by
`log₂ |S| + O(1)`. -/
lemma KP_le_log_card_given_setCode (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (S : Finset BitString) (hS : S.Nonempty) (x : BitString),
      x ∈ S →
      KP U x (codedUniformOn S hS).code ≤ (Nat.bits S.card).length + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.invariance
    ⟨setIndexDecompressor_computable, setIndexDecompressor_isPrefixMachine⟩
  refine ⟨c, fun S hS x hx => ?_⟩
  set idx := (canonicalFinsetList S).findIdx (· == x) with hidx
  set s := (Nat.bits S.card).length with hs
  have hxL : x ∈ canonicalFinsetList S := mem_canonicalFinsetList.mpr hx
  have hlt : (canonicalFinsetList S).findIdx (· == x) < (canonicalFinsetList S).length := by
    rw [List.findIdx_lt_length]; exact ⟨x, hxL, by simp⟩
  have hidx_lt : idx < S.card := by rw [hidx, ← length_canonicalFinsetList]; exact hlt
  have hcard_lt : S.card < 2 ^ s := by
    rw [hs, Nat.size_eq_bits_len]; exact Nat.lt_size_self S.card
  have hplen : (chunkAddress idx s).length = s :=
    chunkAddress_length idx s (lt_trans hidx_lt hcard_lt)
  have hprod := setIndexDecompressor_produces S hS x hx
  calc KP U x (codedUniformOn S hS).code
      ≤ KP setIndexDecompressor x (codedUniformOn S hS).code + (c : ENat) :=
        hc x (codedUniformOn S hS).code
    _ ≤ (programLength (chunkAddress idx s) : ENat) + (c : ENat) := by
        gcongr; exact KP_le_programLength_of_produces hprod
    _ = ((Nat.bits S.card).length : ENat) + (c : ENat) := by
        rw [programLength, hplen]

/-- Lemma 3: Complexity of an element in the intersection. -/
lemma KPPlain_le_intersection (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_int : ℕ, ∀ (E B : Finset BitString) (hE : E.Nonempty) (hB : B.Nonempty) (x : BitString),
      x ∈ E ∩ B →
      KPPlain U x ≤ setComplexity U E hE + setComplexity U B hB +
                    (Nat.bits (E ∩ B).card).length + c_int := by
  obtain ⟨cA, hA⟩ := setComplexity_inter_le U hU
  obtain ⟨cB, hB'⟩ := KP_le_log_card_given_setCode U hU
  obtain ⟨c2, h2⟩ := KPPlain_le_KPPlain_add_KP U hU
  refine ⟨cA + cB + c2, fun E B hE hB x hx => ?_⟩
  have hxE : x ∈ E := (Finset.mem_inter.mp hx).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
  have hI : (E ∩ B).Nonempty := ⟨x, hx⟩
  calc
    KPPlain U x
        ≤ setComplexity U (E ∩ B) hI + KP U x (codedUniformOn (E ∩ B) hI).code + (c2 : ENat) :=
          h2 x (codedUniformOn (E ∩ B) hI).code
    _ ≤ (setComplexity U E hE + setComplexity U B hB + (cA : ENat))
          + ((Nat.bits (E ∩ B).card).length + (cB : ENat)) + (c2 : ENat) := by
          gcongr
          · exact hA E B hE hB hI
          · exact hB' (E ∩ B) hI x hx
    _ = setComplexity U E hE + setComplexity U B hB + (Nat.bits (E ∩ B).card).length
          + ((cA + cB + c2 : ℕ) : ENat) := by push_cast; ring

/-
Linear lower bound on the Hamming volume at radius `n / 64`:
`2 ^ (5 * (n / 64)) ≤ hammingVol n (n / 64)`.  This gives `log₂ V ≥ 5 * ⌊n/64⌋`,
the volume lower bound the Hamming gap argument needs.
-/
lemma hammingVol_ge_two_pow_lin (n : ℕ) :
    2 ^ (5 * (n / 64)) ≤ hammingVol n (n / 64) := by
  rw [ pow_mul ];
  -- The selected binomial coefficient is large enough by induction on the radius.
  suffices h_ind : ∀ r : ℕ, ∀ n : ℕ, 64 * r ≤ n → 32 ^ r ≤ Nat.choose n r by
    exact le_trans (h_ind _ _ (by omega))
      (Finset.single_le_sum (fun x _ => Nat.zero_le (Nat.choose n x))
        (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  intro r n hn
  induction r generalizing n with
  | zero => norm_num [ Nat.pow_succ', Nat.choose ] at *
  | succ r ih =>
    norm_num [ Nat.pow_succ', Nat.choose ] at *
    have := Nat.add_one_mul_choose_eq n r
    nlinarith! [ ih n ( by linarith ), Nat.choose_succ_succ n r ]

/-
Bits-length bound for the list-decoding intersection.  If `V ≥ 2 ^ v` and the
ball cardinality `Bcard ≤ 2 ^ t`, and `W` is bounded by the covering estimate
`n * ((n+1)^7 * Bcard / V + 1)`, then `(Nat.bits W).length` is bounded by
`8 * (Nat.bits (n+1)).length + (t - v) + 1`.  This packages the messy division /
size arithmetic of the Hamming gap argument.
-/
lemma bits_intersection_bound (n Bcard V W t v : ℕ)
    (hv : 2 ^ v ≤ V) (hBcard : Bcard ≤ 2 ^ t)
    (hW : W ≤ n * ((n + 1) ^ 7 * Bcard / V + 1)) :
    (Nat.bits W).length ≤ 8 * (Nat.bits (n + 1)).length + (t - v) + 1 := by
  -- Apply the size bound to W
  have hW_size : W ≤ (n + 1) ^ 8 * 2 ^ (t - v) := by
    -- Bound the quotient using the lower bound on `V`.
    have h_simp : n * ((n + 1) ^ 7 * Bcard / V + 1) ≤ (n + 1) ^ 8 * 2 ^ (t - v) := by
      have h_div : (n + 1) ^ 7 * Bcard / V ≤ (n + 1) ^ 7 * 2 ^ (t - v) := by
        by_cases h : t ≥ v;
        · refine Nat.div_le_of_le_mul ?_;
          rw [show 2 ^ t = 2 ^ (t - v) * 2 ^ v by
            rw [← pow_add, Nat.sub_add_cancel h]] at hBcard
          nlinarith [show 0 < (n + 1) ^ 7 by positivity,
            show 0 < 2 ^ v by positivity, show 0 < 2 ^ (t - v) by positivity,
            mul_le_mul_right hv ((n + 1) ^ 7)]
        · simp_all +decide only [
            ge_iff_le, not_le, Nat.sub_eq_zero_of_le (le_of_not_ge h), pow_zero, mul_one
          ];
          exact Nat.div_le_of_le_mul <| by
            nlinarith [pow_pos (Nat.succ_pos n) 7, pow_pos (zero_lt_two' ℕ) t,
              pow_le_pow_right₀ (by decide : 1 ≤ 2) h.le]
      by_cases h : t - v ≥ 0 <;> simp_all +decide [ Nat.pow_succ' ];
      nlinarith [pow_pos (Nat.succ_pos n) 2, pow_pos (Nat.succ_pos n) 3,
        pow_pos (Nat.succ_pos n) 4, pow_pos (Nat.succ_pos n) 5,
        pow_pos (Nat.succ_pos n) 6, pow_pos (Nat.succ_pos n) 7,
        pow_pos (Nat.succ_pos n) 8, pow_pos (zero_lt_two' ℕ) (t - v)]
    exact Nat.le_trans hW h_simp;
  -- Apply the size bound to W and simplify
  have hW_size_simplified : W < 2 ^ (8 * (n + 1).size + (t - v) + 1) := by
    refine lt_of_le_of_lt hW_size ?_;
    rw [ pow_add, pow_add, pow_mul' ];
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.lt_size_self _ |>.le) _))
      (lt_mul_of_one_lt_right (by positivity) (by norm_num))
  rw [ Nat.size_eq_bits_len ] at *;
  convert Nat.size_le.mpr hW_size_simplified using 1;
  rw [ Nat.size_eq_bits_len ]

/-
The deterministic profile-exclusion lemma.
If E is a list-decoding set of low complexity, and x ∈ E is an element of high complexity,
then x is excluded from a region of the restricted profile P_x^𝒜 (for 𝒜 = Hamming balls).
-/
lemma hamming_gap_exclusion (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ) :
    ∃ c_gap : ℕ, c_gap > 0 ∧ ∃ c_min : ℕ, ∀ n N : ℕ, ∀ E : Finset BitString, ∀ hE : E.Nonempty,
    IsHammingListDecodingSet n (n / 64) N E →
    N = 2 ^ n / hammingVol n (n / 64) →
    setComplexity U E hE ≤ (logSlack c n : ENat) →
    (n ≥ c_min) →
    ∀ x ∈ E, (Nat.bits N).length ≤ KPPlain U x + (c : ENat) →
    ∃ i j : ℕ, InDescriptionProfile U x i j ∧
      ¬ InDescriptionProfileIn hammingFamily U x (i + n / c_gap) (j + n / c_gap) := by
  obtain ⟨ c_int, hc_int ⟩ := KPPlain_le_intersection U hU
  simp +decide only [
    gt_iff_lt, ge_iff_le, KPPlain_eq_KP, InDescriptionProfile,
    InDescriptionProfileIn, not_exists
  ]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ≥ M,
      64 * ((2 * c + 8) * (Nat.bits n).length + (3 * c + 9 + c_int)) ≤ n := by
    exact exists_bits_linear_domination 64 ( 2 * c + 8 ) ( 3 * c + 9 + c_int );
  refine ⟨ 128, by norm_num, Max.max M 64, ?_ ⟩;
  intro n N E hE h_list hN hEcomp hn x hxE hxK
  use logSlack c n, N.bits.length
  constructor;
  · refine ⟨ E, hE, hxE, hEcomp, ?_ ⟩;
    rw [ h_list.2.1, Nat.le_iff_lt_or_eq ];
    exact lt_or_eq_of_le (Nat.le_of_lt (Nat.lt_size_self N) |>
      le_trans <| by rw [Nat.size_eq_bits_len])
  · intro B hB hBdesc
    obtain ⟨hBmem, hBdesc⟩ := hBdesc
    obtain ⟨m, z, r', hzlen, hBeq⟩ := hBmem
    have hz : z.length = n := by
      have := hBdesc.1; simp_all +decide [ hammingBall ] ;
      have := h_list.1 x hxE; simp_all +decide [ stringsOfLength ] ;
    have hBcard : B.card ≤ 2^(N.bits.length + n / 128) := by
      have := hBdesc.2.2; aesop;
    have hW : (E ∩ B).card ≤ n * ((n + 1)^7 * B.card / hammingVol n (n / 64) + 1) := by
      have := hamming_list_decoding_intersection n ( n / 64 ) N r' E z h_list hz; aesop;
    have hbits : (Nat.bits (E ∩ B).card).length ≤
        8 * (Nat.bits (n + 1)).length +
          ((N.bits.length + n / 128) - 5 * (n / 64)) + 1 := by
      apply bits_intersection_bound n B.card (hammingVol n (n / 64)) (E ∩ B).card
        (N.bits.length + n / 128) (5 * (n / 64)) (hammingVol_ge_two_pow_lin n)
        hBcard hW
    have hkey : N.bits.length ≤
        (logSlack c n + (logSlack c n + n / 128) +
          (8 * (Nat.bits (n + 1)).length +
            ((N.bits.length + n / 128) - 5 * (n / 64)) + 1) + c_int : ℕ) + c := by
      have hkey : KPPlain U x ≤
          setComplexity U E hE + setComplexity U B hB +
            (Nat.bits (E ∩ B).card).length + c_int := by
        exact hc_int E B hE hB x ( Finset.mem_inter.mpr ⟨ hxE, hBdesc.1 ⟩ );
      have hkey : KPPlain U x ≤
          (logSlack c n + (logSlack c n + n / 128) +
            (8 * (Nat.bits (n + 1)).length +
              ((N.bits.length + n / 128) - 5 * (n / 64)) + 1) + c_int : ℕ) := by
        refine le_trans hkey ?_;
        norm_num +zetaDelta at *;
        gcongr;
        · exact_mod_cast hBdesc.2.1;
        · norm_cast;
      contrapose! hxK;
      have hsum :
          KP U x [] + (c : ENat) ≤
            ((logSlack c n + (logSlack c n + n / 128) +
              (8 * (Nat.bits (n + 1)).length +
                ((N.bits.length + n / 128) - 5 * (n / 64)) + 1) + c_int + c : ℕ) : ENat) := by
        simpa only [KPPlain_eq_KP, Nat.cast_add] using
          (add_le_add hkey (le_refl (c : ENat)))
      exact lt_of_le_of_lt hsum (Nat.cast_lt.mpr hxK)
    have hlog : 2 ^ (5 * (n / 64)) ≤ N := by
      rw [ hN ];
      refine Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero ?_ ) |>.2 ?_;
      · exact ne_of_gt ( hammingVol_ge_two_pow_lin n |> lt_of_lt_of_le ( by norm_num ) );
      · refine le_trans ( Nat.mul_le_mul_left _ ( hammingVol_le_two_pow_half n ) ) ?_;
        rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by decide ) ( by omega ) ;
    have hlog : 5 * (n / 64) ≤ N.bits.length := by
      rw [ Nat.le_iff_lt_or_eq ];
      refine lt_or_eq_of_le ( Nat.le_of_not_lt fun h => ?_ );
      have := Nat.lt_size_self N
      simp_all +decide only [
        Finset.mem_inter, KPPlain_eq_KP, Nat.size_eq_bits_len, and_imp, ge_iff_le,
        sup_le_iff
      ]
      exact not_le_of_gt this ( Nat.le_trans ( pow_le_pow_right₀ ( by decide ) h.le ) hlog );
    unfold logSlack at *;
    grind

/--
Hamming gap.  For the family 𝒜 of all Hamming balls, For some positive ε
and for all sufficiently large n there exists a string x of length n such that
the distance between P_x^𝒜 and P_x exceeds ε n.

We state "distance > ε n" formally as: there exists a point (i, j)
in the unrestricted profile P_x such that the restricted profile P_x^𝒜 does not
contain (i + ⌊n / c_gap⌋, j + ⌊n / c_gap⌋).
-/
theorem prop_hamming_gap (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c_gap : ℕ, c_gap > 0 ∧ ∃ c : ℕ, ∀ n ≥ c, ∃ x : BitString,
      x.length = n ∧
      ∃ i j : ℕ, InDescriptionProfile U x i j ∧
        ¬ InDescriptionProfileIn hammingFamily U x (i + n / c_gap) (j + n / c_gap) := by
  obtain ⟨c_E, hc_E⟩ := exists_list_decoding_set_low_complexity U hU
  obtain ⟨c_x, hc_x⟩ := exists_high_complexity_element_in_finset U hU
  let c_total := max c_x c_E
  obtain ⟨c_gap, hgap_pos, c_min, hex⟩ := hamming_gap_exclusion U hU c_total
  refine ⟨c_gap, hgap_pos, max c_min (max c_total 64), ?_⟩
  intro n hn
  set r := n / 64
  set N := 2 ^ n / hammingVol n r
  have hn_pos : 0 < n := by omega
  have hN_eq : N = 2 ^ n / hammingVol n r := rfl
  have hr_eq : r = n / 64 := rfl
  have hE_exists := exists_list_decoding_set n r N hn_pos hN_eq
  obtain ⟨E, hE_ne, hE_is, hE_K⟩ := hc_E n r N hr_eq hN_eq hE_exists
  obtain ⟨x, hx_in, hx_K⟩ := hc_x E hE_ne
  have h_len : ∀ x ∈ E, x.length = n := hE_is.1
  have hn_ge : n ≥ c_min := by omega
  have hcE_le : c_E ≤ c_total := by
    dsimp [c_total]
    exact le_max_right _ _
  have hcx_le : c_x ≤ c_total := by
    dsimp [c_total]
    exact le_max_left _ _
  have hE_K' : setComplexity U E hE_ne ≤ (logSlack c_total n : ENat) := by
    calc
      setComplexity U E hE_ne ≤ (logSlack c_E n : ENat) := hE_K
      _ ≤ (logSlack c_total n : ENat) := by
        exact_mod_cast logSlack_mono_left hcE_le n
  have hx_K' : (Nat.bits N).length ≤ KPPlain U x + (c_total : ENat) := by
    have hx_KN : ((Nat.bits N).length : ENat) ≤ KPPlain U x + (c_x : ENat) := by
      simpa [hE_is.2.1] using hx_K
    calc
      ((Nat.bits N).length : ENat) ≤ KPPlain U x + (c_x : ENat) := hx_KN
      _ ≤ KPPlain U x + (c_total : ENat) := by
        exact add_le_add le_rfl (by exact_mod_cast hcx_le : (c_x : ENat) ≤ (c_total : ENat))
  obtain ⟨i, j, h_in_prof, h_not_in_prof⟩ := hex n N E hE_ne hE_is hN_eq hE_K' hn_ge x hx_in hx_K'
  refine ⟨x, h_len x hx_in, i, j, h_in_prof, h_not_in_prof⟩

end Kolmogorov


