import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.Separation
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ProfileRealization

/-!
# Existence of antistochastic strings for the ordinary (plain) profile

Section 7 of the source uses *antistochastic* strings: strings `x` of length `n`
and plain complexity `k` whose whole ordinary plain description profile lies
in the union of the half planes `m > k - eps` and `m + l > n - eps`.

The prefix-complexity version of the construction is already available as
`exists_antistochastic` (a corollary of the curve-realization theorem).  This
file performs the prefix-to-plain bridge and proves the source-facing
`AntistochasticExistenceStatement`.

Two points deserve mention.

* The prefix construction is invoked at the complexity level
  `max k (t + 1)`, where `t` is the total logarithmic overhead of the bridge.
  This is legitimate because the source statement only asks for the displayed
  complexity to agree with `k` up to `O(log n)`, and it removes the degenerate
  regime in which the profile guarantee of the prefix construction is vacuous.

* For the finitely many `n` that are smaller than the accumulated logarithmic
  overhead, every string works except possibly one: a plain description with
  both coordinates `0` is a singleton whose canonical code has plain complexity
  `0`, and at most one bitstring has plain complexity `0`.  Choosing between two
  distinct strings of length `n` avoids it.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-- At most one bitstring has plain complexity `0`: such a string must be the
value of the machine on the empty program and the empty condition. -/
theorem eq_of_plainK_eq_zero (V : Map) {w w' : BitString}
    (h : plainK V w = 0) (h' : plainK V w' = 0) : w = w' := by
  have hw : ∃ p, programLength p ≤ 0 ∧ produces V p [] w := by
    refine (condKLeIff V w [] 0).mp ?_
    simpa [plainK] using h.le
  have hw' : ∃ p, programLength p ≤ 0 ∧ produces V p [] w' := by
    refine (condKLeIff V w' [] 0).mp ?_
    simpa [plainK] using h'.le
  obtain ⟨p, hp, hprod⟩ := hw
  obtain ⟨p', hp', hprod'⟩ := hw'
  have hpe : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hp)
  have hpe' : p' = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hp')
  subst hpe; subst hpe'
  exact Part.mem_unique hprod hprod'

/-- The canonical code of a uniform model determines the underlying set. -/
theorem eq_of_codedUniformOn_code_eq {S T : Finset BitString}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (h : (codedUniformOn S hS).code = (codedUniformOn T hT).code) : S = T := by
  have h1 : canonicalFinsetList S = canonicalFinsetList T := by
    rw [← canonicalPointListOfCode_codedUniformOn S hS,
      ← canonicalPointListOfCode_codedUniformOn T hT, h]
  have h2 : (canonicalFinsetList S).toFinset = (canonicalFinsetList T).toFinset := by
    rw [h1]
  rwa [canonicalFinsetList_toFinset, canonicalFinsetList_toFinset] at h2

/-- For every positive length there is a string of that length that lies in no
singleton model of plain complexity `0`. -/
theorem exists_length_avoiding_zero_singleton (V : Map) (n : Nat) (hn : 1 ≤ n) :
    ∃ x : BitString, x.length = n ∧
      ∀ (S : Finset BitString) (hS : S.Nonempty), x ∈ S → S.card ≤ 1 →
        plainSetComplexity V S hS ≠ 0 := by
  classical
  set a : BitString := List.replicate n false with ha
  set b : BitString := true :: List.replicate (n - 1) false with hb
  have halen : a.length = n := by simp [ha]
  have hblen : b.length = n := by simp [hb]; omega
  have hab : a ≠ b := by
    intro h
    have : a.head? = b.head? := by rw [h]
    rw [ha, hb] at this
    rw [List.head?_replicate] at this
    simp only [List.head?_cons] at this
    have hn0 : n ≠ 0 := by omega
    simp [hn0] at this
  -- the property, restated for a single string
  have key : ∀ x : BitString,
      (∀ (S : Finset BitString) (hS : S.Nonempty), x ∈ S → S.card ≤ 1 →
        plainSetComplexity V S hS ≠ 0) ↔
      plainK V (codedUniformOn {x} (Finset.singleton_nonempty x)).code ≠ 0 := by
    intro x
    constructor
    · intro h
      exact h {x} (Finset.singleton_nonempty x) (Finset.mem_singleton_self x)
        (by simp)
    · intro h S hS hxS hcard
      have hSx : S = {x} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hxS, fun y hy => ?_⟩
        exact Finset.card_le_one.mp hcard y hy x hxS
      subst hSx
      exact h
  by_cases hA : plainK V (codedUniformOn {a} (Finset.singleton_nonempty a)).code ≠ 0
  · exact ⟨a, halen, (key a).mpr hA⟩
  · refine ⟨b, hblen, (key b).mpr ?_⟩
    push Not at hA
    intro hB
    exact hab (Finset.singleton_injective
      (eq_of_codedUniformOn_code_eq (Finset.singleton_nonempty a)
        (Finset.singleton_nonempty b) (eq_of_plainK_eq_zero V hA hB)))

/-- Existence of antistochastic strings in the ordinary plain profile
(the statement preceding VS40's normality proposition). -/
theorem exists_antistochastic_plain (V : Map) (hV : isOptimalConditional V) :
    AntistochasticExistenceStatement V := by
  classical
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c0, h0⟩ := exists_antistochastic U hU
  obtain ⟨c3, h3⟩ := inDescriptionProfile_of_inPlainDescriptionProfile V U hV hU
  obtain ⟨cpl, hpl⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨ckp, hkp⟩ := KPPlain_le_plainK_add_KPPlain_plainK U V hU hV
  obtain ⟨clen2, hlen2⟩ := KPPlain_le_two_mul_length U hU
  obtain ⟨clen, hlen⟩ := plainKLeLength V hV
  obtain ⟨C1, hC1⟩ := logSlack_linear_bound 2 1 clen
  refine ⟨c3 + 2 * c0 + C1 + (clen2 + ckp + cpl + clen + 1), ?_⟩
  set c := c3 + 2 * c0 + C1 + (clen2 + ckp + cpl + clen + 1) with hcdef
  intro n k hkn
  set s := logSlack c0 n with hs
  set u := logSlack c3 n with hu
  set w := logSlack C1 n with hw
  set eps := logSlack c n with heps
  have hbudget : u + s + s + w + (clen2 + ckp + cpl + clen + 1) ≤ eps := by
    simp only [hs, hu, hw, heps, hcdef, logSlack]
    nlinarith [Nat.zero_le ((clen2 + ckp + cpl + clen + 1) * (Nat.bits n).length)]
  have hwbits : 2 * (Nat.bits (n + clen)).length ≤ w := by
    have h := hC1 n
    simp only [hw, logSlack, one_mul] at h ⊢
    omega
  -- plain complexity of any length-`n` string is finite and at most `n + clen`
  have hplainfin : ∀ y : BitString, y.length = n →
      ∃ ky : Nat, plainK V y = (ky : ENat) ∧ ky ≤ n + clen := by
    intro y hy
    have hle : plainK V y ≤ ((n + clen : Nat) : ENat) := by
      have := hlen y
      rw [show programLength y = n from hy] at this
      refine this.trans ?_
      push_cast
      exact le_rfl
    have hne : plainK V y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
    refine ⟨(plainK V y).toNat, (ENat.coe_toNat hne).symm, ?_⟩
    have := hle
    rw [← ENat.coe_toNat hne] at this
    exact_mod_cast this
  by_cases hbig : u + s + 1 ≤ n
  · -- Main regime: realize the extremal curve at complexity `max k (u + s + 1)`.
    set k' := max k (u + s + 1) with hk'
    have hk'n : k' ≤ n := max_le (Nat.le_of_lt hkn) hbig
    have hkk' : k ≤ k' := le_max_left _ _
    have hk'lb : u + s + 1 ≤ k' := le_max_right _ _
    have hk'ub : k' ≤ k + u + s + 1 := by
      simp only [hk']
      omega
    obtain ⟨x, hxlen, hup, hlow, hprof⟩ := h0 n k' hk'n
    obtain ⟨kx, hkx, hkxn⟩ := hplainfin x hxlen
    have hAup : kx ≤ k' + s + cpl := by
      have h1 : plainK V x ≤ KPPlain U x + (cpl : ENat) := hpl x
      have h2 : plainK V x ≤ ((k' + s : Nat) : ENat) + (cpl : ENat) :=
        h1.trans (by gcongr; exact_mod_cast hup)
      rw [hkx] at h2
      have h3' : ((kx : Nat) : ENat) ≤ ((k' + s + cpl : Nat) : ENat) := by
        refine h2.trans ?_
        push_cast
        exact le_rfl
      exact_mod_cast h3'
    have hBlow : k' ≤ kx + w + clen2 + ckp + s := by
      have h1 : KPPlain U x ≤ (kx : ENat) + KPPlain U (Nat.bits kx) + (ckp : ENat) :=
        hkp x kx hkx
      have h2 : KPPlain U (Nat.bits kx) ≤ 2 * ((Nat.bits kx).length : ENat) + (clen2 : ENat) := by
        have := hlen2 (Nat.bits kx)
        exact_mod_cast this
      have hbits : (Nat.bits kx).length ≤ (Nat.bits (n + clen)).length :=
        length_natBits_mono hkxn
      have hnat : kx + (2 * (Nat.bits kx).length + clen2) + ckp ≤ kx + w + clen2 + ckp := by
        omega
      have h3' : KPPlain U x ≤ ((kx + w + clen2 + ckp : Nat) : ENat) := by
        refine h1.trans ?_
        calc (kx : ENat) + KPPlain U (Nat.bits kx) + (ckp : ENat)
            ≤ (kx : ENat) + (2 * ((Nat.bits kx).length : ENat) + (clen2 : ENat))
                + (ckp : ENat) := by gcongr
          _ = ((kx + (2 * (Nat.bits kx).length + clen2) + ckp : Nat) : ENat) := by push_cast; ring
          _ ≤ ((kx + w + clen2 + ckp : Nat) : ENat) := by exact_mod_cast hnat
      have h4 : (k' : ENat) ≤ ((kx + w + clen2 + ckp + s : Nat) : ENat) := by
        refine hlow.trans ?_
        calc KPPlain U x + (logSlack c0 n : ENat)
            ≤ ((kx + w + clen2 + ckp : Nat) : ENat) + (s : ENat) := by
              gcongr
          _ = ((kx + w + clen2 + ckp + s : Nat) : ENat) := by push_cast; ring
      exact_mod_cast h4
    refine ⟨x, kx, hxlen, ⟨hxlen, hkx, ?_⟩, by omega, by omega⟩
    intro m l hml
    by_cases hmn : n < m
    · right; omega
    · push Not at hmn
      have hpref : InDescriptionProfile U x (m + u) l := by
        have hbridge := h3 x m l hml
        refine hbridge.mono_i ?_
        have : logSlack c3 m ≤ u := by
          rw [hu]
          exact logSlack_mono_right c3 hmn
        omega
      by_cases hcase : (m + u) + s < k'
      · have hlen_le := hprof (m + u) l hcase hpref
        right
        omega
      · push Not at hcase
        rcases Nat.eq_zero_or_pos m with hm0 | hm1
        · exfalso; omega
        · left; omega
  · -- Degenerate regime: `n` is below the accumulated logarithmic overhead.
    push Not at hbig
    have hn1 : 1 ≤ n := by omega
    obtain ⟨x, hxlen, havoid⟩ := exists_length_avoiding_zero_singleton V n hn1
    obtain ⟨kx, hkx, hkxn⟩ := hplainfin x hxlen
    have hkxeps : kx ≤ eps := by omega
    have hneps : n ≤ eps := by omega
    refine ⟨x, kx, hxlen, ⟨hxlen, hkx, ?_⟩, by omega, by omega⟩
    intro m l hml
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · rcases Nat.eq_zero_or_pos l with hl0 | hl1
      · exfalso
        subst hm0; subst hl0
        obtain ⟨S, hS, hxS, hcomp, hcard⟩ := hml
        refine havoid S hS hxS (by simpa using hcard) ?_
        refine le_antisymm ?_ (zero_le)
        simpa using hcomp
      · right; omega
    · left; omega

/-- Antistochasticity only becomes weaker when the error parameter grows. -/
theorem IsAntistochastic.mono_epsilon
    {V : Map} {n k epsilon epsilon' : Nat} {x : BitString}
    (hle : epsilon ≤ epsilon') (h : IsAntistochastic V n k epsilon x) :
    IsAntistochastic V n k epsilon' x := by
  refine ⟨h.1, h.2.1, fun m l hml => ?_⟩
  rcases h.2.2 m l hml with hcase | hcase
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Antistochastic strings of every prescribed length and complexity exist and
are normal: combining the existence statement with VS40's normality
proposition. -/
theorem exists_normal_antistochastic (V T : Map)
    (hV : isOptimalConditional V) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ n k : Nat, k < n →
      ∃ (x : BitString) (kx : Nat),
        x.length = n ∧
        IsAntistochastic V n kx (logSlack c n) x ∧
        k ≤ kx + logSlack c n ∧
        kx ≤ k + logSlack c n ∧
        IsNormalString V T x (logSlack c n) (logSlack c n) := by
  obtain ⟨ca, ha⟩ := exists_antistochastic_plain V hV
  obtain ⟨cn, hnormal⟩ := prop_antistochastic_is_normal V T hV hT
  refine ⟨ca + cn, fun n k hkn => ?_⟩
  obtain ⟨x, kx, hxlen, hanti, hlow, hup⟩ := ha n k hkn
  have hmono : logSlack ca n ≤ logSlack (ca + cn) n :=
    logSlack_mono_left (Nat.le_add_right _ _) n
  have hmono' : logSlack cn n ≤ logSlack (ca + cn) n :=
    logSlack_mono_left (Nat.le_add_left _ _) n
  have hnorm : IsNormalString V T x (logSlack cn n) (logSlack ca n + logSlack cn n) :=
    hnormal x n kx (logSlack ca n) hanti
  refine ⟨x, kx, hxlen, hanti.mono_epsilon hmono, by omega, by omega, ?_⟩
  refine (hnorm.mono_delta ?_).mono_epsilon hmono'
  rw [logSlack_add_const]

end Kolmogorov
