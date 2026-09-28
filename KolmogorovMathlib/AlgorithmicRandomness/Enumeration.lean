import KolmogorovMathlib.AlgorithmicRandomness.Disjointify
import Mathlib.Computability.PartrecCode

/-!
# An effective enumeration of all uniformly effective open families

Using the standard enumeration of partial recursive functions by codes, we build
a single computable family `candEnum : ℕ → ℕ → Option BitString` such that for
every computable family `h : ℕ → ℕ → Option BitString` there is a code `c` with

`⋃ s, Ω_{candEnum (pair c n) s} = ⋃ i, Ω_{h (n+1) i}`  for every `n`.

The shift by one in the level is a convenience for the construction of a
universal Martin-Lof test.
-/

namespace Kolmogorov

open MeasureTheory ENNReal Nat.Partrec

/-- The `s`-th interval enumerated by the code `(unpair m).1` at level
`(unpair m).2`: the index `s` codes a pair `(i, t)`, where `i` is the argument
and `t` the number of steps of the simulation. -/
def candEnum (m s : ℕ) : Option BitString :=
  (Code.evaln (Nat.unpair s).2 (Denumerable.ofNat Code (Nat.unpair m).1)
      (Nat.pair (Nat.unpair m).2 (Nat.unpair s).1)).bind
    fun v => (Encodable.decode₂ (Option BitString) v).getD none

/-- The candidate enumeration used to list basic open sets is computable in both arguments. -/
theorem computable₂_candEnum : Computable₂ candEnum := by
  have hk : Computable (fun p : ℕ × ℕ => (Nat.unpair p.2).2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hc : Computable (fun p : ℕ × ℕ => Denumerable.ofNat Code (Nat.unpair p.1).1) :=
    ((Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).to_comp
  have hn : Computable (fun p : ℕ × ℕ => Nat.pair (Nat.unpair p.1).2 (Nat.unpair p.2).1) :=
    (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).to_comp
  have hpair : Computable (fun p : ℕ × ℕ =>
      (((Nat.unpair p.2).2, Denumerable.ofNat Code (Nat.unpair p.1).1),
        Nat.pair (Nat.unpair p.1).2 (Nat.unpair p.2).1)) :=
    Computable.pair (Computable.pair hk hc) hn
  have hev : Computable (fun p : ℕ × ℕ =>
      Code.evaln (Nat.unpair p.2).2 (Denumerable.ofNat Code (Nat.unpair p.1).1)
        (Nat.pair (Nat.unpair p.1).2 (Nat.unpair p.2).1)) :=
    Code.primrec_evaln.to_comp.comp hpair
  refine Computable.option_bind hev ?_
  have hdec : Computable (fun r : (ℕ × ℕ) × ℕ => Encodable.decode₂ (Option BitString) r.2) :=
    (Primrec.decode₂.comp Primrec.snd).to_comp
  exact Computable.option_getD hdec (Computable.const none)

/-- Every computable family of interval sequences is enumerated by some code. -/
theorem exists_code_candEnum {h : ℕ → ℕ → Option BitString} (hh : Computable₂ h) :
    ∃ c : ℕ, ∀ n : ℕ,
      (⋃ s, coverSet (candEnum (Nat.pair c n)) s) = ⋃ i, coverSet (h (n + 1)) i := by
  -- the function to be coded
  set G : ℕ → ℕ := fun x => Encodable.encode (h ((Nat.unpair x).1 + 1) (Nat.unpair x).2) with hG
  have hGcomp : Computable G := by
    have h1 : Computable (fun x : ℕ => h ((Nat.unpair x).1 + 1) (Nat.unpair x).2) :=
      hh.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp
    exact Primrec.encode.to_comp.comp h1
  have hpart : Nat.Partrec (fun x => Part.some (G x)) :=
    Partrec.nat_iff.mp (Computable.partrec hGcomp)
  obtain ⟨c₀, hc₀⟩ := Code.exists_code.mp hpart
  refine ⟨Encodable.encode c₀, fun n => ?_⟩
  have hofNat : Denumerable.ofNat Code (Nat.unpair (Nat.pair (Encodable.encode c₀) n)).1 = c₀ := by
    rw [Nat.unpair_pair]
    exact Denumerable.ofNat_encode c₀
  have hlevel : (Nat.unpair (Nat.pair (Encodable.encode c₀) n)).2 = n := by
    rw [Nat.unpair_pair]
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun s => ?_
    cases hcs0 : candEnum (Nat.pair (Encodable.encode c₀) n) s with
    | none => rw [coverSet, hcs0]; simp
    | some u =>
      -- the value produced by the simulation is the value of `h`
      have hcs := hcs0
      unfold candEnum at hcs
      rw [hofNat, hlevel] at hcs
      cases hev : Code.evaln (Nat.unpair s).2 c₀ (Nat.pair n (Nat.unpair s).1) with
      | none => rw [hev] at hcs; simp at hcs
      | some v =>
        rw [hev] at hcs
        simp only [Option.bind_some] at hcs
        have hmem : v ∈ Code.eval c₀ (Nat.pair n (Nat.unpair s).1) :=
          Code.evaln_sound (by rw [hev]; rfl)
        rw [hc₀] at hmem
        have hveq : v = G (Nat.pair n (Nat.unpair s).1) := by
          simpa [eq_comm] using hmem
        rw [hveq, hG] at hcs
        simp only [Nat.unpair_pair, Encodable.encodek₂, Option.getD_some] at hcs
        refine Set.subset_iUnion_of_subset (Nat.unpair s).1 ?_
        rw [coverSet, coverSet, hcs0, hcs]
  · refine Set.iUnion_subset fun i => ?_
    cases hhi : h (n + 1) i with
    | none => rw [coverSet, hhi]; simp
    | some u =>
      have hmem : Encodable.encode (some u) ∈ Code.eval c₀ (Nat.pair n i) := by
        rw [hc₀]
        simp [hG, hhi]
      obtain ⟨t, ht⟩ := Code.evaln_complete.mp hmem
      refine Set.subset_iUnion_of_subset (Nat.pair i t) ?_
      have hcs : candEnum (Nat.pair (Encodable.encode c₀) n) (Nat.pair i t) = some u := by
        have ht' : Code.evaln t c₀ (Nat.pair n i) = some (Encodable.encode (some u)) := by
          simpa [eq_comm] using ht
        unfold candEnum
        rw [hofNat, hlevel]
        simp only [Nat.unpair_pair, ht', Option.bind_some, Encodable.encodek₂,
          Option.getD_some]
      rw [coverSet, coverSet, hcs, hhi]

end Kolmogorov
