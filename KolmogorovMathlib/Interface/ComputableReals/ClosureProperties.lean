import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Interface.ComputableReals.Part01

/-!
# Building lower semicomputable reals

The constructions that produce new computable and lower semicomputable reals from old ones:
negation (`IsComputableReal.neg`), sums and rational shifts
(`IsLowerSemicomputableReal.add`, `add_rat`), and the comparison principle
`isComputableReal_of_lower_of_lower_neg`, a real semicomputable from both sides is computable.
Two supply routes follow: suprema of computable families of rationals
(`isLowerSemicomputableSeq_of_monotone`, `isLowerSemicomputableReal_of_isLUB_family`) and
partial sums of a computable non-negative sequence
(`computable_partialSum`, `isLowerSemicomputableReal_of_partialSums`, with the cumulative and
supremum forms). The unbounded-search lemma `computable_rfind` underlies the searches.
-/

namespace Kolmogorov
namespace ComputableReals
open Encodable Denumerable

/-- The negation of a computable real is computable. -/
theorem IsComputableReal.neg {a : ℝ} (h : IsComputableReal a) : IsComputableReal (-a) := by
  obtain ⟨f, hf, hspec⟩ := h
  refine ⟨fun e => -(f e), computable_ratNeg.comp hf, fun e he => ?_⟩
  have h1 := hspec e he
  have h2 : (-a) - ((-(f e) : ℚ) : ℝ) = -(a - ((f e : ℚ) : ℝ)) := by push_cast; ring
  rw [h2, abs_neg]
  exact h1

/-- Sums of lower semicomputable reals are lower semicomputable. -/
theorem IsLowerSemicomputableReal.add {a b : ℝ} (ha : IsLowerSemicomputableReal a)
    (hb : IsLowerSemicomputableReal b) : IsLowerSemicomputableReal (a + b) := by
  obtain ⟨q, hq, hmq, htq⟩ := ha
  obtain ⟨p, hp, hmp, htp⟩ := hb
  refine ⟨fun n => q n + p n, computable_ratAdd.comp hq hp, fun m n hmn => ?_, ?_⟩
  · exact add_le_add (hmq hmn) (hmp hmn)
  · have := htq.add htp
    refine Filter.Tendsto.congr (fun n => ?_) this
    push_cast
    ring

/-- Shifting a lower semicomputable real by a rational keeps it lower semicomputable. -/
theorem IsLowerSemicomputableReal.add_rat {a : ℝ} (ha : IsLowerSemicomputableReal a) (r : ℚ) :
    IsLowerSemicomputableReal (a + (r : ℝ)) :=
  ha.add (isLowerSemicomputableReal_ratCast r)

/-! ### Unbounded search -/

/-- If `test a n` is a computable test that succeeds for some `n` at every `a`, and the value
of `f a` is `g a n` at the least successful `n`, then `f` is computable. -/
theorem computable_rfind {α σ : Type*} [Primcodable α] [Primcodable σ]
    {test : α → ℕ → Bool} (htest : Computable₂ test)
    {g : α → ℕ → σ} (hg : Computable₂ g) {f : α → σ}
    (hf : ∀ a, ∃ n, test a n = true ∧ (∀ m, m < n → test a m = false) ∧ f a = g a n) :
    Computable f := by
  have hrf : Partrec (fun a => Nat.rfind (fun n => (Part.some (test a n)))) :=
    Partrec.rfind htest.partrec₂
  have hpart : Partrec (fun a => Part.map (g a) (Nat.rfind (fun n => (Part.some (test a n))))) :=
    Partrec.map hrf hg
  refine Partrec.of_eq_tot hpart (fun a => ?_)
  obtain ⟨n, h1, h2, h3⟩ := hf a
  have hmem : n ∈ Nat.rfind (fun k => (Part.some (test a k))) := by
    refine Nat.mem_rfind.2 ⟨?_, ?_⟩
    · rw [h1]; exact Part.mem_some _
    · intro m hm
      rw [h2 m hm]; exact Part.mem_some _
  rw [h3]
  exact Part.mem_map _ hmem

/-- **Comparison.** A real that is lower semicomputable from both sides is computable. -/
theorem isComputableReal_of_lower_of_lower_neg {a : ℝ} (h₁ : IsLowerSemicomputableReal a)
    (h₂ : IsLowerSemicomputableReal (-a)) : IsComputableReal a := by
  obtain ⟨q, hq, -, hqle, -, htq⟩ := h₁.exists_seq
  obtain ⟨p, hp, -, hple, -, htp⟩ := h₂.exists_seq
  have hpa : ∀ n, a ≤ ((-p n : ℚ) : ℝ) := by
    intro n
    have h := hple n
    push_cast
    linarith
  have hlim : Filter.Tendsto (fun n => ((-p n - q n : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => -((p n : ℚ) : ℝ)) Filter.atTop (nhds a) := by
      simpa using htp.neg
    have h2 := h1.sub htq
    have h3 : (fun n : ℕ => -((p n : ℚ) : ℝ) - ((q n : ℚ) : ℝ))
        = (fun n : ℕ => ((-p n - q n : ℚ) : ℝ)) := by
      funext n
      push_cast
      ring
    rw [h3] at h2
    simpa using h2
  have hcmp : Computable₂ (fun a b : ℚ => decide (a ≤ b)) :=
    (PrimrecRel.decide primrec_ratLe).to_comp
  have hnpq : Computable (fun z : ℚ × ℕ => -p z.2 - q z.2) :=
    computable_ratSub.comp (computable_ratNeg.comp (hp.comp Computable.snd))
      (hq.comp Computable.snd)
  have hle1 : Computable (fun z : ℚ × ℕ => decide (-p z.2 - q z.2 ≤ z.1)) :=
    hcmp.comp hnpq Computable.fst
  have hle2 : Computable (fun z : ℚ × ℕ => decide (z.1 ≤ (0 : ℚ))) :=
    hcmp.comp Computable.fst (Computable.const 0)
  have htest : Computable₂ (fun (e : ℚ) (n : ℕ) =>
      (decide (-p n - q n ≤ e) || decide (e ≤ (0 : ℚ)))) :=
    (((Primrec.dom_bool₂ (fun x y : Bool => x || y)).to_comp).comp hle1 hle2).to₂
  have hexists : ∀ e : ℚ, ∃ n, (decide (-p n - q n ≤ e) || decide (e ≤ (0 : ℚ))) = true := by
    intro e
    by_cases he : e ≤ 0
    · exact ⟨0, by simp [he]⟩
    · push Not at he
      have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
      obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hepos).exists
      have hn' : -p n - q n ≤ e := by
        have : (-p n - q n : ℚ) < e := by exact_mod_cast hn
        exact this.le
      exact ⟨n, by simp [hn']⟩
  refine ⟨fun e => q (Nat.find (hexists e)), ?_, ?_⟩
  · refine computable_rfind htest (hq.comp Computable.snd).to₂ (fun e => ?_)
    refine ⟨Nat.find (hexists e), Nat.find_spec (hexists e), fun m hm => ?_, rfl⟩
    have hmin := Nat.find_min (hexists e) hm
    rcases Bool.eq_false_or_eq_true
      (decide (-p m - q m ≤ e) || decide (e ≤ (0 : ℚ))) with h | h
    · exact absurd h hmin
    · exact h
  · intro e he
    have hspec := Nat.find_spec (hexists e)
    set n := Nat.find (hexists e) with hn
    have hkey : -p n - q n ≤ e := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hspec
      rcases hspec with h | h
      · exact h
      · exact absurd h (not_le.2 he)
    have h1 : ((q n : ℚ) : ℝ) ≤ a := hqle n
    have h2 : a ≤ ((-p n : ℚ) : ℝ) := hpa n
    have h3 : ((-p n - q n : ℚ) : ℝ) ≤ (e : ℝ) := by exact_mod_cast hkey
    rw [abs_le]
    push_cast at h2 h3 ⊢
    constructor <;> linarith

/-! ### Suprema of enumerated families -/

/-- **Suprema of enumerated families.** A computable family of rationals, non-decreasing in
the second argument, has a lower semicomputable sequence of suprema. -/
theorem isLowerSemicomputableSeq_of_monotone {f : ℕ → ℕ → ℚ}
    (hf : Computable (fun z : ℕ × ℕ => f z.1 z.2)) (hmono : ∀ i, Monotone (f i))
    {p : ℕ → ℝ} (hlub : ∀ i, IsLUB (Set.range fun n => ((f i n : ℚ) : ℝ)) (p i)) :
    IsLowerSemicomputableSeq p := by
  refine ⟨fun i n => some (f i n), Computable.option_some.comp hf, ?_, ?_⟩
  · intro i n r hr
    rw [Option.mem_def, Option.some_inj] at hr
    exact ⟨f i (n + 1), rfl, hr ▸ hmono i (Nat.le_succ n)⟩
  · intro i
    have hset : {r : ℝ | ∃ n r', (some (f i n) : Option ℚ) = some r' ∧ (r' : ℝ) = r}
        = Set.range fun n => ((f i n : ℚ) : ℝ) := by
      ext r
      simp only [Set.mem_ofPred_eq, Option.some_inj, Set.mem_range]
      constructor
      · rintro ⟨n, r', rfl, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨n, f i n, rfl, rfl⟩
    rw [hset]
    exact hlub i

/-- Each member of a computable family of rationals has a lower semicomputable supremum. -/
theorem isLowerSemicomputableReal_of_isLUB_family {f : ℕ → ℕ → ℚ}
    (hf : Computable (fun z : ℕ × ℕ => f z.1 z.2)) {p : ℕ → ℝ}
    (hlub : ∀ i, IsLUB (Set.range fun n => ((f i n : ℚ) : ℝ)) (p i)) (i : ℕ) :
    IsLowerSemicomputableReal (p i) :=
  isLowerSemicomputableReal_of_isLUB
    (hf.comp (Computable.pair (Computable.const i) Computable.id)) (hlub i)

/-! ### Partial sums -/

/-- Partial sums of a computable sequence of rationals are computable. -/
theorem computable_partialSum {s : ℕ → ℚ} (hs : Computable s) :
    Computable (fun n : ℕ => ∑ i ∈ Finset.range n, s i) := by
  have hstep : Computable₂ (fun (_ : ℕ) (z : ℕ × ℚ) => z.2 + s z.1) :=
    (computable_ratAdd.comp (Computable.snd.comp Computable.snd)
      (hs.comp (Computable.fst.comp Computable.snd))).to₂
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ : ℕ => (0 : ℚ))
    (h := fun (_ : ℕ) (z : ℕ × ℚ) => z.2 + s z.1) Computable.id (Computable.const 0) hstep
  refine h.of_eq (fun n => ?_)
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← ih]

/-- Partial sums of a non-negative sequence are non-decreasing. -/
theorem monotone_partialSum {s : ℕ → ℚ} (hnn : ∀ n, 0 ≤ s n) :
    Monotone (fun n : ℕ => ∑ i ∈ Finset.range n, s i) :=
  monotone_nat_of_le_succ (fun n => by
    rw [Finset.sum_range_succ]
    linarith [hnn n])

/-- A computable non-negative rational sequence whose partial sums converge to `a` witnesses
`IsLowerSemicomputableReal a`.  The hypothesis is about the *increments*: `s` itself must be
computable and non-negative, and the partial sums are formed here.  When what you have is the
cumulative sequence instead, use `isLowerSemicomputableReal_of_monotone_cumulative`. -/
theorem isLowerSemicomputableReal_of_partialSums {s : ℕ → ℚ} (hs : Computable s)
    (hnn : ∀ n, 0 ≤ s n) {a : ℝ}
    (ht : Filter.Tendsto (fun n => ((∑ i ∈ Finset.range n, s i : ℚ) : ℝ))
      Filter.atTop (nhds a)) :
    IsLowerSemicomputableReal a :=
  ⟨fun n => ∑ i ∈ Finset.range n, s i, computable_partialSum hs, monotone_partialSum hnn, ht⟩

/-- The cumulative form of the partial-sums bridge: a computable non-decreasing sequence of
rationals converging to `a` witnesses `IsLowerSemicomputableReal a` directly.

This is usually the shape one has in practice.  "The probability that the machine halts within
`n` steps" is naturally given as the cumulative quantity, not as a sequence of increments, and
feeding it here avoids having to exhibit the increments and their non-negativity.  The
identification of the limit with the intended real number is left to the caller: that step is
about the object being approximated, not about computability. -/
theorem isLowerSemicomputableReal_of_monotone_cumulative {S : ℕ → ℚ} (hS : Computable S)
    (hmono : Monotone S) {a : ℝ}
    (ht : Filter.Tendsto (fun n => ((S n : ℚ) : ℝ)) Filter.atTop (nhds a)) :
    IsLowerSemicomputableReal a :=
  ⟨S, hS, hmono, ht⟩

/-- Regression test for `ratCode_ofNat`.  That theorem deliberately depends on the current
implementation of `Mathlib`'s `Denumerable ℚ`; if a future `Mathlib` changes the enumeration,
this test fails loudly here rather than silently invalidating every rational computability
result downstream. -/
example : ratCode (Denumerable.ofNat ℚ 7) = unrank 7 := ratCode_ofNat 7

/-- Supremum form of the partial-sums bridge (no monotonicity needed). -/
theorem isLowerSemicomputableReal_of_isLUB_partialSums {s : ℕ → ℚ} (hs : Computable s)
    {a : ℝ} (hlub : IsLUB (Set.range fun n => ((∑ i ∈ Finset.range n, s i : ℚ) : ℝ)) a) :
    IsLowerSemicomputableReal a :=
  isLowerSemicomputableReal_of_isLUB (computable_partialSum hs) hlub

end ComputableReals
end Kolmogorov
