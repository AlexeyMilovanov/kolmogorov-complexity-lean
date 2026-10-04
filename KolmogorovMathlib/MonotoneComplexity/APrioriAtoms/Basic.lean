/-
Copyright (c) 2024 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Authors
-/
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Infra

/-!
# The atom of the branch `x01^∞`

For a bit string `x` the sequence `atomSeq x = x01^∞` is the branch of the binary tree that
follows `x`, turns left once and then goes right forever.  Its finite prefixes beyond `x` are
the strings `tailOnes x k = x ++ [false] ++ 1^k`, and the a priori probability of the branch,

`atomMass x = ⨅ k, universalContinuousSemimeasure (tailOnes x k)`,

is the mass the universal continuous semimeasure gives to the single infinite sequence
`x01^∞` — the limit of a nonincreasing sequence, so an infimum.

The module fixes the two strings, proves the prefix identity `cantorPrefix_atomSeq` and the
uniform computability of `atomSeq`, records that distinct strings give distinct branches
(`atomSeq_injective`), and states the note's first structural claim: the atom masses are a
discrete semimeasure (`tsum_atomMass_le_one`).

The theorem about the atoms `x01^∞` is the note's own; the book supplies only the setting and
the close analogues: SUV Chapter 5, §5.2 — Theorem 78, p. 135, the maximality of the a priori
probability on the tree, and Theorem 79(c),(d), p. 136, the discrete analogues of the
domination and of the antichain sum used here.

Source: the note `apriori-atoms.md`, sections "Вопрос и обозначения" and "Почему нельзя
применить максимальность m"; SUV Chapter 5, §5.2.
-/

open scoped ENNReal

namespace Kolmogorov

/-- The string `x ++ [false] ++ 1^k`: the prefix of length `|x| + 1 + k` of the branch
`x01^∞`.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
def tailOnes (x : BitString) (k : ℕ) : BitString :=
  x ++ false :: List.replicate k true

/-- The length of `tailOnes x k` is `|x| + 1 + k`. -/
@[simp] theorem length_tailOnes (x : BitString) (k : ℕ) :
    (tailOnes x k).length = x.length + 1 + k := by
  simp only [tailOnes, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- The string `tailOnes x k` split after its zero. -/
theorem tailOnes_eq_append (x : BitString) (k : ℕ) :
    tailOnes x k = (x ++ [false]) ++ List.replicate k true := by
  simp [tailOnes]

/-- Each string of the branch of `x` is a prefix of the next one. -/
theorem tailOnes_prefix_succ (x : BitString) (k : ℕ) :
    tailOnes x k <+: tailOnes x (k + 1) :=
  ⟨[true], by simp [tailOnes, List.replicate_succ']⟩

/-- The infinite sequence `x01^∞`: the bits of `x`, then a zero, then only ones.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
def atomSeq (x : BitString) : CantorSeq :=
  fun i => ((x ++ [false])[i]?).getD true

/-- Inside `x` the branch `x01^∞` has the bits of `x`. -/
theorem atomSeq_of_lt {x : BitString} {i : ℕ} (h : i < x.length) :
    atomSeq x i = x[i] := by
  have h1 : i < (x ++ [false]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [atomSeq, List.getElem?_eq_getElem h1]
  simp [List.getElem_append_left h]

/-- At position `|x|` the branch `x01^∞` has its last zero. -/
theorem atomSeq_length (x : BitString) : atomSeq x x.length = false := by
  have h1 : x.length < (x ++ [false]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [atomSeq, List.getElem?_eq_getElem h1]
  simp

/-- Beyond position `|x|` the branch `x01^∞` has only ones. -/
theorem atomSeq_of_gt {x : BitString} {i : ℕ} (h : x.length < i) :
    atomSeq x i = true := by
  have h1 : (x ++ [false]).length ≤ i := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [atomSeq, List.getElem?_eq_none h1]
  rfl

/-- The prefix of length `|x| + 1 + k` of the branch `x01^∞` is `tailOnes x k`.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
theorem cantorPrefix_atomSeq (x : BitString) (k : ℕ) :
    cantorPrefix (atomSeq x) (x.length + 1 + k) = tailOnes x k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [cantorPrefix_getElem]
    rcases lt_trichotomy i x.length with h | h | h
    · rw [atomSeq_of_lt h]
      simp only [tailOnes]
      rw [List.getElem_append_left h]
    · subst h
      rw [atomSeq_length]
      simp only [tailOnes]
      rw [List.getElem_append_right (le_refl _)]
      simp
    · rw [atomSeq_of_gt h]
      simp only [tailOnes_eq_append]
      rw [List.getElem_append_right (by simp; omega)]
      simp

/-- The branch `x01^∞` is computable uniformly in `x`.

Source: the note `apriori-atoms.md`, section "Почему m(x) ≤ C f(x)"; SUV Chapter 5, §5.2. -/
theorem computable_atomSeq :
    Computable₂ (fun (x : BitString) (i : ℕ) => atomSeq x i) := by
  have hconcat : Primrec (fun p : BitString × ℕ => p.1 ++ [false]) :=
    Primrec.list_concat.comp Primrec.fst (Primrec.const false)
  have hget : Primrec (fun p : BitString × ℕ => (p.1 ++ [false])[p.2]?) :=
    Primrec.list_getElem?.comp hconcat Primrec.snd
  exact (Primrec.option_getD.comp hget (Primrec.const true)).to_comp

/-- Different strings give different branches: the position of the last zero recovers `|x|`.

Source: the note `apriori-atoms.md`, section "Почему нельзя применить максимальность m";
SUV Chapter 5, §5.2. -/
theorem atomSeq_injective : Function.Injective atomSeq := by
  intro x y h
  have hlen : x.length = y.length := by
    by_contra hne
    rcases Nat.lt_or_ge x.length y.length with hlt | hge
    · have h1 : atomSeq x y.length = true := atomSeq_of_gt hlt
      rw [h, atomSeq_length] at h1
      exact Bool.noConfusion h1
    · have hlt : y.length < x.length := by omega
      have h1 : atomSeq y x.length = true := atomSeq_of_gt hlt
      rw [← h, atomSeq_length] at h1
      exact Bool.noConfusion h1
  apply List.ext_getElem hlen
  intro i h1 h2
  have hi := congrFun h i
  rwa [atomSeq_of_lt h1, atomSeq_of_lt h2] at hi

/-- Along the branch of `x` the a priori probability is nonincreasing.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
theorem antitone_universalContinuousSemimeasure_tailOnes (x : BitString) :
    Antitone fun k => universalContinuousSemimeasure (tailOnes x k) := by
  have hsemi := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  exact antitone_nat_of_succ_le fun k => hsemi.antitone_of_prefix (tailOnes_prefix_succ x k)

/-- The mass of the atom at `x01^∞`: the limit, i.e. the infimum, of the a priori
probabilities of the strings `tailOnes x k`.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
noncomputable def atomMass (x : BitString) : ℝ≥0∞ :=
  ⨅ k, universalContinuousSemimeasure (tailOnes x k)

/-- The atom mass is below every value along the branch. -/
theorem atomMass_le_apply (x : BitString) (k : ℕ) :
    atomMass x ≤ universalContinuousSemimeasure (tailOnes x k) :=
  iInf_le _ k

/-- A bound valid all along the branch bounds the atom mass. -/
theorem le_atomMass {c : ℝ≥0∞} {x : BitString}
    (h : ∀ k, c ≤ universalContinuousSemimeasure (tailOnes x k)) :
    c ≤ atomMass x :=
  le_iInf h

/-- The a priori probabilities along the branch converge to the atom mass.

Source: the note `apriori-atoms.md`, section "Вопрос и обозначения"; SUV Chapter 5, §5.2. -/
theorem tendsto_atomMass (x : BitString) :
    Filter.Tendsto (fun k => universalContinuousSemimeasure (tailOnes x k)) Filter.atTop
      (nhds (atomMass x)) :=
  tendsto_atTop_iInf (antitone_universalContinuousSemimeasure_tailOnes x)

/-- Inside its length, the string `tailOnes x k` reads the branch `x01^∞`. -/
theorem getElem?_tailOnes {x : BitString} {k i : ℕ} (hi : i < x.length + 1 + k) :
    (tailOnes x k)[i]? = some (atomSeq x i) := by
  rw [← cantorPrefix_atomSeq x k, List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- Branches of distinct strings separate: once `k` is at least the length difference, the
string `tailOnes x k` is not a prefix of `tailOnes y k`.

Source: the note `apriori-atoms.md`, section "Почему нельзя применить максимальность m";
SUV Chapter 5, §5.2. -/
theorem tailOnes_not_prefix {x y : BitString} {k : ℕ} (hne : x ≠ y)
    (hk : y.length ≤ x.length + k) : ¬ tailOnes x k <+: tailOnes y k := by
  rintro ⟨t, ht⟩
  have hle : x.length ≤ y.length := by
    have h1 : (tailOnes x k).length ≤ (tailOnes y k).length := by
      rw [← ht]; simp
    simp only [length_tailOnes] at h1
    omega
  rcases Nat.lt_or_ge x.length y.length with hlt | hge
  · have hy : (tailOnes y k)[y.length]? = some false := by
      rw [getElem?_tailOnes (by omega), atomSeq_length]
    have hx : (tailOnes x k)[y.length]? = some true := by
      rw [getElem?_tailOnes (by omega), atomSeq_of_gt hlt]
    rw [← ht, List.getElem?_append_left (by simp; omega), hx] at hy
    exact Bool.noConfusion (Option.some.inj hy)
  · have hxy : x.length = y.length := by omega
    have heq : tailOnes x k = tailOnes y k := by
      have hlent : t = [] := by
        have h1 : (tailOnes x k).length + t.length = (tailOnes y k).length := by
          rw [← ht]; simp
        simp only [length_tailOnes] at h1
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [← ht, hlent, List.append_nil]
    rw [tailOnes, tailOnes] at heq
    exact hne (List.append_inj_left heq hxy)

/-- For a fixed `k` the map `x ↦ tailOnes x k` is injective. -/
theorem tailOnes_injective (k : ℕ) : Function.Injective fun x => tailOnes x k := by
  intro x y h
  simp only [] at h
  have hlen : x.length = y.length := by
    have := congrArg List.length h
    simp only [length_tailOnes] at this
    omega
  rw [tailOnes, tailOnes] at h
  exact List.append_inj_left h hlen

/-- The strings `tailOnes x k`, for `x` in a finite family and `k` at least every length in
it, form an antichain. -/
theorem tailOnes_antichain {F : Finset BitString} {k : ℕ}
    (hk : ∀ x ∈ F, x.length ≤ k) :
    ∀ y ∈ (F.image fun x => tailOnes x k : Finset BitString),
      ∀ z ∈ (F.image fun x => tailOnes x k : Finset BitString), y <+: z → y = z := by
  intro y hy z hz hyz
  simp only [Finset.mem_image] at hy hz
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨b, hb, rfl⟩ := hz
  by_cases hab : a = b
  · rw [hab]
  · exact absurd hyz (tailOnes_not_prefix hab (le_trans (hk b hb) (Nat.le_add_left _ _)))

/-- Every finite family of atom masses has total mass at most one: the strings `tailOnes x k`
for `x` in the family and a common large `k` form an antichain.

Source: the note `apriori-atoms.md`, section "Почему нельзя применить максимальность m";
SUV Chapter 5, §5.2. -/
theorem sum_atomMass_le_one (F : Finset BitString) :
    ∑ x ∈ F, atomMass x ≤ 1 := by
  classical
  set k := F.sup List.length with hkdef
  have hk : ∀ x ∈ F, x.length ≤ k := fun x hx => Finset.le_sup (f := List.length) hx
  set G : Finset BitString := F.image fun x => tailOnes x k with hG
  have hstep : ∑ x ∈ F, atomMass x ≤ ∑ x ∈ F, universalContinuousSemimeasure (tailOnes x k) :=
    Finset.sum_le_sum fun x _ => atomMass_le_apply x k
  have himage : ∑ x ∈ F, universalContinuousSemimeasure (tailOnes x k) =
      ∑ y ∈ G, universalContinuousSemimeasure y := by
    rw [hG, Finset.sum_image fun a _ b _ h => tailOnes_injective k h]
  have hsub : ∑ y ∈ G, universalContinuousSemimeasure y =
      ∑' y : (G : Set BitString), universalContinuousSemimeasure (y : BitString) := by
    rw [Finset.tsum_subtype']
  have hanti := tailOnes_antichain hk
  have hone : ∑' y : (G : Set BitString), universalContinuousSemimeasure (y : BitString) ≤ 1 := by
    refine tsum_antichain_universalContinuousSemimeasure_le_one (G : Set BitString) ?_
    intro y hy z hz hyz
    exact hanti y (Finset.mem_coe.mp hy) z (Finset.mem_coe.mp hz) hyz
  calc ∑ x ∈ F, atomMass x ≤ ∑ x ∈ F, universalContinuousSemimeasure (tailOnes x k) := hstep
    _ = ∑ y ∈ G, universalContinuousSemimeasure y := himage
    _ = ∑' y : (G : Set BitString), universalContinuousSemimeasure (y : BitString) := hsub
    _ ≤ 1 := hone

/-- **The atom masses form a discrete semimeasure.**  The branches `x01^∞` are pairwise
distinct, so their atoms are disjoint and their masses sum to at most one.

Source: the note `apriori-atoms.md`, section "Почему нельзя применить максимальность m";
SUV Chapter 5, §5.2. -/
theorem tsum_atomMass_le_one : ∑' x : BitString, atomMass x ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun F => sum_atomMass_le_one F

end Kolmogorov
