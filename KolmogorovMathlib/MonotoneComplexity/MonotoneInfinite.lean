import KolmogorovMathlib.MonotoneComplexity.PartialNatPushforward
import KolmogorovMathlib.MonotoneComplexity.MonotoneAPriori
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import Mathlib.Data.Finset.Basic

/-!
# Monotone complexity of an infinite sequence

`KMStreamOf` extends monotone complexity from finite strings to whole streams, agreeing with
`KMOf` on the finite ones (`KMStreamOf_finite`) and bounding each prefix
(`KMOf_cantorPrefix_le_KMStreamOf`). The point of the extension is
`KMStreamOf_infinite_eq_iSup_prefixes`: the complexity of a sequence is the supremum of the
complexities of its prefixes. The proof rests on the compactness argument
`exists_bounded_program_produces_all_cantorPrefixes` together with
`monotoneProduces_anti_prefix` and
`monotoneProduces_all_cantorPrefixes_iff_infinite_le`. Also here is
`exists_const_KPPlain_natBits_le_KMOf`, comparing plain prefix complexity with monotone
complexity.

Source: SUV Theorem 85(h) and Problem 133.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **SUV Theorem 85(h)**. -/
theorem exists_const_KPPlain_natBits_le_KMOf
    (U : Map) (hU : IsOptimalPrefixConditional U)
    {D : BitStream → BitStream} (hD : IsOptimalMonotoneDecompressor D)
    {f : BitStream → Option ℕ} (hf : IsComputablePartialNatMap f) :
    ∃ c : ℝ, ∀ (x : BitString) (n : ℕ), f (.finite x) = some n →
      ((KPPlain U (Nat.bits n)).toNat : ℝ) ≤ ((KMOf D x).toNat : ℝ) + c := by
  obtain ⟨c₁, hc₁⟩ := exists_const_KPPlain_natBits_le_KA U hU hf
  obtain ⟨c₂, hc₂⟩ := exists_const_KA_le_KMOf hD
  refine ⟨c₁ + c₂, fun x n hfx => ?_⟩
  calc
    ((KPPlain U (Nat.bits n)).toNat : ℝ) ≤ KA x + c₁ := hc₁ x n hfx
    _ ≤ ((KMOf D x).toNat : ℝ) + c₂ + c₁ := by gcongr; exact hc₂ x
    _ = ((KMOf D x).toNat : ℝ) + (c₁ + c₂) := by ring

/-- `KM` on all of `E`, finite and infinite. -/
noncomputable def KMStreamOf (D : BitStream → BitStream) (s : BitStream) : ℕ∞ :=
  sInf { l : ℕ∞ | ∃ p : BitString, s ≤ D (.finite p) ∧ l = p.length }

/-- On a finite stream the stream monotone complexity is the monotone complexity of the underlying
string. -/
@[simp] lemma KMStreamOf_finite (D) (x : BitString) :
    KMStreamOf D (.finite x) = KMOf D x := rfl

/-- A bound on the monotone complexity of `x` is witnessed by an actual program of that length. -/
lemma KMOf_exists_program_le {D : BitStream → BitStream} {x : BitString} {k : ℕ}
    (h : KMOf D x ≤ k) : ∃ p, monotoneProduces D p x ∧ p.length ≤ k := by
  have hlt : KMOf D x < (k + 1 : ℕ∞) :=
    lt_of_le_of_lt h (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self k))
  rcases (KMOf_lt_iff D x (k + 1 : ℕ∞)).mp hlt with ⟨p, hp, hlen⟩
  exact ⟨p, hp, Nat.lt_succ_iff.mp (WithTop.coe_lt_coe.mp hlen)⟩

/-- Every prefix of a sequence approximates the corresponding infinite stream. -/
lemma BitStream.finite_cantorPrefix_le_infinite (w : CantorSeq) (n : ℕ) :
    BitStream.finite (cantorPrefix w n) ≤ .infinite w := by
  change IsCantorPrefix _ _
  rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]

/-- Each prefix of a sequence is at most as hard as the sequence itself. -/
lemma KMOf_cantorPrefix_le_KMStreamOf {D : BitStream → BitStream} {w : CantorSeq} {k : ℕ} :
    KMOf D (cantorPrefix w k) ≤ KMStreamOf D (.infinite w) := by
  refine sInf_le_sInf fun l hl => ?_
  rcases hl with ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  calc .finite (cantorPrefix w k)
    _ ≤ .infinite w := BitStream.finite_cantorPrefix_le_infinite w k
    _ ≤ D (.finite p) := hp

/-- A program producing a long prefix of a sequence also produces every shorter prefix. -/
lemma monotoneProduces_anti_prefix {D : BitStream → BitStream} {w : CantorSeq} {p : BitString}
    {m n : ℕ} (h : m ≤ n) (hp : monotoneProduces D p (cantorPrefix w n)) :
    monotoneProduces D p (cantorPrefix w m) := by
  change .finite (cantorPrefix w m) ≤ D (.finite p)
  calc .finite (cantorPrefix w m)
    _ ≤ .finite (cantorPrefix w n) := BitStream.finite_le_finite_iff.mpr (cantorPrefix_mono w h)
    _ ≤ D (.finite p) := hp

/-- If all prefixes of a sequence have monotone complexity at most `k`, one program of length at
most
`k` produces all of them. -/
lemma exists_bounded_program_produces_all_cantorPrefixes
    {D : BitStream → BitStream} {w : CantorSeq} {k : ℕ}
    (h : ∀ n, KMOf D (cantorPrefix w n) ≤ k) :
    ∃ p, p.length ≤ k ∧ ∀ n, monotoneProduces D p (cantorPrefix w n) := by
  by_contra hc
  push_neg at hc
  choose f hf using hc
  let max_n := (boundedPrograms k).toFinset.sup (fun p => if hp : p.length ≤ k then f p hp else 0)
  have h_max : ∀ p (hp : p.length ≤ k), f p hp ≤ max_n := by
    intro p hp
    have : f p hp ≤ max_n := by
      calc f p hp
        _ = (fun p => if hp' : p.length ≤ k then f p hp' else 0) p := by simp [hp]
        _ ≤ max_n := by
          apply Finset.le_sup (f := fun p => if hp' : p.length ≤ k then f p hp' else 0)
          simp [mem_boundedPrograms_iff, hp]
    exact this
  have hk := KMOf_exists_program_le (h max_n)
  rcases hk with ⟨p, hp, hlen⟩
  have h_fail := hf p hlen
  have h_prod : monotoneProduces D p (cantorPrefix w (f p hlen)) := by
    apply monotoneProduces_anti_prefix (h_max p hlen) hp
  exact h_fail h_prod

/-- A program produces every prefix of a sequence exactly when it makes the decompressor output the
whole sequence. -/
lemma monotoneProduces_all_cantorPrefixes_iff_infinite_le
    {D : BitStream → BitStream} {w : CantorSeq} {p : BitString} :
    (∀ n, monotoneProduces D p (cantorPrefix w n)) ↔ .infinite w ≤ D (.finite p) := by
  constructor
  · intro h
    rw [BitStream.le_iff_forall_finite_le]
    intro x hx
    change IsCantorPrefix x w at hx
    rw [isCantorPrefix_iff_cantorPrefix_eq] at hx
    have h2 := h x.length
    rwa [hx] at h2
  · intro h n
    change .finite (cantorPrefix w n) ≤ D (.finite p)
    calc .finite (cantorPrefix w n)
      _ ≤ .infinite w := by 
        change IsCantorPrefix _ _
        rw [isCantorPrefix_iff_cantorPrefix_eq, cantorPrefix_length]
      _ ≤ D (.finite p) := h

/-- **Problem 133**. -/
theorem KMStreamOf_infinite_eq_iSup_prefixes (D : BitStream → BitStream) (w : CantorSeq) :
    KMStreamOf D (.infinite w) = ⨆ k, KMOf D (cantorPrefix w k) := by
  apply le_antisymm
  · have h : ∀ k : ℕ, (⨆ n, KMOf D (cantorPrefix w n)) ≤ (k : ℕ∞) →
        KMStreamOf D (.infinite w) ≤ (k : ℕ∞) := by
      intro k hk
      have hk' : ∀ n, KMOf D (cantorPrefix w n) ≤ k := fun n =>
        le_trans (le_iSup (fun i => KMOf D (cantorPrefix w i)) n) hk
      have ⟨p, hp_len, hp_prod⟩ := exists_bounded_program_produces_all_cantorPrefixes hk'
      have h_inf := monotoneProduces_all_cantorPrefixes_iff_infinite_le.mp hp_prod
      have h_le_p : KMStreamOf D (.infinite w) ≤ p.length := by
        apply sInf_le
        exact ⟨p, h_inf, rfl⟩
      exact le_trans h_le_p (by exact_mod_cast hp_len)
    cases hB : (⨆ n, KMOf D (cantorPrefix w n)) with
    | top => exact le_top
    | coe k => exact h k (le_of_eq hB)
  · apply iSup_le
    intro k
    exact KMOf_cantorPrefix_le_KMStreamOf

end Kolmogorov
