import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.CommonInformation.ConditionalCounting
import KolmogorovMathlib.Foundation.EnumerationComplexity
import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoise
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Foundation.EffectiveNotions
import KolmogorovMathlib.CommonInformation.ConditionalIndependence
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Encoding.Tuples
import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.Prefix.Machine
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.SlackArith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.Inv
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.CommonInformation.Counting
import KolmogorovMathlib.Complexity.ConditionalComplexity.AverageBounds
import KolmogorovMathlib.Complexity.SelfComplexity.TokenGame.BoardMachinery

namespace Kolmogorov
open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-! ### D10. Every white token is cheap -/

/-! ### D11. The lower bound -/

/-! ### D12. Exercise 45 -/

private lemma gameTop_primrec (c : Code) :
    Primrec (fun q : (ℕ × BitString) × ℕ => gameTop c q.1.1 q.1.2 q.2) := by
  unfold gameTop
  exact gameMax_primrec.comp (gameFree_primrec c)

private lemma gameWCol_eq_rec (c : Code) (n T : ℕ) :
    gameWCol c n T =
      Nat.rec (motive := fun _ => ℕ) 0
        (fun T prev =>
          if gameDead c (gameCol n prev) (gameTop c n (gameCol n prev) T) (T + 1)
            then prev + 1 else prev) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    conv_lhs => rw [gameWCol]
    rw [ih]

private lemma gameWCol_primrec (c : Code) : Primrec₂ (fun n T : ℕ => gameWCol c n T) := by
  have hcol : Primrec (fun z : ℕ × ℕ × ℕ => gameCol z.1 z.2.2) :=
    gameCol_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have htop : Primrec (fun z : ℕ × ℕ × ℕ =>
      gameTop c z.1 (gameCol z.1 z.2.2) z.2.1) :=
    (gameTop_primrec c).comp
      (g := fun z : ℕ × ℕ × ℕ => ((z.1, gameCol z.1 z.2.2), z.2.1))
      (Primrec.pair (Primrec.pair Primrec.fst hcol) (Primrec.fst.comp Primrec.snd))
  have hdead : Primrec (fun z : ℕ × ℕ × ℕ =>
      gameDead c (gameCol z.1 z.2.2)
        (gameTop c z.1 (gameCol z.1 z.2.2) z.2.1) (z.2.1 + 1)) :=
    (gameDead_primrec c).comp
      (g := fun z : ℕ × ℕ × ℕ =>
        ((gameCol z.1 z.2.2, gameTop c z.1 (gameCol z.1 z.2.2) z.2.1), z.2.1 + 1))
      (Primrec.pair (Primrec.pair hcol htop)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  have hpred : PrimrecPred (fun z : ℕ × ℕ × ℕ =>
      gameDead c (gameCol z.1 z.2.2)
        (gameTop c z.1 (gameCol z.1 z.2.2) z.2.1) (z.2.1 + 1) = true) :=
    primrecPred_of_primrec_decide (Primrec.of_eq hdead (fun z => by simp))
  have hstep : Primrec₂ (fun (n : ℕ) (q : ℕ × ℕ) =>
      if gameDead c (gameCol n q.2) (gameTop c n (gameCol n q.2) q.1) (q.1 + 1)
        then q.2 + 1 else q.2) :=
    Primrec.ite hpred (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (f := fun _ : ℕ => (0 : ℕ)) (Primrec.const 0) hstep
  exact Primrec₂.of_eq h (fun n T => (gameWCol_eq_rec c n T).symm)

private lemma gameStr_primrec (c : Code) : Primrec₂ (fun n T : ℕ => gameStr c n T) := by
  unfold gameStr
  exact gameCol_primrec.comp Primrec.fst (gameWCol_primrec c)

private lemma gameRow_primrec (c : Code) : Primrec₂ (fun n T : ℕ => gameRow c n T) := by
  unfold gameRow
  exact (gameTop_primrec c).comp
    (g := fun p : ℕ × ℕ => ((p.1, gameStr c p.1 p.2), p.2))
    (Primrec.pair (Primrec.pair Primrec.fst (gameStr_primrec c)) Primrec.snd)

private lemma gameTokens_primrec (c : Code) : Primrec₂ (fun i T : ℕ => gameTokens c i T) := by
  unfold gameTokens
  have hrow : Primrec (fun z : (ℕ × ℕ) × ℕ => gameRow c z.2 z.1.2) :=
    (gameRow_primrec c).comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have hstr : Primrec (fun z : (ℕ × ℕ) × ℕ => gameStr c z.2 z.1.2) :=
    (gameStr_primrec c).comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  refine dedup_primrec.comp (Primrec.listFilterMap
    (Primrec.list_range.comp (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))) ?_)
  exact Primrec.ite (Primrec.eq.comp hrow (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp hstr) (Primrec.const none)

private lemma gameRowEnum_eq_rec (c : Code) (i T : ℕ) :
    gameRowEnum c i T =
      Nat.rec (motive := fun _ => List BitString) []
        (fun T prev => prev ++
          (gameTokens c i T).filter (fun x => !(decide (x ∈ prev)))) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    conv_lhs => rw [gameRowEnum]
    rw [ih]

private lemma gameRowEnum_primrec (c : Code) : Primrec₂ (fun i T : ℕ => gameRowEnum c i T) := by
  have hnotmem : Primrec (fun z : (ℕ × ℕ × List BitString) × BitString =>
      !(decide (z.2 ∈ z.1.2.2))) :=
    Primrec.not.comp (bitString_mem_primrec.comp Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have htok : Primrec (fun a : ℕ × ℕ × List BitString => gameTokens c a.1 a.2.1) :=
    (gameTokens_primrec c).comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hstep : Primrec₂ (fun (i : ℕ) (q : ℕ × List BitString) =>
      q.2 ++ (gameTokens c i q.1).filter (fun x => !(decide (x ∈ q.2)))) :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (list_filter_primrec htok hnotmem)
  have h := Primrec.nat_rec (f := fun _ : ℕ => ([] : List BitString)) (Primrec.const []) hstep
  exact Primrec₂.of_eq h (fun i T => (gameRowEnum_eq_rec c i T).symm)

private lemma gameDecoder_isDecompressor (c : Code) : isDecompressor (gameDecoder c) := by
  have hlist : Primrec (fun q : (BitString × BitString) × ℕ =>
      gameRowEnum c (q.1.1.length - 2) q.2) :=
    (gameRowEnum_primrec c).comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const 2))
      Primrec.snd
  have hidx : Primrec (fun q : (BitString × BitString) × ℕ =>
      decodeFixedWidthNatCode q.1.1) :=
    (bitsToNat_primrec.comp Primrec.list_reverse).comp (Primrec.fst.comp Primrec.fst)
  have hcheck : Computable₂ (fun (pr : BitString × BitString) (T : ℕ) =>
      decide (decodeFixedWidthNatCode pr.1 <
        (gameRowEnum c (pr.1.length - 2) T).length)) :=
    (primrec_decide_of_primrecPred
      (Primrec.nat_lt.comp hidx (Primrec.list_length.comp hlist))).to_comp
  have hval : Computable₂ (fun (pr : BitString × BitString) (T : ℕ) =>
      (gameRowEnum c (pr.1.length - 2) T).getD (decodeFixedWidthNatCode pr.1) []) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp hlist hidx)
      (Primrec.const [])).to_comp
  exact Partrec.map (Partrec.rfind hcheck.partrec₂) hval



/-- Subtracting a bounded constant from the complexity value costs `O(1)`
conditional bits. -/
private theorem game_shift (U : Map) (hU : isOptimalConditional U) (K : ℕ) :
    ∃ c : ℕ, ∀ (x : BitString) (R d : ℕ), d ≤ K → cVal U x = R + d →
      condK U (Nat.bits R) x ≤ condK U (Nat.bits (cVal U x)) x + (c : ℕ∞) := by
  classical
  have hg : Partrec (fun q : BitString × BitString =>
      (U (decodeSecond q.2, q.1)).map
        (fun w => Nat.bits (bitsToNat w - bitsToNat (decodeFirst q.2)))) := by
    have hf : Partrec (fun q : BitString × BitString => U (decodeSecond q.2, q.1)) :=
      hU.1.comp (Computable.pair
        (decodeSecond_primrec.to_comp.comp Computable.snd) Computable.fst)
    have hcp : Primrec (fun r : (BitString × BitString) × BitString =>
        Nat.bits (bitsToNat r.2 - bitsToNat (decodeFirst r.1.2))) :=
      primrec_natBits.comp (Primrec.nat_sub.comp (bitsToNat_primrec.comp Primrec.snd)
        (bitsToNat_primrec.comp (decodeFirst_primrec.comp (Primrec.snd.comp Primrec.fst))))
    exact hf.map hcp.to_comp
  obtain ⟨C, hC⟩ := condK_partrec_cond_map_le U hU
    (fun y p => (U (decodeSecond p, y)).map
      (fun w => Nat.bits (bitsToNat w - bitsToNat (decodeFirst p)))) hg
  refine ⟨2 * (Nat.log 2 K + 1) + 1 + C, ?_⟩
  intro x R d hdK hval
  have hcc : condK U (Nat.bits (cVal U x)) x
      = ((condCVal U (Nat.bits (cVal U x)) x : ℕ) : ℕ∞) := condK_eq_condCVal hU _ _
  obtain ⟨p₀, hp₀len, hp₀prod⟩ :=
    (condK_le_iff U (Nat.bits (cVal U x)) x (condCVal U (Nat.bits (cVal U x)) x)).mp
      (le_of_eq hcc)
  have hmem : Nat.bits R ∈ (U (decodeSecond (pairCode (Nat.bits d) p₀), x)).map
      (fun w => Nat.bits (bitsToNat w - bitsToNat (decodeFirst (pairCode (Nat.bits d) p₀)))) := by
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    have hstep := Part.mem_map
      (fun w : BitString => Nat.bits (bitsToNat w - bitsToNat (Nat.bits d))) hp₀prod
    simp only [bitsToNat_bits, hval, Nat.add_sub_cancel] at hstep ⊢
    exact hstep
  have hle1 := hC x (pairCode (Nat.bits d) p₀) (Nat.bits R) hmem
  have hdlen : (Nat.bits d).length ≤ Nat.log 2 K + 1 := by
    have h1 := length_natBits_le_log d
    have h2 : Nat.log 2 d ≤ Nat.log 2 K := Nat.log_mono_right hdK
    omega
  have hlen : (pairCode (Nat.bits d) p₀).length
      ≤ 2 * (Nat.log 2 K + 1) + 1 + condCVal U (Nat.bits (cVal U x)) x := by
    rw [length_pairCode]
    have : p₀.length ≤ condCVal U (Nat.bits (cVal U x)) x := hp₀len
    omega
  have harith : (pairCode (Nat.bits d) p₀).length + C
      ≤ condCVal U (Nat.bits (cVal U x)) x + (2 * (Nat.log 2 K + 1) + 1 + C) := by omega
  calc condK U (Nat.bits R) x
      ≤ ((pairCode (Nat.bits d) p₀).length : ℕ∞) + (C : ℕ∞) := hle1
    _ = (((pairCode (Nat.bits d) p₀).length + C : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((condCVal U (Nat.bits (cVal U x)) x + (2 * (Nat.log 2 K + 1) + 1 + C) : ℕ) : ℕ∞) := by
        exact_mod_cast harith
    _ = condK U (Nat.bits (cVal U x)) x + ((2 * (Nat.log 2 K + 1) + 1 + C : ℕ) : ℕ∞) := by
        rw [hcc]; push_cast; ring



private lemma gameRowEnum_prefix_succ (c : Code) (i T : ℕ) :
    gameRowEnum c i T <+: gameRowEnum c i (T + 1) := by
  rw [gameRowEnum]
  exact List.prefix_append _ _

private lemma gameRowEnum_prefix_of_le (c : Code) (i : ℕ) {T T' : ℕ} (h : T ≤ T') :
    gameRowEnum c i T <+: gameRowEnum c i T' := by
  induction T' with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge T (k + 1) with hk | hk
    · exact (ih (Nat.lt_succ_iff.mp hk)).trans (gameRowEnum_prefix_succ c i k)
    · rw [le_antisymm h hk]

private lemma gameTokens_mem_rowEnum (c : Code) (i T : ℕ) {x : BitString}
    (h : x ∈ gameTokens c i T) : x ∈ gameRowEnum c i (T + 1) := by
  rw [gameRowEnum, List.mem_append]
  by_cases hx : x ∈ gameRowEnum c i T
  · exact Or.inl hx
  · refine Or.inr ?_
    rw [List.mem_filter]
    exact ⟨h, by simp [hx]⟩

private lemma gameDecoder_produces (c : Code) (i k T : ℕ) (hk : k < 2 ^ (i + 2))
    (hlt : k < (gameRowEnum c i T).length) :
    produces (gameDecoder c) (fixedWidthNatCode k (i + 2)) []
      ((gameRowEnum c i T).getD k []) := by
  have hlen : (fixedWidthNatCode k (i + 2)).length = i + 2 := fixedWidthNatCode_length hk
  have hdec : decodeFixedWidthNatCode (fixedWidthNatCode k (i + 2)) = k :=
    decodeFixedWidthNatCode_encode k (i + 2)
  change _ ∈ gameDecoder c _
  unfold gameDecoder
  simp only [hlen, hdec, Nat.add_sub_cancel]
  have hdom : (Nat.rfind
      (show ℕ →. Bool from fun T => Part.some (decide (k < (gameRowEnum c i T).length)))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨T, Part.mem_some_iff.mpr (decide_eq_true hlt).symm, fun _ => Part.some_dom _⟩
  obtain ⟨T1, hT1⟩ := Part.dom_iff_mem.mp hdom
  have hT1eq : Nat.rfind (show ℕ →. Bool from fun T => Part.some
      (decide (k < (gameRowEnum c i T).length))) = Part.some T1 := Part.eq_some_iff.mpr hT1
  rw [hT1eq, Part.map_some, Part.mem_some_iff]
  have hT1lt : k < (gameRowEnum c i T1).length := by
    have h := Nat.rfind_spec hT1
    simpa using h
  rcases le_total T1 T with hle | hle
  · exact getD_eq_of_prefix_of_lt_length (gameRowEnum_prefix_of_le c i hle) k [] hT1lt
  · exact (getD_eq_of_prefix_of_lt_length (gameRowEnum_prefix_of_le c i hle) k [] hlt).symm

private theorem game_plainK_token {U : Map} (hU : isOptimalConditional U) {c : Code}
    (hc : IsCodeFor c U) :
    ∃ C : ℕ, ∀ (i T : ℕ) (x : BitString), x ∈ gameTokens c i T →
      plainK U x ≤ ((i + 2 + C : ℕ) : ℕ∞) := by
  obtain ⟨C, hC⟩ := hU.2 (gameDecoder c) (gameDecoder_isDecompressor c)
  refine ⟨C, fun i T x hx => ?_⟩
  have hmem : x ∈ gameRowEnum c i (T + 1) := gameTokens_mem_rowEnum c i T hx
  have hklt : List.idxOf x (gameRowEnum c i (T + 1)) < (gameRowEnum c i (T + 1)).length :=
    List.idxOf_lt_length_of_mem hmem
  have hkb : List.idxOf x (gameRowEnum c i (T + 1)) < 2 ^ (i + 2) :=
    lt_of_lt_of_le hklt (gameRowEnum_length hc i (T + 1))
  have hgetD : (gameRowEnum c i (T + 1)).getD
      (List.idxOf x (gameRowEnum c i (T + 1))) [] = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf hmem]
    rfl
  have hprod := gameDecoder_produces c i _ (T + 1) hkb hklt
  rw [hgetD] at hprod
  have hdec : condK (gameDecoder c) x [] ≤ ((i + 2 : ℕ) : ℕ∞) := by
    have h := condK_le_of_produces hprod
    rwa [fixedWidthNatCode_length hkb] at h
  calc plainK U x ≤ condK (gameDecoder c) x [] + (C : ℕ∞) := hC x []
    _ ≤ ((i + 2 : ℕ) : ℕ∞) + (C : ℕ∞) := by gcongr
    _ = ((i + 2 + C : ℕ) : ℕ∞) := by push_cast; ring

private theorem log_length_le_condK_cVal {U : Map} (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, 2 ≤ Nat.log 2 n → ∃ x : BitString, x.length = n ∧
      ((Nat.log 2 n : ℕ) : ℕ∞) ≤ condK U (Nat.bits (cVal U x)) x + (c : ℕ∞) := by
  obtain ⟨c, hc⟩ := Dovetailing.exists_isCodeFor hU
  obtain ⟨C, hC⟩ := game_plainK_token hU hc
  obtain ⟨cs, hcs⟩ := game_shift U hU (2 + C)
  refine ⟨cs + 2, fun n hL => ?_⟩
  have hL' : 2 ≤ gameLog n := by rw [gameLog_eq]; exact hL
  obtain ⟨x, R, T0, hxlen, hn2R, hRpk, hnb, hstab⟩ := exists_game_winner hc n hL'
  refine ⟨x, hxlen, ?_⟩
  have htok : x ∈ gameTokens c R T0 := by
    obtain ⟨hs, hr⟩ := hstab T0 le_rfl
    exact (mem_gameTokens c R T0 x).mpr ⟨n, by omega, hr, hs⟩
  have hup : plainK U x ≤ ((R + 2 + C : ℕ) : ℕ∞) := hC R T0 x htok
  have hcv : plainK U x = ((cVal U x : ℕ) : ℕ∞) := condK_eq_condCVal hU x []
  have hR_le : R ≤ cVal U x := by rw [hcv] at hRpk; exact_mod_cast hRpk
  have hcv_le : cVal U x ≤ R + 2 + C := by rw [hcv] at hup; exact_mod_cast hup
  have hshift := hcs x R (cVal U x - R) (by omega) (by omega)
  have hcc : condK U (Nat.bits (cVal U x)) x
      = ((condCVal U (Nat.bits (cVal U x)) x : ℕ) : ℕ∞) := condK_eq_condCVal hU _ _
  have hlt : ((gameLog n - 2 : ℕ) : ℕ∞) < condK U (Nat.bits R) x := not_le.mp hnb
  rw [hcc] at hshift
  have hlt2 : ((gameLog n - 2 : ℕ) : ℕ∞)
      < ((condCVal U (Nat.bits (cVal U x)) x + cs : ℕ) : ℕ∞) := by
    refine lt_of_lt_of_le hlt (le_trans hshift ?_)
    push_cast
    exact le_rfl
  have hltn : gameLog n - 2 < condCVal U (Nat.bits (cVal U x)) x + cs := by
    exact_mod_cast hlt2
  have hgoal : Nat.log 2 n ≤ condCVal U (Nat.bits (cVal U x)) x + (cs + 2) := by
    rw [← gameLog_eq]
    omega
  rw [hcc]
  calc ((Nat.log 2 n : ℕ) : ℕ∞)
      ≤ ((condCVal U (Nat.bits (cVal U x)) x + (cs + 2) : ℕ) : ℕ∞) := by exact_mod_cast hgoal
    _ = ((condCVal U (Nat.bits (cVal U x)) x : ℕ) : ℕ∞) + ((cs + 2 : ℕ) : ℕ∞) := by
        push_cast; ring

/-- For every length `n` there is a string `x` of that length for which the complexity of its
own complexity is `log n` up to an additive constant:
`log n ≤ C(C(x) | x) + O(1)` and `C(C(x) | x) ≤ log n + O(1)`.  SUV Exercise 45. -/
theorem exists_condK_cVal_within_log_length (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x : BitString, x.length = n ∧
      ((Nat.log 2 n : ℕ) : ℕ∞) ≤ condK U (Nat.bits (cVal U x)) x + (c : ℕ∞) ∧
      condK U (Nat.bits (cVal U x)) x ≤ ((Nat.log 2 n : ℕ) : ℕ∞) + (c : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := log_length_le_condK_cVal hU
  obtain ⟨c2, hc2⟩ := condK_cVal_le_log_length U hU
  refine ⟨max (max c1 c2) 1, fun n => ?_⟩
  have hupper : ∀ x : BitString, x.length = n →
      condK U (Nat.bits (cVal U x)) x
        ≤ ((Nat.log 2 n : ℕ) : ℕ∞) + ((max (max c1 c2) 1 : ℕ) : ℕ∞) := by
    intro x hx
    have h := hc2 x
    rw [hx] at h
    refine le_trans h ?_
    have : Nat.log 2 n + c2 ≤ Nat.log 2 n + max (max c1 c2) 1 := by
      have : c2 ≤ max (max c1 c2) 1 := le_max_of_le_left (le_max_right _ _)
      omega
    calc ((Nat.log 2 n + c2 : ℕ) : ℕ∞)
        ≤ ((Nat.log 2 n + max (max c1 c2) 1 : ℕ) : ℕ∞) := by exact_mod_cast this
      _ = ((Nat.log 2 n : ℕ) : ℕ∞) + ((max (max c1 c2) 1 : ℕ) : ℕ∞) := by push_cast; ring
  by_cases hL : 2 ≤ Nat.log 2 n
  · obtain ⟨x, hxlen, hlow⟩ := hc1 n hL
    refine ⟨x, hxlen, ?_, hupper x hxlen⟩
    refine le_trans hlow ?_
    gcongr
    exact_mod_cast le_max_of_le_left (le_max_left _ _)
  · refine ⟨List.replicate n false, by simp, ?_, hupper _ (by simp)⟩
    have hlog : Nat.log 2 n ≤ max (max c1 c2) 1 := by
      have h1 : (1 : ℕ) ≤ max (max c1 c2) 1 := le_max_right _ _
      omega
    calc ((Nat.log 2 n : ℕ) : ℕ∞) ≤ ((max (max c1 c2) 1 : ℕ) : ℕ∞) := by exact_mod_cast hlog
      _ ≤ condK U (Nat.bits (cVal U (List.replicate n false))) (List.replicate n false)
            + ((max (max c1 c2) 1 : ℕ) : ℕ∞) := le_add_self

end Kolmogorov


