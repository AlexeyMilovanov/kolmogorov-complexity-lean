import KolmogorovMathlib.Interface.ComputableReals
import KolmogorovMathlib.Interface.Dovetailing
import KolmogorovMathlib.Complexity.PairComplexity
import KolmogorovMathlib.Complexity.ConditionalComplexity
import KolmogorovMathlib.Complexity.KolmogorovLevin
import KolmogorovMathlib.Complexity.RandomConditions
import KolmogorovMathlib.Complexity.SelfComplexity
import KolmogorovMathlib.Complexity.InfiniteSequences
import KolmogorovMathlib.Complexity.IncompressibleStrings
import KolmogorovMathlib.Complexity.Information
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.Prefix.TotalCountingBound
import KolmogorovMathlib.Prefix.KPPairSwap
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.CondTwoStage
import KolmogorovMathlib.Foundation.PrimrecExtras
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.Prefix.StableDecompressors

/-!
# Prefix-stable complexity and the extension map

Comparison of prefix-stable with prefix-free complexity
(`condK_prefixExtensionMap_le_condK_V`, `prefixStable_prefixFree_complexity_eq`), and the
non-computability of a minimal restriction (`minimalRestrict`,
`exists_prefixStable_minimalRestrict_not_computable`, `not_KP_le_length_add_log`).

SUV Theorems 48 and 55, pp. 111 and 121.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

/-- The prefix-stable machine obtained from a prefix machine `V` by extension is at
least as efficient as `V` itself: `condK (prefixExtensionMap code) x y ≤ condK V x y`
whenever `code` is a machine code for `V`. -/
theorem condK_prefixExtensionMap_le_condK_V {V : Map} {code : Code}
    (hc : code.eval = fun n =>
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a => Part.map Encodable.encode (V a)))
    (hV : IsPrefixMachine V) (x y : BitString) :
    condK (prefixExtensionMap code) x y ≤ condK V x y := by
  refine sInf_le_sInf fun n hn => ?_
  obtain ⟨p, hp, rfl⟩ := hn
  have hmem : Encodable.encode x ∈ code.eval (Encodable.encode (p, y)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, y), by simp, Part.mem_map Encodable.encode hp⟩
  obtain ⟨t, ht⟩ : ∃ t, Code.evaln t code (Encodable.encode (p, y))
      = some (Encodable.encode x) := by
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    exact ⟨k, Option.mem_def.mp hk⟩
  have hn_out : prefixExtensionOut code p y (Nat.pair p.length t) = some x := by
    unfold prefixExtensionOut
    simp only [Nat.unpair_pair]
    have hdec : decide (p.length ≤ p.length) = true := decide_eq_true (le_refl _)
    rw [hdec]
    simp only [ite_true, List.take_length, ht, Option.bind_some, Encodable.encodek]
  have hcheck : prefixExtensionCheck code p y (Nat.pair p.length t) = true := by
    unfold prefixExtensionCheck; rw [hn_out]; rfl
  have hrdom : (Nat.rfind (show ℕ →. Bool from fun m =>
      Part.some (prefixExtensionCheck code p y m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair p.length t, by rw [Part.mem_some_iff, hcheck], fun {m} _ => Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  have hcheck' : prefixExtensionCheck code p y n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hcheck'
  have hmem_p : x' ∈ prefixExtensionMap code (p, y) := by
    unfold prefixExtensionMap
    rw [Part.mem_bind_iff]
    exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hx'⟩
  obtain ⟨p', hp'p, hp'prod⟩ := prefixExtensionMap_mem_imp_produces hc hmem_p
  have hp_eq : p' = p := IsPrefixMachine.eq_of_prefix hV hp'prod hp hp'p
  have hprod_p : produces V p y x' := hp_eq ▸ hp'prod
  have hx_eq : x' = x := Part.mem_unique hprod_p hp
  exact ⟨p, hx_eq ▸ hmem_p, rfl⟩

/-- **Theorem 55.** The prefix-stable and the prefix-free versions of prefix
complexity agree up to an additive constant. -/
theorem prefixStable_prefixFree_complexity_eq (U V : Map) (hU : IsOptimalPrefixStable U)
    (hV : IsOptimalPrefixConditional V) :
    ∃ c : ℕ, ∀ x y : BitString, condK U x y ≤ condK V x y + (c : ℕ∞) := by
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hV.isDecompressor
  let M := prefixExtensionMap code
  have hM_dec : isDecompressor M := prefixExtensionMap_partrec code
  have hM_st : IsPrefixStableMachine M :=
    prefixExtensionMap_isPrefixStableMachine hc hV.isPrefixMachine
  have hM_psd : IsPrefixStableDecompressor M := ⟨hM_dec, hM_st⟩
  obtain ⟨c, hc_le⟩ := hU.2 M hM_psd
  use c
  intro x y
  have h_le := condK_prefixExtensionMap_le_condK_V hc hV.isPrefixMachine x y
  have h_add : condK M x y + (c : ℕ∞) ≤ condK V x y + (c : ℕ∞) :=
    add_le_add h_le (le_refl (c : ℕ∞))
  exact (hc_le x y).trans h_add

/-- The restriction of a partial function to its *minimal* arguments: the value
is kept only on strings none of whose proper prefixes is in the domain. -/
noncomputable def minimalRestrict (f : BitString →. BitString) : BitString →. BitString :=
  fun x => Part.assert (∀ r : BitString, r <+: x → r ≠ x → ¬ (f r).Dom) (fun _ => f x)

private def diagSelf : ℕ →. ℕ := fun n =>
  (Denumerable.ofNat Nat.Partrec.Code n).eval n

private theorem diagSelf_partrec : Partrec diagSelf := by
  have h : Partrec (fun (p : Nat.Partrec.Code × ℕ) => p.1.eval p.2) :=
    Nat.Partrec.Code.eval_part
  have h_comp : Computable (fun n : ℕ => (Denumerable.ofNat Nat.Partrec.Code n, n)) :=
    Computable.pair (Computable.ofNat Nat.Partrec.Code) Computable.id
  exact h.comp h_comp

private theorem not_partrec_compl_dom :
    ¬ ∃ h : ℕ →. Unit, Partrec h ∧ ∀ n, (h n).Dom ↔ ¬ (diagSelf n).Dom := by
  rintro ⟨h, hh_part, h_dom⟩
  have h_nat : Partrec (fun n => (h n).map (fun _ => 0)) :=
    hh_part.map (Computable.const 0).to₂
  have h_nat' : Nat.Partrec (fun n => (h n).map (fun _ => 0)) :=
    Partrec.nat_iff.mp h_nat
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp h_nat'
  let e := Encodable.encode c
  have he : Denumerable.ofNat Nat.Partrec.Code e = c :=
    Denumerable.ofNat_encode c
  have h_diag_e : (diagSelf e).Dom ↔ (c.eval e).Dom := by
    dsimp [diagSelf]
    rw [he]
  have h_c_eval : (c.eval e).Dom ↔ (h e).Dom := by
    rw [hc]
    simp [Part.dom_iff_mem]
  have h_e_spec := h_dom e
  rw [h_diag_e, h_c_eval] at h_e_spec
  exact iff_not_self h_e_spec

private def isSingleTrue (l : BitString) : Bool :=
  l.head?.getD false

private def isDoubleTrue (l : BitString) : Bool :=
  l.head?.getD false && l.tail.head?.getD false

private lemma primrec_isSingleTrue : Primrec isSingleTrue :=
  Primrec.option_getD.comp Primrec.list_head? (Primrec.const false)

private lemma primrec_isDoubleTrue : Primrec isDoubleTrue := by
  have h1 : Primrec (fun l : BitString => l.head?.getD false) :=
    primrec_isSingleTrue
  have h2 : Primrec (fun l : BitString => l.tail.head?.getD false) :=
    Primrec.option_getD.comp
      (Primrec.list_head?.comp Primrec.list_tail) (Primrec.const false)
  exact Primrec.of_eq (Primrec.cond h1 h2 (Primrec.const false)) (by
    intro l
    dsimp [isDoubleTrue]
    cases (l.head?.getD false) <;> rfl)

private lemma computable_isSingleTrue : Computable isSingleTrue :=
  primrec_isSingleTrue.to_comp
private lemma computable_isDoubleTrue : Computable isDoubleTrue :=
  primrec_isDoubleTrue.to_comp

private def minimalRestrictWitnessFun (x : BitString) : Part BitString :=
  bif isDoubleTrue (List.dropWhile (!·) x) then
    Part.some [false]
  else bif isSingleTrue (List.dropWhile (!·) x) then
    (diagSelf (List.takeWhile (!·) x).length).map (fun _ => [false])
  else
    Part.none

private lemma primrec_not : Primrec (!· : Bool → Bool) :=
  (Primrec.cond Primrec.id (Primrec.const false) (Primrec.const true)).of_eq
    fun b => by cases b <;> rfl

private lemma dropWhile_eq_drop_takeWhile_length {α : Type*}
    (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.dropWhile, List.takeWhile]
    split
    · rw [ih]
      rfl
    · rfl

private lemma Primrec.list_dropWhile' {α : Type*} [Primcodable α]
    {p : α → Bool} (hp : Primrec p) :
    Primrec (fun l : List α => l.dropWhile p) := by
  have h := Primrec.list_drop.comp (Primrec.list_length.comp (Primrec.list_takeWhile hp)) Primrec.id
  exact h.of_eq (fun l => (dropWhile_eq_drop_takeWhile_length p l).symm)

private lemma computable_tail :
    Computable (fun x : BitString => List.dropWhile (!·) x) :=
  (Primrec.list_dropWhile' primrec_not).to_comp

private lemma computable_takeLen :
    Computable (fun x : BitString => (List.takeWhile (!·) x).length) :=
  (Primrec.list_length.comp (Primrec.list_takeWhile primrec_not)).to_comp

private theorem minimalRestrictWitnessFun_partrec : Partrec minimalRestrictWitnessFun := by
  have h_tail := computable_tail
  have h_n := computable_takeLen
  have h_cond1 : Computable (fun x : BitString =>
      isDoubleTrue (List.dropWhile (!·) x)) :=
    computable_isDoubleTrue.comp h_tail
  have h_cond2 : Computable (fun x : BitString =>
      isSingleTrue (List.dropWhile (!·) x)) :=
    computable_isSingleTrue.comp h_tail
  have h_diag : Partrec (fun x : BitString =>
      (diagSelf (List.takeWhile (!·) x).length).map (fun _ => [false])) :=
    (diagSelf_partrec.comp h_n).map (Computable.const [false]).to₂
  have h_inner : Partrec (fun x : BitString =>
      bif isSingleTrue (List.dropWhile (!·) x) then
        (diagSelf (List.takeWhile (!·) x).length).map (fun _ => [false])
      else Part.none) :=
    Partrec.cond h_cond2 h_diag Partrec.none
  have h_outer : Partrec (fun x : BitString =>
      bif isDoubleTrue (List.dropWhile (!·) x) then
        Part.some [false]
      else bif isSingleTrue (List.dropWhile (!·) x) then
        (diagSelf (List.takeWhile (!·) x).length).map (fun _ => [false])
      else Part.none) :=
    Partrec.cond h_cond1 (Computable.const [false]).partrec h_inner
  exact h_outer

private lemma isSingleTrue_of_prefix {u v : BitString} (hpre : u <+: v)
    (hs : isSingleTrue u = true) : isSingleTrue v = true := by
  dsimp [isSingleTrue] at hs ⊢
  rcases u with _ | ⟨a, u'⟩
  · contradiction
  · obtain ⟨t, rfl⟩ := hpre
    dsimp at hs ⊢
    exact hs

private lemma isDoubleTrue_of_prefix {u v : BitString} (hpre : u <+: v)
    (hd : isDoubleTrue u = true) : isDoubleTrue v = true := by
  dsimp [isDoubleTrue] at hd ⊢
  rcases u with _ | ⟨a, _ | ⟨b, u'⟩⟩
  · contradiction
  · cases a <;> contradiction
  · obtain ⟨t, rfl⟩ := hpre
    dsimp at hd ⊢
    exact hd

private lemma dropWhile_not_prefix_of_prefix {x y : BitString}
    (hpre : x <+: y) :
    List.dropWhile (!·) x <+: List.dropWhile (!·) y := by
  obtain ⟨t, rfl⟩ := hpre
  induction x with
  | nil => simp
  | cons a xs ih =>
    dsimp [List.dropWhile]
    split
    · exact ih
    · simp

private lemma takeWhile_not_length_eq_of_prefix {x y : BitString}
    (hpre : x <+: y) (h_nonempty : List.dropWhile (!·) x ≠ []) :
    (List.takeWhile (!·) x).length = (List.takeWhile (!·) y).length := by
  obtain ⟨t, rfl⟩ := hpre
  induction x with
  | nil =>
    dsimp [List.dropWhile] at h_nonempty
    contradiction
  | cons a xs ih =>
    dsimp [List.dropWhile, List.takeWhile] at h_nonempty ⊢
    revert h_nonempty
    cases ha : !a
    · intro _
      rfl
    · intro h_nonempty
      exact congrArg (· + 1) (ih h_nonempty)

private theorem minimalRestrictWitnessFun_prefix_stable :
    IsPrefixStableFun minimalRestrictWitnessFun := by
  intro x y z hz hpre
  unfold minimalRestrictWitnessFun at hz ⊢
  have h_tail_pre := dropWhile_not_prefix_of_prefix hpre
  cases hd_x : isDoubleTrue (List.dropWhile (!·) x)
  · rw [hd_x] at hz
    simp only [Bool.cond_false] at hz
    cases hs_x : isSingleTrue (List.dropWhile (!·) x)
    · rw [hs_x] at hz
      simp only [Bool.cond_false] at hz
      obtain ⟨h_dom, _⟩ := hz
      exact False.elim h_dom
    · rw [hs_x] at hz
      simp only [Bool.cond_true] at hz
      rw [Part.mem_map_iff] at hz
      obtain ⟨a, h_diag_x, rfl⟩ := hz
      have hs_y := isSingleTrue_of_prefix h_tail_pre hs_x
      have h_nonempty : List.dropWhile (!·) x ≠ [] := by
        intro h_nil
        rw [h_nil] at hs_x
        contradiction
      have h_len_eq := takeWhile_not_length_eq_of_prefix hpre h_nonempty
      rw [h_len_eq] at h_diag_x
      cases hd_y : isDoubleTrue (List.dropWhile (!·) y)
      · simp only [Bool.cond_false]
        rw [hs_y]
        simp only [Bool.cond_true]
        exact Part.mem_map (fun _ => [false]) h_diag_x
      · simp only [Bool.cond_true]
        exact Part.mem_some [false]
  · rw [hd_x] at hz
    simp only [Bool.cond_true] at hz
    have hz_eq : z = [false] := Part.mem_some_iff.mp hz
    rw [hz_eq]
    have hd_y := isDoubleTrue_of_prefix h_tail_pre hd_x
    cases hd_y' : isDoubleTrue (List.dropWhile (!·) y)
    · rw [hd_y] at hd_y'
      contradiction
    · simp only [Bool.cond_true]
      exact Part.mem_some [false]

private lemma take_append_self {α : Type*} (r t : List α) :
    (r ++ t).take r.length = r := by
  rw [List.take_append, List.take_of_length_le (by rfl)]
  simp

private lemma take_s_n (n k : ℕ) :
    (List.replicate n false ++ [true, true]).take k =
      if k ≤ n then List.replicate k false
      else if k = n + 1 then List.replicate n false ++ [true]
      else List.replicate n false ++ [true, true] := by
  split_ifs with h1 h2
  · rw [List.take_append_of_le_length
      (by simp [List.length_replicate, h1]),
      List.take_replicate, min_eq_left h1]
  · subst h2
    rw [List.take_append]
    simp [List.length_replicate, List.take_replicate]
  · have hk : n + 2 ≤ k := by omega
    have hlen : (List.replicate n false ++ [true, true]).length ≤ k := by
      simp [List.length_replicate, hk]
    exact List.take_of_length_le hlen

private lemma dropWhile_replicate_false (k : ℕ) :
    List.dropWhile (!·) (List.replicate k false) = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [List.replicate, List.dropWhile]
    exact ih

private lemma dropWhile_replicate_false_true (n : ℕ) :
    List.dropWhile (!·) (List.replicate n false ++ [true]) = [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [List.replicate, List.dropWhile]
    exact ih

private lemma takeWhile_replicate_false_true (n : ℕ) :
    List.takeWhile (!·) (List.replicate n false ++ [true]) =
      List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [List.replicate, List.takeWhile]
    exact congrArg (false :: ·) ih

private lemma dropWhile_replicate_false_true_true (n : ℕ) :
    List.dropWhile (!·) (List.replicate n false ++ [true, true]) =
      [true, true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [List.replicate, List.dropWhile]
    exact ih

private lemma minimalRestrictWitnessFun_s_n_dom (n : ℕ) :
    (minimalRestrictWitnessFun (List.replicate n false ++ [true, true])).Dom := by
  unfold minimalRestrictWitnessFun
  rw [dropWhile_replicate_false_true_true]
  dsimp [isDoubleTrue]
  trivial

private lemma assert_dom_eq {α : Type*} {p : Prop} {f : p → Part α}
    (h_dom : ∀ h, (f h).Dom) :
    (Part.assert p f).Dom ↔ p := by
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, h_dom h⟩

private lemma minimalRestrict_s_n_dom (n : ℕ) :
    (minimalRestrict minimalRestrictWitnessFun
      (List.replicate n false ++ [true, true])).Dom ↔ ¬ (diagSelf n).Dom := by
  unfold minimalRestrict
  rw [assert_dom_eq (fun _ => minimalRestrictWitnessFun_s_n_dom n)]
  constructor
  · intro h_all h_diag
    have h_pre : List.replicate n false ++ [true] <+:
        List.replicate n false ++ [true, true] := by
      exact ⟨[true], by simp⟩
    have h_ne : List.replicate n false ++ [true] ≠
        List.replicate n false ++ [true, true] := by
      intro h_eq
      have : (List.replicate n false ++ [true]).length =
          (List.replicate n false ++ [true, true]).length :=
        congrArg List.length h_eq
      simp [List.length_replicate] at this
    have h_not_dom := h_all (List.replicate n false ++ [true]) h_pre h_ne
    apply h_not_dom
    unfold minimalRestrictWitnessFun
    rw [dropWhile_replicate_false_true, takeWhile_replicate_false_true]
    dsimp [isDoubleTrue, isSingleTrue]
    simp only [List.length_replicate]
    exact h_diag
  · intro h_not_diag r hr hne
    obtain ⟨t, ht⟩ := hr
    have hr_eq : r = (List.replicate n false ++ [true, true]).take r.length := by
      rw [← ht, take_append_self]
    rw [hr_eq, take_s_n]
    split_ifs with h1 h2
    · unfold minimalRestrictWitnessFun
      rw [dropWhile_replicate_false]
      dsimp [isDoubleTrue, isSingleTrue]
      intro h
      exact False.elim h
    · unfold minimalRestrictWitnessFun
      rw [dropWhile_replicate_false_true, takeWhile_replicate_false_true]
      dsimp [isDoubleTrue, isSingleTrue]
      simp only [List.length_replicate]
      exact h_not_diag
    · exfalso
      have h_r_eq : r = List.replicate n false ++ [true, true] := by
        rw [hr_eq, take_s_n, ite_eq_right h1, ite_eq_right h2]
      exact hne h_r_eq

private lemma computable_s_n :
    Computable (fun n : ℕ => List.replicate n false ++ [true, true]) := by
  have h1 : Primrec (fun n : ℕ => List.replicate n false ++ [true, true]) :=
    Primrec.list_append.comp
      (Primrec.list_replicate.comp Primrec.id (Primrec.const false))
      (Primrec.const [true, true])
  exact h1.to_comp

/-- **Exercise 98.** There is a computable prefix-stable function whose
restriction to minimal descriptions (a prefix-free function) is not
computable. -/
theorem exists_prefixStable_minimalRestrict_not_computable :
    ∃ f : BitString →. BitString,
      Partrec f ∧ IsPrefixStableFun f ∧ ¬ Partrec (minimalRestrict f) := by
  refine ⟨minimalRestrictWitnessFun, minimalRestrictWitnessFun_partrec,
    minimalRestrictWitnessFun_prefix_stable, ?_⟩
  intro h_min
  have h_comp := computable_s_n
  have h_h : Partrec (fun n : ℕ =>
      (minimalRestrict minimalRestrictWitnessFun
        (List.replicate n false ++ [true, true])).map (fun _ => ())) :=
    (h_min.comp h_comp).map (Computable.const ()).to₂
  apply not_partrec_compl_dom
  refine ⟨_, h_h, ?_⟩
  intro n
  change (minimalRestrict minimalRestrictWitnessFun
    (List.replicate n false ++ [true, true])).Dom ↔ ¬ (diagSelf n).Dom
  exact minimalRestrict_s_n_dom n

private lemma two_pow_mul_inv_two_pow (n : ℕ) : (2^n : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ n = 1 := by
  have h20 : (2:ℝ≥0∞) ≠ 0 := by positivity
  have h2t : (2:ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [← mul_pow, ENNReal.mul_inv_cancel h20 h2t, one_pow]

/-- **Exercise 99.** The bound `K(x) ≤ |x| + log |x| + O(1)` is false. -/
theorem not_KP_le_length_add_log (U : Map) (hU : IsOptimalPrefixConditional U) :
    ¬ ∃ c : ℕ, ∀ x : BitString,
      KPPlain U x ≤ ((x.length + Nat.log 2 x.length + c : ℕ) : ℕ∞) := by
  rintro ⟨c, hc⟩
  have h_kraft := KPPlain_kraft_sum_le_one U hU.1
  have h_cw_le : ∀ x : BitString,
      (2:ℝ≥0∞)⁻¹ ^ x.length * (2:ℝ≥0∞)⁻¹ ^ (Nat.log 2 x.length) * (2:ℝ≥0∞)⁻¹ ^ c ≤
        complexityWeight (KPPlain U x) := by
    intro x
    have h_le := hc x
    have h1 := complexityWeight_le_of_le h_le
    rw [complexityWeight_coe, pow_add, pow_add] at h1
    exact h1
  have h_block : ∀ k : ℕ,
      (2:ℝ≥0∞)⁻¹ ^ c ≤
        ∑ n ∈ Finset.Ico (2^k) (2^(k+1)),
          ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) := by
    intro k
    have h_log : ∀ n ∈ Finset.Ico (2^k) (2^(k+1)), Nat.log 2 n = k := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
    have h_sum1 : ∀ n ∈ Finset.Ico (2^k) (2^(k+1)),
        (2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c ≤
          ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn_len : ∀ x ∈ stringsOfLength n, x.length = n := by
        intro x hx
        rw [stringsOfLength, List.mem_toFinset, mem_allStrings] at hx
        exact hx
      have h_elem : ∀ x ∈ stringsOfLength n,
          (2:ℝ≥0∞)⁻¹ ^ n * (2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c ≤
            complexityWeight (KPPlain U x) := by
        intro x hx
        have h_len := hn_len x hx
        have this := h_cw_le x
        rw [h_len, h_log n (Finset.mem_Ico.mpr hn)] at this
        exact this
      have h_const :
          ∑ x ∈ stringsOfLength n, ((2:ℝ≥0∞)⁻¹ ^ n * (2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) ≤
            ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) :=
        Finset.sum_le_sum h_elem
      rw [Finset.sum_const, card_stringsOfLength, nsmul_eq_mul] at h_const
      rw [Nat.cast_pow] at h_const
      change (2:ℝ≥0∞)^n * ((2:ℝ≥0∞)⁻¹ ^ n * (2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) ≤ _ at h_const
      have h_assoc : (2:ℝ≥0∞)^n * ((2:ℝ≥0∞)⁻¹ ^ n * (2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) =
          ((2:ℝ≥0∞)^n * (2:ℝ≥0∞)⁻¹ ^ n) * ((2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) := by ring
      rw [h_assoc, two_pow_mul_inv_two_pow, one_mul] at h_const
      exact h_const
    have h_block_sum := Finset.sum_le_sum h_sum1
    rw [Finset.sum_const, nsmul_eq_mul] at h_block_sum
    have h_card : (Finset.Ico (2^k) (2^(k+1))).card = 2^k := by
      rw [Nat.card_Ico, Nat.pow_succ]
      omega
    rw [h_card] at h_block_sum
    rw [Nat.cast_pow] at h_block_sum
    change (2:ℝ≥0∞)^k * ((2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) ≤ _ at h_block_sum
    have h_assoc2 : (2:ℝ≥0∞)^k * ((2:ℝ≥0∞)⁻¹ ^ k * (2:ℝ≥0∞)⁻¹ ^ c) =
        ((2:ℝ≥0∞)^k * (2:ℝ≥0∞)⁻¹ ^ k) * (2:ℝ≥0∞)⁻¹ ^ c := by ring
    rw [h_assoc2, two_pow_mul_inv_two_pow, one_mul] at h_block_sum
    exact h_block_sum
  have h_range : ∀ M : ℕ,
      (M : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ c ≤
        ∑ k ∈ Finset.range M,
          ∑ n ∈ Finset.Ico (2^k) (2^(k+1)),
            ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) := by
    intro M
    have h_sum_k := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range M) => h_block k)
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum_k
    rw [Finset.card_range] at h_sum_k
    exact h_sum_k
  let T (k : ℕ) : Finset BitString :=
    (Finset.Ico (2^k) (2^(k+1))).biUnion stringsOfLength
  have h_disj_inner : ∀ k : ℕ,
      (Finset.Ico (2^k) (2^(k+1)) : Set ℕ).PairwiseDisjoint stringsOfLength := by
    intro k n1 _ n2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [stringsOfLength, List.mem_toFinset, mem_allStrings] at ha hb
    exact hne (ha.symm.trans hb)
  have h_T_eq : ∀ k : ℕ,
      ∑ x ∈ T k, complexityWeight (KPPlain U x) =
        ∑ n ∈ Finset.Ico (2^k) (2^(k+1)),
          ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) := by
    intro k
    exact Finset.sum_biUnion (h_disj_inner k)
  have h_disj_outer : ∀ M : ℕ,
      (Finset.range M : Set ℕ).PairwiseDisjoint T := by
    intro M k1 _ k2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_biUnion] at ha hb
    rcases ha with ⟨n1, hn1, ha⟩
    rcases hb with ⟨n2, hn2, hb⟩
    rw [Finset.mem_Ico] at hn1 hn2
    rw [stringsOfLength, List.mem_toFinset, mem_allStrings] at ha hb
    have h_n1 : n1 = a.length := ha.symm
    have h_n2 : n2 = a.length := hb.symm
    rw [h_n1] at hn1
    rw [h_n2] at hn2
    have h1 := Nat.log_eq_of_pow_le_of_lt_pow hn1.1 hn1.2
    have h2 := Nat.log_eq_of_pow_le_of_lt_pow hn2.1 hn2.2
    exact hne (h1.symm.trans h2)
  have h_S (M : ℕ) :
      ∑ k ∈ Finset.range M,
        ∑ n ∈ Finset.Ico (2^k) (2^(k+1)),
          ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) ≤ 1 := by
    have h_sum_T :
        ∑ k ∈ Finset.range M, ∑ x ∈ T k, complexityWeight (KPPlain U x) =
          ∑ k ∈ Finset.range M,
            ∑ n ∈ Finset.Ico (2^k) (2^(k+1)),
              ∑ x ∈ stringsOfLength n, complexityWeight (KPPlain U x) := by
      refine Finset.sum_congr rfl (fun k _ => h_T_eq k)
    rw [← h_sum_T]
    have h_biunion :
        ∑ k ∈ Finset.range M, ∑ x ∈ T k, complexityWeight (KPPlain U x) =
          ∑ x ∈ (Finset.range M).biUnion T, complexityWeight (KPPlain U x) := by
      exact (Finset.sum_biUnion (h_disj_outer M)).symm
    rw [h_biunion]
    exact le_trans (ENNReal.sum_le_tsum _) h_kraft
  have h_M_bound : ∀ M : ℕ, (M : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ c ≤ 1 := by
    intro M
    exact le_trans (h_range M) (h_S M)
  have h_spec := h_M_bound (2^c + 1)
  have h_expand : ((2^c + 1 : ℕ) : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ c = 1 + (2:ℝ≥0∞)⁻¹ ^ c := by
    push_cast
    rw [add_mul, one_mul]
    have h_cancel : (2:ℝ≥0∞)^c * (2:ℝ≥0∞)⁻¹ ^ c = 1 := two_pow_mul_inv_two_pow c
    rw [h_cancel]
  rw [h_expand] at h_spec
  have h_le_zero : (2:ℝ≥0∞)⁻¹ ^ c ≤ 0 := by
    have h_add : 1 + (2:ℝ≥0∞)⁻¹ ^ c ≤ 1 + 0 := by
      rwa [add_zero]
    rwa [ENNReal.add_le_add_iff_left ENNReal.one_ne_top] at h_add
  have h_eq_zero : (2:ℝ≥0∞)⁻¹ ^ c = 0 := le_antisymm h_le_zero zero_le
  have h_ne_zero : (2:ℝ≥0∞)⁻¹ ^ c ≠ 0 := by
    apply pow_ne_zero
    exact ENNReal.inv_ne_zero.mpr (by norm_num)
  exact h_ne_zero h_eq_zero

end Kolmogorov
