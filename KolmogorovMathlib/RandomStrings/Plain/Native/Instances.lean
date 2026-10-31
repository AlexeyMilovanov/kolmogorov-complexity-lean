/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.MonotoneComplexity.PlainPrefixDips
import KolmogorovMathlib.RandomStrings.Plain.HaltingLanguage
import Mathlib.Computability.Halting

/-!
# Binary threshold instances for the native referees

This module supplies the literal halting instances used by the native referee family.

* `native_halting_representation` records that the binary halting language `HBin` is
  recursively enumerable, undecidable, and receives the diagonal halting set under the
  computable map `n ↦ haltWord n n` (blueprint node `native:representation`).
* `nativeStringIndex` is the injection `χ` of bit strings into the naturals (a one is
  prefixed before the string is read as a binary number), with a checked partial inverse
  `nativeStringDecode`; `nativeThresholdData`, `nativeThresholdInstance` and
  `literal_threshold_instance_length` build the instance `g(m, k)` for a fixed search index
  and bound its length linearly in `m + 1` (blueprint node `native:literal`).
* `exists_threshold_search_index` shows that for a partial computable decompressor `U : Map`
  one search index `e₀` recognizes, through `HBin`, all thresholds
  `k ≤ |{x | C_U x ≤ m}|` (blueprint node `native:search-index`).

All constructors and parsers are executable. No search index is chosen while constructing
these functions or the later referee family: the index of `exists_threshold_search_index`
is obtained only after the decompressor `U` is fixed, so the referee family, which ranges
over all indices in advance, involves no circularity.
-/

namespace Kolmogorov.Milovanov

/-- Canonical halting instances have exactly the fixed numerical evaluator's domain.
Blueprint node `native:representation` (supporting lemma). -/
theorem haltWord_mem_HBin (e y : ℕ) :
    haltWord e y ∈ HBin ↔ ((Denumerable.ofNat Nat.Partrec.Code e).eval y).Dom := by
  constructor
  · rintro ⟨e', y', hword, hdom⟩
    have h := haltWord_injective (a₁ := (e', y')) (a₂ := (e, y)) hword
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hdom
  · intro h
    exact ⟨e, y, rfl, h⟩

/-- A canonically decoded natural number is the one whose binary word was decoded. -/
private lemma eq_bits_of_decodeNat_eq_some {w : BitString} {n : ℕ} (h : decodeNat w = some n) :
    w = bits n := by
  by_cases hc : bits (decodeBits w.reverse) = w
  · simp only [decodeNat, hc, ↓reduceIte, Option.some_inj] at h
    rw [← h, hc]
  · simp [decodeNat, hc] at h

/-- Every word that parses as a halting instance is the halting word of its parse. -/
private lemma haltWord_eq_of_decodeHaltWord_eq_some {w : BitString} {e y : ℕ}
    (h : decodeHaltWord w = some (e, y)) : haltWord e y = w := by
  obtain ⟨⟨data, e'⟩, hq, hd⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y', hy', hp⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hp)
  rw [eq_bits_of_decodeNat_eq_some hy'] at hq
  exact (decodeQuery_eq_some_iff w _).mp hq

/-- A word lies in `HBin` iff it parses as a halting instance whose code halts on its data. -/
private lemma mem_HBin_iff_decode (w : BitString) :
    w ∈ HBin ↔ ∃ p, decodeHaltWord w = some p ∧
      ((Denumerable.ofNat Nat.Partrec.Code p.1).eval p.2).Dom := by
  constructor
  · rintro ⟨e, y, rfl, hdom⟩
    exact ⟨(e, y), decodeHaltWord_haltWord e y, hdom⟩
  · rintro ⟨⟨e, y⟩, hw, hdom⟩
    exact ⟨e, y, haltWord_eq_of_decodeHaltWord_eq_some hw, hdom⟩

/-- `HBin` is semidecided by decoding a word and running the universal evaluator. -/
private lemma rePred_mem_HBin : REPred (fun z ↦ z ∈ HBin) := by
  let f (w : BitString) : Part Unit :=
    (Part.ofOption (decodeHaltWord w)).bind fun p ↦
      ((Denumerable.ofNat Nat.Partrec.Code p.1).eval p.2).map fun _ ↦ ()
  have hdecode : Partrec fun w : BitString ↦ Part.ofOption (decodeHaltWord w) :=
    Computable.ofOption haltWord_computable.2
  have heval : Partrec fun p : ℕ × ℕ ↦ (Denumerable.ofNat Nat.Partrec.Code p.1).eval p.2 :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst) Computable.snd
  have hf : Partrec f :=
    hdecode.bind ((heval.map (Computable.const ()).to₂).comp Computable.snd)
  refine REPred.of_eq hf.dom_re fun w ↦ ?_
  rw [mem_HBin_iff_decode]
  cases h : decodeHaltWord w <;> simp [f, h]

/-- The test "the code `c` has halted on input zero within `t` steps". -/
private def haltsWithin (c : Nat.Partrec.Code) (t : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln t c 0).isSome

private lemma computable₂_haltsWithin : Computable₂ haltsWithin := by
  have h : Computable fun p : Nat.Partrec.Code × ℕ ↦ Nat.Partrec.Code.evaln p.2 p.1 0 :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((Computable.snd.pair Computable.fst).pair (Computable.const 0))
  exact Primrec.option_isSome.to_comp.comp h

private lemma exists_haltsWithin_iff (c : Nat.Partrec.Code) :
    (∃ t, haltsWithin c t = true) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ht
    exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    exact ⟨t, Option.isSome_iff_exists.mpr ⟨x, ht⟩⟩

/-- A predicate computable on the target is computable after a computable change of variable. -/
private lemma computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {P : β → Prop}
    {f : α → β} (hP : ComputablePred P) (hf : Computable f) : ComputablePred (fun a ↦ P (f a)) :=
  let ⟨_, hdec⟩ := hP
  ⟨_, hdec.comp hf⟩

/-- `HBin` is undecidable: it would decide the halting problem on input zero. -/
private lemma not_computablePred_mem_HBin : ¬ComputablePred (fun z ↦ z ∈ HBin) := by
  intro hHBin
  have hdiag : Computable fun n : ℕ ↦ haltWord n n :=
    haltWord_computable.1.comp Computable.id Computable.id
  have hhalting : ComputablePred Kolmogorov.haltingSet :=
    (computablePred_comp hHBin hdiag).of_eq fun n ↦ by
      rw [haltWord_mem_HBin]
      rfl
  obtain ⟨idx, hidx, hspec⟩ := Kolmogorov.exists_haltingIndex computable₂_haltsWithin
  refine ComputablePred.halting_problem 0 ((computablePred_comp hhalting hidx).of_eq fun c ↦ ?_)
  rw [hspec c, exists_haltsWithin_iff]

/-- The fixed language is enumerable, undecidable, and receives the diagonal halting set.
Blueprint node `native:representation`. The reduction is ordinary computability only. -/
theorem native_halting_representation :
    (∀ e y, haltWord e y ∈ HBin ↔
      ((Denumerable.ofNat Nat.Partrec.Code e).eval y).Dom) ∧
    REPred (fun z => z ∈ HBin) ∧ ¬ComputablePred (fun z => z ∈ HBin) ∧
    Computable (fun n => haltWord n n) ∧
    ∀ n, Kolmogorov.haltingSet n ↔ haltWord n n ∈ HBin :=
  ⟨haltWord_mem_HBin, rePred_mem_HBin, not_computablePred_mem_HBin,
    haltWord_computable.1.comp Computable.id Computable.id,
    fun n ↦ (haltWord_mem_HBin n n).symm⟩

/-- The injection `χ`: interpret `true :: s` as a most-significant-bit-first integer.
Blueprint node `native:literal` (supporting definition). -/
def nativeStringIndex (s : BitString) : ℕ := decodeBits (true :: s).reverse

/-- The inverse of `χ` on its range, rejecting the canonical zero word.
Blueprint node `native:literal` (supporting definition). -/
def nativeStringDecode (n : ℕ) : Option BitString :=
  match bits n with
  | true :: s => some s
  | _ => none

/-- The partial-function interpretation of the checked inverse of `χ`.
Blueprint node `native:literal` (supporting definition). -/
def nativeStringInverse (n : ℕ) : Part BitString := Part.ofOption (nativeStringDecode n)

/-- The binary representation and inverse recover exactly the supplied string.
Blueprint node `native:literal` (supporting lemma). -/
theorem native_string_index_spec (s : BitString) :
    bits (nativeStringIndex s) = true :: s ∧
      nativeStringDecode (nativeStringIndex s) = some s := by
  have hrev : (true :: s).reverse = s.reverse ++ [true] := by simp
  have h1 : bits (nativeStringIndex s) = true :: s := by
    have hz : decodeBits (true :: s).reverse ≠ 0 := by
      rw [hrev]
      exact decodeBits_append_true_ne_zero s.reverse
    simp only [nativeStringIndex, bits, hz, ↓reduceIte]
    rw [hrev, natBits_decodeBits_append_true]
    simp
  exact ⟨h1, by simp [nativeStringDecode, h1]⟩

/-- Prefixing one makes the integer representation injective, including the empty string.
Blueprint node `native:literal` (supporting lemma). -/
theorem native_string_index_injective : Function.Injective nativeStringIndex := by
  intro s t h
  have hs := (native_string_index_spec s).1
  have ht := (native_string_index_spec t).1
  rw [h, ht] at hs
  exact (List.cons.inj hs).2.symm

/-- Stripping a leading `true` from a list is primitive recursive. -/
private lemma primrec_tail_of_cons_true :
    Primrec fun l : List Bool ↦ match l with | true :: s => some s | _ => none := by
  have h : Primrec fun l : List Bool ↦ (List.casesOn (id l) none
      fun (b : Bool) (s : List Bool) ↦ cond b (some s) none : Option (List Bool)) := by
    refine Primrec.list_casesOn (f := id) (g := fun _ ↦ none)
      (h := fun _ p ↦ cond p.1 (some p.2) none) Primrec.id (Primrec.const none) ?_
    exact Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  exact h.of_eq fun l ↦ by rcases l with _ | ⟨_ | _, _⟩ <;> rfl

/-- The injection and both interpretations of its inverse are effective.
Blueprint node `native:literal` (supporting lemma). -/
theorem native_string_index_computable :
    Computable nativeStringIndex ∧ Computable nativeStringDecode ∧
      Partrec nativeStringInverse := by
  have h_index : Computable nativeStringIndex :=
    decodeBits_computable.comp (Computable.list_reverse.comp
      (Computable₂.comp Computable.list_cons (Computable.const true) Computable.id))
  have h_decode : Computable nativeStringDecode :=
    primrec_tail_of_cons_true.to_comp.comp bits_computable.1
  exact ⟨h_index, h_decode, Computable.ofOption h_decode⟩

/-- Literal data `data(m,k) = χ(sd(bits m) ++ bits k)` for the one search program.
Blueprint node `native:literal` (supporting definition). -/
def nativeThresholdData (m k : ℕ) : ℕ :=
  nativeStringIndex (sd (bits m) ++ bits k)

/-- Recover both threshold parameters, rejecting noncanonical component encodings.
Blueprint node `native:search-index` (supporting definition). -/
def decodeNativeThresholdData (n : ℕ) : Option (ℕ × ℕ) := do
  let s ← nativeStringDecode n
  let (first, second) ← parseSd s
  let m ← decodeNat first
  let k ← decodeNat second
  some (m, k)

private theorem parseSd_sd_append (s y : BitString) : parseSd (sd s ++ y) = some (s, y) := by
  have h1 : sd s ++ y = pairCode s y := by
    rw [sd_eq]
    dsimp [pairCode, natCode]
    simp
  rw [h1, parseSd_pairCode]

/-- The threshold data parser is effective and is a left inverse of the literal constructor.
Blueprint node `native:search-index` (supporting lemma). -/
theorem native_threshold_data_spec :
    Computable₂ nativeThresholdData ∧ Computable decodeNativeThresholdData ∧
      ∀ m k, decodeNativeThresholdData (nativeThresholdData m k) = some (m, k) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Computable nativeStringIndex := native_string_index_computable.1
    have h2 : Computable sd := literalCode_computable.1
    have h3 : Computable bits := bits_computable.1
    have h4 : Computable₂ (· ++ · : List Bool → List Bool → List Bool) :=
      Primrec.list_append.to_comp
    exact h1.comp (h4.comp (h2.comp (h3.comp Computable.fst)) (h3.comp Computable.snd))
  · have hd : decodeNativeThresholdData = fun n ↦
        Option.bind (nativeStringDecode n) fun s ↦
          Option.bind (parseSd s) fun p ↦
            Option.bind (decodeNat p.1) fun m ↦
              Option.bind (decodeNat p.2) fun k ↦ some (m, k) := rfl
    rw [hd]
    have H4 : Computable₂ fun (p : BitString × BitString) (m : ℕ) ↦
        Option.bind (decodeNat p.2) fun k ↦ some (m, k) := by
      refine Computable.option_bind ?_ ?_
      · exact bits_computable.2.comp (Computable.snd.comp Computable.fst)
      · exact Computable.option_some.comp
          (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
    have H3 : Computable₂ fun (_ : BitString) (p : BitString × BitString) ↦
        Option.bind (decodeNat p.1) fun m ↦
          Option.bind (decodeNat p.2) fun k ↦ some (m, k) := by
      refine Computable.option_bind ?_ ?_
      · exact bits_computable.2.comp (Computable.fst.comp Computable.snd)
      · exact H4.comp (Computable.snd.comp Computable.fst) Computable.snd
    have H2 : Computable₂ fun (_ : ℕ) (s : BitString) ↦
        Option.bind (parseSd s) fun p ↦
          Option.bind (decodeNat p.1) fun m ↦
            Option.bind (decodeNat p.2) fun k ↦ some (m, k) := by
      refine Computable.option_bind ?_ ?_
      · exact literalCode_computable.2.1.comp Computable.snd
      · exact H3.comp (Computable.snd.comp Computable.fst) Computable.snd
    exact Computable.option_bind native_string_index_computable.2.1 H2
  · intro m k
    simp [nativeThresholdData, decodeNativeThresholdData, (native_string_index_spec _).2,
      parseSd_sd_append, decodeNat_bits]

/-- The literal halting instance `g` with its search index written as a binary suffix.
Blueprint node `native:literal` (supporting definition). -/
def nativeThresholdInstance (e₀ m k : ℕ) : BitString :=
  haltWord e₀ (nativeThresholdData m k)

/-- An explicit coefficient for the literal input length, computed from the search index.
Blueprint node `native:literal` (supporting definition). -/
def nativeLiteralFactor (e₀ : ℕ) : ℕ := 12 + (bits e₀).length

/-- Threshold tests in the half-open search interval have uniformly bounded literal length.
Blueprint node `native:literal`. Neither assertion claims OTM construction time. -/
theorem literal_threshold_instance_length :
    (∀ e₀, 1 ≤ nativeLiteralFactor e₀ ∧ ∀ m k, k < 2 ^ (m + 1) →
      (nativeThresholdInstance e₀ m k).length ≤ nativeLiteralFactor e₀ * (m + 1)) ∧
    Computable nativeLiteralFactor ∧
    Computable (fun input : ℕ × ℕ × ℕ =>
      nativeThresholdInstance input.1 input.2.1 input.2.2) := by
  refine ⟨fun e₀ ↦ ⟨by unfold nativeLiteralFactor; omega, fun m k hk ↦ ?_⟩, ?_, ?_⟩
  · dsimp [nativeLiteralFactor, nativeThresholdInstance, haltWord, encF]
    have hbits : bits (nativeThresholdData m k) = true :: (sd (bits m) ++ bits k) :=
      (native_string_index_spec _).1
    rw [length_pairCode, hbits]
    simp only [List.length_cons, List.length_append, length_sd]
    have h1 : (bits m).length ≤ m + 1 := length_bits_le m
    have h2 : (bits k).length ≤ m + 1 := length_bits_le_of_lt hk
    nlinarith
  · exact (Primrec.nat_add.to_comp.comp (Computable.const 12)
      (Computable.list_length.comp bits_computable.1))
  · exact haltWord_computable.1.comp Computable.fst
      (native_threshold_data_spec.1.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))

/-- A single search index recognizes every bounded-output cardinality threshold for `U`.
Blueprint node `native:search-index`. The `k = 0` test halts even for an empty domain;
the count includes every output length and is finite by `simple_finite_card_lt`. -/
theorem exists_threshold_search_index (U : Map) (hU : Partrec U) :
    ∃ e₀ : ℕ, ∀ m k : ℕ, nativeThresholdInstance e₀ m k ∈ HBin ↔
      k ≤ {x | plainK U x ≤ (m : ℕ)}.ncard := by
  obtain ⟨c, hc⟩ : ∃ c : Nat.Partrec.Code, IsCodeFor c U := Nat.Partrec.Code.exists_code.mp hU
  -- the semantic count is the length of the completed stage list
  have hcard : ∀ m : ℕ,
      {x | plainK U x ≤ (m : ℕ)}.ncard = (completedBoundedOutput c m).length := by
    intro m
    have hset : {x | plainK U x ≤ (m : ℕ)} =
        ((completedBoundedOutput c m).toFinset : Set BitString) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
      exact (mem_completedBoundedOutput_iff_plainK_le hc m x).symm
    rw [hset, Set.ncard_coe_finset]
    exact List.toFinset_card_of_nodup (boundedOutputStage_nodup c m _)
  -- `k ≤ count` is witnessed at a finite stage
  have key : ∀ m k : ℕ, k ≤ {x | plainK U x ≤ (m : ℕ)}.ncard ↔
      ∃ t, k ≤ (boundedOutputStage c m t).length := by
    intro m k
    rw [hcard m]
    exact ⟨fun hk ↦ ⟨maxHaltingStage c m, hk⟩, fun ⟨t, ht⟩ ↦
      ht.trans (boundedOutputStage_prefix_completed c m t).length_le⟩
  -- the finite-stage test is computable
  have htest : Computable₂ (fun (p : ℕ × ℕ) (t : ℕ) ↦
      decide (p.2 ≤ (boundedOutputStage c p.1 t).length)) := by
    have h0 : Computable (fun q : (ℕ × ℕ) × ℕ ↦ (q.1.1, q.2)) :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    have h1 : Computable (fun q : (ℕ × ℕ) × ℕ ↦ boundedOutputStage c q.1.1 q.2) :=
      (boundedOutputStage_computable c).comp h0
    have h2 : Computable (fun q : (ℕ × ℕ) × ℕ ↦ (boundedOutputStage c q.1.1 q.2).length) :=
      Computable.list_length.comp h1
    have h3 : Computable (fun q : (ℕ × ℕ) × ℕ ↦ q.1.2) := Computable.snd.comp Computable.fst
    have hle : Computable₂ (fun a b : ℕ ↦ decide (a ≤ b)) :=
      (PrimrecRel.decide Primrec.nat_le).to_comp
    exact Computable₂.comp hle h3 h2
  -- unbounded search over stages
  have hrfind : Partrec (fun p : ℕ × ℕ ↦ Nat.rfind (fun t ↦
      (decide (p.2 ≤ (boundedOutputStage c p.1 t).length) : Part Bool))) :=
    Partrec.rfind htest.partrec₂
  have hF : Partrec (fun n : ℕ ↦ (Part.ofOption (decodeNativeThresholdData n)).bind
      (fun p : ℕ × ℕ ↦ (Nat.rfind (fun t ↦
        (decide (p.2 ≤ (boundedOutputStage c p.1 t).length) : Part Bool))).map
          (fun _ ↦ 0))) := by
    refine Partrec.bind (Computable.ofOption native_threshold_data_spec.2.1) ?_
    exact Partrec.map (hrfind.comp Computable.snd) (Computable.const 0).to₂
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hF)
  refine ⟨Encodable.encode e, fun m k ↦ ?_⟩
  rw [nativeThresholdInstance, haltWord_mem_HBin, Denumerable.ofNat_encode, he]
  dsimp only
  rw [native_threshold_data_spec.2.2 m k, key m k]
  simp only [Part.ofOption, Part.bind_some]
  change (Nat.rfind fun t ↦ (decide (k ≤ (boundedOutputStage c m t).length) : Part Bool)).Dom ↔ _
  refine Nat.rfind_dom.trans ?_
  exact ⟨fun ⟨n, hn, _⟩ ↦ ⟨n, by simpa using hn⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, by simpa using hn, fun _ ↦ trivial⟩⟩

end Kolmogorov.Milovanov
