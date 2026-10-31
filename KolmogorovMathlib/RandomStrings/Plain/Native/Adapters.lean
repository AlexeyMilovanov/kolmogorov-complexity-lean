/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.Foundation.ListUtil
import KolmogorovMathlib.RandomStrings.Effective.Configs
import KolmogorovMathlib.RandomStrings.Plain.Construction.Effective.StateMachine
import KolmogorovMathlib.RandomStrings.Plain.Construction.Referees
import KolmogorovMathlib.RandomStrings.Plain.Native.Instances

/-!
# Effective tables and the two native oracle adapters

This module supplies the effective finite tables used by the native counting referee.
Raw tables record Boolean answers, with missing entries defaulting to false. The bounded
simulator uses their positive entries and the test's own clock, even when the table covers
a larger domain (blueprint node `native:finite-table-api`).

The cumulative and random-string adapters translate raw queries into coordinates and
apply literal-threshold normalization (`native:adapters`). We prove computability,
agreement with the actual oracles, and bounds on the inspected coordinates
(`native:adapter-correct`). The native referee's effective interface uses the resulting
finite coordinate lists to turn coordinate tables into bounded oracle computations.
-/

namespace Kolmogorov.Milovanov

open RandomStrings

/-- The two raw oracle conventions used by the native family.
Blueprint node `native:adapters` (supporting definition). -/
inductive NativeOracleFlag where
  /-- Canonically encoded cumulative queries. -/
  | cumulative
  /-- Raw random-string membership queries. -/
  | random
  deriving DecidableEq, Repr

/-- A concrete Boolean encoding of the two flags, with cumulative encoded as false.
Blueprint node `native:adapters` (supporting definition). -/
def NativeOracleFlag.equivBool : NativeOracleFlag ≃ Bool where
  toFun flag := match flag with | .cumulative => false | .random => true
  invFun b := if b then .random else .cumulative
  left_inv := by intro flag; cases flag <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- Primitive flag coding uses the displayed Boolean equivalence.
Blueprint node `native:adapters` (supporting definition). -/
instance : Primcodable NativeOracleFlag := Primcodable.ofEquiv _ NativeOracleFlag.equivBool

/-- A finite Boolean table of raw oracle answers, in first-match lookup order.
Blueprint node `native:finite-table-api` (supporting definition). -/
abbrev NativeRawTable := List (BitString × Bool)

/-- A finite Boolean table of cumulative coordinate answers.
Blueprint node `native:adapters` (supporting definition). -/
abbrev NativeCoordinateTable := List (Coordinate × Bool)

/-- Every raw word of length at most the bound, in prefix-first lexicographic order.
Blueprint node `native:referee` (supporting definition). False precedes true. -/
def nativeRawWords : ℕ → List BitString
  | 0 => [[]]
  | T + 1 =>
    let shorter := nativeRawWords T
    [] :: (shorter.map (false :: ·) ++ shorter.map (true :: ·))

private lemma primrec_nativeRawWords : Primrec nativeRawWords := by
  have h_map_false : Primrec (fun (l : List BitString) ↦ l.map (false :: ·)) :=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
  have h_map_true : Primrec (fun (l : List BitString) ↦ l.map (true :: ·)) :=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
  have hstep : Primrec (fun (l : List BitString) ↦
      [] :: (l.map (false :: ·) ++ l.map (true :: ·))) :=
    Primrec.list_cons.comp (Primrec.const []) (Primrec.list_append.comp h_map_false h_map_true)
  have hh : Primrec₂ (fun (x : ℕ) (l : List BitString) ↦
      ([] : BitString) :: (l.map (false :: ·) ++ l.map (true :: ·))) := hstep.comp Primrec.snd
  have hiterate := Primrec.nat_iterate Primrec.id (Primrec.const [[]]) hh
  have h_eq : (fun (a : ℕ) ↦ (fun l ↦ ([] : BitString) ::
      (List.map (fun x ↦ false :: x) l ++ List.map (fun x ↦ true :: x) l))^[a] [[]]) =
      nativeRawWords := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl
  exact h_eq ▸ hiterate

/-- The universal raw-word table domain is effective, exhaustive, and duplicate-free.
Blueprint node `native:finite-table-api` (supporting lemma). -/
theorem native_raw_words_spec :
    Computable nativeRawWords ∧ ∀ T, (nativeRawWords T).Nodup ∧
      ∀ z, z ∈ nativeRawWords T ↔ z.length ≤ T := by
  constructor
  · exact primrec_nativeRawWords.to_comp
  · intro T
    constructor
    · induction T with
      | zero =>
        dsimp [nativeRawWords]
        exact List.nodup_singleton []
      | succ T ih =>
        dsimp [nativeRawWords]
        apply List.nodup_cons.mpr
        constructor
        · intro h
          simp only [List.mem_append, List.mem_map] at h
          rcases h with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
          · injection h
          · injection h
        · apply List.Nodup.append
          · apply List.Nodup.map _ ih
            intro a b hab
            injection hab
          · apply List.Nodup.map _ ih
            intro a b hab
            injection hab
          · intro a ha hb
            simp only [List.mem_map] at ha hb
            rcases ha with ⟨x, hx, rfl⟩
            rcases hb with ⟨y, hy, hyy⟩
            injection hyy
            contradiction
    · intro z
      induction T generalizing z with
      | zero =>
        dsimp [nativeRawWords]
        simp
      | succ T ih =>
        dsimp [nativeRawWords]
        simp only [List.mem_cons, List.mem_append, List.mem_map]
        constructor
        · intro h
          rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
          · simp
          · rw [ih] at ha
            simp [ha]
          · rw [ih] at ha
            simp [ha]
        · intro h
          cases z with
          | nil => left; rfl
          | cons hd tl =>
            right
            cases hd
            · left
              use tl
              rw [ih]
              simpa using h
            · right
              use tl
              rw [ih]
              simpa using h

/-- Read a raw table, using the repository's explicit first-match Boolean lookup.
Blueprint node `native:finite-table-api` (supporting definition). -/
def nativeRawTableAnswer (table : NativeRawTable) (z : BitString) : Bool :=
  (lookupB z table).getD false

/-- List exactly the positive table answers in the universal domain of radius `T`.
Blueprint node `native:finite-table-api` (supporting definition). -/
def nativeRawPositives (T : ℕ) (table : NativeRawTable) : List BitString :=
  (nativeRawWords T).filter (nativeRawTableAnswer table)

/-- Effective acceptance from a numerical finite transition table, at the input's own clock.
Blueprint node `native:finite-table-api` (supporting definition). `T` bounds only the table. -/
def nativeClockedAcceptanceCode (code e T : ℕ) (table : NativeRawTable)
    (z : BitString) : Bool :=
  clockedOutcomeT code (clock e z.length) (nativeRawPositives T table) z

/-- The finite-table acceptance adapter for an actual repository `OTMCode`.
Blueprint node `native:finite-table-api` (supporting definition). -/
def nativeClockedAcceptance (c : OTMCode) (e T : ℕ) (table : NativeRawTable)
    (z : BitString) : Bool :=
  nativeClockedAcceptanceCode (encodeCode c) e T table z

private lemma primrec_nativeRawPositives :
    Primrec₂ nativeRawPositives := by
  have h_words2 : Primrec fun p : ℕ × NativeRawTable ↦ nativeRawWords p.1 :=
    primrec_nativeRawWords.comp Primrec.fst
  have h_ans : Primrec fun p : (ℕ × NativeRawTable) × BitString ↦ nativeRawTableAnswer p.1.2 p.2 :=
    Primrec.option_getD.comp (lookupB_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.const false)
  exact list_filter_primrec h_words2 h_ans.to₂

/-- Bounded table acceptance is computable uniformly in explicit finite machine codes.
Blueprint node `native:finite-table-api` (supporting lemma). -/
theorem native_clocked_acceptance_computable :
    Computable (fun input : ℕ × ℕ × ℕ × NativeRawTable × BitString =>
      nativeClockedAcceptanceCode input.1 input.2.1 input.2.2.1
        input.2.2.2.1 input.2.2.2.2) := by
  have hprimrec : Primrec fun input : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦
      nativeClockedAcceptanceCode input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2 := by
    have h_code : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.1 := Primrec.fst
    have h_e : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.2.1 :=
      Primrec.fst.comp Primrec.snd
    have h_T : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have h_table : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have h_z : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have h_z_len : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦ p.2.2.2.2.length :=
      Primrec.list_length.comp h_z
    have h_clock : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦
        clock p.2.1 p.2.2.2.2.length :=
      clock_primrec.comp h_e h_z_len
    have h_pos : Primrec fun p : ℕ × ℕ × ℕ × NativeRawTable × BitString ↦
        nativeRawPositives p.2.2.1 p.2.2.2.1 :=
      primrec_nativeRawPositives.comp h_T h_table
    have houtcome : Primrec fun p : ℕ × ℕ × List BitString × BitString ↦
        clockedOutcomeT p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      clockedOutcomeT_primrec
    exact houtcome.comp (h_code.pair (h_clock.pair (h_pos.pair h_z)))
  exact hprimrec.to_comp

/-- Agreement on a sufficiently large raw table gives exactly clocked semantic acceptance.
Blueprint node `native:finite-table-api`. The cutoff remains `clock e z.length`. -/
theorem clocked_acceptance_finite_table_adapter (c : OTMCode) (e T : ℕ)
    (table : NativeRawTable) (z : BitString) (B : Set BitString)
    (hT : clock e z.length ≤ T)
    (hagree : ∀ w, w.length ≤ T → (nativeRawTableAnswer table w = true ↔ w ∈ B)) :
    nativeClockedAcceptance c e T table z = true ↔ ClockedAccepts c e B z := by
  have h := clockedAcceptsT_iff_clockedOutcomeT (encodeCode c) (clock e z.length)
    z B (nativeRawPositives T table) (by
      intro w hw
      have hlen := length_le_of_mem_queryAll (decodeCode (encodeCode c)).toOTM z
        (clock e z.length) w ((mem_queryListCodeT _ _ _ _).mp hw)
      have hshort := hlen.trans hT
      have hmem := (native_raw_words_spec.2 T).2 w
      simpa only [nativeRawPositives, List.mem_filter, hmem, hshort, true_and] using
        (hagree w hshort).symm)
  simpa only [decodeCode_encodeCode, ← clockedAccepts_iff_T,
    nativeClockedAcceptance, nativeClockedAcceptanceCode] using h.symm

/-- Lookup a coordinate table; arbitrary absent coordinates have negative default answers.
Blueprint node `native:adapters` (supporting definition). -/
def nativeCoordinateAnswer (table : NativeCoordinateTable) (q : Coordinate) : Bool :=
  ((table.find? (fun entry ↦ decide (entry.1 = q))).map Prod.snd).getD false

/-- Translate raw queries using literal-threshold normalization.
Blueprint node `native:adapters` (supporting definition). Empty random queries are positive. -/
def nativeRawAnswer (cU : ℕ) (flag : NativeOracleFlag) (answer : Coordinate → Bool)
    (z : BitString) : Bool :=
  match flag with
  | .cumulative =>
    match decodeQuery z with
    | some q => normalizedAnswer cU answer q
    | none => false
  | .random =>
    match z with
    | [] => true
    | _ :: _ => !(normalizedAnswer cU answer (z, z.length - 1))

/-- The two raw adapters on an explicit finite coordinate table.
Blueprint node `native:adapters`. The constant supplied by construction is `d + cV`. -/
def native_oracle_answer_adapters (cU : ℕ) (flag : NativeOracleFlag)
    (table : NativeCoordinateTable) (z : BitString) : Bool :=
  nativeRawAnswer cU flag (nativeCoordinateAnswer table) z

/-- The possible coordinate of a raw query, before literal-threshold normalization.
Blueprint node `native:adapter-correct` (supporting definition). -/
def nativeRawCoordinate (flag : NativeOracleFlag) (z : BitString) : Option Coordinate :=
  match flag with
  | .cumulative => decodeQuery z
  | .random => if z = [] then none else some (z, z.length - 1)

/-- Discard malformed, empty-random, and fixed high-threshold queries.
Blueprint node `native:referee` (supporting definition). -/
def nativeInspectedCoordinate (cU : ℕ) (flag : NativeOracleFlag)
    (z : BitString) : Option Coordinate := do
  let q ← nativeRawCoordinate flag z
  if q.2 < q.1.length + cU then some q else none

/-- Translate the universal raw domain to variable coordinates, removing all repetitions.
Blueprint node `native:referee` (supporting definition). -/
def nativeCoordinateList (cU : ℕ) (flag : NativeOracleFlag) (T : ℕ) : List Coordinate :=
  ((nativeRawWords T).filterMap (nativeInspectedCoordinate cU flag)).eraseDups

/-- The selected semantic raw oracle, using cumulative or random-string membership.
Blueprint node `native:adapter-correct` (supporting definition). -/
def nativeOracle (flag : NativeOracleFlag) (U : Map) : Set BitString :=
  match flag with
  | .cumulative => CumulativeOracle encF U
  | .random => PlainRandomOracle U

private lemma primrec_nativeCoordinateAnswer :
    Primrec₂ nativeCoordinateAnswer := by
  have h_find : Primrec₂ (fun (table : NativeCoordinateTable) (q : Coordinate) ↦
      table.find? (fun entry ↦ decide (entry.1 = q))) := by
    have hp : Primrec₂ (fun (a : NativeCoordinateTable × Coordinate)
        (e : Coordinate × Bool) ↦ decide (e.1 = a.2)) := by
      apply PrimrecPred.decide
      exact Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)
    exact list_find?_primrec Primrec.fst hp
  have h_map : Primrec₂ (fun (table : NativeCoordinateTable) (q : Coordinate) ↦
      (table.find? (fun entry ↦ decide (entry.1 = q))).map Prod.snd) :=
    Primrec.option_map h_find (Primrec.snd.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp h_map (Primrec.const false)).to₂

private lemma primrec_normalizedCoordinateAnswer :
    Primrec₂ (fun (p : ℕ × NativeCoordinateTable) (q : Coordinate) ↦
      normalizedAnswer p.1 (nativeCoordinateAnswer p.2) q) := by
  dsimp only [normalizedAnswer]
  have h_cond : Primrec₂ (fun (p : ℕ × NativeCoordinateTable) (q : Coordinate) ↦
      decide (q.1.length + p.1 ≤ q.2)) := by
    have h_cond2 : PrimrecPred (fun (a : (ℕ × NativeCoordinateTable) × Coordinate) ↦
        a.2.1.length + a.1.1 ≤ a.2.2) := by
      apply Primrec.nat_le.comp
      · apply Primrec.nat_add.comp
        · exact Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
        · exact Primrec.fst.comp Primrec.fst
      · exact Primrec.snd.comp Primrec.snd
    exact PrimrecPred.decide h_cond2
  have h_lookup : Primrec₂ (fun (p : ℕ × NativeCoordinateTable) (q : Coordinate) ↦
      nativeCoordinateAnswer p.2 q) :=
    primrec_nativeCoordinateAnswer.comp₂ (Primrec.snd.comp Primrec₂.left) Primrec₂.right
  exact Primrec₂.comp₂ Primrec.or h_cond h_lookup

private lemma computable_cumulativeAnswer
    (n : (ℕ × NativeCoordinateTable) → Coordinate → Bool)
    (hn : Computable₂ n) :
    Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      match decodeQuery p.2.2.2 with
      | some q => n (p.1, p.2.2.1) q
      | none => false) := by
  have hdecode : Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      decodeQuery p.2.2.2) :=
    encF_computable.2.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hsome : Computable₂ (fun (p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString)
      (q : Coordinate) ↦ n (p.1, p.2.2.1) q) := by
    apply Computable₂.mk
    exact hn.comp
      (Computable.pair
        (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
      Computable.snd
  exact (Computable.option_casesOn hdecode (Computable.const false) hsome).of_eq fun p ↦ by
    cases decodeQuery p.2.2.2 <;> rfl

private lemma computable_randomAnswer
    (n : (ℕ × NativeCoordinateTable) → Coordinate → Bool)
    (hn : Computable₂ n) :
    Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      match p.2.2.2 with
      | [] => true
      | _ :: _ => !(n (p.1, p.2.2.1)
          (p.2.2.2, p.2.2.2.length - 1))) := by
  have hz : Primrec (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hempty := (Primrec.eq.comp hz (Primrec.const [])).decide.to_comp
  have hcoord : Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      (p.2.2.2, p.2.2.2.length - 1)) :=
    (hz.pair (Primrec.nat_sub.comp (Primrec.list_length.comp hz) (Primrec.const 1))).to_comp
  have htable : Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      (p.1, p.2.2.1)) :=
    Computable.fst.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have hanswer := Primrec.not.to_comp.comp (hn.comp htable hcoord)
  exact (Computable.cond hempty (Computable.const true) hanswer).of_eq fun p ↦ by
    cases p.2.2.2 <;> rfl

private lemma computable_flag_cases
    (f g : (ℕ × NativeOracleFlag × NativeCoordinateTable × BitString) → Bool)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      match p.2.1 with
      | .cumulative => f p
      | .random => g p) := by
  have h_flag : Computable (fun p : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      NativeOracleFlag.equivBool p.2.1) :=
    (Primrec.of_equiv (e := NativeOracleFlag.equivBool)).to_comp.comp
      (Computable.fst.comp Computable.snd)
  exact (Computable.cond h_flag hg hf).of_eq fun p ↦ by
    cases p.2.1 <;> rfl

private lemma computable_rawAnswer :
    Computable (fun input : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString ↦
      native_oracle_answer_adapters input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  let n : (ℕ × NativeCoordinateTable) → Coordinate → Bool :=
    fun p q ↦ normalizedAnswer p.1 (nativeCoordinateAnswer p.2) q
  have hn : Computable₂ n :=
    primrec_normalizedCoordinateAnswer.to_comp
  exact computable_flag_cases _ _
    (computable_cumulativeAnswer n hn)
    (computable_randomAnswer n hn)

private lemma computable_rawCoordinate :
    Computable (fun input : NativeOracleFlag × BitString ↦
      nativeRawCoordinate input.1 input.2) := by
  have hrandom : Primrec (fun z : BitString ↦
      if z = [] then (none : Option Coordinate) else some (z, z.length - 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const [])) (Primrec.const none)
      (Primrec.option_some.comp
        (Primrec.id.pair (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))))
  have hflag : Primrec NativeOracleFlag.equivBool := Primrec.of_equiv
  have h := Computable.cond (hflag.to_comp.comp Computable.fst)
    (hrandom.to_comp.comp Computable.snd) (encF_computable.2.comp Computable.snd)
  exact h.of_eq (fun input ↦ by cases input.1 <;> rfl)

private lemma computable_inspectedCoordinate :
    Computable (fun input : ℕ × NativeOracleFlag × BitString ↦
      nativeInspectedCoordinate input.1 input.2.1 input.2.2) := by
  have hraw : Computable (fun input : ℕ × NativeOracleFlag × BitString ↦
      nativeRawCoordinate input.2.1 input.2.2) :=
    computable_rawCoordinate.comp Computable.snd
  have hkeep : Primrec₂ (fun (input : ℕ × NativeOracleFlag × BitString) (q : Coordinate) ↦
      if q.2 < q.1.length + input.1 then some q else none) :=
    Primrec.ite
      (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.nat_add.comp
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst)))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact (Computable.option_bind hraw hkeep.to_comp).of_eq (fun _ ↦ rfl)

private lemma computable_coordinateList :
    Computable (fun input : ℕ × NativeOracleFlag × ℕ ↦
      nativeCoordinateList input.1 input.2.1 input.2.2) := by
  have hwords : Computable (fun input : ℕ × NativeOracleFlag × ℕ ↦
      nativeRawWords input.2.2) :=
    native_raw_words_spec.1.comp (Computable.snd.comp Computable.snd)
  have hargs : Computable (fun p : (ℕ × NativeOracleFlag × ℕ) × BitString ↦
      (p.1.1, p.1.2.1, p.2)) :=
    ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have hinspected' : Computable (fun p : (ℕ × NativeOracleFlag × ℕ) × BitString ↦
      nativeInspectedCoordinate p.1.1 p.1.2.1 p.2) :=
    (computable_inspectedCoordinate.comp hargs).of_eq
      (fun _ ↦ rfl)
  have hinspected : Computable₂ (fun (input : ℕ × NativeOracleFlag × ℕ) (z : BitString) ↦
      nativeInspectedCoordinate input.1 input.2.1 z) := hinspected'
  have hfilter : Computable (fun input : ℕ × NativeOracleFlag × ℕ ↦
      (nativeRawWords input.2.2).filterMap (nativeInspectedCoordinate input.1 input.2.1)) :=
    computable_filterMap hwords hinspected
  exact (primrec_eraseDups.to_comp.comp
    hfilter).of_eq (fun _ ↦ rfl)

/-- Finite raw answers and coordinate-domain construction are uniformly computable.
Blueprint node `native:adapters` (supporting lemma). -/
theorem native_oracle_adapters_computable :
    Computable (fun input : ℕ × NativeOracleFlag × NativeCoordinateTable × BitString =>
      native_oracle_answer_adapters input.1 input.2.1 input.2.2.1 input.2.2.2) ∧
    Computable (fun input : ℕ × NativeOracleFlag × ℕ =>
      nativeCoordinateList input.1 input.2.1 input.2.2) :=
  ⟨computable_rawAnswer, computable_coordinateList⟩

private lemma normalizedAnswer_actualCoordinateOracle
    (U : Map) (cU : ℕ)
    (hliteral : ∀ x, plainK U x ≤ (x.length + cU : ℕ))
    (q : Coordinate) :
    normalizedAnswer cU (coordinateOracleAnswer (actualCoordinateOracle U)) q =
      coordinateOracleAnswer (actualCoordinateOracle U) q := by
  classical
  by_cases h : q.1.length + cU ≤ q.2
  · have hx : Simple U q.1 q.2 :=
      (hliteral q.1).trans (by exact_mod_cast h)
    simp [normalizedAnswer, h, coordinateOracleAnswer, actualCoordinateOracle, hx]
  · simp [normalizedAnswer, h]

private lemma nativeRawAnswer_eq_true_iff
    (U : Map) (cU : ℕ)
    (hliteral : ∀ x, plainK U x ≤ (x.length + cU : ℕ)) :
    (∀ flag z, nativeRawAnswer cU flag (coordinateOracleAnswer (actualCoordinateOracle U))
      z = true ↔ z ∈ nativeOracle flag U) := by
  intro flag z
  cases flag with
  | cumulative =>
    dsimp [nativeRawAnswer, nativeOracle, CumulativeOracle]
    cases hq : decodeQuery z with
    | none =>
      constructor
      · intro ht; contradiction
      · rintro ⟨x, k, hx, -⟩
        have h_dec := decodeQuery_eq_some_iff z (x, k) |>.mpr hx
        rw [h_dec] at hq
        contradiction
    | some q =>
      dsimp [nativeRawAnswer]
      rw [normalizedAnswer_actualCoordinateOracle U cU hliteral q]
      dsimp [coordinateOracleAnswer, actualCoordinateOracle]
      simp only [decide_eq_true_eq]
      constructor
      · intro hS
        have h_dec := decodeQuery_eq_some_iff z q |>.mp hq
        have h_eq : encF (q.1, q.2) = z := by rw [← h_dec]
        exact ⟨q.1, q.2, h_eq, hS⟩
      · rintro ⟨x, k, hx, hS⟩
        have h_dec2 := decodeQuery_eq_some_iff z (x, k) |>.mpr hx
        rw [h_dec2] at hq
        have heq := Option.some.inj hq
        rw [← heq]
        exact hS
  | random =>
    dsimp [nativeRawAnswer, nativeOracle, PlainRandomOracle]
    cases z with
    | nil =>
      simp only [List.length_nil, ENat.natCast_zero, zero_le]
    | cons hd tl =>
      dsimp [nativeRawAnswer]
      rw [normalizedAnswer_actualCoordinateOracle U cU hliteral (hd :: tl, tl.length)]
      simp only [Bool.not_eq_true']
      dsimp [coordinateOracleAnswer, actualCoordinateOracle, Simple]
      simp only [decide_eq_false_iff_not, not_le]
      have hdisc : plainK U (hd :: tl) < ((tl.length + 1 : ℕ) : ENat) ↔
          plainK U (hd :: tl) ≤ (tl.length : ENat) := by
        rw [Nat.cast_add, Nat.cast_one]
        exact ENat.lt_add_one_iff (ENat.natCast_ne_top _)
      have hfinal :
          (tl.length : ENat) < plainK U (hd :: tl) ↔
            ((tl.length + 1 : ℕ) : ENat) ≤ plainK U (hd :: tl) := by
        rw [← not_le, ← hdisc, not_lt]
      exact hfinal

private lemma length_le_of_nativeRawCoordinate_eq_some
    {flag : NativeOracleFlag} {z : BitString} {q : Coordinate}
    (hq : nativeRawCoordinate flag z = some q) : q.1.length ≤ z.length := by
  cases flag with
  | cumulative =>
    have he := (decodeQuery_eq_some_iff z q).mp hq
    simpa only [he] using target_length_le_encF q.1 q.2
  | random =>
    dsimp only [nativeRawCoordinate] at hq
    split at hq
    · contradiction
    · cases Option.some.inj hq
      exact le_rfl

private lemma bounds_of_nativeInspectedCoordinate_eq_some
    {cU T : ℕ} {flag : NativeOracleFlag} {z : BitString} {q : Coordinate}
    (hz : z.length ≤ T) (hq : nativeInspectedCoordinate cU flag z = some q) :
    q.1.length ≤ T ∧ q.2 < T + cU := by
  cases hraw : nativeRawCoordinate flag z with
  | none => simp [nativeInspectedCoordinate, hraw] at hq
  | some q' =>
    by_cases h : q'.2 < q'.1.length + cU
    · have heq : q' = q := by
        simpa [nativeInspectedCoordinate, hraw, h] using hq
      subst q'
      have hl := (length_le_of_nativeRawCoordinate_eq_some hraw).trans hz
      exact ⟨hl, by omega⟩
    · simp [nativeInspectedCoordinate, hraw, h] at hq

/-- Correct literal normalization gives the two actual raw oracles and the query bounds.
Blueprint node `native:adapter-correct`. The literal bound is explicit data supplied by
the constructed simulation branch, uniformly in the target string. -/
theorem native_oracle_adapters_correct (U : Map) (cU : ℕ)
    (hliteral : ∀ x, plainK U x ≤ (x.length + cU : ℕ)) :
    (∀ flag z, nativeRawAnswer cU flag (coordinateOracleAnswer (actualCoordinateOracle U))
      z = true ↔ z ∈ nativeOracle flag U) ∧
    (∀ flag z T q, z.length ≤ T → nativeRawCoordinate flag z = some q →
      q.1.length ≤ T) ∧
    ∀ flag z T q, z.length ≤ T → nativeInspectedCoordinate cU flag z = some q →
      q.1.length ≤ T ∧ q.2 < T + cU :=
  ⟨nativeRawAnswer_eq_true_iff U cU hliteral,
    fun _ _ _ _ hz hq ↦ (length_le_of_nativeRawCoordinate_eq_some hq).trans hz,
    fun _ _ _ _ hz hq ↦ bounds_of_nativeInspectedCoordinate_eq_some hz hq⟩

private lemma nativeRawAnswer_congr (cU : ℕ) (flag : NativeOracleFlag)
    (a b : Coordinate → Bool) (z : BitString)
    (h : ∀ q, nativeInspectedCoordinate cU flag z = some q → a q = b q) :
    nativeRawAnswer cU flag a z = nativeRawAnswer cU flag b z := by
  have hnormalized (q : Coordinate) (hq : nativeRawCoordinate flag z = some q) :
      normalizedAnswer cU a q = normalizedAnswer cU b q := by
    by_cases hhigh : q.1.length + cU ≤ q.2
    · simp [normalizedAnswer, hhigh]
    · have hlow : q.2 < q.1.length + cU := Nat.lt_of_not_ge hhigh
      have heq := h q (by simp [nativeInspectedCoordinate, hq, hlow])
      simp [normalizedAnswer, hhigh, heq]
  cases flag with
  | cumulative =>
    cases hq : decodeQuery z with
    | none => simp [nativeRawAnswer, hq]
    | some q => simpa only [nativeRawAnswer, hq] using hnormalized q hq
  | random =>
    cases z with
    | nil => rfl
    | cons hd tl =>
      have heq := hnormalized (hd :: tl, (hd :: tl).length - 1) (by
        simp [nativeRawCoordinate])
      exact congrArg Bool.not heq

/-- The translated table is duplicate-free and covers exactly the nonfixed raw queries.
Blueprint node `native:referee` (supporting lemma). Agreement on this domain suffices
for every raw answer in the universal table, including fixed positive answers. -/
theorem native_coordinate_list_spec (cU T : ℕ) (flag : NativeOracleFlag) :
    (nativeCoordinateList cU flag T).Nodup ∧
    (∀ q, q ∈ nativeCoordinateList cU flag T ↔
      ∃ z, z.length ≤ T ∧ nativeInspectedCoordinate cU flag z = some q) ∧
    ∀ (table : NativeCoordinateTable) (answer : Coordinate → Bool),
      (∀ q ∈ nativeCoordinateList cU flag T, nativeCoordinateAnswer table q = answer q) →
      ∀ z, z.length ≤ T → native_oracle_answer_adapters cU flag table z =
        nativeRawAnswer cU flag answer z := by
  have hmem (q : Coordinate) : q ∈ nativeCoordinateList cU flag T ↔
      ∃ z, z.length ≤ T ∧ nativeInspectedCoordinate cU flag z = some q := by
    simp only [nativeCoordinateList, List.mem_eraseDups, List.mem_filterMap,
      (native_raw_words_spec.2 T).2]
  refine ⟨nodup_eraseDups_list _, hmem, ?_⟩
  intro table answer hagree z hz
  apply nativeRawAnswer_congr
  intro q hq
  exact hagree q ((hmem q).mpr ⟨z, hz, hq⟩)

end Kolmogorov.Milovanov
