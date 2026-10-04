import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Partrec
import Mathlib.Computability.Halting
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayInverse.Core

/-!
# Solovay's theorem: the padding and inequality machinery

The padded codes `ShortDescriptions.padBits` and the derived counting used to turn the
construction of `MonotoneComplexity.Omega.SolovayInverse.Core` into the Solovay inequality
between plain and prefix complexity.

SUV Theorem 72, p. 148.
-/

namespace Kolmogorov
open scoped ENNReal
open Nat.Partrec (Code)
open Kolmogorov.ComputableReals

section SolovayInequality

/-- Padding the binary digits of `k` to width `L` gives a string of length `L`. -/
theorem length_padBits {k L : ℕ} (_h : (Nat.bits k).length ≤ L) :
    (ShortDescriptions.padBits k L).length = L := by
  simp [ShortDescriptions.padBits]
  omega

/-- A string of zeros reads as the numeral zero. -/
theorem bitsToNat_replicate_false (m : ℕ) :
    bitsToNat (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change 2 * bitsToNat (List.replicate m false) + (if false then 1 else 0) = 0
    rw [ih]
    rfl

/-- Reading a concatenation as a little-endian numeral adds the second value shifted by the
length of the first. -/
theorem bitsToNat_append (l1 l2 : BitString) :
    bitsToNat (l1 ++ l2) = bitsToNat l1 + 2 ^ l1.length * bitsToNat l2 := by
  induction l1 with
  | nil =>
    simp [bitsToNat]
  | cons b t ih =>
    have h1 : bitsToNat ((b :: t) ++ l2) = 2 * bitsToNat (t ++ l2) + (if b then 1 else 0) := rfl
    have h2 : bitsToNat (b :: t) = 2 * bitsToNat t + (if b then 1 else 0) := rfl
    rw [h1, ih, h2, List.length_cons, pow_succ]
    ring

/-- Padding preserves the value: the padded digits of `k` read back as `k`. -/
theorem bitsToNat_padBits {k L : ℕ} (_h : (Nat.bits k).length ≤ L) :
    bitsToNat (ShortDescriptions.padBits k L) = k := by
  unfold ShortDescriptions.padBits
  rw [bitsToNat_append, bitsToNat_replicate_false, mul_zero, add_zero, bitsToNat_bits]

/-- Raw output of `runOut` for the prefix `w.take m.unpair.1` with fuel `m.unpair.2`. -/
def solovayOut (c : Code) (w : BitString) (m : ℕ) : Option BitString :=
  runOut c m.unpair.2 (w.take m.unpair.1)

/-- The raw output read by the Solovay decompressor is computable in the string and the index. -/
lemma solovayOut_computable (c : Code) :
    Computable (fun p : BitString × ℕ => solovayOut c p.1 p.2) := by
  unfold solovayOut
  have h_ro : Computable (fun p : ℕ × BitString => runOut c p.1 p.2) := by
    unfold runOut
    have h_ev : Computable (fun p : ℕ × BitString =>
        Code.evaln p.1 c (Encodable.encode (α := BitString × BitString) (p.2, []))) := by
      have h_pair : Computable (fun p : ℕ × BitString => ((p.2, []) : BitString × BitString)) :=
        Computable.pair Computable.snd (Computable.const [])
      exact (evaln_fixed_computable c).comp (Computable.pair Computable.fst
        (Computable.encode.comp h_pair))
    exact Computable.option_bind h_ev (Computable.decode.comp Computable.snd)
  have h_unpair : Computable (fun p : BitString × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have h_i : Computable (fun p : BitString × ℕ => p.2.unpair.1) :=
    Computable.fst.comp h_unpair
  have h_t : Computable (fun p : BitString × ℕ => p.2.unpair.2) :=
    Computable.snd.comp h_unpair
  have h_q : Computable (fun p : BitString × ℕ => p.1.take p.2.unpair.1) :=
    Primrec.list_take.to_comp.comp h_i Computable.fst
  exact h_ro.comp (Computable.pair h_t h_q)

/-- The raw output of the Solovay machine on `p`, read as a bit string, the empty string
standing for no output. -/
def solovayOutStr (c : Code) (p : BitString × ℕ) : BitString :=
  Option.getD (solovayOut c p.1 p.2) []

/-- The string extracted from the raw output is computable. -/
lemma solovayOutStr_computable (c : Code) :
    Computable (fun p : BitString × ℕ => solovayOutStr c p) :=
  Computable.option_getD (solovayOut_computable c) (Computable.const [])

/-- The complexity level coded by the raw output of the Solovay machine on `p`. -/
def solovayKN (c : Code) (p : BitString × ℕ) : ℕ :=
  decodeBits (solovayOutStr c p)

/-- The complexity level read from the output is computable. -/
lemma solovayKN_computable (c : Code) :
    Computable (fun p : BitString × ℕ => solovayKN c p) :=
  decodeBits_computable.comp (solovayOutStr_computable c)

/-- The target length used inside the Solovay decompressor:
`(p.1.drop p.2.unpair.1).length + solovayKN c p - c₆₄`, the length of the tail of the program
after the split index plus the complexity level read from the machine output, less `c₆₄`
(truncated subtraction). -/
def solovayN (c : Code) (c₆₄ : ℕ) (p : BitString × ℕ) : ℕ :=
  (p.1.drop p.2.unpair.1).length + solovayKN c p - c₆₄

/-- The target length computed inside the Solovay decompressor is computable. -/
lemma solovayN_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ => solovayN c c₆₄ p) := by
  have h_unpair : Computable (fun p : BitString × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have h_u : Computable (fun p : BitString × ℕ => p.1.drop p.2.unpair.1) :=
    Primrec.list_drop.to_comp.comp (Computable.fst.comp h_unpair) Computable.fst
  have h_L : Computable (fun p : BitString × ℕ => (p.1.drop p.2.unpair.1).length) :=
    Computable.list_length.comp h_u
  have h_sum : Computable (fun p : BitString × ℕ =>
      (p.1.drop p.2.unpair.1).length + solovayKN c p) :=
    Primrec.nat_add.to_comp.to₂.comp h_L (solovayKN_computable c)
  have h_sub : Computable (fun p : BitString × ℕ =>
      (p.1.drop p.2.unpair.1).length + solovayKN c p - c₆₄) :=
    Primrec.nat_sub.to_comp.to₂.comp h_sum (Computable.const c₆₄)
  exact h_sub

/-- The codes of complexity at most `n` enumerated up to stage `t`, cumulated over all stages
and with duplicates removed. -/
def cumSnapshotCodes (c : Code) (q : ℕ × ℕ) : List BitString :=
  ((List.range (q.2 + 1)).flatMap (fun s => snapshotCodes c q.1 s)).eraseDups

/-- The snapshot enumeration used by the cumulative list is primitive recursive in the level and
the stage. -/
lemma cumSnapHelper_primrec (c : Code) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => snapshotCodes c p.1.1 p.2) :=
  (snapshotCodes_primrec c).comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

/-- The cumulative snapshot list is computable. -/
lemma cumSnapshotCodes_computable (c : Code) :
    Computable (cumSnapshotCodes c) := by
  have h_range : Primrec (fun q : ℕ × ℕ => List.range (q.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  have h_flatMap : Primrec (fun q : ℕ × ℕ =>
      (List.range (q.2 + 1)).flatMap (fun s => snapshotCodes c q.1 s)) :=
    Primrec.list_flatMap h_range (cumSnapHelper_primrec c).to₂
  have h_prim :=
    (_root_.Kolmogorov.CodedFiniteDistribution.eraseDups_bitstring_primrec).comp h_flatMap
  exact h_prim.to_comp

/-- The cumulative snapshot list at an earlier stage is a prefix of the one at a later stage. -/
lemma cumSnapshotCodes_prefix_of_le (c : Code) (n : ℕ) {t1 t2 : ℕ} (ht : t1 ≤ t2) :
    cumSnapshotCodes c (n, t1) <+: cumSnapshotCodes c (n, t2) := by
  dsimp [cumSnapshotCodes]
  have h_take : List.take (t1 + 1) (List.range (t2 + 1)) = List.range (t1 + 1) := by
    rw [List.take_range, min_eq_left (by omega)]
  have h_range_pre : List.range (t1 + 1) <+: List.range (t2 + 1) :=
    h_take ▸ List.take_prefix (t1 + 1) (List.range (t2 + 1))
  obtain ⟨r, hr⟩ := h_range_pre
  rw [← hr, List.flatMap_append, List.eraseDups_append]
  exact List.prefix_append _ _

/-- Snapshot list of codes computed inside the Solovay decompressor. -/
def solovayCodes (c : Code) (c₆₄ : ℕ) (p : BitString × ℕ) : List BitString :=
  cumSnapshotCodes c (solovayN c c₆₄ p, p.2.unpair.2)

/-- The snapshot list used inside the Solovay decompressor is computable. -/
lemma solovayCodes_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ => solovayCodes c c₆₄ p) := by
  have h_unpair : Computable (fun p : BitString × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have h_t : Computable (fun p : BitString × ℕ => p.2.unpair.2) :=
    Computable.snd.comp h_unpair
  have h_pair : Computable (fun p : BitString × ℕ => (solovayN c c₆₄ p, p.2.unpair.2)) :=
    Computable.pair (solovayN_computable c c₆₄) h_t
  exact (cumSnapshotCodes_computable c).comp h_pair

/-- Convergence of the raw output is a computable predicate. -/
lemma solovayCond1_computable (c : Code) :
    Computable (fun p : BitString × ℕ => (solovayOut c p.1 p.2).isSome) :=
  Primrec.option_isSome.to_comp.comp (solovayOut_computable c)

/-- The agreement of the read level with the produced string is a computable predicate. -/
lemma solovayCond2_computable (c : Code) :
    Computable (fun p : BitString × ℕ =>
      decide (Nat.bits (solovayKN c p) = solovayOutStr c p)) := by
  have h_bits : Computable (fun p : BitString × ℕ => Nat.bits (solovayKN c p)) :=
    natBits_computable.comp (solovayKN_computable c)
  have h_str : Computable (fun p : BitString × ℕ => solovayOutStr c p) :=
    solovayOutStr_computable c
  exact (PrimrecPred.decide Primrec.eq).to_comp.to₂.comp h_bits h_str

/-- The index bound against the length of the snapshot list is a computable predicate. -/
lemma solovayCond3_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ =>
      decide (bitsToNat (p.1.drop p.2.unpair.1) < (solovayCodes c c₆₄ p).length)) := by
  have h_unpair : Computable (fun p : BitString × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have h_u : Computable (fun p : BitString × ℕ => p.1.drop p.2.unpair.1) :=
    Primrec.list_drop.to_comp.comp (Computable.fst.comp h_unpair) Computable.fst
  have h_k : Computable (fun p : BitString × ℕ => bitsToNat (p.1.drop p.2.unpair.1)) :=
    bitsToNat_computable.comp h_u
  have h_len : Computable (fun p : BitString × ℕ => (solovayCodes c c₆₄ p).length) :=
    Computable.list_length.comp (solovayCodes_computable c c₆₄)
  exact (PrimrecPred.decide Primrec.nat_lt).to_comp.to₂.comp h_k h_len

/-- Boolean check condition for Solovay decompressor. -/
def solovayCond (c : Code) (c₆₄ : ℕ) (w : BitString) (m : ℕ) : Bool :=
  bif (solovayOut c w m).isSome then
    bif decide (Nat.bits (solovayKN c (w, m)) = solovayOutStr c (w, m)) then
      decide (bitsToNat (w.drop m.unpair.1) < (solovayCodes c c₆₄ (w, m)).length)
    else false
  else false

/-- The full check condition of the Solovay decompressor is computable. -/
lemma solovayCond_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ => solovayCond c c₆₄ p.1 p.2) := by
  have h1 := solovayCond1_computable c
  have h2 := solovayCond2_computable c
  have h3 := solovayCond3_computable c c₆₄
  have h23 : Computable (fun p : BitString × ℕ =>
      bif decide (Nat.bits (solovayKN c p) = solovayOutStr c p) then
        decide (bitsToNat (p.1.drop p.2.unpair.1) < (solovayCodes c c₆₄ p).length)
      else false) :=
    Computable.cond h2 h3 (Computable.const false)
  exact Computable.cond h1 h23 (Computable.const false)

/-- Calculated output string for Solovay decompressor. -/
def solovayVal (c : Code) (c₆₄ : ℕ) (w : BitString) (m : ℕ) : BitString :=
  let u := w.drop m.unpair.1
  let k := bitsToNat u
  (solovayCodes c c₆₄ (w, m)).getD k []

/-- The output string of the Solovay decompressor is computable in its inputs. -/
lemma solovayVal_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ => solovayVal c c₆₄ p.1 p.2) := by
  unfold solovayVal
  have h_unpair : Computable (fun p : BitString × ℕ => p.2.unpair) :=
    Computable.unpair.comp Computable.snd
  have h_u : Computable (fun p : BitString × ℕ => p.1.drop p.2.unpair.1) :=
    Primrec.list_drop.to_comp.comp (Computable.fst.comp h_unpair) Computable.fst
  have h_k : Computable (fun p : BitString × ℕ => bitsToNat (p.1.drop p.2.unpair.1)) :=
    bitsToNat_computable.comp h_u
  have h_getD : Computable (fun p : List BitString × ℕ => p.1.getD p.2 []) :=
    (Primrec.list_getD []).to_comp
  exact @Computable.comp (BitString × ℕ) (List BitString × ℕ) BitString _ _ _
    (fun p => p.1.getD p.2 [])
    (fun p => (solovayCodes c c₆₄ p, bitsToNat (p.1.drop p.2.unpair.1)))
    h_getD
    (Computable.pair (solovayCodes_computable c c₆₄) h_k)

/-- The computable check function for the Solovay decompressor. -/
def solovayCheck (c : Code) (c₆₄ : ℕ) (w : BitString) (m : ℕ) : Option BitString :=
  cond (solovayCond c c₆₄ w m) (some (solovayVal c c₆₄ w m)) none

/-- The check function of the Solovay decompressor is computable. -/
lemma solovayCheck_computable (c : Code) (c₆₄ : ℕ) :
    Computable (fun p : BitString × ℕ => solovayCheck c c₆₄ p.1 p.2) := by
  exact Computable.cond (solovayCond_computable c c₆₄)
    (Computable.option_some.comp (solovayVal_computable c c₆₄)) (Computable.const none)

/-- The Solovay decompressor: it searches for the first `m` at which `solovayCheck` succeeds and
returns the string that check produces. -/
def solovayMap (c : Code) (c₆₄ : ℕ) : Map := fun pr =>
  (Nat.rfind (fun m => Part.some (solovayCheck c c₆₄ pr.1 m).isSome)).bind
    (fun m => Part.ofOption (solovayCheck c c₆₄ pr.1 m))

/-- The unbounded search for a successful check is partial recursive. -/
lemma solovayRfind_partrec (c : Code) (c₆₄ : ℕ) :
    Partrec (fun (pr : BitString × BitString) =>
      Nat.rfind (fun m => Part.some (solovayCheck c c₆₄ pr.1 m).isSome)) := by
  have h_comp : Computable (fun p : BitString × ℕ => solovayCheck c c₆₄ p.1 p.2) :=
    solovayCheck_computable c c₆₄
  have h_isSome : Computable₂ (fun (w : BitString) (m : ℕ) => (solovayCheck c c₆₄ w m).isSome) :=
    (Primrec.option_isSome.to_comp.comp h_comp).to₂
  have h_rfind : Partrec (fun (w : BitString) =>
      Nat.rfind (fun m => Part.some (solovayCheck c c₆₄ w m).isSome)) :=
    Partrec.rfind h_isSome.partrec₂
  exact h_rfind.comp Computable.fst

/-- The check function read off the first component of a program–condition pair. -/
def solovayCheckPair (c : Code) (c₆₄ : ℕ) (p : (BitString × BitString) × ℕ) : Option BitString :=
  solovayCheck c c₆₄ p.1.1 p.2

/-- The paired check function is computable. -/
lemma solovayCheckPair_computable (c : Code) (c₆₄ : ℕ) :
    Computable (solovayCheckPair c c₆₄) :=
  @Computable.comp ((BitString × BitString) × ℕ) (BitString × ℕ) (Option BitString) _ _ _
    (fun p => solovayCheck c c₆₄ p.1 p.2)
    (fun p => (p.1.1, p.2))
    (solovayCheck_computable c c₆₄)
    (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)

/-- Turning the optional check result into a partial value is partial recursive. -/
lemma solovayOfOpt_partrec (c : Code) (c₆₄ : ℕ) :
    Partrec (fun (p : (BitString × BitString) × ℕ) =>
      Part.ofOption (solovayCheck c c₆₄ p.1.1 p.2)) :=
  Computable.ofOption (solovayCheckPair_computable c c₆₄)

/-- The Solovay map is a decompressor. -/
lemma solovayMap_isDecompressor (c : Code) (c₆₄ : ℕ) :
    isDecompressor (solovayMap c c₆₄) :=
  Partrec.bind (solovayRfind_partrec c c₆₄) (solovayOfOpt_partrec c c₆₄)

/-- A string enumerated in the snapshot at level `n` has plain prefix complexity at most `n`. -/
lemma KPPlain_le_of_mem_snapshotCodes {c : Code} {U : Map} (hc : IsCodeFor c U)
    {n t : ℕ} {y : BitString} (hy : y ∈ snapshotCodes c n t) :
    KPPlain U y ≤ (n : ENat) := by
  unfold snapshotCodes at hy
  rw [List.mem_filterMap] at hy
  obtain ⟨p, hp_mem, hp_run⟩ := hy
  rw [mem_boundedPrograms_iff] at hp_mem
  unfold runOut at hp_run
  cases h_ev : Code.evaln t c (Encodable.encode ((p, []) : BitString × BitString)) with
  | none =>
    rw [h_ev] at hp_run
    dsimp at hp_run
    contradiction
  | some r =>
    rw [h_ev] at hp_run
    dsimp at hp_run
    have hr_eval : r ∈ c.eval (Encodable.encode ((p, []) : BitString × BitString)) :=
      Code.evaln_sound h_ev
    rw [hc] at hr_eval
    rw [Part.mem_bind_iff] at hr_eval
    obtain ⟨a, ha_mem, hr_in⟩ := hr_eval
    rw [Part.mem_ofOption, Encodable.encodek] at ha_mem
    injection ha_mem with ha_eq
    subst a
    rw [Part.mem_map_iff] at hr_in
    obtain ⟨y', hy'_U, hr_eq⟩ := hr_in
    subst hr_eq
    rw [Encodable.encodek] at hp_run
    injection hp_run with hy_eq
    subst hy_eq
    have hprod : produces U p [] y' := hy'_U
    have hKP := KP_le_programLength_of_produces hprod
    unfold programLength at hKP
    exact le_trans hKP (by exact_mod_cast hp_mem)

/-- A string in the cumulative snapshot at level `n` has plain prefix complexity at most `n`. -/
lemma KPPlain_le_of_mem_cumSnapshotCodes {c : Code} {U : Map} (hc : IsCodeFor c U)
    {n t : ℕ} {y : BitString} (hy : y ∈ cumSnapshotCodes c (n, t)) :
    KPPlain U y ≤ (n : ENat) := by
  dsimp [cumSnapshotCodes] at hy
  rw [mem_eraseDups_bitString, List.mem_flatMap] at hy
  obtain ⟨s, _, hs⟩ := hy
  exact KPPlain_le_of_mem_snapshotCodes hc hs

/-- A cardinality bounded by `2 ^ (n + c) * 2 ^ -kn` in the extended reals is at most
`2 ^ (n - kn + c)`. -/
lemma card_le_of_ennreal_bound {A : Finset BitString} {n kn c : ℕ}
    (h : (A.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn) :
    A.card ≤ 2 ^ (n - kn + c) := by
  have h_mul : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ kn ≤ (2 : ℝ≥0∞) ^ (n + c) := by
    calc (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ kn
      _ ≤ ((2 : ℝ≥0∞) ^ (n + c) * (2 : ℝ≥0∞)⁻¹ ^ kn) * (2 : ℝ≥0∞) ^ kn := by gcongr
      _ = (2 : ℝ≥0∞) ^ (n + c) * ((2 : ℝ≥0∞)⁻¹ ^ kn * (2 : ℝ≥0∞) ^ kn) := by ring
      _ = (2 : ℝ≥0∞) ^ (n + c) * 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      _ = (2 : ℝ≥0∞) ^ (n + c) := by ring
  have h_nat : A.card * 2 ^ kn ≤ 2 ^ (n + c) := by exact_mod_cast h_mul
  by_cases hkn : kn ≤ n + c
  · have h_pow_eq : 2 ^ (n + c) = 2 ^ ((n + c) - kn) * 2 ^ kn := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    rw [h_pow_eq] at h_nat
    have h2pos : 0 < 2 ^ kn := Nat.two_pow_pos kn
    have h_le := Nat.le_of_mul_le_mul_right h_nat h2pos
    have h_sub_le : (n + c) - kn ≤ n - kn + c := by omega
    exact le_trans h_le (Nat.pow_le_pow_right (by norm_num) h_sub_le)
  · have h_lt : 2 ^ (n + c) < 2 ^ kn := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h_prod_lt : A.card * 2 ^ kn < 2 ^ kn := lt_of_le_of_lt h_nat h_lt
    have h_card0 : A.card = 0 := by
      by_contra h_ne
      have h1 : 1 ≤ A.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_ne)
      have h2 : 1 * 2 ^ kn ≤ A.card * 2 ^ kn := Nat.mul_le_mul_right _ h1
      rw [one_mul] at h2
      exact not_lt_of_ge h2 h_prod_lt
    rw [h_card0]
    exact Nat.zero_le _

/-- Two prefixes of a common list agree at every index below both their lengths. -/
lemma getD_eq_of_prefix_common {α : Type*} {l1 l2 L : List α} {d : α} {k : ℕ}
    (h1 : l1 <+: L) (h2 : l2 <+: L) (hk1 : k < l1.length) (hk2 : k < l2.length) :
    l1.getD k d = l2.getD k d := by
  rw [← StagedEnumeration.getD_eq_of_prefix l1 L h1 k d hk1,
      ← StagedEnumeration.getD_eq_of_prefix l2 L h2 k d hk2]

/-- When the check condition holds, the index read from the program is below the length of the
snapshot list. -/
lemma solovayCond_lt_length (cU : Code) (c₆₄ : ℕ) (w : BitString) (m_val : ℕ)
    (h_cond : solovayCond cU c₆₄ w m_val = true)
    (h_out : (solovayOut cU w m_val).isSome = true) :
    bitsToNat (w.drop m_val.unpair.1) < (solovayCodes cU c₆₄ (w, m_val)).length := by
  unfold solovayCond at h_cond
  rw [h_out] at h_cond
  cases h_eq : decide (Nat.bits (solovayKN cU (w, m_val)) = solovayOutStr cU (w, m_val)) with
  | false => rw [h_eq] at h_cond; contradiction
  | true =>
    rw [h_eq] at h_cond
    simp only [Bool.cond_true] at h_cond
    exact of_decide_eq_true h_cond

/-- At a stage where the halting count is maximal, the check succeeds on the program consisting
of a description of the level followed by a padded index into the snapshot list. -/
lemma solovayCheck_max_isSome (cU : Code) (c₆₄ : ℕ) (v u : BitString) (T_max kn n k : ℕ)
    (hv : runOut cU T_max v = some (natBits kn))
    (hkn_le : kn ≤ n)
    (hu_len : u.length = n - kn + c₆₄)
    (hu_nat : bitsToNat u = k)
    (hk_lt : k < (cumSnapshotCodes cU (n, T_max)).length) :
    (solovayCheck cU c₆₄ (v ++ u) (Nat.pair v.length T_max)).isSome = true := by
  set w := v ++ u
  set m_max := Nat.pair v.length T_max
  have hm_max_pair := Nat.unpair_pair v.length T_max
  have hm_max_1 : m_max.unpair.1 = v.length := congr_arg Prod.fst hm_max_pair
  have hm_max_2 : m_max.unpair.2 = T_max := congr_arg Prod.snd hm_max_pair
  unfold solovayCheck solovayCond
  dsimp [solovayOut]
  rw [hm_max_1, hm_max_2, List.take_left, hv]
  dsimp
  have h_kn : solovayKN cU (w, m_max) = kn := by
    dsimp [solovayKN, solovayOutStr, solovayOut]
    rw [hm_max_1, hm_max_2, List.take_left, hv]
    dsimp
    exact decodeBits_natBits kn
  rw [h_kn]
  have h_bits : Nat.bits kn = Option.getD (solovayOut cU w m_max) [] := by
    dsimp [solovayOut]
    rw [hm_max_1, hm_max_2, List.take_left, hv]
    rfl
  rw [h_bits]
  have h_sol_N : solovayN cU c₆₄ (w, m_max) = n := by
    dsimp [solovayN]
    rw [hm_max_1, List.drop_left, hu_len, h_kn]
    omega
  have h_codes : solovayCodes cU c₆₄ (w, m_max) = cumSnapshotCodes cU (n, T_max) := by
    dsimp [solovayCodes]
    rw [h_sol_N, hm_max_2]
  rw [h_codes, List.drop_left, hu_nat]
  have h_dec_lt : decide (k < (cumSnapshotCodes cU (n, T_max)).length) = true :=
    decide_eq_true hk_lt
  rw [h_dec_lt]
  simp [solovayOutStr]

end SolovayInequality

end Kolmogorov
