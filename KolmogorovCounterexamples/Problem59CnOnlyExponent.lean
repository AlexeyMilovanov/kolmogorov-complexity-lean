/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib

/-!
# The `O(C n)`-only exponent in Problem 59 is false

Problem 59 (SUV, p. 45) bounds the fraction of `n`-bit conditions `r` for which a
computable transformation `f` increases the information `I(x : y)` by more than `l`
by `2 ^ (-l + O(C n + C l))`.  The modelling mistake closed here is the reading in
which the `C l` summand is dropped, i.e. the exponent `-l + O(C n)`: for the
projection `f (x, r) = r` no constant `c` makes the bound
`2 ^ (-l + c (C n + 1))` true, so any formalisation of Problem 59 with that
exponent is refutable.  The true statement, with the book's exponent, is
`Kolmogorov.levin_information_conservation`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open StagedEnumeration CodedFiniteDistribution
open Kolmogorov.CodedFiniteDistribution

/-- The projection `f (x, r) = r`, a partial computable function of two
arguments. -/
def conditionProjection : BitString × BitString →. BitString := fun p => Part.some p.2

/-- The projection is partial computable. -/
lemma conditionProjection_partrec : Partrec conditionProjection := Computable.partrec Computable.snd

/-- Output of the auxiliary decompressor on program `q` with condition `r`. -/
def shiftDecompressorOutput (q r : BitString) : BitString :=
  pairCode (Nat.bits q.length) (r.drop (q.length + 1) ++ q)

/-- The auxiliary decompressor used to refute the `O(C n)` exponent. -/
def shiftDecompressor : Map := fun qr => Part.some (shiftDecompressorOutput qr.1 qr.2)

/-- The auxiliary decompressor is computable. -/
lemma shiftDecompressorOutput_computable :
    Computable (fun qr : BitString × BitString => shiftDecompressorOutput qr.1 qr.2) := by
  have hlen : Computable (fun qr : BitString × BitString => qr.1.length) :=
    Primrec.list_length.to_comp.comp Computable.fst
  have hsucc : Computable (fun qr : BitString × BitString => qr.1.length + 1) :=
    Primrec.succ.to_comp.comp hlen
  have hbits : Computable (fun qr : BitString × BitString => Nat.bits qr.1.length) :=
    natBits_computable.comp hlen
  have hdrop : Computable (fun qr : BitString × BitString =>
      qr.2.drop (qr.1.length + 1)) :=
    primrec_list_drop.to_comp.comp Computable.snd hsucc
  have happ : Computable (fun qr : BitString × BitString =>
      qr.2.drop (qr.1.length + 1) ++ qr.1) :=
    Primrec.list_append.to_comp.comp hdrop Computable.fst
  have hmain : Computable (fun qr : BitString × BitString =>
      pairCode (Nat.bits qr.1.length) (qr.2.drop (qr.1.length + 1) ++ qr.1)) :=
    Computable₂.comp pairCode_computable hbits happ
  exact hmain

/-- The auxiliary decompressor is a decompressor. -/
lemma shiftDecompressor_isDecompressor : isDecompressor shiftDecompressor :=
  Computable.partrec shiftDecompressorOutput_computable

/-- The key hit lemma: for every `(k + 1)`-bit prefix `pre` the string
`pre ++ w.take (n - 1 - k)` is an `n`-bit condition from which a program of
length exactly `k` produces `pairCode (Nat.bits k) w`. -/
lemma shiftDecompressorOutput_hit {k n : ℕ} (hk : k + 1 ≤ n) {w pre : BitString}
    (hw : w.length = n - 1) (hpre : pre.length = k + 1) :
    shiftDecompressorOutput (w.drop (n - 1 - k)) (pre ++ w.take (n - 1 - k)) =
      pairCode (Nat.bits k) w := by
  have hq : (w.drop (n - 1 - k)).length = k := by
    rw [List.length_drop, hw]; omega
  unfold shiftDecompressorOutput
  rw [hq]
  congr 1
  have hdrop : (pre ++ w.take (n - 1 - k)).drop (k + 1) = w.take (n - 1 - k) := by
    rw [← hpre]; exact List.drop_left
  rw [hdrop, List.take_append_drop]

/-- Pigeonhole: a finite set with at least `2 ^ (L + 1)` elements contains a
string of plain complexity greater than `L`. -/
lemma exists_incompressible_mem (U : Map) (L : ℕ) (F : Finset BitString)
    (hF : 2 ^ (L + 1) ≤ F.card) : ∃ z ∈ F, (L : ℕ∞) < plainK U z := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hsub : F ⊆ compressibleWords U [] L := by
    intro z hz
    have hle : plainK U z ≤ (L : ℕ∞) := hcon z hz
    rw [compressibleWords, Finset.mem_filter]
    refine ⟨?_, hle⟩
    have hlt : condK U z [] < ((L + 1 : ℕ) : ℕ∞) := by
      refine lt_of_le_of_lt hle ?_
      exact_mod_cast Nat.lt_succ_self L
    obtain ⟨len, hmem, hvlt⟩ := (sInf_lt_iff).mp hlt
    obtain ⟨p, hp_prod, rfl⟩ := hmem
    have hlen_le : programLength p ≤ L := by
      have h2 : ((programLength p : ℕ) : ℕ∞) < ((L + 1 : ℕ) : ℕ∞) := hvlt
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)
    rw [generatedWords, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, mem_programsLe L p hlen_le, progToOut_eq_some.mpr hp_prod⟩
  have h1 := Finset.card_le_card hsub
  have h2 := card_compressibleWordsLt U [] L
  omega

/-- The encoding `(k, w) ↦ pairCode (Nat.bits k) w`. -/
def lengthTaggedCode (p : ℕ × BitString) : BitString := pairCode (Nat.bits p.1) p.2

/-- The encoding `(k, w) ↦ pairCode (Nat.bits k) w` is injective. -/
lemma lengthTaggedCode_injective : Function.Injective lengthTaggedCode := by
  rintro ⟨a, u⟩ ⟨b, v⟩ h
  have h1 : Nat.bits a = Nat.bits b := by
    have h' := congrArg decodeFirst h
    simpa [lengthTaggedCode, decodeFirst_pairCode] using h'
  have h2 : u = v := by
    have h' := congrArg decodeSecond h
    simpa [lengthTaggedCode, decodeSecond_pairCode] using h'
  have h3 : a = b := by
    have h' := congrArg bitsToNat h1
    simpa [bitsToNat_bits] using h'
  simp [h3, h2]

/-- The family of `n * 2 ^ (n - 1)` strings used in the refutation. -/
noncomputable def refutationFamily (n : ℕ) : Finset BitString :=
  (Finset.range n ×ˢ stringsOfLength (n - 1)).image lengthTaggedCode

/-- The refutation family has `n * 2 ^ (n - 1)` members. -/
lemma refutationFamily_card (n : ℕ) : (refutationFamily n).card = n * 2 ^ (n - 1) := by
  rw [refutationFamily, Finset.card_image_of_injective _ lengthTaggedCode_injective,
    Finset.card_product, Finset.card_range, card_stringsOfLength]

open Classical in
/-- Every extension of the common suffix by a `(k+1)`-bit prefix is an `n`-bit condition that
raises the information about `z` by more than `l`: the shift decompressor recovers `z` from such
a condition with a `k`-bit program. -/
private lemma extendedPrefixes_subset_infoGap_filter {U : Map} {c₁ : ℕ}
    (hc₁ : ∀ x y : BitString, condK U x y ≤ condK shiftDecompressor x y + (c₁ : ℕ∞))
    {k n l : ℕ} (hk : k < n) {w suf z : BitString}
    (hw : w.length = n - 1) (hsufdef : suf = w.take (n - 1 - k))
    (hsuf_len : suf.length = n - 1 - k) (hz : z = pairCode (Nat.bits k) w)
    (hl_eq : cVal U z = k + c₁ + 1 + l) :
    ((allStrings (k + 1)).map (fun pre => pre ++ suf)) ⊆
      (allStrings n).filter (fun r => decide (∃ v ∈ conditionProjection (([] : BitString), r),
        info U [] z + (l : ℤ) < info U v z)) := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨pre, hpre_mem, hpre_eq⟩ := hr
  have hpre : pre.length = k + 1 := (mem_allStrings _ _).mp hpre_mem
  have hrlen : r.length = n := by
    rw [← hpre_eq, List.length_append, hpre, hsuf_len]; omega
  -- a short `shiftDecompressor`-program for z given r
  have hq_len : (w.drop (n - 1 - k)).length = k := by
    rw [List.length_drop, hw]; omega
  have hhit : shiftDecompressorOutput (w.drop (n - 1 - k)) r = z := by
    rw [← hpre_eq, hsufdef, hz]
    exact shiftDecompressorOutput_hit (by omega) hw hpre
  have hprod : z ∈ shiftDecompressor (w.drop (n - 1 - k), r) := by
    change z ∈ Part.some (shiftDecompressorOutput (w.drop (n - 1 - k)) r)
    rw [hhit]
    exact Part.mem_some z
  have hD_le : condK shiftDecompressor z r ≤ ((k : ℕ) : ℕ∞) := by
    refine sInf_le ⟨w.drop (n - 1 - k), hprod, ?_⟩
    rw [show programLength (w.drop (n - 1 - k)) = k from hq_len]
  have hU_le : condK U z r ≤ ((k + c₁ : ℕ) : ℕ∞) := by
    calc condK U z r ≤ condK shiftDecompressor z r + (c₁ : ℕ∞) := hc₁ z r
      _ ≤ ((k : ℕ) : ℕ∞) + (c₁ : ℕ∞) := by gcongr
      _ = ((k + c₁ : ℕ) : ℕ∞) := by push_cast; ring
  have hne2 : condK U z r ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hU_le
  have hCond : condCVal U z r ≤ k + c₁ := by
    have h := hU_le
    rw [← ENat.natCast_toNat hne2] at h
    exact_mod_cast h
  rw [List.mem_filter]
  refine ⟨(mem_allStrings _ _).mpr hrlen, ?_⟩
  refine decide_eq_true ⟨r, Part.mem_some r, ?_⟩
  have hinfo0 : info U [] z = 0 := by
    change ((cVal U z : ℤ) - (condCVal U z [] : ℤ)) = 0
    have h0 : condCVal U z [] = cVal U z := rfl
    rw [h0]; ring
  have hinfor : info U r z = (cVal U z : ℤ) - (condCVal U z r : ℤ) := rfl
  rw [hinfo0, hinfor]
  have : (condCVal U z r : ℤ) + (l : ℤ) < (cVal U z : ℤ) := by
    have hc1 : (condCVal U z r : ℤ) ≤ ((k + c₁ : ℕ) : ℤ) := by exact_mod_cast hCond
    have hc2 : (cVal U z : ℤ) = ((k + c₁ + 1 + l : ℕ) : ℤ) := by exact_mod_cast hl_eq
    push_cast at hc1 hc2 ⊢
    omega
  linarith

open Classical in
/-- **The exponent `2 ^ (-l + O(C n))` of Exercise 59 is false.**

For the projection `f (x, r) = r` there is no constant `c` for which the
probability of `I (f (x, r) : y) > I (x : y) + l` is at most
`2 ^ (-l + c * (C n + 1))`.  The witnesses are `x = []`, `n = 2 ^ m`, and a
string `y` of high complexity in the family `refutationFamily n`, whose `n * 2 ^ (n-1)`
members are all reachable, from many `n`-bit conditions, by short programs of
`shiftDecompressor`.  This is why the book's exponent carries the extra summand `C l`. -/
theorem information_conservation_Cn_only_exponent_false (U : Map) (hU : isOptimalConditional U) :
    ¬ ∃ c : ℕ, ∀ (x y : BitString) (n l : ℕ),
      ((((allStrings n).filter (fun r => decide (∃ v ∈ conditionProjection (x, r),
            info U x y + (l : ℤ) < info U v y))).length : ℝ)) / (2 : ℝ) ^ n
        ≤ (2 : ℝ) ^ (-(l : ℤ) + (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1)) := by
  rintro ⟨c, hc⟩
  obtain ⟨c₁, hc₁⟩ := hU.2 shiftDecompressor shiftDecompressor_isDecompressor
  obtain ⟨c_len, hc_len⟩ := plainK_le_length U hU
  -- every plain complexity is finite
  have hpne : ∀ s : BitString, plainK U s ≠ ⊤ := by
    intro s
    refine ne_top_of_le_ne_top ?_ (hc_len s)
    exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _⟩
  have hpk : ∀ s : BitString, plainK U s = ((cVal U s : ℕ) : ℕ∞) := by
    intro s; exact (ENat.natCast_toNat (hpne s)).symm
  -- the computable map  bits m ↦ bits (2 ^ m)
  have hpow : Computable (fun s : BitString => Nat.bits (2 ^ bitsToNat s)) := by
    have hpp : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
    have h2 : Computable (fun s : BitString => 2 ^ bitsToNat s) :=
      (Primrec₂.comp hpp (Primrec.const 2) bitsToNat_primrec).to_comp
    exact natBits_computable.comp h2
  obtain ⟨c₂, hc₂⟩ := plainK_map_le U hU (fun s : BitString => Nat.bits (2 ^ bitsToNat s)) hpow
  -- the parameters
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 2 + c_len + c₂ := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = 2 + c₁ + c * B := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = K + 2 * c + 2 := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = 2 * P := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = 2 ^ t := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = 2 ^ m := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ, S = c * t + c * B := ⟨_, rfl⟩
  -- the arithmetic core:  K + c * t < m
  have hPpos : 0 < P := by omega
  have hPlt : P < 2 ^ P := Nat.lt_two_pow_self
  have hmP : m = 2 ^ P * 2 ^ P := by rw [hmdef, htdef, two_mul, pow_add]
  have hsq : P * P < 2 ^ P * 2 ^ P := Nat.mul_lt_mul_of_lt_of_lt hPlt hPlt
  have hlin : (2 * c + 1) * P < P * P := by
    have h2c : 2 * c + 1 < P := by omega
    exact Nat.mul_lt_mul_of_lt_of_le h2c (le_refl P) hPpos
  have hKct : 2 + c₁ + S < m := by
    have e1 : (2 * c + 1) * P = c * t + P := by rw [htdef]; ring
    omega
  -- m is large
  have htge : 4 ≤ t := by omega
  have hmge : 4 ≤ m := by
    rw [hmdef]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnge : 4 ≤ n := by
    rw [hndef]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the complexity of n is small
  have hlogm : Nat.log 2 m = t := by rw [hmdef]; exact Nat.log_pow (by norm_num) t
  have hCn : cVal U (Nat.bits n) + 1 ≤ t + B := by
    have h1 : plainK U (Nat.bits n) ≤ plainK U (Nat.bits m) + (c₂ : ℕ∞) := by
      have h := hc₂ (Nat.bits m)
      have e2 : Nat.bits (2 ^ bitsToNat (Nat.bits m)) = Nat.bits n := by
        rw [bitsToNat_bits, hndef]
      rwa [e2] at h
    have h2 : plainK U (Nat.bits m) ≤ (((Nat.bits m).length : ℕ) : ℕ∞) + (c_len : ℕ∞) :=
      hc_len (Nat.bits m)
    have h3 : (Nat.bits m).length ≤ t + 1 := by
      have := length_natBits_le_log m
      omega
    have h4 : plainK U (Nat.bits n) ≤ ((t + 1 + c_len + c₂ : ℕ) : ℕ∞) := by
      calc plainK U (Nat.bits n) ≤ plainK U (Nat.bits m) + (c₂ : ℕ∞) := h1
        _ ≤ ((((Nat.bits m).length : ℕ) : ℕ∞) + (c_len : ℕ∞)) + (c₂ : ℕ∞) := by gcongr
        _ ≤ (((t + 1 : ℕ) : ℕ∞) + (c_len : ℕ∞)) + (c₂ : ℕ∞) := by
              have h3' : (((Nat.bits m).length : ℕ) : ℕ∞) ≤ ((t + 1 : ℕ) : ℕ∞) := by
                exact_mod_cast h3
              gcongr
        _ = ((t + 1 + c_len + c₂ : ℕ) : ℕ∞) := by push_cast; ring
    rw [hpk (Nat.bits n)] at h4
    have h5 : cVal U (Nat.bits n) ≤ t + 1 + c_len + c₂ := by exact_mod_cast h4
    omega
  -- pick a complex member of the family
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = n + m - 3 := ⟨_, rfl⟩
  have hcard : 2 ^ (L + 1) ≤ (refutationFamily n).card := by
    rw [refutationFamily_card]
    have h1 : n * 2 ^ (n - 1) = 2 ^ (m + (n - 1)) := by rw [pow_add, hndef]
    rw [h1]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨z, hz_mem, hz_complex⟩ := exists_incompressible_mem U L (refutationFamily n) hcard
  rw [refutationFamily, Finset.mem_image] at hz_mem
  obtain ⟨⟨k, w⟩, hkw_mem, hz_eq⟩ := hz_mem
  rw [Finset.mem_product] at hkw_mem
  have hk : k < n := Finset.mem_range.mp hkw_mem.1
  have hw : w.length = n - 1 := (mem_stringsOfLength _ _).mp hkw_mem.2
  have hz : z = pairCode (Nat.bits k) w := by rw [← hz_eq]; rfl
  -- the complexity of z
  have hcz : L < cVal U z := by
    rw [hpk z] at hz_complex
    exact_mod_cast hz_complex
  -- the parameter l
  obtain ⟨l, hldef⟩ : ∃ l : ℕ, l = cVal U z - k - c₁ - 1 := ⟨_, rfl⟩
  have hl_eq : cVal U z = k + c₁ + 1 + l := by omega
  -- the good conditions
  obtain ⟨suf, hsufdef⟩ : ∃ s : BitString, s = w.take (n - 1 - k) := ⟨_, rfl⟩
  have hsuf_len : suf.length = n - 1 - k := by
    rw [hsufdef, List.length_take, hw]; omega
  have hRsub : ((allStrings (k + 1)).map (fun pre => pre ++ suf)) ⊆
      (allStrings n).filter (fun r => decide (∃ v ∈ conditionProjection (([] : BitString), r),
        info U [] z + (l : ℤ) < info U v z)) :=
    extendedPrefixes_subset_infoGap_filter hc₁ hk hw hsufdef hsuf_len hz hl_eq
  have hcount : 2 ^ (k + 1) ≤
      ((allStrings n).filter (fun r => decide (∃ v ∈ conditionProjection (([] : BitString), r),
        info U [] z + (l : ℤ) < info U v z))).length := by
    have hnd : ((allStrings (k + 1)).map (fun pre => pre ++ suf)).Nodup := by
      refine (allStrings_nodup (k + 1)).map ?_
      intro a b hab
      exact List.append_cancel_right hab
    have h := (hnd.subperm hRsub).length_le
    rwa [List.length_map, length_allStrings] at h
  -- feed the assumed bound
  have hmain := hc [] z n l
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hlenR : ((2 : ℝ) ^ (k + 1)) ≤
      (((allStrings n).filter (fun r => decide (∃ v ∈ conditionProjection (([] : BitString), r),
        info U [] z + (l : ℤ) < info U v z))).length : ℝ) := by
    exact_mod_cast hcount
  have hreal : ((2 : ℝ) ^ (k + 1)) / (2 : ℝ) ^ n ≤
      (2 : ℝ) ^ (-(l : ℤ) + (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1)) := by
    refine le_trans ?_ hmain
    gcongr
  have hzpow : ((2 : ℝ) ^ (k + 1)) / (2 : ℝ) ^ n = (2 : ℝ) ^ (((k : ℤ) + 1) - (n : ℤ)) := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
      show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast]
  rw [hzpow] at hreal
  have hexp : ((k : ℤ) + 1) - (n : ℤ) ≤
      -(l : ℤ) + (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1) :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hreal
  have hCn' : (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1) ≤ (S : ℤ) := by
    have h1 : ((cVal U (Nat.bits n) : ℤ) + 1) ≤ ((t + B : ℕ) : ℤ) := by exact_mod_cast hCn
    calc (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1) ≤ (c : ℤ) * ((t + B : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (S : ℤ) := by rw [hSdef]; push_cast; ring
  have hfin : ((k : ℤ) + 1) - (n : ℤ) ≤ -(l : ℤ) + (S : ℤ) := le_trans hexp (by linarith)
  omega

open Classical in
/-- The statement proved by `levin_information_conservation` — with the
exponent `-l + c * (C n + 1)` — is inconsistent: instantiating it at the
computable projection `f (x, r) = r` contradicts
`information_conservation_Cn_only_exponent_false`.  The book's exponent
`-l + O (C n + C l)` is the correct one. -/
theorem information_conservation_Cn_only_exponent_unprovable (U : Map)
    (hU : isOptimalConditional U) :
    ¬ ∀ (f : BitString × BitString →. BitString), Partrec f →
      ∃ c : ℕ, ∀ (x y : BitString) (n l : ℕ),
        ((((allStrings n).filter (fun r => decide (∃ v ∈ f (x, r),
              info U x y + (l : ℤ) < info U v y))).length : ℝ)) / (2 : ℝ) ^ n
          ≤ (2 : ℝ) ^ (-(l : ℤ) + (c : ℤ) * ((cVal U (Nat.bits n) : ℤ) + 1)) := by
  intro h
  exact information_conservation_Cn_only_exponent_false U hU
    (h conditionProjection conditionProjection_partrec)

end Kolmogorov
