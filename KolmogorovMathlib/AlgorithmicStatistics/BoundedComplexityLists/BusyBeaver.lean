import KolmogorovMathlib.AlgorithmicStatistics.BoundedComplexityLists.OmegaCount

/-!
# VS40 Section 4, Milestone B2: completion time and busy beaver

This module formalizes the busy-beaver quantity `B(m)` (as the optional maximal
natural number of plain complexity at most `m`) and the enumeration completion
time `B'(m) = boundedOutputCompletionTime`, and proves the two uniform
argument-shift comparisons of `prop:busy-beavers`.

The plain machine is `V` with `hV : isOptimalConditional V`, connected to the
finite `evaln` snapshots by `hc : IsCodeFor c V`.  Small-bound nonexistence of a
busy-beaver maximum is kept explicit through `Option`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)
open Kolmogorov.CodedFiniteDistribution

/-! ### Bounded natural outputs and the busy-beaver maximum -/

/-- The natural numbers whose canonical binary code lies in the completed
bound-`m` output list.  Only genuinely canonical codes `w = Nat.bits (bitsToNat w)`
are retained, so `n ∈ boundedNatOutputs c m ↔ Nat.bits n ∈ completedBoundedOutput c m`. -/
noncomputable def boundedNatOutputs (c : Code) (m : ℕ) : Finset ℕ :=
  ((completedBoundedOutputFinset c m).filter (fun w => Nat.bits (bitsToNat w) = w)).image bitsToNat

theorem mem_boundedNatOutputs_iff_mem_completed (c : Code) (m n : ℕ) :
    n ∈ boundedNatOutputs c m ↔ Nat.bits n ∈ completedBoundedOutput c m := by
  unfold boundedNatOutputs completedBoundedOutputFinset
  simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨w, ⟨hwmem, hcanon⟩, rfl⟩
    rwa [hcanon]
  · intro h
    exact ⟨Nat.bits n, ⟨h, by rw [bitsToNat_bits]⟩, by rw [bitsToNat_bits]⟩

/-- **B2 machine-facing membership.** `n` is a bounded natural output iff its
plain complexity is at most `m`. -/
theorem mem_boundedNatOutputs_iff_plainKNat_le
    {V : Map} {c : Code} (hc : IsCodeFor c V) (m n : ℕ) :
    n ∈ boundedNatOutputs c m ↔ plainKNat V n ≤ (m : ENat) := by
  rw [mem_boundedNatOutputs_iff_mem_completed, mem_completedBoundedOutput_iff_plainK_le hc]
  rfl

/-- The busy-beaver number `B(m)`: the maximal natural number of plain complexity
at most `m`, or `none` when no such number exists (small bounds). -/
noncomputable def busyBeaver (c : Code) (m : ℕ) : Option ℕ :=
  (boundedNatOutputs c m).max

/-- **B2 finset-facing specification.** `busyBeaver c m = some b` iff `b` is the
maximum of `boundedNatOutputs c m`. -/
theorem busyBeaver_some_iff (c : Code) (m b : ℕ) :
    busyBeaver c m = some b ↔
      b ∈ boundedNatOutputs c m ∧ ∀ n ∈ boundedNatOutputs c m, n ≤ b := by
  unfold busyBeaver
  constructor
  · intro h
    refine ⟨Finset.mem_of_max h, fun n hn => ?_⟩
    have hle := Finset.le_max hn
    rw [show (boundedNatOutputs c m).max = (b : WithBot ℕ) from h] at hle
    exact WithBot.coe_le_coe.mp hle
  · rintro ⟨hb, hmax⟩
    change (boundedNatOutputs c m).max = (b : WithBot ℕ)
    exact le_antisymm (Finset.max_le (fun n hn => WithBot.coe_le_coe.mpr (hmax n hn)))
      (Finset.le_max hb)

theorem busyBeaver_eq_none_iff (c : Code) (m : ℕ) :
    busyBeaver c m = none ↔ boundedNatOutputs c m = ∅ := by
  unfold busyBeaver
  rw [← Finset.max_eq_bot]
  rfl

theorem busyBeaver_isSome_of_nonempty (c : Code) (m : ℕ)
    (h : (boundedNatOutputs c m).Nonempty) : ∃ b, busyBeaver c m = some b := by
  rcases Option.eq_none_or_eq_some (busyBeaver c m) with hn | hs
  · exact absurd ((busyBeaver_eq_none_iff c m).mp hn) h.ne_empty
  · exact hs

/-- **B2 machine-facing specification.** `busyBeaver c m = some b` iff `b` is the
maximal natural number of plain complexity at most `m`. -/
theorem busyBeaver_some_iff_plainKNat
    {V : Map} {c : Code} (hc : IsCodeFor c V) (m b : ℕ) :
    busyBeaver c m = some b ↔
      plainKNat V b ≤ (m : ENat) ∧ ∀ n, plainKNat V n ≤ (m : ENat) → n ≤ b := by
  rw [busyBeaver_some_iff]
  constructor
  · rintro ⟨hb, hmax⟩
    refine ⟨(mem_boundedNatOutputs_iff_plainKNat_le hc m b).mp hb, fun n hn => ?_⟩
    exact hmax n ((mem_boundedNatOutputs_iff_plainKNat_le hc m n).mpr hn)
  · rintro ⟨hb, hmax⟩
    refine ⟨(mem_boundedNatOutputs_iff_plainKNat_le hc m b).mpr hb, fun n hn => ?_⟩
    exact hmax n ((mem_boundedNatOutputs_iff_plainKNat_le hc m n).mp hn)

/-! ### Successor bound and strict busy-beaver growth -/

/-- **Successor bound.** The plain complexity of `n + 1` exceeds that of `n` by at
most a constant, via the computable successor map on canonical codes. -/
theorem plainKNat_succ_le (V : Map) (hV : isOptimalConditional V) :
    ∃ C : ℕ, ∀ n : ℕ, plainKNat V (n + 1) ≤ plainKNat V n + (C : ENat) := by
  have hg : Computable (fun w : BitString => Nat.bits (bitsToNat w + 1)) :=
    natBitsComputable.comp (Computable.succ.comp bitsToNat_computable)
  obtain ⟨C, hC⟩ := plainKMapLe V hV (fun w => Nat.bits (bitsToNat w + 1)) hg
  refine ⟨C, fun n => ?_⟩
  have hval := hC (Nat.bits n)
  rwa [bitsToNat_bits] at hval

/-- **Fixed-shift strict growth.** Whenever the busy-beaver maximum exists at bound
`m`, it strictly increases after a uniform shift `C`. -/
theorem busyBeaver_strict_shift (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m b, busyBeaver c m = some b →
      ∃ b', busyBeaver c (m + C) = some b' ∧ b < b' := by
  obtain ⟨C, hC⟩ := plainKNat_succ_le V hV
  refine ⟨C, fun m b hb => ?_⟩
  have hbK : plainKNat V b ≤ (m : ENat) :=
    ((busyBeaver_some_iff_plainKNat hc m b).mp hb).1
  have hsuccK : plainKNat V (b + 1) ≤ ((m + C : ℕ) : ENat) := by
    calc plainKNat V (b + 1) ≤ plainKNat V b + (C : ENat) := hC b
      _ ≤ (m : ENat) + (C : ENat) := by gcongr
      _ = ((m + C : ℕ) : ENat) := by rw [Nat.cast_add]
  have hmem : (b + 1) ∈ boundedNatOutputs c (m + C) :=
    (mem_boundedNatOutputs_iff_plainKNat_le hc (m + C) (b + 1)).mpr hsuccK
  obtain ⟨b', hb'⟩ := busyBeaver_isSome_of_nonempty c (m + C) ⟨b + 1, hmem⟩
  refine ⟨b', hb', ?_⟩
  have hle := ((busyBeaver_some_iff c (m + C) b').mp hb').2 (b + 1) hmem
  omega

/-! ### Completion-time reconstruction from the fixed-width Omega code -/

theorem decodeFixedWidthNatCode_primrec : Primrec decodeFixedWidthNatCode := by
  unfold decodeFixedWidthNatCode
  exact bitsToNat_primrec.comp Primrec.list_reverse

/-- Reconstruct the enumeration completion time from a fixed-width Omega code:
recover `m` from the width, decode the count, and search for the least stage
reaching that count. -/
noncomputable def completionFromOmega (c : Code) (z : BitString) : Part BitString :=
  (Nat.rfind (fun t => Part.some
    ((boundedOutputStage c (z.length - 1) t).length == decodeFixedWidthNatCode z))).map Nat.bits

theorem completionFromOmega_partrec (c : Code) : Partrec (completionFromOmega c) := by
  have hm : Primrec (fun p : BitString × ℕ => p.1.length - 1) :=
    Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1)
  have hstage : Primrec (fun p : BitString × ℕ => boundedOutputStage c (p.1.length - 1) p.2) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hm Primrec.snd)
  have hcount : Primrec (fun p : BitString × ℕ => decodeFixedWidthNatCode p.1) :=
    decodeFixedWidthNatCode_primrec.comp Primrec.fst
  have hcheck : Computable₂ (fun (z : BitString) (t : ℕ) =>
      (boundedOutputStage c (z.length - 1) t).length == decodeFixedWidthNatCode z) :=
    (Primrec.beq.comp (Primrec.list_length.comp hstage) hcount).to_comp.to₂
  have hrfind : Partrec (fun z : BitString =>
      Nat.rfind (fun t => Part.some
        ((boundedOutputStage c (z.length - 1) t).length == decodeFixedWidthNatCode z))) :=
    Partrec.rfind hcheck.partrec₂
  have hmapg : Computable₂ (fun (_ : BitString) (t : ℕ) => Nat.bits t) :=
    natBitsComputable.comp Computable.snd
  exact (hrfind.map hmapg).of_eq (fun z => rfl)

/-- On the fixed-width Omega code the reconstruction returns the binary code of the
completion time `B'(m)`. -/
theorem completionFromOmega_omegaFixedCode (c : Code) (m : ℕ) :
    Nat.bits (boundedOutputCompletionTime c m) ∈ completionFromOmega c (omegaFixedCode c m) := by
  have hwidth : (omegaFixedCode c m).length - 1 = m := by
    simp [omegaFixedCode_length]
  have hdec : decodeFixedWidthNatCode (omegaFixedCode c m) = omegaCount c m :=
    decode_omegaFixedCode c m
  have hTlen :
      (boundedOutputStage c m (boundedOutputCompletionTime c m)).length = omegaCount c m := by
    change (boundedOutputStage c m (boundedOutputCompletionTime c m)).length
      = (completedBoundedOutput c m).length
    exact boundedOutputCompletionTime_spec c m
  have hTsearch : boundedOutputCompletionTime c m ∈ Nat.rfind (fun t => Part.some
      ((boundedOutputStage c m t).length == omegaCount c m)) := by
    rw [Nat.mem_rfind]
    refine ⟨by simp [hTlen], ?_⟩
    intro n hn
    have hne : (boundedOutputStage c m n).length ≠ omegaCount c m := by
      intro heq
      have hle : boundedOutputCompletionTime c m ≤ n :=
        boundedOutputCompletionTime_le_complete_stage c m n heq
      omega
    simp [hne]
  unfold completionFromOmega
  rw [Part.mem_map_iff]
  refine ⟨boundedOutputCompletionTime c m, ?_, rfl⟩
  rw [hwidth, hdec]
  exact hTsearch

/-- **Forward completion-time bound.** The completion time `B'(m)` has plain
complexity at most `m + O(1)`, since it is reconstructible from the fixed-width
Omega code (of length `m + 1`). -/
theorem plainKNat_completionTime_le (V : Map) (hV : isOptimalConditional V) (c : Code) :
    ∃ C : ℕ, ∀ m,
      plainKNat V (boundedOutputCompletionTime c m) ≤ ((m + C : ℕ) : ENat) := by
  obtain ⟨Cmap, hmap⟩ :=
    plainK_partrec_map_le V hV (completionFromOmega c) (completionFromOmega_partrec c)
  obtain ⟨Clen, hlen⟩ := plainKLeLength V hV
  refine ⟨1 + Clen + Cmap, fun m => ?_⟩
  calc
    plainKNat V (boundedOutputCompletionTime c m)
        = plainK V (Nat.bits (boundedOutputCompletionTime c m)) := rfl
    _ ≤ plainK V (omegaFixedCode c m) + (Cmap : ENat) :=
        hmap _ _ (completionFromOmega_omegaFixedCode c m)
    _ ≤ (((omegaFixedCode c m).length : ENat) + (Clen : ENat)) + (Cmap : ENat) := by
        gcongr
        exact hlen _
    _ = (((m + 1 : ℕ) : ENat) + (Clen : ENat)) + (Cmap : ENat) := by
        rw [omegaFixedCode_length]
    _ = ((m + (1 + Clen + Cmap) : ℕ) : ENat) := by
        push_cast; ring

/-- **Forward busy-beaver comparison** `B'(m) ≤ B(m + C)`: the completion time is
bounded by the busy-beaver number at a uniform shift. -/
theorem boundedOutputCompletionTime_le_busyBeaver (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ, ∀ m, ∃ b,
      busyBeaver c (m + C) = some b ∧ boundedOutputCompletionTime c m ≤ b := by
  obtain ⟨C, hC⟩ := plainKNat_completionTime_le V hV c
  refine ⟨C, fun m => ?_⟩
  have hmem : boundedOutputCompletionTime c m ∈ boundedNatOutputs c (m + C) :=
    (mem_boundedNatOutputs_iff_plainKNat_le hc (m + C) _).mpr (by
      simpa [Nat.cast_add] using hC m)
  obtain ⟨b, hb⟩ := busyBeaver_isSome_of_nonempty c (m + C) ⟨_, hmem⟩
  exact ⟨b, hb, ((busyBeaver_some_iff c (m + C) b).mp hb).2 _ hmem⟩

/-! ### The late cutoff selector and the reverse comparison

The reverse comparison avoids any monotonicity assumption on the completion
time.  A total computable selector `lateCutoffSelector c (Nat.bits N)` returns a
length-`N+1` string missing from `boundedOutputStage c N N`; when the bound-`q`
enumeration has completed by time `N` (and `q ≤ N`), budget and time inclusion
place every complexity-`≤ q` string into that stage, so the missing string has
complexity greater than `q`. -/

theorem boundedOutputStage_length_lt (c : Code) (m t : ℕ) :
    (boundedOutputStage c m t).length < 2 ^ (m + 1) := by
  have h1 : (boundedOutputStage c m t).length = (boundedOutputStage c m t).toFinset.card :=
    (List.toFinset_card_of_nodup (boundedOutputStage_nodup c m t)).symm
  rw [h1, boundedOutputStage_toFinset_eq_snapshotCodes c m t]
  have h2 : (snapshotCodes c m t).toFinset.card ≤ (snapshotCodes c m t).length :=
    List.toFinset_card_le _
  have h3 : (snapshotCodes c m t).length ≤ (boundedPrograms m).length :=
    List.length_filterMap_le _ _
  have h4 := length_boundedPrograms_lt m
  omega

/-- The total cutoff selector: from `w = Nat.bits N`, examine the bound-`N`,
time-`N` stage and return the first length-`N+1` string missing from it. -/
noncomputable def lateCutoffSelector (c : Code) (w : BitString) : BitString :=
  ((canonicalFinsetList (stringsOfLength (bitsToNat w + 1))).find?
    (fun s => decide (s ∉ boundedOutputStage c (bitsToNat w) (bitsToNat w)))).getD []

theorem lateCutoffSelector_computable (c : Code) : Computable (lateCutoffSelector c) := by
  have hN : Primrec (fun w : BitString => bitsToNat w) := bitsToNat_primrec
  have hstage : Primrec (fun w : BitString =>
      boundedOutputStage c (bitsToNat w) (bitsToNat w)) :=
    (boundedOutputStage_primrec c).comp (Primrec.pair hN hN)
  have hstrings : Primrec (fun w : BitString =>
      canonicalFinsetList (stringsOfLength (bitsToNat w + 1))) :=
    canonicalFinsetList_toFinset_primrec.comp (allStrings_primrec.comp (Primrec.succ.comp hN))
  have hpred : Primrec₂ (fun (w : BitString) (s : BitString) =>
      decide (s ∉ boundedOutputStage c (bitsToNat w) (bitsToNat w))) := by
    refine (Primrec.not.comp
      (bitString_mem_primrec.comp Primrec.snd (hstage.comp Primrec.fst))).to₂.of_eq ?_
    intro w s; simp
  have hfind : Primrec (fun w : BitString =>
      (canonicalFinsetList (stringsOfLength (bitsToNat w + 1))).find?
        (fun s => decide (s ∉ boundedOutputStage c (bitsToNat w) (bitsToNat w)))) :=
    list_find?_primrec hstrings hpred
  exact (Primrec.option_getD.comp hfind (Primrec.const [])).to_comp

/-- The cutoff selector produces a length-`N+1` string that is missing from the
bound-`N` time-`N` stage. -/
theorem lateCutoffSelector_spec (c : Code) (N : ℕ) :
    (lateCutoffSelector c (Nat.bits N)).length = N + 1 ∧
    lateCutoffSelector c (Nat.bits N) ∉ boundedOutputStage c N N := by
  have hnodup : (boundedOutputStage c N N).Nodup := boundedOutputStage_nodup c N N
  have hlen : (boundedOutputStage c N N).length < 2 ^ (N + 1) := boundedOutputStage_length_lt c N N
  obtain ⟨x0, hx0all, hx0missing⟩ :=
    exists_mem_allStrings_not_mem_of_length_lt hnodup hlen
  have hx0len : x0.length = N + 1 := (mem_allStrings (N + 1) x0).mp hx0all
  have hx0full : x0 ∈ canonicalFinsetList (stringsOfLength (N + 1)) :=
    mem_canonicalFinsetList.mpr ((memStringsOfLength (N + 1) x0).mpr hx0len)
  obtain ⟨x, hxfind⟩ : ∃ x, (canonicalFinsetList (stringsOfLength (N + 1))).find?
      (fun s => decide (s ∉ boundedOutputStage c N N)) = some x := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    exact ⟨x0, hx0full, by simp [hx0missing]⟩
  have hxfull : x ∈ canonicalFinsetList (stringsOfLength (N + 1)) :=
    List.mem_of_find?_eq_some hxfind
  have hxlen : x.length = N + 1 :=
    (memStringsOfLength (N + 1) x).mp (mem_canonicalFinsetList.mp hxfull)
  have hxmissing : x ∉ boundedOutputStage c N N := by
    have := List.find?_some hxfind
    simpa using this
  have hsel : lateCutoffSelector c (Nat.bits N) = x := by
    unfold lateCutoffSelector
    rw [bitsToNat_bits, hxfind]
    rfl
  rw [hsel]
  exact ⟨hxlen, hxmissing⟩

theorem lateCutoffSelector_length (c : Code) (N : ℕ) :
    (lateCutoffSelector c (Nat.bits N)).length = N + 1 :=
  (lateCutoffSelector_spec c N).1

theorem lateCutoffSelector_not_mem (c : Code) (N : ℕ) :
    lateCutoffSelector c (Nat.bits N) ∉ boundedOutputStage c N N :=
  (lateCutoffSelector_spec c N).2

/-- **High complexity of the cutoff string.** If `q ≤ N` and the bound-`q`
enumeration has completed by time `N`, then the cutoff string has plain
complexity greater than `q`. -/
theorem lateCutoffSelector_high_complexity
    {V : Map} {c : Code} (hc : IsCodeFor c V) {q N : ℕ}
    (hqN : q ≤ N) (hdone : boundedOutputCompletionTime c q ≤ N) :
    (q : ENat) < plainK V (lateCutoffSelector c (Nat.bits N)) := by
  apply lt_of_not_ge
  intro hle
  have hmem_comp : lateCutoffSelector c (Nat.bits N) ∈ completedBoundedOutput c q :=
    (mem_completedBoundedOutput_iff_plainK_le hc q _).mpr hle
  have heq : boundedOutputStage c q N = completedBoundedOutput c q :=
    boundedOutputStage_eq_completed_of_completion_le c q N hdone
  have hmem_q : lateCutoffSelector c (Nat.bits N) ∈ boundedOutputStage c q N := heq ▸ hmem_comp
  have hmem_N : lateCutoffSelector c (Nat.bits N) ∈ boundedOutputStage c N N :=
    boundedOutputStage_mem_of_bound_le hqN hmem_q
  exact (lateCutoffSelector_not_mem c N) hmem_N

/-- **Cutoff complexity implication.** If `q ≤ N` and the bound-`q` enumeration
completes by time `N`, then `q` is below the complexity of `N` up to a uniform
constant.  This is the reverse-direction engine: `N` cannot be a very simple
description once it exceeds both `q` and the completion time `B'(q)`. -/
theorem lateCutoff_complexity_implication (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ c₀ : ℕ, ∀ q N : ℕ, q ≤ N → boundedOutputCompletionTime c q ≤ N →
      (q : ENat) < plainKNat V N + (c₀ : ENat) := by
  obtain ⟨Cmap, hmap⟩ := plainKMapLe V hV (lateCutoffSelector c) (lateCutoffSelector_computable c)
  refine ⟨Cmap, fun q N hqN hdone => ?_⟩
  calc (q : ENat) < plainK V (lateCutoffSelector c (Nat.bits N)) :=
        lateCutoffSelector_high_complexity hc hqN hdone
    _ ≤ plainK V (Nat.bits N) + (Cmap : ENat) := hmap (Nat.bits N)
    _ = plainKNat V N + (Cmap : ENat) := rfl

/-- Monotonicity of the busy-beaver value in the complexity bound. -/
theorem busyBeaver_mono {V : Map} {c : Code} (hc : IsCodeFor c V) {m m' b : ℕ}
    (hmm : m ≤ m') (hb : busyBeaver c m = some b) :
    ∃ b', busyBeaver c m' = some b' ∧ b ≤ b' := by
  have hbmem : b ∈ boundedNatOutputs c m := ((busyBeaver_some_iff c m b).mp hb).1
  have hbmem' : b ∈ boundedNatOutputs c m' := by
    rw [mem_boundedNatOutputs_iff_plainKNat_le hc] at hbmem ⊢
    exact le_trans hbmem (by exact_mod_cast hmm)
  obtain ⟨b', hb'⟩ := busyBeaver_isSome_of_nonempty c m' ⟨b, hbmem'⟩
  exact ⟨b', hb', ((busyBeaver_some_iff c m' b').mp hb').2 b hbmem'⟩

/-- Eventually `log k + A ≤ k`: past a uniform threshold the binary length of `k`
plus any constant `A` is dominated by `k` itself.  This "linear beats log" bound
lets the reverse comparison discard the small-argument regime. -/
theorem bits_length_add_le_self_of_large (A : ℕ) :
    ∃ M₀ : ℕ, ∀ k : ℕ, M₀ ≤ k → (Nat.bits k).length + A ≤ k := by
  refine ⟨(A + 3) * (A + 3), fun k hk => ?_⟩
  have hbits : (Nat.bits k).length ≤ Nat.sqrt k + 2 := bits_length_le_sqrt_add_two k
  have h1 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  have h2 : A + 3 ≤ Nat.sqrt k := by
    have := Nat.sqrt_le_sqrt hk
    rwa [Nat.sqrt_eq] at this
  have h3 : 2 * Nat.sqrt k ≤ Nat.sqrt k * Nat.sqrt k :=
    Nat.mul_le_mul_right (Nat.sqrt k) (by omega)
  omega

/-- **Reverse busy-beaver comparison** `B(m) ≤ B'(m + C)` (for every shift `C`
past a uniform threshold), with no completion-time monotonicity assumption.  For
`m + C ≤ b` the cutoff implication (at `q = m + C`, `N = b`) forces `C < c₀`; for
`b < m + C` it (at `q = N = m + C`) forces `m + C < log(m + C) + O(1)`, false once
`m + C` is large.  Taking the shift past both thresholds rules out both. -/
theorem busyBeaver_le_completionTime_shift (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C₀ : ℕ, ∀ C, C₀ ≤ C → ∀ m b, busyBeaver c m = some b →
      b ≤ boundedOutputCompletionTime c (m + C) := by
  obtain ⟨c₀, hc₀⟩ := lateCutoff_complexity_implication V hV c hc
  obtain ⟨Clen, hClen⟩ := plainKNatLeLength V hV
  obtain ⟨M₀, hM₀⟩ := bits_length_add_le_self_of_large (Clen + c₀)
  refine ⟨max c₀ M₀, fun C hC₀C m b hb => ?_⟩
  have hc0C : c₀ ≤ C := le_trans (le_max_left c₀ M₀) hC₀C
  have hM0C : M₀ ≤ C := le_trans (le_max_right c₀ M₀) hC₀C
  by_contra hlt
  push Not at hlt
  have hbK : plainKNat V b ≤ (m : ENat) := ((busyBeaver_some_iff_plainKNat hc m b).mp hb).1
  by_cases hcase : m + C ≤ b
  · have himpl := hc₀ (m + C) b hcase (le_of_lt hlt)
    have hchain : ((m + C : ℕ) : ENat) < ((m + c₀ : ℕ) : ENat) :=
      calc ((m + C : ℕ) : ENat) < plainKNat V b + (c₀ : ENat) := himpl
        _ ≤ (m : ENat) + (c₀ : ENat) := by gcongr
        _ = ((m + c₀ : ℕ) : ENat) := by rw [Nat.cast_add]
    have hCC : m + C < m + c₀ := by exact_mod_cast hchain
    omega
  · push Not at hcase
    have hdone : boundedOutputCompletionTime c (m + C) ≤ m + C := by omega
    have himpl := hc₀ (m + C) (m + C) (le_refl _) hdone
    have hMle : M₀ ≤ m + C := le_trans hM0C (Nat.le_add_left C m)
    have hbig : (Nat.bits (m + C)).length + (Clen + c₀) ≤ m + C := hM₀ (m + C) hMle
    have hupper : plainKNat V (m + C) ≤ ((Nat.bits (m + C)).length : ENat) + (Clen : ENat) := by
      have h := hClen (m + C); simpa [programLength] using h
    have hchain : ((m + C : ℕ) : ENat) < (((Nat.bits (m + C)).length + Clen + c₀ : ℕ) : ENat) :=
      calc ((m + C : ℕ) : ENat) < plainKNat V (m + C) + (c₀ : ENat) := himpl
        _ ≤ (((Nat.bits (m + C)).length : ENat) + (Clen : ENat)) + (c₀ : ENat) := by gcongr
        _ = (((Nat.bits (m + C)).length + Clen + c₀ : ℕ) : ENat) := by push_cast; ring
    have hlt2 : m + C < (Nat.bits (m + C)).length + Clen + c₀ := by exact_mod_cast hchain
    omega

/-- **B2 endpoint: `prop:busy-beavers`.** The busy-beaver number `B(m)` and the
enumeration completion time `B'(m) = boundedOutputCompletionTime` coincide up to a
uniform `O(1)` change of argument, in both directions.  Small-bound nonexistence of
`B` remains visible through `Option`. -/
theorem prop_busy_beavers
    (V : Map) (hV : isOptimalConditional V)
    (c : Code) (hc : IsCodeFor c V) :
    ∃ C : ℕ,
      (∀ m, ∃ b,
        busyBeaver c (m + C) = some b ∧
        boundedOutputCompletionTime c m ≤ b) ∧
      (∀ m b,
        busyBeaver c m = some b →
        b ≤ boundedOutputCompletionTime c (m + C)) := by
  obtain ⟨Cf, hf⟩ := boundedOutputCompletionTime_le_busyBeaver V hV c hc
  obtain ⟨Cr, hr⟩ := busyBeaver_le_completionTime_shift V hV c hc
  refine ⟨max Cf Cr, ?_, ?_⟩
  · intro m
    obtain ⟨b, hb, hle⟩ := hf m
    obtain ⟨b', hb', hbb'⟩ := busyBeaver_mono hc (by omega : m + Cf ≤ m + max Cf Cr) hb
    exact ⟨b', hb', le_trans hle hbb'⟩
  · intro m b hb
    exact hr (max Cf Cr) (le_max_right Cf Cr) m b hb

end Kolmogorov
