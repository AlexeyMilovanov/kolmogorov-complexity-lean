import KolmogorovMathlib.Restricted.FamilyCurve.RunChain
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredVocabulary
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredRun
import KolmogorovMathlib.Restricted.FamilyCurve.RunBounds
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain.PrefixRuns
import KolmogorovMathlib.Foundation.BigOperators
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# The version count of an anchored rebuild is a square-root slack

The bound that keeps the anchored construction affordable:
`anchoredVersionExp_le_sqrtSlack` shows that for a family of polynomial covering overhead the
version-count exponent is a genuine square-root slack. The estimates leading there are the
arithmetic core `version_count_arith`, the volume bound on the processed bad union
(`restrictedAnchored_bad_subset_processed`,
`restrictedAnchoredProcessedBadUnion_card_lt`), the counting bounds on the event stream
(`restrictedAnchoredEventChain_root_live_bound`, `restrictedAnchoredEventChain_L_card_le`,
`restrictedAnchoredEventChain_S_sum_le`), and the two binary-length lemmas that convert the
ambient budget and the overhead into logarithmically many bits.
-/

namespace Kolmogorov
section CountInstantiation
open Nat.Partrec (Code)

/-- The arithmetic core of the version-count bound. -/
lemma version_count_arith {I Δm mesh LN Lob NN OB s : ℕ}
    (hNN : NN + 1 ≤ 2 ^ LN) (hOB : OB ≤ 2 ^ Lob) (hs : s ≤ NN) :
    (s + 1) * (NN * 2 ^ (I + 1) + 1 +
        2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4))) ≤
      2 ^ (I + ((NN + 1) * Lob + 2 * LN + Δm + mesh + 9)) := by
  set E : ℕ := I + (NN + 1) * Lob + LN + Δm + mesh + 5 with hE
  have hNN' : NN ≤ 2 ^ LN := by omega
  have hOBpow : OB ^ (s + 1) ≤ 2 ^ ((NN + 1) * Lob) := by
    calc OB ^ (s + 1) ≤ (2 ^ Lob) ^ (s + 1) := Nat.pow_le_pow_left hOB _
      _ = 2 ^ (Lob * (s + 1)) := by rw [← pow_mul]
      _ ≤ 2 ^ ((NN + 1) * Lob) := by
          apply Nat.pow_le_pow_right (by omega)
          calc Lob * (s + 1) ≤ Lob * (NN + 1) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = (NN + 1) * Lob := Nat.mul_comm _ _
  have h1 : NN * 2 ^ (I + 1) ≤ 2 ^ E := by
    refine le_trans (mul_pow_le_pow_add hNN' le_rfl) ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (1 : ℕ) ≤ 2 ^ E := Nat.one_le_two_pow
  have h3 : 2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)) ≤ 2 ^ E := by
    have ha : 2 * OB ^ (s + 1) ≤ 2 ^ (1 + (NN + 1) * Lob) :=
      mul_pow_le_pow_add (by omega) hOBpow
    have hb : NN * 2 ^ (I + Δm + mesh + 4) ≤
        2 ^ (LN + (I + Δm + mesh + 4)) :=
      mul_pow_le_pow_add hNN' le_rfl
    refine le_trans (mul_pow_le_pow_add ha hb) ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hbr : NN * 2 ^ (I + 1) + 1 +
      2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)) ≤ 2 ^ (E + 2) := by
    have h4 : (2:ℕ) ^ (E + 2) = 4 * 2 ^ E := by
      rw [pow_add]
      ring
    omega
  calc (s + 1) * (NN * 2 ^ (I + 1) + 1 +
        2 * OB ^ (s + 1) * (NN * 2 ^ (I + Δm + mesh + 4)))
      ≤ 2 ^ LN * 2 ^ (E + 2) :=
        Nat.mul_le_mul (by omega) hbr
    _ = 2 ^ (LN + (E + 2)) := (pow_add 2 LN (E + 2)).symm
    _ ≤ 2 ^ (I + ((NN + 1) * Lob + 2 * LN + Δm + mesh + 9)) :=
        Nat.pow_le_pow_right (by omega) (by omega)

/-- Every bad code in the sampled bad stream belongs to the processed bad union. -/
private lemma restrictedAnchored_bad_subset_processed
    (𝒜 : DescriptionFamily) (c : Code) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target) (T m : ℕ)
    (hm : m < (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).length) :
    (decodeCoverCodeList
      ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).getD m [])).toFinset ⊆
      restrictedAnchoredProcessedBadUnion c 𝒜 (sqrtSlack 8 n) grid (T + 1) := by
  intro x hx
  rw [List.mem_toFinset] at hx
  rw [restrictedAnchoredProcessedBadUnion_eq_codes,
    restrictedAnchoredProcessedBadCodes_succ]
  refine (mem_restrictedDecodedBadCodesUnion_iff _ x).mpr
    ⟨(restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).getD m [], ?_, List.mem_toFinset.mpr hx⟩
  rw [List.getD_eq_getElem _ _ hm]
  exact List.getElem_mem hm

/-- Volume bound on the processed bad union for an anchored curve grid. -/
private lemma restrictedAnchoredProcessedBadUnion_card_lt
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (c : Code) (𝒜 : DescriptionFamily) (T : ℕ)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) :
    2 * (restrictedAnchoredProcessedBadUnion c 𝒜 (sqrtSlack 8 n) grid (T + 1)).card <
      2 ^ (n + logSlack 8 n) := by
  calc 2 * (restrictedAnchoredProcessedBadUnion c 𝒜 (sqrtSlack 8 n) grid (T + 1)).card
      ≤ 2 * ((List.range N).map fun s' =>
          2 ^ (grid.i (s' + 1) + 1) *
            2 ^ (grid.j s' - (sqrtSlack 8 n + 1))).sum :=
        Nat.mul_le_mul_left 2
          (restrictedAnchoredProcessedBadUnion_card_le c 𝒜 (sqrtSlack 8 n) grid T)
    _ < 2 ^ (n + logSlack 8 n) :=
        restrictedCurveGrid_bad_volume_padding_half grid hN hkn htarget hstrict

/-- Lower bound on the live set size at level 0 across event steps. -/
private lemma restrictedAnchoredEventChain_root_live_bound
    (𝒜 : DescriptionFamily) (c : Code) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) (T : ℕ)
    {chain : RestrictedAnchoredChain 𝒜 grid (restrictedAnchoredBadStream c 𝒜 grid T).length}
    (hbads : RestrictedAnchoredChainBads 𝒜 𝒜 c grid T chain)
    (hlive0 : (chain.states 0).live 0 = stringsOfLength (restrictedAnchoredAmbient n))
    (m : ℕ) (hm : m ≤ (restrictedAnchoredBadStream c 𝒜 grid T).length) :
    2 ^ restrictedAnchoredTarget (restrictedAnchoredAmbient n)
        (restrictedAnchoredSlack n) grid 0 ≤
      2 * ((chain.states m).live 0).card := by
  have hwin := chain.window_live_eq (Nat.zero_le m) hm (fun _ _ _ => Nat.zero_le _)
  rw [hwin, hlive0]
  simp only [restrictedAnchoredAmbient, restrictedAnchoredSlack]
  have hsub : (Finset.Ico 0 m).biUnion chain.bads ⊆
      restrictedAnchoredProcessedBadUnion c 𝒜 (sqrtSlack 8 n) grid (T + 1) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.mem_Ico] at ha
    rw [hbads a] at hxa
    have haM : a < (restrictedAnchoredBadStream c 𝒜 grid T).length := by omega
    exact restrictedAnchored_bad_subset_processed 𝒜 c grid T a haM hxa
  have hcardsub := Finset.card_le_card hsub
  have hcube : (stringsOfLength (n + logSlack 8 n)).card =
      2 ^ (n + logSlack 8 n) := card_stringsOfLength _
  have hsdiff := Finset.card_le_card_sdiff_add_card
    (s := stringsOfLength (n + logSlack 8 n))
    (t := (Finset.Ico 0 m).biUnion chain.bads)
  have hUcard :=
    restrictedAnchoredProcessedBadUnion_card_lt grid c 𝒜 T hN hkn htarget hstrict
  rw [restrictedAnchoredTarget_zero]
  omega

/-- Upper bound on the number of L-events in the event stream. -/
private lemma restrictedAnchoredEventChain_L_card_le
    (𝒜 : DescriptionFamily) (c : Code) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target) (T s : ℕ) :
    let Δ := sqrtSlack 8 n
    let events := restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N Δ T
    let isL := fun m => decide (∃ l, l < N ∧
      grid.i (l + 1) ≤ grid.i s ∧ events.getD m [] ∈
        familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
          (grid.j l - (Δ + 1)) T)
    ((Finset.range events.length).filter fun a => isL a = true).card ≤
      N * 2 ^ (grid.i s + 1) := by
  intro Δ events isL
  have hnodup : events.Nodup :=
    restrictedSampledBadCodeStream_nodup c (restrictedCurveGridCode grid) 𝒜.toPre N Δ T
  have hgetD_inj : ∀ {a a' : ℕ}, a < events.length → a' < events.length →
      events.getD a [] = events.getD a' [] → a = a' := by
    intro a a' ha ha' hEq
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at hEq
    have hinj := List.nodup_iff_injective_get.mp hnodup
    have h2 := hinj (show events.get ⟨a, ha⟩ = events.get ⟨a', ha'⟩ by simpa using hEq)
    simpa using h2
  have hmapsTo : ∀ a ∈ (Finset.range events.length).filter (fun a => isL a = true),
      events.getD a [] ∈ (((List.range N).filter (fun l =>
        grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
          (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
            (grid.j l - (Δ + 1)) T).toFinset)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hprop : ∃ l, l < N ∧ grid.i (l + 1) ≤ grid.i s ∧
        events.getD a [] ∈ familyStageModelCodesList c (grid.i (l + 1))
          𝒜.toPre (grid.j l - (Δ + 1)) T := of_decide_eq_true ha.2
    obtain ⟨l, hlN, hle, hmem⟩ := hprop
    refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hmem⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr hlN, by simpa using hle⟩
  have hinj : Set.InjOn (fun a => events.getD a [])
      ↑((Finset.range events.length).filter fun a => isL a = true) := by
    intro a ha a' ha' hEq
    have ha1 : a ∈ (Finset.range events.length).filter fun a => isL a = true := ha
    have ha2 : a' ∈ (Finset.range events.length).filter fun a => isL a = true := ha'
    rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    exact hgetD_inj ha1.1 ha2.1 hEq
  calc ((Finset.range events.length).filter fun a => isL a = true).card
      ≤ (((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset)).card :=
        Finset.card_le_card_of_injOn _ hmapsTo hinj
    _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset,
          (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
            (grid.j l - (Δ + 1)) T).toFinset.card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset, 2 ^ (grid.i s + 1) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [List.mem_toFinset, List.mem_filter] at hl
        have hle : grid.i (l + 1) ≤ grid.i s := by
          have := hl.2
          simpa using this
        calc (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset.card
            ≤ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).length := List.toFinset_card_le _
          _ ≤ 2 ^ (grid.i (l + 1) + 1) :=
              familyStageModelCodesList_length_le c _ 𝒜.toPre _ T
          _ ≤ 2 ^ (grid.i s + 1) :=
              Nat.pow_le_pow_right (by omega) (by omega)
    _ = (((List.range N).filter (fun l =>
          grid.i (l + 1) ≤ grid.i s)).toFinset).card *
          2 ^ (grid.i s + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * 2 ^ (grid.i s + 1) := by
        apply Nat.mul_le_mul_right
        calc (((List.range N).filter (fun l =>
              grid.i (l + 1) ≤ grid.i s)).toFinset).card
            ≤ ((List.range N).filter (fun l =>
                grid.i (l + 1) ≤ grid.i s)).length :=
              List.toFinset_card_le _
          _ ≤ (List.range N).length := List.length_filter_le _ _
          _ = N := List.length_range

/-- Upper bound on the sum of bad set sizes for non-L events (S-events). -/
private lemma restrictedAnchoredEventChain_S_sum_le
    (𝒜 : DescriptionFamily) (c : Code) {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target) (T s : ℕ)
    (hstrict : ∀ i < k, target (i + 1) < target i) (hsN : s ≤ N)
    {chain : RestrictedAnchoredChain 𝒜 grid (restrictedAnchoredBadStream c 𝒜 grid T).length}
    (hbads : RestrictedAnchoredChainBads 𝒜 𝒜 c grid T chain) :
    let Δ := restrictedAnchoredSlack n
    let events := restrictedAnchoredBadStream c 𝒜 grid T
    let isL := fun m => decide (∃ l, l < N ∧
      grid.i (l + 1) ≤ grid.i s ∧ events.getD m [] ∈
        familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
          (grid.j l - (Δ + 1)) T)
    ∑ a ∈ (Finset.range events.length).filter (fun a => isL a = false),
        (chain.bads a).card ≤
      N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
  intro Δ events isL
  have hnodup : events.Nodup :=
    restrictedSampledBadCodeStream_nodup c (restrictedCurveGridCode grid) 𝒜.toPre N Δ T
  have hgetD_inj : ∀ {a a' : ℕ}, a < events.length → a' < events.length →
      events.getD a [] = events.getD a' [] → a = a' := by
    intro a a' ha ha' hEq
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ ha'] at hEq
    have hinj := List.nodup_iff_injective_get.mp hnodup
    have h2 := hinj (show events.get ⟨a, ha⟩ = events.get ⟨a', ha'⟩ by simpa using hEq)
    simpa using h2
  have hinj2 : Set.InjOn (fun a => events.getD a [])
      ↑((Finset.range events.length).filter (fun a => isL a = false)) := by
    intro a ha a' ha' hEq
    have ha1 : a ∈ (Finset.range events.length).filter (fun a => isL a = false) := ha
    have ha2 : a' ∈ (Finset.range events.length).filter (fun a => isL a = false) := ha'
    rw [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    exact hgetD_inj ha1.1 ha2.1 hEq
  have hstep1 : ∑ a ∈ (Finset.range events.length).filter (fun a => isL a = false),
      (chain.bads a).card =
      ∑ w ∈ ((Finset.range events.length).filter (fun a => isL a = false)).image
        (fun a => events.getD a []),
        (decodeCoverCodeList w).toFinset.card := by
    rw [Finset.sum_image hinj2]
    exact Finset.sum_congr rfl (fun a _ => by rw [hbads a])
  rw [hstep1]
  have himg : ((Finset.range events.length).filter (fun a => isL a = false)).image
      (fun a => events.getD a []) ⊆
      (((List.range N).filter (fun l =>
        ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
          (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
            (grid.j l - (Δ + 1)) T).toFinset)) := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨haM, hnotL⟩ := ha
    have hmem : events.getD a [] ∈ events := by
      rw [List.getD_eq_getElem _ _ haM]
      exact List.getElem_mem haM
    have hraw := restrictedSampledBadCodeStream_mem_raw c (restrictedCurveGridCode grid)
      𝒜.toPre N Δ T hmem
    rw [restrictedSampledBadCodesRaw, List.mem_flatMap] at hraw
    obtain ⟨l, hlrange, hlmem⟩ := hraw
    have hlN : l < N := List.mem_range.mp hlrange
    rw [decode_restrictedCurveGridCode_sample_eq grid (show l + 1 ≤ N by omega),
      decode_restrictedCurveGridCode_sample_eq grid (show l ≤ N by omega)] at hlmem
    have hgt : ¬ grid.i (l + 1) ≤ grid.i s := by
      intro hle
      have htrue : isL a = true := decide_eq_true ⟨l, hlN, hle, hlmem⟩
      rw [hnotL] at htrue
      exact absurd htrue (by decide)
    refine Finset.mem_biUnion.mpr ⟨l, ?_, List.mem_toFinset.mpr hlmem⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨List.mem_range.mpr hlN, by simpa using hgt⟩
  calc ∑ w ∈ ((Finset.range events.length).filter
        (fun a => isL a = false)).image (fun a => events.getD a []),
        (decodeCoverCodeList w).toFinset.card
      ≤ ∑ w ∈ (((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset.biUnion (fun l =>
            (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset)),
          (decodeCoverCodeList w).toFinset.card :=
        Finset.sum_le_sum_of_subset himg
    _ ≤ ∑ l ∈ ((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
          ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
            (grid.j l - (Δ + 1)) T).toFinset,
            (decodeCoverCodeList w).toFinset.card :=
        sum_biUnion_le' _ _ _
    _ ≤ ∑ _l ∈ ((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset,
          2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [List.mem_toFinset, List.mem_filter] at hl
        have hlN : l < N := List.mem_range.mp hl.1
        have hgt : grid.i s < grid.i (l + 1) := by
          have := hl.2
          simp at this
          omega
        calc ∑ w ∈ (familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
              (grid.j l - (Δ + 1)) T).toFinset,
              (decodeCoverCodeList w).toFinset.card
            ≤ ((familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
                (grid.j l - (Δ + 1)) T).map fun w =>
                  (decodeCoverCodeList w).toFinset.card).sum :=
              sum_toFinset_le_list_sum _ _
          _ ≤ 2 ^ (grid.i (l + 1) + 1) * 2 ^ (grid.j l - (Δ + 1)) :=
              familyStageModelCodesList_decoded_volume_le c _ 𝒜.toPre _ T
          _ = 2 ^ (grid.i (l + 1) + 1 + (grid.j l - (Δ + 1))) :=
              (pow_add 2 _ _).symm
          _ ≤ 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
                (n / N + 1) + 4) :=
              Nat.pow_le_pow_right (by omega)
                (restrictedCurveGrid_sStage_exponent_le grid hstrict hsN hlN hgt)
    _ = (((List.range N).filter (fun l =>
          ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card *
          2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ + (n / N + 1) + 4) := by
        apply Nat.mul_le_mul_right
        calc (((List.range N).filter (fun l =>
              ¬ grid.i (l + 1) ≤ grid.i s)).toFinset).card
            ≤ ((List.range N).filter (fun l =>
                ¬ grid.i (l + 1) ≤ grid.i s)).length :=
              List.toFinset_card_le _
          _ ≤ (List.range N).length := List.length_filter_le _ _
          _ = N := List.length_range

/-- The anchored event chain of the specialized run (ambient
`n + logSlack 8 n`, stream slack `sqrtSlack 8 n`) rebuilds each level `s + 1`
at most `2 ^ (grid.i s + anchoredVersionExp 𝒜 n N)` times. -/
theorem exists_restrictedAnchoredEventChain_with_count
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n) (htarget : target 0 ≤ n)
    (hstrict : ∀ i < k, target (i + 1) < target i) (T : ℕ) :
    ∃ (chain : RestrictedRunChain 𝒜 (N + 1) (n + logSlack 8 n)
        (2 * 𝒜.overhead (n + logSlack 8 n))
        (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)
      (codes : ℕ → BitString),
      (∀ m,
        (restrictedEffectiveAnchoredInitialState 𝒜 (n + logSlack 8 n)
            (sqrtSlack 8 n) grid).bind
          (fun st0 => restrictedEventPrefixRun 𝒜
            (𝒜.overhead (n + logSlack 8 n))
            (restrictedEffectiveAnchoredSizes (n + logSlack 8 n)
              (sqrtSlack 8 n) grid) st0
            (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
              𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
        DecodesToRestrictedSampledRunState (codes m) (chain.states m)) ∧
      (∀ m, chain.bads m = (decodeCoverCodeList
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).getD m [])).toFinset) ∧
      (chain.states 0).B 0 = stringsOfLength (n + logSlack 8 n) ∧
      (chain.states 0).live 0 = stringsOfLength (n + logSlack 8 n) ∧
      ∀ s ≤ N, (chain.rebuildSteps s).card ≤
        2 ^ (grid.i s + anchoredVersionExp 𝒜 n N) := by
  classical
  set Δ := sqrtSlack 8 n with hΔdef
  set gridCode := restrictedCurveGridCode grid with hgridCodeDef
  set events := restrictedSampledBadCodeStream c gridCode 𝒜.toPre N Δ T
    with heventsDef
  set M := events.length with hMdef
  set OB := 2 * 𝒜.overhead (n + logSlack 8 n) with hOBdef
  have hnamb : n ≤ n + logSlack 8 n := Nat.le_add_right _ _
  obtain ⟨chain, codes, hfold, hbads, hB0, hlive0⟩ :=
    exists_restrictedAnchoredEventChain 𝒜 c (n + logSlack 8 n) Δ grid
      hnamb T
  refine ⟨chain, codes, hfold, hbads, hB0, hlive0, ?_⟩
  intro s hsN
  have hroot := restrictedAnchoredEventChain_root_live_bound 𝒜 c grid hN hkn htarget
    hstrict T hbads hlive0
  have hmono : ∀ r < N + 1,
      restrictedAnchoredTarget (n + logSlack 8 n) Δ grid (r + 1) ≤
        restrictedAnchoredTarget (n + logSlack 8 n) Δ grid r :=
    restrictedAnchoredTarget_mono _ _ grid hnamb
  have hOB1 : 1 ≤ OB := by
    have := 𝒜.overhead_pos (n + logSlack 8 n)
    omega
  set isL : ℕ → Bool := fun m => decide (∃ l, l < N ∧
    grid.i (l + 1) ≤ grid.i s ∧ events.getD m [] ∈
      familyStageModelCodesList c (grid.i (l + 1)) 𝒜.toPre
        (grid.j l - (Δ + 1)) T) with hisL
  have hLcard := restrictedAnchoredEventChain_L_card_le 𝒜 c grid T s
  have hSsum := restrictedAnchoredEventChain_S_sum_le 𝒜 c grid T s hstrict hsN hbads
  have hmain := chain.rebuildSteps_card_mul_le hroot hmono hOB1
    (show s < N + 1 by omega) isL hLcard hSsum
  rw [restrictedAnchoredTarget_succ] at hmain
  have hVSsplit : N * 2 ^ (grid.i s + (grid.j s - (Δ + 1)) + Δ +
      (n / N + 1) + 4) =
      N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
        2 ^ (grid.j s - (Δ + 1)) := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hVSsplit] at hmain
  have hfact : (s + 1) * ((N * 2 ^ (grid.i s + 1) + 1) *
      2 ^ (grid.j s - (Δ + 1)) +
      2 * OB ^ (s + 1) *
        (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4) *
          2 ^ (grid.j s - (Δ + 1)))) =
      ((s + 1) * (N * 2 ^ (grid.i s + 1) + 1 +
        2 * OB ^ (s + 1) *
          (N * 2 ^ (grid.i s + Δ + (n / N + 1) + 4)))) *
        2 ^ (grid.j s - (Δ + 1)) := by
    ring
  rw [hfact] at hmain
  have hcount := Nat.le_of_mul_le_mul_right hmain (pow_pos (by omega) _)
  have hNN : N + 1 ≤ 2 ^ (Nat.bits (N + 1)).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self (N + 1)).le
  have hOBsize : OB ≤ 2 ^ (Nat.bits OB).length := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size_self OB).le
  have harith := version_count_arith (I := grid.i s) (Δm := Δ)
    (mesh := n / N + 1) (LN := (Nat.bits (N + 1)).length)
    (Lob := (Nat.bits OB).length) (NN := N) (OB := OB) (s := s)
    hNN hOBsize hsN
  refine hcount.trans (harith.trans (Nat.pow_le_pow_right (by omega) ?_))
  have hexp : anchoredVersionExp 𝒜 n N =
      (N + 2) * (Nat.bits OB).length +
        2 * (Nat.bits (N + 1)).length + Δ + (n / N + 1) + 9 := rfl
  rw [hexp]
  have hmul : (N + 1) * (Nat.bits OB).length ≤
      (N + 2) * (Nat.bits OB).length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The ambient budget `n + logSlack 8 n` has binary length at most `(Nat.bits n).length + 4`:
the slack `logSlack 8 n` is `8 * (Nat.bits n).length + 8`, so the ambient budget stays below
`16 * 2 ^ (Nat.bits n).length`. -/
lemma bits_length_ambient_le (n : ℕ) :
    (Nat.bits (n + logSlack 8 n)).length ≤ (Nat.bits n).length + 4 := by
  set L := (Nat.bits n).length with hL
  have hLsize : L = Nat.size n := Nat.size_eq_bits_len n
  have hn2 : n < 2 ^ L := by
    rw [hLsize]
    exact Nat.lt_size_self n
  have hLpow : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hlog : logSlack 8 n = 8 * L + 8 := by
    unfold logSlack
    rfl
  have hpow4 : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by
    rw [pow_add]
    ring
  omega

/-- Twice the overhead at the ambient length has logarithmically many bits, with the constant
made explicit. -/
private lemma bits_length_two_mul_overhead_le (𝒜 : DescriptionFamily) {c_over : ℕ}
    (hover : ∀ m, (Nat.bits (𝒜.overhead m)).length ≤ logSlack c_over m) (n : ℕ) :
    (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      (5 * c_over + 2) * ((Nat.bits n).length + 1) := by
  set L := (Nat.bits n).length with hL
  set C₁ := 5 * c_over + 2 with hC₁
  have hambBits : (Nat.bits (n + logSlack 8 n)).length ≤ L + 4 := bits_length_ambient_le n
  have hovpos := 𝒜.overhead_pos (n + logSlack 8 n)
  have hsz : (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length + 1 := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have := Nat.lt_size_self (𝒜.overhead (n + logSlack 8 n))
    calc 2 * 𝒜.overhead (n + logSlack 8 n)
        < 2 * 2 ^ Nat.size (𝒜.overhead (n + logSlack 8 n)) := by omega
      _ = 2 ^ (Nat.size (𝒜.overhead (n + logSlack 8 n)) + 1) := by
          rw [pow_succ]
          ring
  have hlogS : logSlack c_over (n + logSlack 8 n) ≤
      c_over * (L + 4) + c_over := by
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left c_over hambBits) c_over
  have hov := hover (n + logSlack 8 n)
  have hexpand : c_over * (L + 4) + c_over + 1 ≤ C₁ * (L + 1) := by
    rw [hC₁]
    nlinarith
  calc (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length
      ≤ (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length + 1 := hsz
    _ ≤ logSlack c_over (n + logSlack 8 n) + 1 :=
        Nat.add_le_add_right hov 1
    _ ≤ c_over * (L + 4) + c_over + 1 := Nat.add_le_add_right hlogS 1
    _ ≤ C₁ * (L + 1) := hexpand

/-- For a polynomial-overhead family the version-count exponent is a genuine
square-root slack. -/
lemma anchoredVersionExp_le_sqrtSlack
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead) :
    ∃ c_P : ℕ, ∀ n N : ℕ, N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1 →
      anchoredVersionExp 𝒜 n N ≤ sqrtSlack c_P n := by
  obtain ⟨c_over, hover⟩ := 𝒜.overhead_bits_le_logSlack hPoly
  refine ⟨5 * (5 * c_over + 2) + 40, ?_⟩
  intro n N hN
  set L := (Nat.bits n).length with hL
  set S := Nat.sqrt (n * L) with hS
  set q := Nat.sqrt (n / (Nat.log2 n + 1)) with hq
  set C₁ := 5 * c_over + 2 with hC₁
  -- the ambient length has at most `L + 4` bits
  have hLsize : L = Nat.size n := Nat.size_eq_bits_len n
  have hn2 : n < 2 ^ L := by
    rw [hLsize]
    exact Nat.lt_size_self n
  have hLpow : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  have hambBits : (Nat.bits (n + logSlack 8 n)).length ≤ L + 4 :=
    bits_length_ambient_le n
  -- the overhead bound in bits
  have hOBbits : (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      C₁ * (L + 1) :=
    bits_length_two_mul_overhead_le 𝒜 hover n
  -- N + 1 has at most L + 2 bits
  have hNle : N ≤ n + 1 := by
    rw [hN]
    exact Nat.add_le_add_right
      ((Nat.sqrt_le_self (n / (Nat.log2 n + 1))).trans
        (Nat.div_le_self n (Nat.log2 n + 1))) 1
  have hN1bits : (Nat.bits (N + 1)).length ≤ L + 2 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hpow2 : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by
      rw [pow_add]
      ring
    omega
  -- square-root balances
  have hqL : q * L ≤ S := by
    apply Nat.le_sqrt.mpr
    have hq2 : q * q ≤ n / (Nat.log2 n + 1) := by
      simpa [pow_two] using Nat.sqrt_le' (n / (Nat.log2 n + 1))
    have hLb : L ≤ Nat.log2 n + 1 := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp [hL]
      · have : (Nat.bits n).length = Nat.log2 n + 1 := by
          rw [Nat.size_eq_bits_len, Nat.le_antisymm_iff]
          constructor
          · rw [Nat.size_le]
            exact Nat.lt_log2_self
          · rw [Nat.add_one_le_iff, Nat.log2_lt (by omega)]
            exact Nat.lt_size_self n
        omega
    have hdivL : n / (Nat.log2 n + 1) * L ≤ n := by
      calc n / (Nat.log2 n + 1) * L
          ≤ n / (Nat.log2 n + 1) * (Nat.log2 n + 1) :=
            Nat.mul_le_mul_left _ hLb
        _ ≤ n := Nat.div_mul_le_self n _
    calc q * L * (q * L) = q * q * (L * L) := by ring
      _ ≤ n / (Nat.log2 n + 1) * (L * L) := Nat.mul_le_mul_right _ hq2
      _ = n / (Nat.log2 n + 1) * L * L := by ring
      _ ≤ n * L := Nat.mul_le_mul_right _ hdivL
  have hnL : n ≤ n * L := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · simp [hn0]
    · have hLpos : 0 < L := by
        rw [hLsize]
        exact Nat.size_pos.mpr hnpos
      exact Nat.le_mul_of_pos_right n hLpos
  have hq_le : q ≤ S := by
    apply Nat.le_sqrt.mpr
    have hq2 : q * q ≤ n / (Nat.log2 n + 1) := by
      simpa [pow_two] using Nat.sqrt_le' (n / (Nat.log2 n + 1))
    calc q * q ≤ n / (Nat.log2 n + 1) := hq2
      _ ≤ n := Nat.div_le_self _ _
      _ ≤ n * L := hnL
  have hL_le : L ≤ S := by
    apply Nat.le_sqrt.mpr
    have hLn : L ≤ n := by
      rw [hLsize]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    exact Nat.mul_le_mul_right _ hLn
  -- mesh
  have hmesh : n / N + 1 ≤ sqrtSlack 8 n := by
    rw [hN]
    exact restrictedCurveGrid_mesh_le_sqrtSlack n
  -- assemble
  have hNq : N + 2 = q + 3 := by
    rw [hN]
  have hOBterm : (N + 2) *
      (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤
      C₁ * (5 * S + 3) := by
    calc (N + 2) * (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length
        ≤ (N + 2) * (C₁ * (L + 1)) := Nat.mul_le_mul_left _ hOBbits
      _ = C₁ * ((q + 3) * (L + 1)) := by
          rw [hNq]
          ring
      _ = C₁ * (q * L + q + 3 * L + 3) := by ring
      _ ≤ C₁ * (S + S + 3 * S + 3) := by
          apply Nat.mul_le_mul_left
          have h3L : 3 * L ≤ 3 * S := Nat.mul_le_mul_left 3 hL_le
          omega
      _ = C₁ * (5 * S + 3) := by ring
  have hsq8 : sqrtSlack 8 n = 8 * S + 8 := by
    unfold sqrtSlack
    rw [hS]
  unfold anchoredVersionExp
  set X := C₁ * (S + 1) with hX
  have hOBterm' : (N + 2) *
      (Nat.bits (2 * 𝒜.overhead (n + logSlack 8 n))).length ≤ 5 * X := by
    refine hOBterm.trans ?_
    rw [hX]
    calc C₁ * (5 * S + 3) ≤ C₁ * (5 * S + 5) := by
          apply Nat.mul_le_mul_left
          omega
      _ = 5 * (C₁ * (S + 1)) := by ring
  have htarget : sqrtSlack (5 * C₁ + 40) n = (5 * C₁ + 40) * S +
      (5 * C₁ + 40) := by
    unfold sqrtSlack
    rw [hS]
  rw [htarget]
  have hexp : (5 * C₁ + 40) * S + (5 * C₁ + 40) = 5 * X + 40 * S + 40 := by
    rw [hX]
    ring
  rw [hexp]
  have hN1 : 2 * (Nat.bits (N + 1)).length ≤ 2 * S + 4 := by
    have := hN1bits
    have h2 : 2 * (Nat.bits (N + 1)).length ≤ 2 * (L + 2) :=
      Nat.mul_le_mul_left 2 hN1bits
    have h3 : 2 * L ≤ 2 * S := Nat.mul_le_mul_left 2 hL_le
    omega
  omega

end CountInstantiation

end Kolmogorov
