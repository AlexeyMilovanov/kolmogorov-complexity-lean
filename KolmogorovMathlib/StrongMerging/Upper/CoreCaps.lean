import KolmogorovMathlib.StrongMerging.Upper.CoreCaps.CapDecoder

/-!
# Coverage and caps of minimum cores (blueprint M04, M05, M07, M08)

`sublinear-merging.tex`, subsections "Finite minimum-core profiles" (tex ~719–728), "Ordinary
factors in a partial compression argument" (Lemma `lem:ordinary-factor-initial-core`, tex
~730–805) and "Adjacent comparisons and finite trial algorithms" (eq. `extractability-adjacent`,
tex ~834–849); appendix `bp-upper-mincores` (tex ~3852–3943).

All three compression arguments of the layer are one parent, `capCompression`.  Suppose `x` lies
in the capped residual `U` (budget `s`, cap `2^(K+1)`, `K = C(x | P)`) and an object `P` is
obtained from each actual endpoint by a fixed acquisition rule (`acquire`): the constant `[]`
(mode `0`, the unconditional enumeration), an ordinary program `aux` run by `V` (mode `1`, a common
factor), or a local rank `aux` of a core at an earlier budget `s₀` (mode `2`, the adjacent cap).
The dovetailed enumeration `coreEnum` of the residual edges `z` with `C(z | P) ≤ K` has fewer than
`2^(K+1)` arrivals, which fit the cap, so they are core-free; the online orientation then indexes
`x` from its owner endpoint, and the plain decoder `coreMachine 8 (capKer V cV)` (partial: it runs
`V`) gives `C(x | A) ≤ (a - s) + |aux| + c H` or `C(x | B) ≤ (b - s) + |aux| + c H`.

* **M04 (`UpperMinCoreCoverage`)**: `upperMinCoreCoverage`.  An uncovered `x` lies in the full
  residual, hence in every capped residual; mode `0` and typicality bound `s ≤ c H`.
* **M05 (`UpperInitialFactorCap`)**: `upperInitialFactorCap`, with `L_r = c_* (H + r)` for every
  `c_* ≥ c_min`: `f_{L_r} ≤ C(x | P) + 1 ≤ k - C(P) + b (H + r)` (mode `1`; the chain rule).
* **M07 (`UpperInitialProfileCap`)**: `upperInitialProfileCap`:
  `f_{L_r} ≤ k - 𝓔_p(r) + b (H + r)`; a positive profile is attained (M06) and M05 applies; a zero
  profile uses mode `0` (no empty program for a constant object is assumed).
* **M08 (`UpperAdjacentCap`)**: `upperAdjacentCap`: `f_{s+L} ≤ C(x | F_s) + 1` (mode `2`, the
  local rank costs `s + 1` and the rank `a - s - L`), and
  `Score(F_s, x) ≤ f_s - f_{s+L} + b H` (point decoder M03 and the chain rule).  No inclusion
  between `F_s` and `F_{s+L}` is used.

Here `H = e + ⌈log₂ (n + 2)⌉` (`baseBudget n e`), `k = C(x)`, `f_s = log₂ |F_s|` (real), and the
constants are quantified after `V` and before `c_*` and all instance data.

The first part of the development is in `KolmogorovMathlib.StrongMerging.Upper.CoreCaps.CapDecoder`,
imported here.
-/

namespace Kolmogorov.StrongMerging.Upper

open Nat.Partrec (Code)

/-! ### The shared compression parent -/

/-- **The capped-residual compression** (the common argument of M04, M05 and M08).  For an optimal
plain machine `V` there is a constant `c` such that at every qualifying instance, budget `s ≤ a, b`
and acquisition (`mode ≤ 2`, earlier budget `s₀ ≤ a`, auxiliary strings of length
`≤ n + a + 1`), if `x` lies in the capped residual with cap `2^(K+1)`, `K = C(x | P)`, and `P` is
acquired from `A` with `auxA` and from `B` with `auxB`, then
`C(x | A) ≤ (a - s) + |auxA| + c H` or `C(x | B) ≤ (b - s) + |auxB| + c H`. -/
theorem capCompression (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s mode s₀ : ℕ)
      (auxA auxB Pobj : BitString), IsCoreInstance V n e pA pB x A B →
        s ≤ Nat.log 2 A.card → s ≤ Nat.log 2 B.card → s₀ ≤ Nat.log 2 A.card → mode ≤ 2 →
        auxA.length ≤ n + Nat.log 2 A.card + 1 → auxB.length ≤ n + Nat.log 2 A.card + 1 →
        x ∈ vertexResidual (coreShape pA pB n A B) s (2 ^ ((condK V x Pobj).toNat + 1))
          (shapeSrc (coreShape pA pB n A B) x) →
        Pobj ∈ acquire V (coreShape pA pB n A B) mode s₀ false auxA (canonicalFiniteSetCode A) →
        Pobj ∈ acquire V (coreShape pA pB n A B) mode s₀ true auxB (canonicalFiniteSetCode B) →
          condC V x (canonicalFiniteSetCode A) ≤
              ((Nat.log 2 A.card - s : ℕ) : ℝ) + auxA.length + c * baseBudget n e ∨
            condC V x (canonicalFiniteSetCode B) ≤
              ((Nat.log 2 B.card - s : ℕ) : ℝ) + auxB.length + c * baseBudget n e := by
  obtain ⟨cV, hcV⟩ := Lower.exists_isCodeFor_of_isDecompressor hV.1
  obtain ⟨cD, hcD⟩ := condC_le_of_decoder V hV (coreMachine 8 (capKer V cV))
    (coreMachine_partrec 8 (capKer_partrec hV hcV))
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨cpl, hpl⟩ := condC_le_plainC_add V hV
  obtain ⟨cpk, hpk⟩ := length_corePacket_le 8 (bsize + blit + cpl + 3)
  obtain ⟨ctl, htl⟩ := length_capTail_le bsize
  refine ⟨cpk + ctl + cD + 1, fun n e pA pB x A B s mode s₀ auxA auxB Pobj h hsa hsb hs₀ hmode
    hauxA hauxB hxU hacqA hacqB => ?_⟩
  set P := coreShape pA pB n A B with hP
  set K := (condK V x Pobj).toNat with hK
  have hxG := h.mem_shapeEdges
  have ha := (htyp n e x A h.length_x h.le_n h.sufA).2
  have hb := (htyp n e x B h.length_x h.le_n h.sufB).2
  have hH := mc_one_le_baseBudget n e
  have hhl := mc_headerLog_le_baseBudget n e
  -- the bound on `K`
  have hKle : K ≤ n + blit + cpl := by
    have h1 := hpl x Pobj
    have h2 := hlit x
    rw [h.length_x] at h2
    have h3 : condC V x Pobj = K := rfl
    have h4 : (K : ℝ) ≤ n + blit + cpl := by linarith
    exact_mod_cast h4
  -- the enumeration and the arrival of `x`
  set U := vertexResidual P s (2 ^ (K + 1)) (shapeSrc P x) with hUdef
  obtain ⟨p, hprod, hplen⟩ := Lower.exists_program_of_condC V hV x Pobj
  have hpK : p.length ≤ K := by
    have : (p.length : ℝ) = K := hplen
    exact_mod_cast this.le
  obtain ⟨t, hxt⟩ := exists_mem_arrivals_coreEnum hcV hxU hpK hprod
  set l := arrivals (coreEnum cV U Pobj K) t with hl
  have hnd : l.Nodup := arrivals_nodup _ t
  have hEU : ∀ z ∈ l.toFinset, z ∈ U ∧ condC V z Pobj ≤ K := fun z hz =>
    mem_arrivals_coreEnum hcV (List.mem_toFinset.mp hz)
  have hEcard : l.toFinset.card < 2 ^ (K + 1) :=
    Lower.card_lt_two_pow_of_condC_lt V hV Pobj (K + 1) l.toFinset fun z hz => by
      have := (hEU z hz).2
      push_cast
      linarith
  have hUsub : U ⊆ shapeComponent P (shapeEdges P) (shapeSrc P x) :=
    fun z hz => ((mem_coreResidual_iff P s (2 ^ (K + 1))
      (shapeComponent P (shapeEdges P) (shapeSrc P x)) z).mp hz).1
  have hfree : CoreFree (shapeSrc P) (shapeTgt P) (coreCap P s) l.toFinset := by
    refine coreFree_of_noSmallElig (M := 2 ^ (K + 1)) (fun T hT hel => ?_) hEcard.le
    exact (upperMinCoreFamily P s (2 ^ (K + 1))
      (shapeComponent P (shapeEdges P) (shapeSrc P x))).2.2.2.2.2.2.2.1 T
      (fun z hz => (hEU z (hT hz)).1) hel
  have hxl : x ∈ l := hxt
  have hrank := rank_lt_of_orientation l hnd (fun v _ => coreCap_pos P s v) hfree hxl
  have hW : Nat.log 2 (∑ u ∈ incidentVerts (shapeSrc P) (shapeTgt P) l.toFinset, coreCap P s u) ≤
      P.n + 1 + max P.a P.b := by
    refine log_sum_incidentVerts_le ?_ (coreCap_le P s)
    refine (Finset.card_le_card fun z hz => ?_).trans (card_shapeEdges_le P)
    exact shapeComponent_subset _ _ _ (hUsub (hEU z hz).1)
  have hWn : Nat.log 2 (∑ u ∈ incidentVerts (shapeSrc P) (shapeTgt P) l.toFinset,
      coreCap P s u) ≤ 3 * n + 1 + bsize := by
    have hmax : max P.a P.b ≤ 2 * n + bsize := max_le ha hb
    have : P.n = n := rfl
    omega
  have hinv := orientInv_orient (shapeSrc P) (shapeTgt P) (coreCap P s) l hnd
  have hown := hinv.owner_mem x (List.mem_toFinset.mpr hxl)
  -- the fields of the packet
  have hfields : ∀ (t' : ℕ), t' ≤ 1 → ∀ k ∈ [n, Nat.log 2 A.card, Nat.log 2 B.card, t', s, K, mode,
      s₀], k ≤ (bsize + blit + cpl + 3) * (n + 1) := by
    intro t' ht' k hk
    apply mc_le_mul_succ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hcD0 : (cD : ℝ) ≤ cD * baseBudget n e := le_mul_of_one_le_right (Nat.cast_nonneg _) hH
  have hctl : (ctl : ℝ) * headerLog n ≤ ctl * baseBudget n e :=
    mul_le_mul_of_nonneg_left hhl (Nat.cast_nonneg _)
  have hpos : (0 : ℝ) ≤ (cpk : ℝ) * baseBudget n e := by positivity
  rcases hown with hsrc | htgt
  · -- the row endpoint owns `x`
    left
    have hy : coreEnd false (canonicalFiniteSetCode A) = shapeSrc P x := by
      simp only [coreEnd, shapeSrc, h.outA_eq, Bool.false_eq_true, ↓reduceIte, hP]
    have hmem := capMachine_spec h s K mode s₀ false auxA Pobj (canonicalFiniteSetCode A) U
      (by rw [hy]) hacqA t hxt (by rw [hsrc, hy])
    have h1 := hcD _ _ _ hmem
    have hcap : coreCap P s (shapeSrc P x) = 2 ^ (Nat.log 2 A.card - s) := rfl
    rw [hsrc, hcap] at hrank
    have h2 := htl n (Nat.log 2 A.card - s) _ _ auxA (by omega) hWn hrank
    have h3 := hpk n e _ pA pB (totalProgramPairCode auxA (Nat.bits ((orient (shapeSrc P)
      (shapeTgt P) (coreCap P s) l).rank x))) (by simp) (hfields 0 (Nat.zero_le _)) h.lenA h.lenB
      h.le_n
    have h4 : ((corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, (false).toNat, s, K, mode, s₀]
        pA pB (totalProgramPairCode auxA (Nat.bits ((orient (shapeSrc P) (shapeTgt P)
          (coreCap P s) l).rank x)))).length : ℝ) ≤
        auxA.length + ((Nat.log 2 A.card - s : ℕ) : ℝ) + ctl * headerLog n +
          cpk * baseBudget n e := by
      have := h3.trans (Nat.add_le_add_right h2 _)
      exact_mod_cast this
    have hexp : ((cpk + ctl + cD + 1 : ℕ) : ℝ) * baseBudget n e = cpk * baseBudget n e +
        ctl * baseBudget n e + cD * baseBudget n e + baseBudget n e := by
      push_cast
      ring
    rw [hexp]
    linarith
  · -- the column endpoint owns `x`
    right
    have hy : coreEnd true (canonicalFiniteSetCode B) = shapeTgt P x := by
      simp only [coreEnd, shapeTgt, h.outB_eq, ↓reduceIte, hP]
    have hU' : vertexResidual P s (2 ^ (K + 1)) (coreEnd true (canonicalFiniteSetCode B)) = U := by
      rw [hy, vertexResidual_tgt_eq_src s _ hxG]
    have hmem := capMachine_spec h s K mode s₀ true auxB Pobj (canonicalFiniteSetCode B) U
      hU' hacqB t hxt (by rw [htgt, hy])
    have h1 := hcD _ _ _ hmem
    have hcap : coreCap P s (shapeTgt P x) = 2 ^ (Nat.log 2 B.card - s) := rfl
    rw [htgt, hcap] at hrank
    have h2 := htl n (Nat.log 2 B.card - s) _ _ auxB (by omega) hWn hrank
    have h3 := hpk n e _ pA pB (totalProgramPairCode auxB (Nat.bits ((orient (shapeSrc P)
      (shapeTgt P) (coreCap P s) l).rank x))) (by simp) (hfields 1 le_rfl) h.lenA h.lenB h.le_n
    have h4 : ((corePacket [n, Nat.log 2 A.card, Nat.log 2 B.card, (true).toNat, s, K, mode, s₀]
        pA pB (totalProgramPairCode auxB (Nat.bits ((orient (shapeSrc P) (shapeTgt P)
          (coreCap P s) l).rank x)))).length : ℝ) ≤
        auxB.length + ((Nat.log 2 B.card - s : ℕ) : ℝ) + ctl * headerLog n +
          cpk * baseBudget n e := by
      have := h3.trans (Nat.add_le_add_right h2 _)
      exact_mod_cast this
    have hexp : ((cpk + ctl + cD + 1 : ℕ) : ℝ) * baseBudget n e = cpk * baseBudget n e +
        ctl * baseBudget n e + cD * baseBudget n e + baseBudget n e := by
      push_cast
      ring
    rw [hexp]
    linarith

/-! ### M04: coverage -/

/-- The full residual is contained in every capped residual: the capped family is a sublist of the
full family. -/
theorem vertexResidual_full_subset (P : ShapeParams) (s M : ℕ) (v : BitString ⊕ BitString) :
    vertexResidual P s (shapeComponent P (shapeEdges P) v).card v ⊆ vertexResidual P s M v := by
  intro z hz
  obtain ⟨hzC, hno⟩ := (mem_coreResidual_iff P s _ _ z).mp hz
  refine (mem_coreResidual_iff P s M _ z).mpr ⟨hzC, fun T hT => ?_⟩
  rw [coreFamily_cap, List.mem_filter] at hT
  exact hno T hT.1

/-- **Coverage (blueprint M04, `UpperMinCoreCoverage`).**  For an optimal plain machine `V` there
is a constant `c₀` such that at every qualifying instance and every budget `s` with
`c₀ H ≤ s < min (a, b)`, the actual string lies in a selected core at budget `s`.  (Otherwise it
lies in the core-free full residual; the compression from the owner endpoint, with the
unconditional enumeration, contradicts typicality.)  The existence is an analysis statement only:
the algorithms keep their missing-core defaults. -/
theorem upperMinCoreCoverage (V : Map) (hV : isOptimalConditional V) :
    ∃ c₀ : ℕ, ∀ (n e : ℕ) (pA pB x : BitString) (A B : Finset BitString) (s : ℕ),
      IsCoreInstance V n e pA pB x A B → (c₀ : ℝ) * baseBudget n e ≤ s →
        s < Nat.log 2 A.card → s < Nat.log 2 B.card →
          ∃ F, coreOf (coreShape pA pB n A B) s x = some F := by
  obtain ⟨c, hc⟩ := capCompression V hV
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  refine ⟨c + btyp + 1, fun n e pA pB x A B s h hs hsa hsb => ?_⟩
  by_contra hno
  have hnone : coreOf (coreShape pA pB n A B) s x = none := by
    cases hco : coreOf (coreShape pA pB n A B) s x with
    | none => rfl
    | some F => exact absurd ⟨F, hco⟩ hno
  have hxG := h.mem_shapeEdges
  have hxU := vertexResidual_full_subset _ s (2 ^ ((condK V x []).toNat + 1)) _
    (mem_vertexResidual_of_coreOf_eq_none hxG hnone)
  have hacq : ∀ side y, ([] : BitString) ∈
      acquire V (coreShape pA pB n A B) 0 0 side [] y := by
    intro side y
    simp [acquire]
  have hH := mc_one_le_baseBudget n e
  have htA := (htyp n e x A h.length_x h.le_n h.sufA).1
  have htB := (htyp n e x B h.length_x h.le_n h.sufB).1
  rcases hc n e pA pB x A B s 0 0 [] [] [] h hsa.le hsb.le (Nat.zero_le _) (by norm_num)
    (by simp) (by simp) hxU (hacq false _) (hacq true _) with hA | hB
  · have hcast : ((Nat.log 2 A.card - s : ℕ) : ℝ) = (Nat.log 2 A.card : ℝ) - s := by
      rw [Nat.cast_sub hsa.le]
    rw [hcast] at hA
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hA
    push_cast at hs
    have hexp : ((c : ℝ) + btyp + 1) * baseBudget n e =
        c * baseBudget n e + btyp * baseBudget n e + baseBudget n e := by ring
    linarith
  · have hcast : ((Nat.log 2 B.card - s : ℕ) : ℝ) = (Nat.log 2 B.card : ℝ) - s := by
      rw [Nat.cast_sub hsb.le]
    rw [hcast] at hB
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hB
    push_cast at hs
    have hexp : ((c : ℝ) + btyp + 1) * baseBudget n e =
        c * baseBudget n e + btyp * baseBudget n e + baseBudget n e := by ring
    linarith

/-! ### M05: the common-factor initial cap -/

/-- **The initial cap for an acquired object** (modes `0` and `1`): with `L = c_* (H + r)` for
every `c_* ≥ c_min`, if `L < a, b` and `P` is acquired from both endpoints with auxiliary strings
of length `≤ r ≤ n`, then the selected core `F_L` exists and `log₂ |F_L| ≤ C(x | P) + 1`. -/
theorem factorCap_core (V : Map) (hV : isOptimalConditional V) :
    ∃ cmin : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r : ℕ) (pA pB x : BitString)
      (A B : Finset BitString) (mode : ℕ) (auxA auxB Pobj : BitString),
        IsCoreInstance V n e pA pB x A B → r ≤ n → mode ≤ 1 →
        auxA.length ≤ r → auxB.length ≤ r →
        Pobj ∈ acquire V (coreShape pA pB n A B) mode 0 false auxA (canonicalFiniteSetCode A) →
        Pobj ∈ acquire V (coreShape pA pB n A B) mode 0 true auxB (canonicalFiniteSetCode B) →
        cstar * (baseBudget n e + r) < Nat.log 2 A.card →
        cstar * (baseBudget n e + r) < Nat.log 2 B.card →
          ∃ F, coreOf (coreShape pA pB n A B) (cstar * (baseBudget n e + r)) x = some F ∧
            Real.logb 2 F.card ≤ condC V x Pobj + 1 := by
  obtain ⟨c₀, hc₀⟩ := upperMinCoreCoverage V hV
  obtain ⟨c, hc⟩ := capCompression V hV
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  refine ⟨c₀ + c + btyp + 1, fun cstar hcstar n e r pA pB x A B mode auxA auxB Pobj h hrn hmode
    hauxA hauxB hacqA hacqB hLa hLb => ?_⟩
  have hH := mc_one_le_baseBudget n e
  set L := cstar * (baseBudget n e + r) with hL
  have hLreal : (L : ℝ) = cstar * ((baseBudget n e : ℝ) + r) := by rw [hL]; push_cast; ring
  have hcov : (c₀ : ℝ) * baseBudget n e ≤ L := by
    rw [hLreal]
    have h1 : (c₀ : ℝ) ≤ cstar := by exact_mod_cast (by omega : c₀ ≤ cstar)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hm := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
    have hc0r : (0 : ℝ) ≤ (c₀ : ℝ) * r := by positivity
    linarith
  obtain ⟨F, hF⟩ := hc₀ n e pA pB x A B L h hcov hLa hLb
  refine ⟨F, hF, ?_⟩
  set K := (condK V x Pobj).toNat with hK
  have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨x, (coreOf_spec hF).2⟩
  have hcard : F.card ≤ 2 ^ (K + 1) := by
    by_contra hlt
    have hxU := mem_vertexResidual_of_lt_card hF (not_le.mp hlt)
    have htA := (htyp n e x A h.length_x h.le_n h.sufA).1
    have htB := (htyp n e x B h.length_x h.le_n h.sufB).1
    have hcs : (c + btyp + 1 : ℝ) ≤ cstar := by exact_mod_cast (by omega : c + btyp + 1 ≤ cstar)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
    rcases hc n e pA pB x A B L mode 0 auxA auxB Pobj h hLa.le hLb.le (Nat.zero_le _)
      (by omega) (by omega) (by omega) hxU hacqA hacqB with hA | hB
    · rw [Nat.cast_sub hLa.le, hLreal] at hA
      have haux : (auxA.length : ℝ) ≤ r := by exact_mod_cast hauxA
      have hm := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
      have hcr : (0 : ℝ) ≤ ((c : ℝ) + btyp) * r := by positivity
      linarith
    · rw [Nat.cast_sub hLb.le, hLreal] at hB
      have haux : (auxB.length : ℝ) ≤ r := by exact_mod_cast hauxB
      have hm := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
      have hcr : (0 : ℝ) ≤ ((c : ℝ) + btyp) * r := by positivity
      linarith
  have hK1 : Real.logb 2 F.card ≤ ((K + 1 : ℕ) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast hFpos), Real.rpow_natCast]
    exact_mod_cast hcard
  have hKC : (K : ℝ) = condC V x Pobj := rfl
  push_cast at hK1
  linarith

/-- **The common factor from `x`.**  If `P` has an ordinary description of length `≤ r` from `A`,
and `A = p_A(x)` for a total witness of length `≤ e`, then `C(P | x) ≤ e + r + b ⌈log₂ (n + 2)⌉`
(`e, r ≤ n`).

Proof sketch: `upperComplexityChain_trans` with `u = P`, `v = code A`, `w = x`:
`C(P | x) ≤ C(A | x) + C(P | A) + c log₂ (C(A | x) + C(P | A) + 2)`; `C(A | x) ≤ CT(A | x) + c' ≤
e + c'` (`condC_le_totalC_add`, `Lower.totalC_le_length_of_totalProgram`); the logarithm of a
quantity `≤ 2 n + c' + 2` is at most `c'' ⌈log₂ (n + 2)⌉` (`logb_add_two_mono`,
`logb_linear_le_headerLog`). -/
theorem condC_factor_le (V : Map) (hV : isOptimalConditional V) :
    ∃ b : ℕ, ∀ (n e r : ℕ) (x pA Pobj : BitString) (A : Finset BitString), x.length = n →
      e ≤ n → r ≤ n → IsTotalProgram universalDecompressor pA → pA.length ≤ e →
      produces universalDecompressor pA x (canonicalFiniteSetCode A) →
      condC V Pobj (canonicalFiniteSetCode A) ≤ r →
        condC V Pobj x ≤ e + r + b * headerLog n := by
  obtain ⟨ct, hct⟩ := upperComplexityChain_trans V hV
  obtain ⟨cT, hcT⟩ := condC_le_totalC_add V hV
  obtain ⟨ch, hch⟩ := logb_linear_le_headerLog 2 cT
  refine ⟨ct * ch + cT, fun n e r x pA Pobj A hx hen hrn hpA hlen hprod hP => ?_⟩
  have h1 := hct Pobj (canonicalFiniteSetCode A) x
  have hT : totalC (canonicalFiniteSetCode A) x ≤ pA.length :=
    Lower.totalC_le_length_of_totalProgram hpA hprod
  have hAx : condC V (canonicalFiniteSetCode A) x ≤ e + cT := by
    have := hcT (canonicalFiniteSetCode A) x
    have hl : (pA.length : ℝ) ≤ e := by exact_mod_cast hlen
    linarith
  have hsum0 : 0 ≤ condC V (canonicalFiniteSetCode A) x + condC V Pobj (canonicalFiniteSetCode A) :=
    add_nonneg (condC_nonneg _ _ _) (condC_nonneg _ _ _)
  have hsum : condC V (canonicalFiniteSetCode A) x + condC V Pobj (canonicalFiniteSetCode A) ≤
      ((2 : ℕ) : ℝ) * n + ((cT : ℕ) : ℝ) := by
    have h3 : (e : ℝ) ≤ n := by exact_mod_cast hen
    have h4 : (r : ℝ) ≤ n := by exact_mod_cast hrn
    push_cast
    linarith
  have hlog := (logb_add_two_mono hsum0 hsum).trans (hch n)
  have hct0 : (0 : ℝ) ≤ ct := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlog hct0
  have hl1 : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hcT' : (cT : ℝ) ≤ cT * headerLog n := le_mul_of_one_le_right (Nat.cast_nonneg _) hl1
  push_cast
  linarith

/-- **Swap of a pair**: `C(v, u) ≤ C(u, v) + c` (a computable re-pairing). -/
theorem mc_pairC_swap_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ u v : BitString, pairC V v u ≤ pairC V u v + c := by
  have hf : Computable fun w : BitString => pairCode (decodeSecond w) (decodeFirst w) :=
    CodedFiniteDistribution.pairCode_primrec.to_comp.comp decodeSecond_computable
      decodeFirst_computable
  obtain ⟨c, hc⟩ := plainK_map_le V hV _ hf
  refine ⟨c, fun u v => ?_⟩
  have h := hc (pairCode u v)
  rw [decodeFirst_pairCode, decodeSecond_pairCode] at h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (plainK_ne_top V hV (pairCode u v))
  have h1 : plainK V (pairCode v u) ≤ ((k + c : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, hk]
    exact h
  have h2 : pairC V u v = k := by rw [pairC, plainC, ← hk, ENat.toNat_natCast]
  rw [h2]
  unfold pairC plainC
  exact_mod_cast toNat_le_of_le_natCast h1

/-- **Symmetry of information at linear complexities.**  For every `c₁` there is `b` such that if
`C(u) ≤ c₁ (n + 1)` and `C(v | u) ≤ c₁ (n + 1)` then
`C(v) + C(u | v) ≤ C(u) + C(v | u) + b ⌈log₂ (n + 2)⌉`.

Proof sketch: `upperComplexityChain_lower` for `(v, u)`: `C(v) + C(u | v) ≤ C(v, u) + c log₂ (…)`;
swap `C(v, u) ≤ C(u, v) + c'` (computable swap of `pairCode`, `plainK_map_le`); and
`upperComplexityChain_upper` for `(u, v)`.  All joint complexities are `O(n)`: `C(v) ≤ 2 c₁ (n + 1)
+ O(log n)` (`upperComplexityChain_trans` with `w = []`) and `pairC_le_crude`; their logarithms are
`O(⌈log₂ (n + 2)⌉)` (`logb_add_two_mono`, `logb_linear_le_headerLog`). -/
theorem chain_swap_le (V : Map) (hV : isOptimalConditional V) (c₁ : ℕ) :
    ∃ b : ℕ, ∀ (n : ℕ) (u v : BitString), plainC V u ≤ c₁ * (n + 1) →
      condC V v u ≤ c₁ * (n + 1) →
        plainC V v + condC V u v ≤ plainC V u + condC V v u + b * headerLog n := by
  obtain ⟨cl, hcl⟩ := upperComplexityChain_lower V hV
  obtain ⟨cu, hcu⟩ := upperComplexityChain_upper V hV
  obtain ⟨cs, hcs⟩ := mc_pairC_swap_le V hV
  obtain ⟨ccr, hcr⟩ := pairC_le_crude V hV
  obtain ⟨ctr, hctr⟩ := upperComplexityChain_trans V hV
  obtain ⟨k₁, hk₁⟩ := logb_linear_le_headerLog (2 * c₁) (2 * c₁)
  obtain ⟨k₂, hk₂⟩ := logb_linear_le_headerLog (5 * c₁ + ctr * k₁) (5 * c₁ + ctr * k₁ + ccr + cs)
  refine ⟨cl * k₂ + cu * k₂ + cs, fun n u v hu hv => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl1 : (1 : ℝ) ≤ headerLog n := by exact_mod_cast one_le_headerLog n
  have hln : (headerLog n : ℝ) ≤ n + 1 := by exact_mod_cast mc_headerLog_le_add_one n
  have hc10 : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  have hctr0 : (0 : ℝ) ≤ ctr := Nat.cast_nonneg _
  have hk10 : (0 : ℝ) ≤ k₁ := Nat.cast_nonneg _
  have hccr0 : (0 : ℝ) ≤ ccr := Nat.cast_nonneg _
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg _
  have hv0 := hctr v u []
  rw [← plainC_eq_condC_nil V v, ← plainC_eq_condC_nil V u] at hv0
  have hs0 : 0 ≤ plainC V u + condC V v u := add_nonneg (plainC_nonneg _ _) (condC_nonneg _ _ _)
  have hlogA : Real.logb 2 (plainC V u + condC V v u + 2) ≤ k₁ * headerLog n := by
    have hs1 : plainC V u + condC V v u ≤ ((2 * c₁ : ℕ) : ℝ) * n + ((2 * c₁ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact (logb_add_two_mono hs0 hs1).trans (hk₁ n)
  have hCv : plainC V v ≤ ((2 * c₁ + ctr * k₁ : ℕ) : ℝ) * (n + 1) := by
    have m1 := mul_le_mul_of_nonneg_left hlogA hctr0
    have hk1n : (k₁ : ℝ) * headerLog n ≤ k₁ * (n + 1) :=
      mul_le_mul_of_nonneg_left hln hk10
    have m2 := mul_le_mul_of_nonneg_left hk1n hctr0
    push_cast
    linarith
  have hCuv : pairC V u v ≤ ((5 * c₁ + ctr * k₁ : ℕ) : ℝ) * n +
      ((5 * c₁ + ctr * k₁ + ccr + cs : ℕ) : ℝ) := by
    have := hcr u v
    push_cast at hCv ⊢
    linarith
  have hCvu : pairC V v u ≤ ((5 * c₁ + ctr * k₁ : ℕ) : ℝ) * n +
      ((5 * c₁ + ctr * k₁ + ccr + cs : ℕ) : ℝ) := by
    have := hcs u v
    have h' : pairC V u v ≤ ((5 * c₁ + ctr * k₁ : ℕ) : ℝ) * n +
        ((5 * c₁ + ctr * k₁ + ccr : ℕ) : ℝ) := by
      have := hcr u v
      push_cast at hCv ⊢
      linarith
    push_cast at h' ⊢
    linarith
  have hL1 := (logb_add_two_mono (pairC_nonneg V v u) hCvu).trans (hk₂ n)
  have hL2 := (logb_add_two_mono (pairC_nonneg V u v) hCuv).trans (hk₂ n)
  have h1 := hcl v u
  have h2 := hcu u v
  have h3 := hcs u v
  have m1 := mul_le_mul_of_nonneg_left hL1 (Nat.cast_nonneg cl : (0 : ℝ) ≤ cl)
  have m2 := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg cu : (0 : ℝ) ≤ cu)
  have hcs' : (cs : ℝ) ≤ cs * headerLog n := le_mul_of_one_le_right hcs0 hl1
  push_cast
  linarith

/-- **The common-factor initial cap (blueprint M05, `UpperInitialFactorCap`;
`lem:ordinary-factor-initial-core`).**  For an optimal plain machine `V` there are constants
`c_min`, `b` such that for every `c_* ≥ c_min`, with `L_r = c_* (H + r)`: at every qualifying
instance and `0 ≤ r ≤ n` with `L_r < a, b`, and every object `P` with `C(P | A), C(P | B) ≤ r`
(ordinary, possibly partial extraction programs), the selected core `F_{L_r}` exists and
`log₂ |F_{L_r}| ≤ C(x | P) + 1 ≤ k - C(P) + b (H + r)`.  The core does not depend on `P`. -/
theorem upperInitialFactorCap (V : Map) (hV : isOptimalConditional V) :
    ∃ cmin bfac : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r : ℕ) (pA pB x : BitString)
      (A B : Finset BitString) (Pobj : BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
        cstar * (baseBudget n e + r) < Nat.log 2 A.card →
        cstar * (baseBudget n e + r) < Nat.log 2 B.card →
        condC V Pobj (canonicalFiniteSetCode A) ≤ r → condC V Pobj (canonicalFiniteSetCode B) ≤ r →
          ∃ F, coreOf (coreShape pA pB n A B) (cstar * (baseBudget n e + r)) x = some F ∧
            Real.logb 2 F.card ≤ condC V x Pobj + 1 ∧
            condC V x Pobj + 1 ≤ plainC V x - plainC V Pobj + bfac * (baseBudget n e + r) := by
  obtain ⟨cmin, hcore⟩ := factorCap_core V hV
  obtain ⟨b₁, hb₁⟩ := condC_factor_le V hV
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨b₂, hb₂⟩ := chain_swap_le V hV (blit + b₁ + 2)
  refine ⟨cmin, b₁ + b₂ + 2, fun cstar hcstar n e r pA pB x A B Pobj h hrn hLa hLb hPA hPB => ?_⟩
  obtain ⟨pa, hpa, hpalen⟩ := Lower.exists_program_of_condC V hV Pobj (canonicalFiniteSetCode A)
  obtain ⟨pb, hpb, hpblen⟩ := Lower.exists_program_of_condC V hV Pobj (canonicalFiniteSetCode B)
  have hpar : pa.length ≤ r := by
    have : (pa.length : ℝ) ≤ r := hpalen ▸ hPA
    exact_mod_cast this
  have hpbr : pb.length ≤ r := by
    have : (pb.length : ℝ) ≤ r := hpblen ▸ hPB
    exact_mod_cast this
  have hacqA :
      Pobj ∈ acquire V (coreShape pA pB n A B) 1 0 false pa (canonicalFiniteSetCode A) := by
    simpa [acquire] using hpa
  have hacqB :
      Pobj ∈ acquire V (coreShape pA pB n A B) 1 0 true pb (canonicalFiniteSetCode B) := by
    simpa [acquire] using hpb
  obtain ⟨F, hF, hcap⟩ := hcore cstar hcstar n e r pA pB x A B 1 pa pb Pobj h hrn le_rfl hpar hpbr
    hacqA hacqB hLa hLb
  refine ⟨F, hF, hcap, ?_⟩
  -- the chain rule
  have hH := mc_one_le_baseBudget n e
  have hhl := mc_headerLog_le_baseBudget n e
  have hhn : (headerLog n : ℝ) ≤ n + 1 := by exact_mod_cast mc_headerLog_le_add_one n
  have h1 := hb₁ n e r x pA Pobj A h.length_x h.le_n hrn h.totalA h.lenA h.prodA hPA
  have hx := hlit x
  rw [h.length_x] at hx
  have hen : (e : ℝ) ≤ n := by exact_mod_cast h.le_n
  have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hb0 : (0 : ℝ) ≤ b₁ := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbn : (0 : ℝ) ≤ ((blit : ℝ) + b₁ + 1) * n := by positivity
  have hbl : (b₁ : ℝ) * headerLog n ≤ b₁ * (n + 1) :=
    mul_le_mul_of_nonneg_left hhn (Nat.cast_nonneg _)
  have hblit : (0 : ℝ) ≤ blit := Nat.cast_nonneg _
  have hbn2 : (0 : ℝ) ≤ (blit : ℝ) * n := by positivity
  have hl0 : (0 : ℝ) ≤ headerLog n := Nat.cast_nonneg _
  have hu : plainC V x ≤ ((blit + b₁ + 2 : ℕ) : ℝ) * (n + 1) := by
    push_cast
    linarith
  have hv : condC V Pobj x ≤ ((blit + b₁ + 2 : ℕ) : ℝ) * (n + 1) := by
    push_cast
    linarith
  have h2 := hb₂ n x Pobj hu hv
  have hBr : (baseBudget n e : ℝ) = e + headerLog n := by unfold baseBudget; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hb10 : (b₁ : ℝ) * headerLog n ≤ b₁ * baseBudget n e :=
    mul_le_mul_of_nonneg_left hhl (Nat.cast_nonneg _)
  have hb20 : (b₂ : ℝ) * headerLog n ≤ b₂ * baseBudget n e :=
    mul_le_mul_of_nonneg_left hhl (Nat.cast_nonneg _)
  have hbr : (0 : ℝ) ≤ ((b₁ : ℝ) + b₂ + 1) * r := by positivity
  push_cast
  linarith

/-! ### M07: the initial profile cap -/

/-- **The initial profile cap (blueprint M07, `UpperInitialProfileCap`;
eq. `extractability-initial-size`).**  For an optimal plain machine `V` there are constants
`c_min`, `b` such that for every `c_* ≥ c_min`, with `L_r = c_* (H + r)`: at every qualifying
instance and `0 ≤ r ≤ n` with `L_r < a, b`, the selected core `F_{L_r}` exists and
`log₂ |F_{L_r}| ≤ k - 𝓔_p(r) + b (H + r)`.  A positive profile value is attained (M06) and M05
applies to an attaining object; the value zero uses the unconditional enumeration (mode `0`), with
no empty program for a constant object. -/
theorem upperInitialProfileCap (V : Map) (hV : isOptimalConditional V) :
    ∃ cmin bini : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r : ℕ) (pA pB x : BitString)
      (A B : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
        cstar * (baseBudget n e + r) < Nat.log 2 A.card →
        cstar * (baseBudget n e + r) < Nat.log 2 B.card →
          ∃ F, coreOf (coreShape pA pB n A B) (cstar * (baseBudget n e + r)) x = some F ∧
            Real.logb 2 F.card ≤ plainC V x - ordinaryCommonProfile V A B r +
              bini * (baseBudget n e + r) := by
  obtain ⟨cmin₁, hcore⟩ := factorCap_core V hV
  obtain ⟨cmin₂, bfac, hfac⟩ := upperInitialFactorCap V hV
  refine ⟨cmin₁ + cmin₂, bfac + 1, fun cstar hcstar n e r pA pB x A B h hrn hLa hLb => ?_⟩
  have hH := mc_one_le_baseBudget n e
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases (ordinaryCommonProfile_spec V hV A B r).2 with h0 | ⟨P, hPk, hPA, hPB⟩
  · -- zero profile: the unconditional enumeration
    have hacq : ∀ side y, ([] : BitString) ∈
        acquire V (coreShape pA pB n A B) 0 0 side [] y := by
      intro side y
      simp [acquire]
    obtain ⟨F, hF, hcap⟩ := hcore cstar (by omega) n e r pA pB x A B 0 [] [] [] h hrn
      (Nat.zero_le _) (by simp) (by simp) (hacq false _) (hacq true _) hLa hLb
    refine ⟨F, hF, ?_⟩
    rw [h0]
    rw [← plainC_eq_condC_nil] at hcap
    have hbf : (0 : ℝ) ≤ (bfac : ℝ) * (baseBudget n e + r) := by positivity
    push_cast
    linarith
  · -- positive profile: an attaining common factor
    have hA : condC V P (canonicalFiniteSetCode A) ≤ r := by
      unfold condC
      exact_mod_cast toNat_le_of_le_natCast hPA
    have hB : condC V P (canonicalFiniteSetCode B) ≤ r := by
      unfold condC
      exact_mod_cast toNat_le_of_le_natCast hPB
    obtain ⟨F, hF, h1, h2⟩ := hfac cstar (by omega) n e r pA pB x A B P h hrn hLa hLb hA hB
    refine ⟨F, hF, ?_⟩
    have hCP : plainC V P = ordinaryCommonProfile V A B r := by
      rw [plainC, hPk, ENat.toNat_natCast]
    rw [hCP] at h2
    have hpos : (0 : ℝ) ≤ baseBudget n e + r := by positivity
    push_cast
    linarith

/-! ### M08: the adjacent cap -/

/-- **The adjacent cap (blueprint M08, `UpperAdjacentCap`; eq. `extractability-adjacent`).**  For
an optimal plain machine `V` there are constants `c_min`, `b` such that for every `c_* ≥ c_min`,
with `L = c_* (H + r)`: at every qualifying instance, `0 ≤ r ≤ n` and budget `s` with
`s + L < a, b`, if the selected core `F_s ∋ x` exists, then the selected core `F_{s+L}` exists and
`log₂ |F_{s+L}| ≤ C(x | F_s) + 1` and `Score(F_s, x) ≤ log₂ |F_s| - log₂ |F_{s+L}| + b H`.
(The blueprint also assumes `L ≤ s`; it is not needed.)  No inclusion between `F_s` and
`F_{s+L}` is assumed. -/
theorem upperAdjacentCap (V : Map) (hV : isOptimalConditional V) :
    ∃ cmin badj : ℕ, ∀ cstar : ℕ, cmin ≤ cstar → ∀ (n e r s : ℕ) (pA pB x : BitString)
      (A B Fs : Finset BitString), IsCoreInstance V n e pA pB x A B → r ≤ n →
        s + cstar * (baseBudget n e + r) < Nat.log 2 A.card →
        s + cstar * (baseBudget n e + r) < Nat.log 2 B.card →
        coreOf (coreShape pA pB n A B) s x = some Fs →
          ∃ F', coreOf (coreShape pA pB n A B) (s + cstar * (baseBudget n e + r)) x = some F' ∧
            Real.logb 2 F'.card ≤ condC V x (canonicalFiniteSetCode Fs) + 1 ∧
            modelScore V Fs x ≤ Real.logb 2 Fs.card - Real.logb 2 F'.card +
              badj * baseBudget n e := by
  obtain ⟨c₀, hc₀⟩ := upperMinCoreCoverage V hV
  obtain ⟨c, hc⟩ := capCompression V hV
  obtain ⟨btyp, bsize, htyp⟩ := upperTypicality V hV
  obtain ⟨cpt, hpt⟩ := upperMinCoreLocalDecoder V hV
  obtain ⟨blit, hlit⟩ := plainC_le_length_add V hV
  obtain ⟨b₂, hb₂⟩ := chain_swap_le V hV (blit + 2 * cpt + 1)
  refine ⟨c₀ + c + btyp + 2, cpt + b₂ + 1, fun cstar hcstar n e r s pA pB x A B Fs h hrn hLa hLb
    hFs => ?_⟩
  have hH := mc_one_le_baseBudget n e
  have hhl := mc_headerLog_le_baseBudget n e
  have hxG := h.mem_shapeEdges
  set L := cstar * (baseBudget n e + r) with hL
  have hLreal : (L : ℝ) = cstar * ((baseBudget n e : ℝ) + r) := by rw [hL]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hcs : (c₀ + c + btyp + 2 : ℝ) ≤ cstar := by
    exact_mod_cast (by omega : c₀ + c + btyp + 2 ≤ cstar)
  have hcov : (c₀ : ℝ) * baseBudget n e ≤ ((s + L : ℕ) : ℝ) := by
    push_cast
    rw [hLreal]
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hm := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
    have hcr : (0 : ℝ) ≤ ((c₀ : ℝ) + c + btyp + 2) * r := by positivity
    have hcH : (0 : ℝ) ≤ ((c : ℝ) + btyp + 2) * baseBudget n e := by positivity
    linarith
  obtain ⟨F', hF'⟩ := hc₀ n e pA pB x A B (s + L) h hcov hLa hLb
  have hcap1 : Real.logb 2 F'.card ≤ condC V x (canonicalFiniteSetCode Fs) + 1 := by
    -- the cap: the local rank of `F_s` costs `s + 1`, the orientation rank `a - s - L`
    set K := (condK V x (canonicalFiniteSetCode Fs)).toNat with hK
    have hFpos : 0 < F'.card := Finset.card_pos.mpr ⟨x, (coreOf_spec hF').2⟩
    have hcard : F'.card ≤ 2 ^ (K + 1) := by
      by_contra hlt
      have hxU := mem_vertexResidual_of_lt_card hF' (not_le.mp hlt)
      have hsa : s ≤ (coreShape pA pB n A B).a := by
        change s ≤ Nat.log 2 A.card
        omega
      have hsb : s ≤ (coreShape pA pB n A B).b := by
        change s ≤ Nat.log 2 B.card
        omega
      obtain ⟨iA, hiA, hiAF⟩ := exists_local_index hsa hsb hxG hFs false
      obtain ⟨iB, hiB, hiBF⟩ := exists_local_index hsa hsb hxG hFs true
      have hlenA : (Nat.bits iA).length ≤ s + 1 := by
        rw [Nat.size_eq_bits_len, Nat.size_le]
        exact hiA
      have hlenB : (Nat.bits iB).length ≤ s + 1 := by
        rw [Nat.size_eq_bits_len, Nat.size_le]
        exact hiB
      have hacqA : canonicalFiniteSetCode Fs ∈ acquire V (coreShape pA pB n A B) 2 s false
          (Nat.bits iA) (canonicalFiniteSetCode A) := by
        have hy : coreEnd false (canonicalFiniteSetCode A) =
            shapeSrc (coreShape pA pB n A B) x := by
          simp only [coreEnd, shapeSrc, h.outA_eq, Bool.false_eq_true, ↓reduceIte]
        simp only [acquire, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.succ_ne_self, hy,
          decodeBits_natBits]
        simp only [Bool.false_eq_true, ↓reduceIte] at hiAF
        rw [hiAF]
        exact Part.mem_some _
      have hacqB : canonicalFiniteSetCode Fs ∈ acquire V (coreShape pA pB n A B) 2 s true
          (Nat.bits iB) (canonicalFiniteSetCode B) := by
        have hy : coreEnd true (canonicalFiniteSetCode B) =
            shapeTgt (coreShape pA pB n A B) x := by
          simp only [coreEnd, shapeTgt, h.outB_eq, ↓reduceIte]
        simp only [acquire, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.succ_ne_self, hy,
          decodeBits_natBits]
        simp only [↓reduceIte] at hiBF
        rw [hiBF]
        exact Part.mem_some _
      have htA := (htyp n e x A h.length_x h.le_n h.sufA).1
      have htB := (htyp n e x B h.length_x h.le_n h.sufB).1
      rcases hc n e pA pB x A B (s + L) 2 s (Nat.bits iA) (Nat.bits iB)
        (canonicalFiniteSetCode Fs) h hLa.le hLb.le (by omega) le_rfl (by omega) (by omega)
        hxU hacqA hacqB with hA | hB
      · rw [Nat.cast_sub hLa.le] at hA
        have haux : ((Nat.bits iA).length : ℝ) ≤ s + 1 := by exact_mod_cast hlenA
        push_cast at hA
        rw [hLreal] at hA
        have hm := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
        have hcr : (0 : ℝ) ≤ ((c₀ : ℝ) + c + btyp + 2) * r := by positivity
        have hcH : (0 : ℝ) ≤ (c₀ : ℝ) * baseBudget n e := by positivity
        linarith
      · rw [Nat.cast_sub hLb.le] at hB
        have haux : ((Nat.bits iB).length : ℝ) ≤ s + 1 := by exact_mod_cast hlenB
        push_cast at hB
        rw [hLreal] at hB
        have hm := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℝ) ≤ baseBudget n e + r)
        have hcr : (0 : ℝ) ≤ ((c₀ : ℝ) + c + btyp + 2) * r := by positivity
        have hcH : (0 : ℝ) ≤ (c₀ : ℝ) * baseBudget n e := by positivity
        linarith
    have hK1 : Real.logb 2 F'.card ≤ ((K + 1 : ℕ) : ℝ) := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast hFpos), Real.rpow_natCast]
      exact_mod_cast hcard
    have hKC : (K : ℝ) = condC V x (canonicalFiniteSetCode Fs) := rfl
    push_cast at hK1
    linarith
  refine ⟨F', hF', hcap1, ?_⟩
  -- the score: the point decoder and the chain rule
  have hsa' : s ≤ Nat.log 2 A.card := by omega
  have hsb' : s ≤ Nat.log 2 B.card := by omega
  have hpt' := (hpt n e pA pB x A B s Fs h hsa' hsb' hFs).2.2
  have hx := hlit x
  rw [h.length_x] at hx
  have hHn : (baseBudget n e : ℝ) ≤ 2 * n + 1 := by
    have h1 := mc_headerLog_le_add_one n
    have h2 := h.le_n
    have h3 : baseBudget n e ≤ 2 * n + 1 := by unfold baseBudget; omega
    exact_mod_cast h3
  have hcpt0 : (0 : ℝ) ≤ cpt := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hbn : (0 : ℝ) ≤ ((blit : ℝ) + 2 * cpt) * n := by positivity
  have hblit : (0 : ℝ) ≤ blit := Nat.cast_nonneg _
  have hbn2 : (0 : ℝ) ≤ (blit : ℝ) * n := by positivity
  have hcH := mul_le_mul_of_nonneg_left hHn hcpt0
  have hu : plainC V x ≤ ((blit + 2 * cpt + 1 : ℕ) : ℝ) * (n + 1) := by
    push_cast
    linarith
  have hv : condC V (canonicalFiniteSetCode Fs) x ≤
      ((blit + 2 * cpt + 1 : ℕ) : ℝ) * (n + 1) := by
    push_cast
    linarith
  have h2 := hb₂ n x (canonicalFiniteSetCode Fs) hu hv
  have hb20 : (b₂ : ℝ) * headerLog n ≤ b₂ * baseBudget n e :=
    mul_le_mul_of_nonneg_left hhl (Nat.cast_nonneg _)
  unfold modelScore setC
  push_cast
  linarith

end Kolmogorov.StrongMerging.Upper
