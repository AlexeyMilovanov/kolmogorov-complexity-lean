import KolmogorovMathlib.Restricted.FamilyCurve.VersionPartrec2
import KolmogorovMathlib.Restricted.FamilyCurve.AnchoredChain
import KolmogorovMathlib.Encoding.TuplesComplexity

/-!
# M7: terminal evaluation of the version decoder

Given the event chain of the anchored run, the version decoder — fed the
encoded grid, the covering overhead, the scale, and the number of changes of
the decoded scale-`s` model list up to the terminal event — outputs exactly
the canonical uniform code of the terminal sampled model, and that ordinal is
bounded by the chain's rebuild count.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-- The number of changes of the decoded scale-`s` model list along a code
trace. -/
def anchoredListChangeCount (s : ℕ) (codes : ℕ → BitString) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if anchoredModelListAt s (codes (m + 1)) =
          anchoredModelListAt s (codes m) then
        anchoredListChangeCount s codes m
      else
        anchoredListChangeCount s codes m + 1

/-- One step changes the count by at most one. -/
lemma anchoredListChangeCount_succ_le (s : ℕ) (codes : ℕ → BitString)
    (m : ℕ) :
    anchoredListChangeCount s codes m ≤
      anchoredListChangeCount s codes (m + 1) := by
  rw [anchoredListChangeCount]
  split <;> omega

/-- The change count is monotone in the event index. -/
lemma anchoredListChangeCount_mono (s : ℕ) (codes : ℕ → BitString)
    {m m' : ℕ} (h : m ≤ m') :
    anchoredListChangeCount s codes m ≤ anchoredListChangeCount s codes m' := by
  induction h with
  | refl => exact le_rfl
  | @step m'' _ ih =>
      exact ih.trans (anchoredListChangeCount_succ_le s codes m'')

/-- A stalled count step means the decoded list did not change. -/
lemma anchoredListChangeCount_succ_eq_iff (s : ℕ) (codes : ℕ → BitString)
    (m : ℕ) :
    anchoredListChangeCount s codes (m + 1) =
        anchoredListChangeCount s codes m ↔
      anchoredModelListAt s (codes (m + 1)) =
        anchoredModelListAt s (codes m) := by
  rw [anchoredListChangeCount]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hEq => absurd hEq (by omega), fun hEq => absurd hEq h⟩

/-- Evaluation of the decoder on an explicit four-component bundle. -/
lemma anchoredVersionDecoder_eval (𝒜 : DescriptionFamily) (c : Code)
    (g q0b sb vb : BitString) :
    anchoredVersionDecoder 𝒜 c (listCode [g, q0b, sb, vb]) =
      (Nat.rfind (fun m =>
        (anchoredChangeTrace 𝒜 c g (bitsToNat q0b) (bitsToNat sb) m).map
          (fun p => decide (bitsToNat vb ≤ p.1)))).bind
        (fun m =>
          (anchoredChangeTrace 𝒜 c g (bitsToNat q0b) (bitsToNat sb) m).map
            (fun p => uniformCodeOfList p.2)) := by
  unfold anchoredVersionDecoder
  rw [decodeListCode_listCode]
  rfl

/-- Terminal decoder evaluation over the anchored event chain: the change
count of the decoded scale-`s` list is bounded by the chain's rebuild count,
and the decoder at that ordinal returns the terminal model's canonical
uniform code. -/
lemma anchoredVersionDecoder_terminal
    (𝒜 : DescriptionFamily) (c : Code)
    {n k N : ℕ} {target : ℕ → ℕ}
    (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (T : ℕ)
    (chain : RestrictedRunChain 𝒜 (N + 1) (n + logSlack 8 n)
        (2 * 𝒜.overhead (n + logSlack 8 n))
        (restrictedAnchoredTarget (n + logSlack 8 n) (sqrtSlack 8 n) grid)
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)
    (codes : ℕ → BitString)
    (hfold : ∀ m,
      (restrictedEffectiveAnchoredInitialState 𝒜 (n + logSlack 8 n)
          (sqrtSlack 8 n) grid).bind
        (fun st0 => restrictedEventPrefixRun 𝒜
          (𝒜.overhead (n + logSlack 8 n))
          (restrictedEffectiveAnchoredSizes (n + logSlack 8 n)
            (sqrtSlack 8 n) grid) st0
          (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
            𝒜.toPre N (sqrtSlack 8 n) T) m) = Part.some (codes m) ∧
      DecodesToRestrictedSampledRunState (codes m) (chain.states m))
    (s : ℕ) (hs : s ≤ N)
    (hS : ((chain.states (restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
          T).length).B (s + 1)).Nonempty) :
    ∃ v, v ≤ (chain.rebuildSteps s).card ∧
      anchoredVersionDecoder 𝒜 c
        (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)),
          Nat.bits s, Nat.bits v]) =
      Part.some ((codedUniformOn ((chain.states
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length).B (s + 1)) hS).code) := by
  classical
  -- the decoded change trace follows the chain codes
  have htrace : ∀ m,
      m ≤ (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length →
      anchoredChangeTrace 𝒜 c (restrictedCurveGridCode grid)
          (𝒜.overhead (n + logSlack 8 n)) s m =
        Part.some (anchoredListChangeCount s codes m,
          anchoredModelListAt s (codes m)) := by
    intro m hm
    induction m with
    | zero =>
        rw [anchoredChangeTrace,
          anchoredDecoderTrace_replay 𝒜 c grid hN T 0 (codes 0)
            (by omega) (hfold 0).1,
          Part.map_some]
        rfl
    | succ m ih =>
        rw [anchoredChangeTrace, ih (by omega), Part.bind_some,
          anchoredDecoderTrace_replay 𝒜 c grid hN T (m + 1) (codes (m + 1))
            (by omega) (hfold (m + 1)).1,
          Part.map_some]
        by_cases hEq : anchoredModelListAt s (codes (m + 1)) =
            anchoredModelListAt s (codes m)
        · rw [if_pos hEq]
          rw [show anchoredListChangeCount s codes (m + 1) =
              anchoredListChangeCount s codes m by
            rw [anchoredListChangeCount, if_pos hEq], hEq]
        · rw [if_neg hEq]
          rw [show anchoredListChangeCount s codes (m + 1) =
              anchoredListChangeCount s codes m + 1 by
            rw [anchoredListChangeCount, if_neg hEq]]
  -- the change count is bounded by the rebuild count
  have hcount_le : ∀ m,
      m ≤ (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length →
      anchoredListChangeCount s codes m ≤
        ((Finset.range m).filter (fun a => chain.edges a ≤ s)).card := by
    intro m hm
    induction m with
    | zero => simp [anchoredListChangeCount]
    | succ m ih =>
        have hstep := ih (by omega)
        have hsub : (Finset.range m).filter (fun a => chain.edges a ≤ s) ⊆
            (Finset.range (m + 1)).filter (fun a => chain.edges a ≤ s) :=
          Finset.filter_subset_filter _
            (fun x hx => Finset.mem_range.mpr
              (Nat.lt_succ_of_lt (Finset.mem_range.mp hx)))
        by_cases hEq : anchoredModelListAt s (codes (m + 1)) =
            anchoredModelListAt s (codes m)
        · rw [anchoredListChangeCount, if_pos hEq]
          exact hstep.trans (Finset.card_le_card hsub)
        · rw [anchoredListChangeCount, if_neg hEq]
          -- a genuine list change forces a rebuild at an edge ≤ s
          have hedge : chain.edges m ≤ s := by
            by_contra hgt
            have hpres := ((chain.spec m (by omega)).2.2.1 (s + 1)
              (by omega)).1
            have h1 := anchoredModelListAt_eq (hfold m).2 s hs
            have h2 := anchoredModelListAt_eq (hfold (m + 1)).2 s hs
            rw [h1, h2, hpres] at hEq
            exact hEq rfl
          have hmem : m ∈ (Finset.range (m + 1)).filter
              (fun a => chain.edges a ≤ s) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hedge⟩
          have hnot : m ∉ (Finset.range m).filter
              (fun a => chain.edges a ≤ s) := by
            intro hmm
            exact absurd (Finset.mem_range.mp (Finset.mem_filter.mp hmm).1)
              (by omega)
          have hins : insert m ((Finset.range m).filter
              (fun a => chain.edges a ≤ s)) ⊆
              (Finset.range (m + 1)).filter (fun a => chain.edges a ≤ s) := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact hmem
            · exact hsub hx'
          calc anchoredListChangeCount s codes m + 1
              ≤ ((Finset.range m).filter
                  (fun a => chain.edges a ≤ s)).card + 1 := by omega
            _ = (insert m ((Finset.range m).filter
                  (fun a => chain.edges a ≤ s))).card :=
                (Finset.card_insert_of_notMem hnot).symm
            _ ≤ ((Finset.range (m + 1)).filter
                  (fun a => chain.edges a ≤ s)).card :=
                Finset.card_le_card hins
  -- the terminal ordinal and its first attainment
  set v := anchoredListChangeCount s codes
    (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).length with hv
  have hvexists : ∃ m, v ≤ anchoredListChangeCount s codes m :=
    ⟨(restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
      𝒜.toPre N (sqrtSlack 8 n) T).length, le_rfl⟩
  set mstar := Nat.find hvexists with hmstar
  have hmstarM : mstar ≤ (restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n) T).length :=
    Nat.find_min' hvexists le_rfl
  have hcntstar : anchoredListChangeCount s codes mstar = v := by
    have h1 : v ≤ anchoredListChangeCount s codes mstar :=
      Nat.find_spec hvexists
    have h2 : anchoredListChangeCount s codes mstar ≤ v :=
      anchoredListChangeCount_mono s codes hmstarM
    omega
  have hbelow : ∀ m' < mstar, anchoredListChangeCount s codes m' < v := by
    intro m' hm'
    have := Nat.find_min hvexists hm'
    omega
  -- the decoded list is constant from the first attainment to the end
  have hconst : ∀ m, mstar ≤ m →
      m ≤ (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length →
      anchoredModelListAt s (codes m) = anchoredModelListAt s (codes mstar) := by
    intro m hm hmM
    induction hm with
    | refl => rfl
    | @step m' hm' ih =>
        have hm'M : m' ≤ (restrictedSampledBadCodeStream c
            (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
            T).length := by omega
        have hcm' : anchoredListChangeCount s codes m' = v := by
          have h1 : v ≤ anchoredListChangeCount s codes m' := by
            rw [← hcntstar]
            exact anchoredListChangeCount_mono s codes hm'
          have h2 : anchoredListChangeCount s codes m' ≤ v :=
            anchoredListChangeCount_mono s codes hm'M
          omega
        have hcm'1 : anchoredListChangeCount s codes (m' + 1) = v := by
          have h1 : v ≤ anchoredListChangeCount s codes (m' + 1) := by
            rw [← hcm']
            exact anchoredListChangeCount_succ_le s codes m'
          have h2 : anchoredListChangeCount s codes (m' + 1) ≤ v :=
            anchoredListChangeCount_mono s codes hmM
          omega
        have hEq := (anchoredListChangeCount_succ_eq_iff s codes m').mp
          (by omega)
        exact hEq.trans (ih hm'M)
  -- the μ-search stops exactly at the first attainment
  have hrfind : Nat.rfind (fun m =>
      (anchoredChangeTrace 𝒜 c (restrictedCurveGridCode grid)
        (𝒜.overhead (n + logSlack 8 n)) s m).map
        (fun p => decide (v ≤ p.1))) = Part.some mstar := by
    rw [Part.eq_some_iff, Nat.mem_rfind]
    constructor
    · rw [htrace mstar hmstarM, Part.map_some]
      simp [hcntstar]
    · intro k hk
      rw [htrace k (by omega), Part.map_some]
      simp only [Part.mem_some_iff]
      have := hbelow k hk
      simp [Nat.not_le.mpr this]
  refine ⟨v, ?_, ?_⟩
  · exact (hcount_le _ le_rfl).trans (le_of_eq rfl)
  · rw [anchoredVersionDecoder_eval, bitsToNat_bits, bitsToNat_bits,
      bitsToNat_bits, hrfind, Part.bind_some, htrace mstar hmstarM,
      Part.map_some]
    congr 1
    have hlist : anchoredModelListAt s (codes
        (restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length) =
        anchoredModelListAt s (codes mstar) :=
      hconst _ hmstarM le_rfl
    rw [← hlist]
    exact uniformCodeOfList_anchoredModelListAt_eq
      (hfold _).2 s hs hS

section FinalAssembly

/-- `sqrtSlack` is literally a multiple of `√(n·len n) + 1`. -/
private lemma sqrtSlack_eq_mul (m n : ℕ) :
    sqrtSlack m n = m * (Nat.sqrt (n * (Nat.bits n).length) + 1) := by
  unfold sqrtSlack
  ring

/-- `sqrtSlack` is additive in its constant. -/
private lemma sqrtSlack_add' (a b n : ℕ) :
    sqrtSlack a n + sqrtSlack b n = sqrtSlack (a + b) n := by
  rw [sqrtSlack_eq_mul, sqrtSlack_eq_mul, sqrtSlack_eq_mul]
  ring

/-- Binary size is subadditive under multiplication. -/
private lemma size_mul_le (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  apply Nat.size_le.mpr
  calc a * b < 2 ^ Nat.size a * 2 ^ Nat.size b :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self a)
          (Nat.le_of_lt (Nat.lt_size_self b)) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add 2 _ _).symm

/-- A number has at most as many binary digits as its value. -/
private lemma bits_len_le_self (a : ℕ) : (Nat.bits a).length ≤ a := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self)

set_option maxHeartbeats 3200000 in
-- Raised heartbeat limit: a long `Nat`-arithmetic budget chain.
/-- The `ℕ`-level cost budget of the decoder bundle. -/
private lemma decoder_bundle_cost_le
    (𝒜 : DescriptionFamily)
    {n k N : ℕ} {target : ℕ → ℕ} (grid : RestrictedCurveGrid n k N target)
    (hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
    (hkn : k ≤ n)
    {c_over c_P : ℕ}
    (hover : ∀ m, (Nat.bits (𝒜.overhead m)).length ≤ logSlack c_over m)
    (hP : anchoredVersionExp 𝒜 n N ≤ sqrtSlack c_P n)
    {s v : ℕ} (hs : s ≤ N)
    (hv : v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N))
    (c_lg c_L c_F : ℕ) :
    ((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
        2 * (Nat.bits (Nat.bits
          (𝒜.overhead (n + logSlack 8 n))).length).length + c_lg) +
      ((Nat.bits s).length + 2 * (Nat.bits (Nat.bits s).length).length +
        c_lg) +
      ((Nat.bits v).length + 2 * (Nat.bits (Nat.bits v).length).length +
        c_lg) + c_L * 5 + c_F ≤
    grid.i s +
      sqrtSlack (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
        2 * Nat.size (c_P + 1) + 40) n := by
  set L := (Nat.bits n).length with hL
  set S := Nat.sqrt (n * L) with hS
  have hLsize : L = Nat.size n := Nat.size_eq_bits_len n
  have hn2 : n < 2 ^ L := by
    rw [hLsize]
    exact Nat.lt_size_self n
  have hLS : L ≤ S := by
    apply Nat.le_sqrt.mpr
    have hLn : L ≤ n := by
      rw [hLsize]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    exact Nat.mul_le_mul_right _ hLn
  -- ambient bit length
  have hambBits : (Nat.bits (n + logSlack 8 n)).length ≤ L + 4 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hlog : logSlack 8 n = 8 * L + 8 := by
      unfold logSlack
      rfl
    have hLpow : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    have hpow4 : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by
      rw [pow_add]
      ring
    omega
  -- q0 bit length
  have hq0 : (Nat.bits (𝒜.overhead (n + logSlack 8 n))).length ≤
      c_over * (L + 4) + c_over := by
    refine (hover (n + logSlack 8 n)).trans ?_
    unfold logSlack
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left c_over hambBits) c_over
  -- s bit length
  have hsn : s ≤ n + 1 := by
    have hNle : N ≤ n + 1 := by
      rw [hN]
      exact Nat.add_le_add_right
        ((Nat.sqrt_le_self _).trans (Nat.div_le_self n _)) 1
    omega
  have hsbits : (Nat.bits s).length ≤ L + 1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by
      rw [pow_add]
      ring
    omega
  -- v bit length
  have hisn : grid.i s ≤ n := (grid.i_le_k s hs).trans hkn
  have hvbits : (Nat.bits v).length ≤
      grid.i s + anchoredVersionExp 𝒜 n N + 1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    calc v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N) := hv
      _ < 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N + 1) :=
        Nat.pow_lt_pow_right (by omega) (by omega)
  -- double-log of the v component
  have hvlen_le : (Nat.bits v).length ≤ n + sqrtSlack c_P n + 1 := by
    refine hvbits.trans ?_
    have := hP
    omega
  have hprod : n + sqrtSlack c_P n + 1 ≤ (c_P + 1) * ((n + 1) * (L + 1)) := by
    have h1 : sqrtSlack c_P n ≤ c_P * ((n + 1) * (L + 1)) := by
      rw [sqrtSlack_eq_mul]
      apply Nat.mul_le_mul_left
      have hSn : S + 1 ≤ (n + 1) * (L + 1) := by
        have hSle : S ≤ n * L := by
          have := Nat.sqrt_le_self (n * L)
          omega
        calc S + 1 ≤ n * L + 1 := by omega
          _ ≤ (n + 1) * (L + 1) := by nlinarith
      exact hSn
    have h2 : n + 1 ≤ (n + 1) * (L + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    calc n + sqrtSlack c_P n + 1 ≤ (n + 1) + c_P * ((n + 1) * (L + 1)) := by
          omega
      _ ≤ (n + 1) * (L + 1) + c_P * ((n + 1) * (L + 1)) := by omega
      _ = (c_P + 1) * ((n + 1) * (L + 1)) := by ring
  have hvdlog : (Nat.bits (Nat.bits v).length).length ≤
      Nat.size (c_P + 1) + (L + 1) + (L + 1) + 2 := by
    rw [Nat.size_eq_bits_len]
    have hmono := Nat.size_le_size (hvlen_le.trans hprod)
    refine hmono.trans ?_
    have h1 := size_mul_le (c_P + 1) ((n + 1) * (L + 1))
    have h2 := size_mul_le (n + 1) (L + 1)
    have h3 : Nat.size (n + 1) ≤ L + 1 := by
      apply Nat.size_le.mpr
      have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by
        rw [pow_add]
        ring
      omega
    have h4 : Nat.size (L + 1) ≤ L + 1 :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  -- double-logs of the small components, crudely
  have hq0dlog : (Nat.bits (Nat.bits
      (𝒜.overhead (n + logSlack 8 n))).length).length ≤
      c_over * (L + 4) + c_over :=
    (bits_len_le_self _).trans hq0
  have hsdlog : (Nat.bits (Nat.bits s).length).length ≤ L + 1 :=
    (bits_len_le_self _).trans hsbits
  -- assemble: every additive block against `coeff * (S + 1)`
  rw [sqrtSlack_eq_mul, ← hS]
  have hq0S : c_over * (L + 4) + c_over ≤ 5 * c_over * (S + 1) := by
    have h1 : L + 4 ≤ 4 * (S + 1) := by omega
    calc c_over * (L + 4) + c_over
        ≤ c_over * (4 * (S + 1)) + c_over * (S + 1) := by
          have := Nat.mul_le_mul_left c_over h1
          have h2 : c_over ≤ c_over * (S + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          omega
      _ = 5 * c_over * (S + 1) := by ring
  have hExpS : anchoredVersionExp 𝒜 n N ≤ c_P * (S + 1) := by
    refine hP.trans ?_
    rw [sqrtSlack_eq_mul, ← hS]
  have hLS1 : L + 1 ≤ S + 1 := by omega
  have hvdlogS : Nat.size (c_P + 1) + (L + 1) + (L + 1) + 2 ≤
      (Nat.size (c_P + 1) + 4) * (S + 1) := by
    have h1 : Nat.size (c_P + 1) ≤ Nat.size (c_P + 1) * (S + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  calc ((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
        2 * (Nat.bits (Nat.bits
          (𝒜.overhead (n + logSlack 8 n))).length).length + c_lg) +
      ((Nat.bits s).length + 2 * (Nat.bits (Nat.bits s).length).length +
        c_lg) +
      ((Nat.bits v).length + 2 * (Nat.bits (Nat.bits v).length).length +
        c_lg) + c_L * 5 + c_F
      ≤ (5 * c_over * (S + 1) + 2 * (5 * c_over * (S + 1)) + c_lg) +
        ((S + 1) + 2 * (S + 1) + c_lg) +
        ((grid.i s + c_P * (S + 1) + 1) +
          2 * ((Nat.size (c_P + 1) + 4) * (S + 1)) + c_lg) +
        c_L * 5 + c_F := by
        have b1 := hq0.trans hq0S
        have b2 := hq0dlog.trans hq0S
        have b3 := hsbits.trans hLS1
        have b4 := hsdlog.trans hLS1
        have b5 : (Nat.bits v).length ≤ grid.i s + c_P * (S + 1) + 1 := by
          refine hvbits.trans ?_
          have := hExpS
          omega
        have b6 := hvdlog.trans hvdlogS
        omega
    _ ≤ grid.i s + (c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
          2 * Nat.size (c_P + 1) + 40) * (S + 1) := by
        have hpos : 1 ≤ S + 1 := by omega
        have hclg : c_lg ≤ c_lg * (S + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have hcL : c_L * 5 ≤ 5 * c_L * (S + 1) := by
          have : c_L * 5 ≤ c_L * 5 * (S + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          calc c_L * 5 ≤ c_L * 5 * (S + 1) := this
            _ = 5 * c_L * (S + 1) := by ring
        have hcF : c_F ≤ c_F * (S + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        nlinarith

/-- The version-coding theorem for a fixed decompressor code: every terminal
sampled model of the anchored run is describable by the encoded grid, the
covering overhead, the scale index, and a bounded version ordinal, so its set
complexity is the grid coordinate plus square-root slack plus the grid code's
complexity. -/
theorem restrictedAnchoredState_model_complexity
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (𝒜 : DescriptionFamily) (hPoly : 𝒜.HasPolynomialOverhead)
    (c : Code) (_hc : IsCodeFor c U) :
    ∃ c_ver : ℕ, ∀ {n k N : ℕ} {t : ℕ → ℕ}
      (grid : RestrictedCurveGrid n k N t)
      (_hN : N = Nat.sqrt (n / (Nat.log2 n + 1)) + 1)
      (_hkn : k ≤ n) (_ht0 : t 0 ≤ n)
      (_hstrict : ∀ i : ℕ, i < k → t (i + 1) < t i)
      (T : ℕ) (output : BitString)
      (state : RestrictedSampledRunState 𝒜 (N + 1)
          (n + logSlack 8 n) (2 * 𝒜.overhead (n + logSlack 8 n))
          (restrictedAnchoredTarget (n + logSlack 8 n)
            (sqrtSlack 8 n) grid)),
      restrictedEffectiveAnchoredSampledRun 𝒜 c
          (n + logSlack 8 n) (sqrtSlack 8 n) grid (T + 1) =
            Part.some output →
      DecodesToRestrictedSampledRunState output state →
      ∀ s (_hs : s ≤ N) (hS : (state.B (s + 1)).Nonempty),
        setComplexity U (state.B (s + 1)) hS ≤
          (grid.i s + sqrtSlack c_ver n +
            KPPlain U (restrictedCurveGridCode grid) : ENat) := by
  classical
  obtain ⟨c_F, hF⟩ := KPPlain_partrec_map_le U hU
    (anchoredVersionDecoder 𝒜 c) (anchoredVersionDecoder_partrec 𝒜 c)
  obtain ⟨c_L, hLc⟩ := KPPlain_listCode_le U hU
  obtain ⟨c_lg, hlg⟩ := KPPlain_le_length_add_log U hU
  obtain ⟨c_P, hPex⟩ := anchoredVersionExp_le_sqrtSlack 𝒜 hPoly
  obtain ⟨c_over, hover⟩ := 𝒜.overhead_bits_le_logSlack hPoly
  refine ⟨c_P + 15 * c_over + 3 * c_lg + 5 * c_L + c_F +
    2 * Nat.size (c_P + 1) + 40, ?_⟩
  intro n k N t grid hN hkn ht0 hstrict T output state hrun hdec s hs hS
  obtain ⟨chain, codes, hfold, hbads, hB0, hlive0, hcount⟩ :=
    exists_restrictedAnchoredEventChain_with_count 𝒜 c grid hN hkn ht0
      hstrict T
  have hboundary := restrictedEffectiveAnchoredSampledRun_eq_eventPrefix
    𝒜 c (n + logSlack 8 n) (sqrtSlack 8 n) grid (le_refl T)
  have hout : output = codes ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length) := by
    rw [hboundary] at hrun
    exact Part.some_injective (hrun.symm.trans (hfold _).1)
  have hdec' : DecodesToRestrictedSampledRunState
      (codes ((restrictedSampledBadCodeStream c
        (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
          T).length)) state := hout ▸ hdec
  have hBeq := decodesTo_eq_B_live hdec'
    ((hfold ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length)).2) (s := s + 1) (by omega)
  have hS' : ((chain.states ((restrictedSampledBadCodeStream c
      (restrictedCurveGridCode grid) 𝒜.toPre N (sqrtSlack 8 n)
        T).length)).B (s + 1)).Nonempty := by
    rw [← hBeq.1]
    exact hS
  obtain ⟨v, hvle, heval⟩ := anchoredVersionDecoder_terminal 𝒜 c grid hN T
    chain codes hfold s hs hS'
  have hv2 : v ≤ 2 ^ (grid.i s + anchoredVersionExp 𝒜 n N) :=
    hvle.trans (hcount s hs)
  have hmem : (codedUniformOn ((chain.states
      ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
        𝒜.toPre N (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code ∈
      anchoredVersionDecoder 𝒜 c
        (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)),
          Nat.bits s, Nat.bits v]) := by
    rw [heval]
    exact Part.mem_some_iff.mpr rfl
  have hKP1 := hF _ _ hmem
  have hKP2 := hLc [restrictedCurveGridCode grid,
    Nat.bits (𝒜.overhead (n + logSlack 8 n)), Nat.bits s, Nat.bits v]
  have hq0c : KPPlain U (Nat.bits (𝒜.overhead (n + logSlack 8 n))) ≤
      (((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
        2 * (Nat.bits (Nat.bits
          (𝒜.overhead (n + logSlack 8 n))).length).length + c_lg : ℕ) :
        ENat) := by
    have h := hlg (Nat.bits (𝒜.overhead (n + logSlack 8 n)))
    push_cast
    exact h
  have hsc : KPPlain U (Nat.bits s) ≤
      (((Nat.bits s).length +
        2 * (Nat.bits (Nat.bits s).length).length + c_lg : ℕ) : ENat) := by
    have h := hlg (Nat.bits s)
    push_cast
    exact h
  have hvc : KPPlain U (Nat.bits v) ≤
      (((Nat.bits v).length +
        2 * (Nat.bits (Nat.bits v).length).length + c_lg : ℕ) : ENat) := by
    have h := hlg (Nat.bits v)
    push_cast
    exact h
  have hNat := decoder_bundle_cost_le 𝒜 grid hN hkn hover (hPex n N hN)
    hs hv2 c_lg c_L c_F
  have hset : setComplexity U (state.B (s + 1)) hS =
      KPPlain U ((codedUniformOn ((chain.states
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code) := by
    unfold setComplexity
    congr 1
    exact codedUniformOn_code_congr hS hS' hBeq.1
  rw [hset]
  have hsum : (([restrictedCurveGridCode grid,
      Nat.bits (𝒜.overhead (n + logSlack 8 n)), Nat.bits s,
      Nat.bits v]).map fun x => KPPlain U x).sum =
      KPPlain U (restrictedCurveGridCode grid) +
        (KPPlain U (Nat.bits (𝒜.overhead (n + logSlack 8 n))) +
          (KPPlain U (Nat.bits s) + KPPlain U (Nat.bits v))) := by
    simp [List.sum_cons]
  calc KPPlain U ((codedUniformOn ((chain.states
        ((restrictedSampledBadCodeStream c (restrictedCurveGridCode grid)
          𝒜.toPre N (sqrtSlack 8 n) T).length)).B (s + 1)) hS').code)
      ≤ KPPlain U (listCode [restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)), Nat.bits s,
          Nat.bits v]) + (c_F : ENat) := hKP1
    _ ≤ ((([restrictedCurveGridCode grid,
          Nat.bits (𝒜.overhead (n + logSlack 8 n)), Nat.bits s,
          Nat.bits v]).map fun x => KPPlain U x).sum +
          ((c_L * 5 : ℕ) : ENat)) + (c_F : ENat) := by
        gcongr
        simpa using hKP2
    _ = KPPlain U (restrictedCurveGridCode grid) +
          (KPPlain U (Nat.bits (𝒜.overhead (n + logSlack 8 n))) +
            (KPPlain U (Nat.bits s) + KPPlain U (Nat.bits v))) +
          ((c_L * 5 : ℕ) : ENat) + (c_F : ENat) := by
        rw [hsum]
    _ ≤ KPPlain U (restrictedCurveGridCode grid) +
          ((((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
            2 * (Nat.bits (Nat.bits
              (𝒜.overhead (n + logSlack 8 n))).length).length +
            c_lg : ℕ) : ENat) +
          ((((Nat.bits s).length +
            2 * (Nat.bits (Nat.bits s).length).length + c_lg : ℕ) :
              ENat) +
          (((Nat.bits v).length +
            2 * (Nat.bits (Nat.bits v).length).length + c_lg : ℕ) :
              ENat))) + ((c_L * 5 : ℕ) : ENat) + (c_F : ENat) := by
        gcongr
    _ = KPPlain U (restrictedCurveGridCode grid) +
          ((((Nat.bits (𝒜.overhead (n + logSlack 8 n))).length +
            2 * (Nat.bits (Nat.bits
              (𝒜.overhead (n + logSlack 8 n))).length).length + c_lg) +
          ((Nat.bits s).length +
            2 * (Nat.bits (Nat.bits s).length).length + c_lg) +
          ((Nat.bits v).length +
            2 * (Nat.bits (Nat.bits v).length).length + c_lg) +
          c_L * 5 + c_F : ℕ) : ENat) := by
        push_cast
        ring
    _ ≤ KPPlain U (restrictedCurveGridCode grid) +
          ((grid.i s + sqrtSlack (c_P + 15 * c_over + 3 * c_lg +
            5 * c_L + c_F + 2 * Nat.size (c_P + 1) + 40) n : ℕ) : ENat) := by
        gcongr
    _ = (grid.i s + sqrtSlack (c_P + 15 * c_over + 3 * c_lg + 5 * c_L +
          c_F + 2 * Nat.size (c_P + 1) + 40) n +
          KPPlain U (restrictedCurveGridCode grid) : ENat) := by
        push_cast
        ring

end FinalAssembly

end Kolmogorov
