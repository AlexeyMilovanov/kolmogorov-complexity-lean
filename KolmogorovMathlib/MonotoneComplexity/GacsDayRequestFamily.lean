import KolmogorovMathlib.MonotoneComplexity.GacsDayServer
import KolmogorovMathlib.MonotoneComplexity.GacsDayReplay
import KolmogorovMathlib.MonotoneComplexity.MonotoneComplexityBounds
import KolmogorovMathlib.MonotoneComplexity.ConcatenationBound
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding.Part01
import KolmogorovMathlib.MonotoneComplexity.GacsDayEmbedding

/-!
# Decompressor-induced request family

This file states the single source-faithful bridge from an unpacked
Gács–Day winning strategy (the data `C`, `σ`, its computability, and the
uniform win) to a uniformly lower-semicomputable family of request
subsemimeasures `μ c` induced by the server that reads an optimal monotone
decompressor `D`. The signature passes `C` and `σ` explicitly: they cannot be
hidden inside `BinaryGacsDayStatement`, since the length bound
`(C * 2 ^ c) ^ (C * 2 ^ c)` mentions `C`.

The module is isolated: it does not depend on
`GrayFamilyGameSpec`, does not mention either public endpoint, and is not
imported by `GacsDayTheorems.lean`.
-/

namespace Kolmogorov
open MeasureTheory ENNReal

/-- `List.ofFn` over `Fin n` of a function on `ℕ` is the map over `List.range n`. -/
lemma ofFn_val_eq_map_range {α : Type*} (f : ℕ → α) (n : ℕ) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

/-- Reading a bit string as a node of the game tree is primitive recursive. -/
lemma primrec_gacsDayNodeOfBitString : Primrec gacsDayNodeOfBitString := by
  have hbody : Primrec₂ (fun (_ : BitString) (b : Bool) => bif b then 1 else 0) :=
    (Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)).to₂
  refine (Primrec.list_map Primrec.id hbody).of_eq ?_
  intro x
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [id_eq] at ih
      cases b <;> simp [gacsDayNodeOfBitString, ih]

/-- The `t`-th client move only depends on the first `t` moves of both players. -/
lemma playClient_eq_map_range (σ' : ClientStrategy) (sm : ℕ → ServerMove) (t : ℕ) :
    playClient σ' sm t =
      σ' ((List.range t).map (playClient σ' sm), (List.range t).map sm) := by
  cases t with
  | zero => simp [playClient]
  | succ u => rw [playClient, ofFn_val_eq_map_range, ofFn_val_eq_map_range]

/-- The client's `t`-th move is obtained by replaying the strategy against the
first `t` server moves. -/
lemma playClient_eq_selfPlay (σ' : ClientStrategy) (sm : ℕ → ServerMove) (t : ℕ) :
    playClient σ' sm t =
      σ' (selfPlay σ' ((List.range t).map sm), (List.range t).map sm) := by
  rw [playClient_eq_map_range, ← ofFn_val_eq_map_range sm t, selfPlay_ofFn,
    ofFn_val_eq_map_range, ofFn_val_eq_map_range]

/-- Playing a computable family of client strategies against a computable
sequence of server moves is computable, uniformly in the family index. -/
lemma computable_playClient_family {σ' : ℕ → ClientStrategy} {sm : ℕ → ServerMove}
    (hσ : Computable₂ σ') (hsm : Computable sm) :
    Computable (fun p : ℕ × ℕ => playClient (σ' p.1) sm p.2) := by
  have hrange : Computable (fun p : ℕ × ℕ => (List.range p.2).map sm) :=
    Computable.list_map (Primrec.list_range.to_comp.comp Computable.snd)
      (hsm.comp Computable.snd).to₂
  have h := hσ.comp Computable.fst
    (((computable₂_selfPlay hσ).comp Computable.fst hrange).pair hrange)
  exact h.of_eq (fun p => (playClient_eq_selfPlay _ _ _).symm)

/-- The request the level-`c` strategy puts on the node of `x` after `s` rounds against the
staged server. -/
def gacsDayRequestStage (chk : (BitString × BitString) → ℕ → Bool) (σ : ℕ
  → ClientStrategy) (c s : ℕ) (x : BitString) : ℚ :=
  getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk) s) (gacsDayNodeOfBitString x)

/-- The staged requests are nondecreasing in the stage. -/
lemma gacsDayRequestStage_mono (D : BitStream → BitStream) (chk : (BitString × BitString) → ℕ
  → Bool) (σ : ℕ → ClientStrategy)
    (hD : IsContinuousStreamMap D)
    (hchk : ∀ p t, chk p t = true → chk p (t + 1) = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (C : ℕ) (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d))
    (c s : ℕ) (x : BitString) :
    gacsDayRequestStage chk σ c s x ≤ gacsDayRequestStage chk σ c (s + 1) x := by
  have h_server_legal := serverPlayLegal_gacsDayServerStage chk hD (fun a s1 t hst h => by
    induction hst with
    | refl => exact h
    | step _ ih => exact hchk a _ ih) h_approx
  have h_win_c := hwin (2 ^ c) (Nat.one_le_two_pow)
  have h_client_legal := (h_win_c.1 (gacsDayServerStage chk) h_server_legal).1
  exact h_client_legal.2 s (gacsDayNodeOfBitString x)

/-- Appending the bit `false` to a string appends the child `0` to its node. -/
lemma gacsDayNodeOfBitString_append_false (x : BitString) : (gacsDayNodeOfBitString x) ++ [0]
  = gacsDayNodeOfBitString (x ++ [false]) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    change (if b then 1 else 0) :: (gacsDayNodeOfBitString x ++ [0])
      = (if b then 1 else 0) :: gacsDayNodeOfBitString (x ++ [false])
    rw [ih]

/-- Appending the bit `true` to a string appends the child `1` to its node. -/
lemma gacsDayNodeOfBitString_append_true (x : BitString) : (gacsDayNodeOfBitString x) ++ [1]
  = gacsDayNodeOfBitString (x ++ [true]) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    change (if b then 1 else 0) :: (gacsDayNodeOfBitString x ++ [1])
      = (if b then 1 else 0) :: gacsDayNodeOfBitString (x ++ [true])
    rw [ih]

/-- At every stage the requests are nonnegative, at most `2 ^ (-c)` at the root, and
superadditive over the two children. -/
lemma gacsDayRequestStage_coherent (D : BitStream → BitStream) (chk : (BitString × BitString) → ℕ
  → Bool) (σ : ℕ → ClientStrategy)
    (hD : IsContinuousStreamMap D)
    (hchk : ∀ p t, chk p t = true → chk p (t + 1) = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (C : ℕ) (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d))
    (c s : ℕ) :
    (∀ x, 0 ≤ gacsDayRequestStage chk σ c s x) ∧
    gacsDayRequestStage chk σ c s [] ≤ 1 / (2 ^ c : ℚ) ∧
    (∀ x,
      gacsDayRequestStage chk σ c s (x ++ [false]) + gacsDayRequestStage chk σ c s (x ++ [true])
      ≤ gacsDayRequestStage chk σ c s x) := by
  have h_server_legal := serverPlayLegal_gacsDayServerStage chk hD (fun a s1 t hst h => by
    induction hst with
    | refl => exact h
    | step _ ih => exact hchk a _ ih) h_approx
  have h_win_c := hwin (2 ^ c) (Nat.one_le_two_pow)
  have h_client_legal := (h_win_c.1 (gacsDayServerStage chk) h_server_legal).1
  have h_coh := h_client_legal.1 s
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact h_coh.1 (gacsDayNodeOfBitString x)
  · exact_mod_cast h_coh.2.1
  · intro x
    have hsum := h_coh.2.2 (gacsDayNodeOfBitString x)
    have heq1 := gacsDayNodeOfBitString_append_false x
    have heq2 := gacsDayNodeOfBitString_append_true x
    have hsum2 : ∑ i : Fin 2,
      getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk) s) (gacsDayNodeOfBitString x
      ++ [i.val]) =
        getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk)
          s) (gacsDayNodeOfBitString x ++ [0]) +
        getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk) s) (gacsDayNodeOfBitString x
          ++ [1]) := by
      rw [Fin.sum_univ_two]
      rfl
    rw [hsum2, heq1, heq2] at hsum
    exact hsum

/-- The staged requests are computable in the level, the stage and the string. -/
lemma computable_gacsDayRequestStage {chk : (BitString × BitString) → ℕ → Bool} {σ : ℕ
  → ClientStrategy}
    (hchk : Computable₂ chk) (hcomp : Computable₂ σ) :
    Computable (fun p : ℕ × ℕ × BitString => gacsDayRequestStage chk σ p.1 p.2.1 p.2.2) := by
  have hsm : Computable (fun t => gacsDayServerStage chk t) :=
    computable_gacsDayServerStage chk hchk
  have hσ : Computable₂ (fun c => σ (2 ^ c)) :=
    hcomp.comp (comp_pow.comp Computable.fst) Computable.snd
  have hplay := computable_playClient_family hσ hsm
  have hproj : Computable (fun p : ℕ × ℕ × BitString => (p.1, p.2.1)) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hplay' := hplay.comp hproj
  have hnode : Computable (fun p : ℕ × ℕ × BitString =>
      gacsDayNodeOfBitString p.2.2) :=
    primrec_gacsDayNodeOfBitString.to_comp.comp (Computable.snd.comp Computable.snd)
  exact primrec_getReq.to_comp.comp hplay' hnode

/-- Splitting a dyadic numerator: additivity of `dyadicValue` at a fixed scale. -/
lemma dyadicValue_add_le {a b n : ℕ} (h : a + b ≤ n) (s : ℕ) :
    dyadicValue a s + dyadicValue b s ≤ dyadicValue n s := by
  unfold dyadicValue
  rw [← ENNReal.add_div]
  gcongr
  exact_mod_cast h

/-- The limit of the staged requests, as the supremum of their dyadic floors. -/
noncomputable def gacsDayRequestLimit (chk : (BitString × BitString) → ℕ → Bool) (σ : ℕ
  → ClientStrategy) (c : ℕ) (x : BitString) : ℝ≥0∞ :=
  ⨆ s, dyadicValue (ratDyadicFloor (gacsDayRequestStage chk σ c s x) s) s

/-- The limit requests form a semimeasure: the two children never exceed their parent. -/
lemma gacsDayRequestLimit_children_le (D : BitStream → BitStream) (chk : (BitString × BitString) → ℕ
  → Bool) (σ : ℕ → ClientStrategy)
    (hD : IsContinuousStreamMap D)
    (hchk : ∀ p t, chk p t = true → chk p (t + 1) = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (C : ℕ) (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d))
    (c : ℕ) (x : BitString) :
    gacsDayRequestLimit chk σ c (x ++ [false]) + gacsDayRequestLimit chk σ c (x ++ [true])
      ≤ gacsDayRequestLimit chk σ c x := by
  have hmono0 : Monotone (fun s =>
      dyadicValue (ratDyadicFloor (gacsDayRequestStage chk σ c s (x ++ [false])) s) s) :=
    dyadicValue_ratDyadicFloor_monotone
      (fun s => gacsDayRequestStage_mono D chk σ hD hchk h_approx C hwin c s (x ++ [false]))
  have hmono1 : Monotone (fun s =>
      dyadicValue (ratDyadicFloor (gacsDayRequestStage chk σ c s (x ++ [true])) s) s) :=
    dyadicValue_ratDyadicFloor_monotone
      (fun s => gacsDayRequestStage_mono D chk σ hD hchk h_approx C hwin c s (x ++ [true]))
  refine ENNReal.iSup_add_iSup_le ?_
  intro i j
  have hfloor : ∀ s,
      ratDyadicFloor (gacsDayRequestStage chk σ c s (x ++ [false])) s +
          ratDyadicFloor (gacsDayRequestStage chk σ c s (x ++ [true])) s ≤
        ratDyadicFloor (gacsDayRequestStage chk σ c s x) s := by
    intro s
    obtain ⟨hnn, -, hchild⟩ := gacsDayRequestStage_coherent D chk σ hD hchk h_approx C hwin c s
    rw [ratDyadicFloor_eq_floor, ratDyadicFloor_eq_floor, ratDyadicFloor_eq_floor]
    have h0 : ((⌊gacsDayRequestStage chk σ c s (x ++ [false]) * (2 ^ s : ℕ)⌋₊ : ℚ)) ≤
        gacsDayRequestStage chk σ c s (x ++ [false]) * (2 ^ s : ℕ) :=
      Nat.floor_le (mul_nonneg (hnn _) (by positivity))
    have h1 : ((⌊gacsDayRequestStage chk σ c s (x ++ [true]) * (2 ^ s : ℕ)⌋₊ : ℚ)) ≤
        gacsDayRequestStage chk σ c s (x ++ [true]) * (2 ^ s : ℕ) :=
      Nat.floor_le (mul_nonneg (hnn _) (by positivity))
    apply Nat.le_floor
    have hmul := mul_le_mul_of_nonneg_right (hchild x)
      (show (0 : ℚ) ≤ ((2 ^ s : ℕ) : ℚ) by positivity)
    push_cast at h0 h1 hmul ⊢
    nlinarith [h0, h1, hmul]
  have hmax0 := hmono0 (le_max_left i j)
  have hmax1 := hmono1 (le_max_right i j)
  refine le_trans (add_le_add hmax0 hmax1) ?_
  refine le_trans (dyadicValue_add_le (hfloor (max i j)) (max i j)) ?_
  exact le_iSup (fun s =>
    dyadicValue (ratDyadicFloor (gacsDayRequestStage chk σ c s x) s) s) (max i j)

/-- The limit request at the root is at most `2 ^ (-c)`. -/
lemma gacsDayRequestLimit_root_le (D : BitStream → BitStream) (chk : (BitString × BitString) → ℕ
  → Bool) (σ : ℕ → ClientStrategy)
    (hD : IsContinuousStreamMap D)
    (hchk : ∀ p t, chk p t = true → chk p (t + 1) = true)
    (h_approx : ∀ p : BitString × BitString, (∃ s, chk p s = true) ↔ streamLowerGraph D p.1 p.2)
    (C : ℕ) (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d))
    (c : ℕ) :
    gacsDayRequestLimit chk σ c [] ≤ (2 : ℝ≥0∞)⁻¹ ^ c := by
  refine iSup_le ?_
  intro s
  obtain ⟨hnn, hroot, -⟩ := gacsDayRequestStage_coherent D chk σ hD hchk h_approx C hwin c s
  have hnat : ratDyadicFloor (gacsDayRequestStage chk σ c s []) s * 2 ^ c ≤ 2 ^ s := by
    have hfl : ((⌊gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ)⌋₊ : ℚ)) ≤
        gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ) :=
      Nat.floor_le (mul_nonneg (hnn _) (by positivity))
    have hpow : (0 : ℚ) < 2 ^ c := by positivity
    have hq : ((⌊gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ)⌋₊ : ℚ)) * 2 ^ c ≤ 2 ^ s := by
      have hmul := mul_le_mul_of_nonneg_right hroot
        (show (0 : ℚ) ≤ ((2 ^ s : ℕ) : ℚ) by positivity)
      have hstep : gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ) * 2 ^ c ≤ 2 ^ s := by
        push_cast at hmul ⊢
        rw [div_mul_eq_mul_div, one_mul] at hmul
        have h2 : gacsDayRequestStage chk σ c s [] * 2 ^ s * 2 ^ c ≤
            (2 : ℚ) ^ s / 2 ^ c * 2 ^ c :=
          mul_le_mul_of_nonneg_right hmul (le_of_lt hpow)
        rwa [div_mul_cancel₀ _ (ne_of_gt hpow)] at h2
      calc ((⌊gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ)⌋₊ : ℚ)) * 2 ^ c
          ≤ gacsDayRequestStage chk σ c s [] * (2 ^ s : ℕ) * 2 ^ c :=
            mul_le_mul_of_nonneg_right hfl (le_of_lt hpow)
        _ ≤ 2 ^ s := hstep
    rw [ratDyadicFloor_eq_floor]
    exact_mod_cast hq
  have hcast : ((ratDyadicFloor (gacsDayRequestStage chk σ c s []) s : ℝ≥0∞)) *
      (2 : ℝ≥0∞) ^ c ≤ (2 : ℝ≥0∞) ^ s := by
    have := (Nat.cast_le (α := ℝ≥0∞)).mpr hnat
    push_cast at this
    exact this
  have hle : ((ratDyadicFloor (gacsDayRequestStage chk σ c s []) s : ℝ≥0∞)) ≤
      (2 : ℝ≥0∞) ^ s / (2 : ℝ≥0∞) ^ c :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))).mpr hcast
  have hrewrite : (2 : ℝ≥0∞) ^ s / (2 : ℝ≥0∞) ^ c = (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞) ^ s := by
    rw [div_eq_mul_inv, ← ENNReal.inv_pow, mul_comm]
  rw [hrewrite] at hle
  exact ENNReal.div_le_of_le_mul hle

/-- At every level the limit requests exceed `2 ^ (-KM x)` at some string of length at most
`(C 2^c) ^ (C 2^c)`. -/
lemma gacsDayRequestLimit_witness (D : BitStream → BitStream) (chk : (BitString × BitString) → ℕ
  → Bool) (σ : ℕ → ClientStrategy)
    (hD : IsOptimalMonotoneDecompressor D)
    (hchk : ∀ p t, chk p t = true → chk p (t + 1) = true)
    (h_approx : ∀ p, (∃ t, chk p t = true) ↔ streamLowerGraph D p.1 p.2)
    (C : ℕ) (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d))
    (c : ℕ) :
    ∃ x, x.length ≤ (C * 2 ^ c) ^ (C * 2 ^ c) ∧
      (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat < gacsDayRequestLimit chk σ c x := by
  have hchk_mono' : ∀ a s t, s ≤ t → chk a s = true → chk a t = true := fun a s t hst h => by
    induction hst with
    | refl => exact h
    | step _ ih => exact hchk a _ ih
  have h_server_legal := serverPlayLegal_gacsDayServerStage chk hD.1.1 hchk_mono' h_approx
  have h_win_c := hwin (2 ^ c) (Nat.one_le_two_pow)
  have hw := h_win_c.1 (gacsDayServerStage chk) h_server_legal
  rcases hw.2 with ⟨T, x_node, hlen, hin, hfail⟩
  let x := gacsDayNodeToBitString x_node
  use x
  have h_x_len : x.length ≤ (C * 2 ^ c) ^ (C * 2 ^ c) := by
    rwa [gacsDayNodeToBitString_length]
  refine ⟨h_x_len, ?_⟩
  have h_KM_not_top : KMOf D x ≠ ⊤ := KMOf_ne_top_of_isOptimal hD x
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KMOf_ne_top h_KM_not_top
  have h_len_eq : (KMOf D x).toNat = p.length := by
    rw [← hp_len]
    rfl
  rw [h_len_eq]
  have hp_prod' : monotoneProduces D p (gacsDayNodeToBitString x_node) := hp_prod
  obtain ⟨t1, ht1⟩ :=
    monotoneProduces_eventually_mem_gacsDayServerStage chk hchk_mono' h_approx x_node hin p hp_prod'
  let t := max t1 T
  have h_alloc : p ∈ getAlloc (gacsDayServerStage chk t) x_node := by
    have h_mono : ∀ s1 s2,
      s1 ≤ s2 → getAlloc (gacsDayServerStage chk s1) x_node
      ⊆ getAlloc (gacsDayServerStage chk s2) x_node := by
      intro s1 s2 hs
      induction hs with
      | refl => exact fun _ h => h
      | step _ ih => exact fun y hy => getAlloc_gacsDayServerStage_mono chk hchk_mono' _ _ (ih hy)
    exact h_mono t1 t (le_max_left t1 T) ht1
  have h_fail_t := hfail t
  have h_req : (1 / 2 : ℝ) ^ p.length < (gacsDayRequestStage chk σ c T x : ℝ) := by
    have h_serves : ¬ Serves (getAlloc (gacsDayServerStage chk t) x_node) (getReq (playClient (σ (2
      ^ c)) (gacsDayServerStage chk) T) x_node) := h_fail_t
    have h_req_T : (1 / 2 : ℝ) ^ p.length
      < (getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk) T) x_node : ℝ) := by
      by_contra! hcontra
      apply h_serves
      exact ⟨p, h_alloc, hcontra⟩
    have h_node_eq : gacsDayNodeOfBitString x = x_node := gacsDayNodeOfBitString_nodeToBitString hin
    have h_req_eq : gacsDayRequestStage chk σ c T x
      = getReq (playClient (σ (2 ^ c)) (gacsDayServerStage chk) T) x_node := by
      dsimp [gacsDayRequestStage]
      rw [h_node_eq]
    rwa [← h_req_eq] at h_req_T
  have h_sup : (⨆ s,
    ENNReal.ofReal (gacsDayRequestStage chk σ c s x : ℝ)) = gacsDayRequestLimit chk σ c x := by
    have h_mono : Monotone (fun s => gacsDayRequestStage chk σ c s x) :=
      monotone_nat_of_le_succ (fun s =>
        gacsDayRequestStage_mono D chk σ hD.1.1 hchk h_approx C hwin c s x)
    exact (iSup_dyadicValue_ratDyadicFloor h_mono).symm
  rw [← h_sup]
  have h_pow_cast : (2 : ℝ≥0∞)⁻¹ ^ p.length = ENNReal.ofReal ((1 / 2 : ℝ) ^ p.length) := by
    have h_pos : (0 : ℝ) ≤ 1 / 2 := by positivity
    rw [ENNReal.ofReal_pow h_pos]
    have h_half : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      congr
      norm_num
    rw [h_half]
  rw [h_pow_cast]
  have h_req_T_le_sup : ENNReal.ofReal (gacsDayRequestStage chk σ c T x : ℝ) ≤ ⨆ s,
    ENNReal.ofReal (gacsDayRequestStage chk σ c s x : ℝ) :=
    le_iSup (fun s => ENNReal.ofReal (gacsDayRequestStage chk σ c s x : ℝ)) T
  have h_lt : ENNReal.ofReal ((1 / 2 : ℝ) ^ p.length)
    < ENNReal.ofReal (gacsDayRequestStage chk σ c T x : ℝ) := by
    rw [ENNReal.ofReal_lt_ofReal_iff]
    · exact h_req
    · exact lt_trans (by positivity) h_req
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) ^ p.length)
      < ENNReal.ofReal (gacsDayRequestStage chk σ c T x : ℝ) := h_lt
    _ ≤ ⨆ s, ENNReal.ofReal (gacsDayRequestStage chk σ c s x : ℝ) := h_req_T_le_sup

/-- The server induced by an optimal monotone decompressor `D`, played
against the (unpacked) uniform winning strategy `σ`, yields a uniformly
lower-semicomputable family of child-superadditive request subsemimeasures
`μ c` with root mass `≤ 2⁻¹ ^ c`, each of which beats `2⁻¹ ^ (KM_D x)` at a
witness of length `≤ (C·2^c)^(C·2^c)`. The last two conjuncts package the
uniform lower-semicomputability as an explicit computable dyadic approximation
`A`. -/
theorem exists_gacsDayRequestFamily
    (D : BitStream → BitStream) (hD : IsOptimalMonotoneDecompressor D)
    (C : ℕ) (σ : ℕ → ClientStrategy) (hcomp : Computable₂ σ)
    (hwin : ∀ d ≥ 1, IsUniformWinningStrategy ((C * d) ^ (C * d)) 2 d (σ d)) :
    ∃ (μ : ℕ → BitString → ℝ≥0∞) (A : ℕ → ℕ → BitString → ℕ),
      (∀ c x, μ c (x ++ [false]) + μ c (x ++ [true]) ≤ μ c x) ∧
      (∀ c, μ c [] ≤ (2 : ℝ≥0∞)⁻¹ ^ c) ∧
      (∀ c, ∃ x, x.length ≤ (C * 2 ^ c) ^ (C * 2 ^ c) ∧
        (2 : ℝ≥0∞)⁻¹ ^ (KMOf D x).toNat < μ c x) ∧
      (∀ m s x, dyadicValue (A m s x) s ≤ dyadicValue (A m (s + 1) x) (s + 1)) ∧
      (∀ m x, ⨆ s, dyadicValue (A m s x) s = μ m x) ∧
      (Computable fun p : ℕ × ℕ × BitString => A p.1 p.2.1 p.2.2) := by
  have h_RE : IsRE (fun p : BitString × BitString => streamLowerGraph D p.1 p.2) := hD.1.2
  obtain ⟨chk, hchk_comp, hchk_mono_t, hchk_limit⟩ := h_RE.exists_stageApprox
  have hchk_mono : ∀ p t, chk p t = true → chk p (t + 1) = true :=
    fun p t ht => hchk_mono_t p t (t + 1) (Nat.le_succ t) ht
  let μ := fun c x => gacsDayRequestLimit chk σ c x
  let A := fun c s x => ratDyadicFloor (gacsDayRequestStage chk σ c s x) s
  use μ, A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c x
    exact gacsDayRequestLimit_children_le D chk σ hD.1.1 hchk_mono (fun p =>
      (hchk_limit p).symm) C hwin c x
  · intro c
    exact gacsDayRequestLimit_root_le D chk σ hD.1.1 hchk_mono (fun p =>
      (hchk_limit p).symm) C hwin c
  · intro c
    exact gacsDayRequestLimit_witness D chk σ hD hchk_mono (fun p => (hchk_limit p).symm) C hwin c
  · intro m s x
    have h_mono : gacsDayRequestStage chk σ m s x ≤ gacsDayRequestStage chk σ m (s + 1) x :=
      gacsDayRequestStage_mono D chk σ hD.1.1 hchk_mono (fun p => (hchk_limit p).symm) C hwin m s x
    exact dyadicValue_ratDyadicFloor_mono_of_le h_mono s
  · intro m x
    rfl
  · have hcomp_req := computable_gacsDayRequestStage hchk_comp hcomp
    exact computable_ratDyadicFloor.comp hcomp_req (Computable.fst.comp Computable.snd)

end Kolmogorov
