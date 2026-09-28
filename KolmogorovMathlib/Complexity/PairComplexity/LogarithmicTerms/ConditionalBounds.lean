import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.OrdinalPlainRandomness
import KolmogorovMathlib.Complexity.PairComplexity.LogarithmicTerms.PlainBounds
import KolmogorovMathlib.Complexity.PairComplexity.Overhead

namespace Kolmogorov
open Nat.Partrec (Code)

/-! ### Exercises 25–34: conditional complexity -/

/-- **Exercise 25, continuity.** `C(x | y0) = C(x | y) + O(1)` and
`C(x | y1) = C(x | y) + O(1)`. -/
theorem condK_append_bit_eq (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (x y : BitString) (b : Bool),
      condK U x (y ++ [b]) ≤ condK U x y + (k : ℕ∞) ∧
        condK U x y ≤ condK U x (y ++ [b]) + (k : ℕ∞) := by
  let D_drop : Map := fun (p, y) => U (p, y.take (y.length - 1))
  have hD_drop : isDecompressor D_drop := by
    apply Partrec.comp hU.1
    have h_take : Computable₂ (fun (l : BitString) (n : ℕ) => l.take n) :=
      Primrec.list_take.to_comp
    have h_len_sub_1 : Computable (fun (y : BitString) => y.length - 1) :=
      Computable.pred.comp Computable.list_length
    have h_dropLast : Computable (fun (y : BitString) => y.take (y.length - 1)) :=
      h_take.comp Computable.id h_len_sub_1
    exact Computable.pair Computable.fst (h_dropLast.comp Computable.snd)
  obtain ⟨c_drop, hc_drop⟩ := hU.2 D_drop hD_drop
  let D_add : Map := fun (p, y) => U (p.drop 1, y ++ p.take 1)
  have hD_add : isDecompressor D_add := by
    apply Partrec.comp hU.1
    have h_p_drop : Computable (fun (py : BitString × BitString) => py.1.drop 1) :=
      Primrec.list_drop.to_comp.comp Computable.fst (Computable.const 1)
    have h_p_take : Computable (fun (py : BitString × BitString) => py.1.take 1) :=
      Primrec.list_take.to_comp.comp Computable.fst (Computable.const 1)
    have h_ctx : Computable (fun (py : BitString × BitString) => py.2 ++ py.1.take 1) :=
      Computable.list_append.comp Computable.snd h_p_take
    exact Computable.pair h_p_drop h_ctx
  obtain ⟨c_add, hc_add⟩ := hU.2 D_add hD_add
  use max c_drop (c_add + 1)
  intro x y b
  constructor
  · have h_drop_le : condK D_drop x (y ++ [b]) ≤ condK U x y := by
      by_cases h_top : condK U x y = ⊤
      · rw [h_top]; exact le_top
      · set N := (condK U x y).toNat
        have h_eq_N : condK U x y = (N : ℕ∞) := (ENat.coe_toNat h_top).symm
        have hN : condK U x y ≤ (N : ℕ∞) := by rw [h_eq_N]
        obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U x y N).mp hN
        have h_prod_drop : produces D_drop p (y ++ [b]) x := by
          dsimp [D_drop, produces]
          have h_eq_ctx : (y ++ [b]).take ((y ++ [b]).length - 1) = y := by
            rw [List.length_append, List.length_singleton, Nat.add_sub_cancel]
            exact List.take_left
          rw [h_eq_ctx]
          exact hp_prod
        have h_le := (condK_le_iff D_drop x (y ++ [b]) N).mpr ⟨p, hp_len, h_prod_drop⟩
        calc
          condK D_drop x (y ++ [b]) ≤ (N : ℕ∞) := h_le
          _ = condK U x y := h_eq_N.symm
    calc
      condK U x (y ++ [b]) ≤ condK D_drop x (y ++ [b]) + (c_drop : ℕ∞) := hc_drop x (y ++ [b])
      _ ≤ condK U x y + (c_drop : ℕ∞) := by gcongr
      _ ≤ condK U x y + ((max c_drop (c_add + 1) : ℕ) : ℕ∞) := by
        gcongr
        exact_mod_cast le_max_left c_drop (c_add + 1)
  · have h_add_le : condK D_add x y ≤ condK U x (y ++ [b]) + 1 := by
      by_cases h_top : condK U x (y ++ [b]) = ⊤
      · rw [h_top]; exact le_top
      · set N := (condK U x (y ++ [b])).toNat
        have h_eq_N : condK U x (y ++ [b]) = (N : ℕ∞) := (ENat.coe_toNat h_top).symm
        have hN : condK U x (y ++ [b]) ≤ (N : ℕ∞) := by rw [h_eq_N]
        obtain ⟨q, hq_len, hq_prod⟩ := (condK_le_iff U x (y ++ [b]) N).mp hN
        have h_prod_add : produces D_add (b :: q) y x := by
          dsimp [D_add, produces]
          exact hq_prod
        have h_len : programLength (b :: q) ≤ N + 1 := by
          change List.length (b :: q) ≤ N + 1
          change List.length q ≤ N at hq_len
          rw [List.length_cons]
          omega
        have h_le := (condK_le_iff D_add x y (N + 1)).mpr ⟨b :: q, h_len, h_prod_add⟩
        calc
          condK D_add x y ≤ ((N + 1 : ℕ) : ℕ∞) := h_le
          _ = (N : ℕ∞) + 1 := by exact_mod_cast rfl
          _ = condK U x (y ++ [b]) + 1 := by rw [← h_eq_N]
    calc
      condK U x y ≤ condK D_add x y + (c_add : ℕ∞) := hc_add x y
      _ ≤ condK U x (y ++ [b]) + 1 + (c_add : ℕ∞) := by gcongr
      _ = condK U x (y ++ [b]) + ((c_add + 1 : ℕ) : ℕ∞) := by
        rw [add_assoc]
        congr 1
        exact_mod_cast add_comm 1 c_add
      _ ≤ condK U x (y ++ [b]) + ((max c_drop (c_add + 1) : ℕ) : ℕ∞) := by
        gcongr
        exact_mod_cast le_max_right c_drop (c_add + 1)

/-- **Exercise 25, intermediate values.** Every level `l ≤ C(x)` is realized as a
conditional complexity `C(x | y)` up to an additive constant. -/
theorem exists_condK_eq_of_le_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (x : BitString) (l : ℕ), (l : ℕ∞) ≤ plainK U x → ∃ y : BitString,
      condK U x y ≤ ((l + k : ℕ) : ℕ∞) ∧ (l : ℕ∞) ≤ condK U x y + (k : ℕ∞) := by
  obtain ⟨kc, hkc⟩ := condK_append_bit_eq U hU
  obtain ⟨ks, hks⟩ := condK_self U hU
  use max kc ks
  intro x l hl
  let P : ℕ → Prop := fun i => l ≤ condK U x (x.take i)
  have hP_dec : ∀ i, Decidable (P i) := fun i => inferInstance
  have h0 : P 0 := hl
  set m := Nat.findGreatest P x.length
  have h_Pm : P m := Nat.findGreatest_spec (P := P) (Nat.zero_le x.length) h0
  have hm_le : m ≤ x.length := Nat.findGreatest_le x.length
  by_cases hm_len : m = x.length
  · use x
    have h_m' := h_Pm
    rw [hm_len] at h_m'
    dsimp [P] at h_m'
    rw [List.take_length] at h_m'
    have h_P_len : (l : ℕ∞) ≤ condK U x x := h_m'
    have h_l_le_ks : (l : ℕ∞) ≤ (ks : ℕ∞) := le_trans h_P_len (hks x)
    constructor
    · calc
        condK U x x ≤ (ks : ℕ∞) := hks x
        _ ≤ ((l + max kc ks : ℕ) : ℕ∞) := by
          have : ks ≤ l + max kc ks := by
            have : ks ≤ max kc ks := le_max_right kc ks
            omega
          exact_mod_cast this
    · calc
        (l : ℕ∞) ≤ (ks : ℕ∞) := h_l_le_ks
        _ ≤ condK U x x + (ks : ℕ∞) := self_le_add_left _ _
        _ ≤ condK U x x + ((max kc ks : ℕ) : ℕ∞) := by
          gcongr
          exact_mod_cast le_max_right kc ks
  · have hm_lt : m < x.length := Nat.lt_of_le_of_ne hm_le hm_len
    have h_not_Pm1 : ¬ P (m + 1) := by
      intro h_Pm1
      have h_ge : m + 1 ≤ Nat.findGreatest P x.length :=
        Nat.le_findGreatest (P := P) hm_lt h_Pm1
      omega
    use x.take m
    have h_cond_m : (l : ℕ∞) ≤ condK U x (x.take m) := h_Pm
    have h_step : x.take (m + 1) = x.take m ++ [x.getD m false] := by
      have h_getElem : x[m] = x.getD m false := (List.getD_eq_getElem x false hm_lt).symm
      have h_concat := List.take_concat_get' x m hm_lt
      rw [h_getElem] at h_concat
      exact h_concat.symm
    have h_cond_m1 : condK U x (x.take m ++ [x.getD m false]) < (l : ℕ∞) := by
      have h_lt_l : condK U x (x.take (m + 1)) < (l : ℕ∞) := not_le.mp h_not_Pm1
      rwa [h_step] at h_lt_l
    obtain ⟨hkc1, hkc2⟩ := hkc x (x.take m) (x.getD m false)
    constructor
    · calc
        condK U x (x.take m) ≤ condK U x (x.take m ++ [x.getD m false]) + (kc : ℕ∞) := hkc2
        _ ≤ (l : ℕ∞) + (kc : ℕ∞) := by
          have h_le_l : condK U x (x.take m ++ [x.getD m false]) ≤ (l : ℕ∞) := le_of_lt h_cond_m1
          exact add_le_add h_le_l (le_refl (kc : ℕ∞))
        _ = ((l + kc : ℕ) : ℕ∞) := by exact_mod_cast rfl
        _ ≤ ((l + max kc ks : ℕ) : ℕ∞) := by
          gcongr
          exact le_max_left kc ks
    · calc
        (l : ℕ∞) ≤ condK U x (x.take m) := h_cond_m
        _ ≤ condK U x (x.take m) + ((max kc ks : ℕ) : ℕ∞) := self_le_add_right _ _

private def condShiftDecompressor (U : Map) : Map :=
  fun p => (U (decodeFirst p.1, [])).bind (fun y => U (decodeSecond p.1, y))

private theorem condShiftDecompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (condShiftDecompressor U) := by
  have h1 : Partrec (fun p : BitString × BitString => U (decodeFirst p.1, [])) := by
    have h_pair : Computable (fun p : BitString × BitString =>
        (decodeFirst p.1, ([] : BitString))) :=
      Computable.pair (decodeFirst_computable.comp Computable.fst) (Computable.const [])
    exact Partrec.comp hU h_pair
  have h2 : Partrec (fun p : (BitString × BitString) × BitString =>
      U (decodeSecond p.1.1, p.2)) := by
    have h_pair : Computable (fun p : (BitString × BitString) × BitString =>
        (decodeSecond p.1.1, p.2)) :=
      Computable.pair
        (decodeSecond_computable.comp (Computable.fst.comp Computable.fst)) Computable.snd
    exact Partrec.comp hU h_pair
  exact Partrec.bind h1 h2

/-- Plain complexity with respect to a conditionally optimal machine is always finite. -/
theorem plainK_ne_top (U : Map) (hU : isOptimalConditional U) (y : BitString) :
    plainK U y ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainK_le_length U hU
  exact ne_top_of_le_natCast_add (hc y)

/-- **Exercise 26.** For fixed `y`, `x ↦ C(x | y)` differs from `C` by at most
`2 C(y) + O(1)`. -/
theorem plainK_sub_condK_le_two_mul_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      condK U x y ≤ plainK U x + (k : ℕ∞) ∧
        plainK U x ≤ condK U x y + ((2 * cVal U y + k : ℕ) : ℕ∞) := by
  obtain ⟨c1, hc1⟩ := condK_le_plainK U hU
  let D := condShiftDecompressor U
  have hD : isDecompressor D := condShiftDecompressor_isDecompressor U hU.1
  obtain ⟨c2, hc2⟩ := hU.2 D hD
  use c1 + c2 + 1
  intro x y
  constructor
  · calc condK U x y ≤ plainK U x + (c1 : ℕ∞) := hc1 x y
    _                ≤ plainK U x + ((c1 + c2 + 1 : ℕ) : ℕ∞) := by
      gcongr
      omega
  · have hx := condK_ne_top_of_optimal U hU x y
    have hy_top := plainK_ne_top U hU y
    have h_eq_y : plainK U y = (cVal U y : ℕ∞) := (ENat.coe_toNat hy_top).symm
    have h_le_y : condK U y [] ≤ (cVal U y : ℕ∞) := by
      change plainK U y ≤ (cVal U y : ℕ∞)
      rw [h_eq_y]
    rw [condK_le_iff] at h_le_y
    obtain ⟨qy, hqy_len, hqy_prod⟩ := h_le_y
    change qy.length ≤ cVal U y at hqy_len
    have h_eq_x : condK U x y = (condCVal U x y : ℕ∞) := (ENat.coe_toNat hx).symm
    have h_le_x : condK U x y ≤ (condCVal U x y : ℕ∞) := by rw [h_eq_x]
    rw [condK_le_iff] at h_le_x
    obtain ⟨px, hpx_len, hpx_prod⟩ := h_le_x
    change px.length ≤ condCVal U x y at hpx_len
    have h_prod_D : produces D (pairCode qy px) [] x := by
      dsimp [D, condShiftDecompressor, produces]
      rw [decodeFirst_pairCode, decodeSecond_pairCode]
      rw [Part.mem_bind_iff]
      exact ⟨y, hqy_prod, hpx_prod⟩
    have h_D_le : plainK D x ≤ ((pairCode qy px).length : ℕ∞) := by
      change condK D x [] ≤ ((pairCode qy px).length : ℕ∞)
      rw [condK_le_iff]
      exact ⟨pairCode qy px, le_rfl, h_prod_D⟩
    have h_U_le : plainK U x ≤ plainK D x + (c2 : ℕ∞) := hc2 x []
    have h_code_len : (pairCode qy px).length =
        qy.length + 1 + qy.length + px.length := length_pairCode qy px
    have h_len_bound : (pairCode qy px).length ≤ 2 * cVal U y + condCVal U x y + 1 := by
      rw [h_code_len]
      omega
    calc plainK U x ≤ plainK D x + (c2 : ℕ∞) := h_U_le
    _               ≤ ((pairCode qy px).length : ℕ∞) + (c2 : ℕ∞) := by gcongr
    _               ≤ ((2 * cVal U y + condCVal U x y + 1 : ℕ) : ℕ∞) + (c2 : ℕ∞) := by
      gcongr
    _               = ((2 * cVal U y + condCVal U x y + 1 + c2 : ℕ) : ℕ∞) := by
      push_cast
      rfl
    _               ≤ (condCVal U x y : ℕ∞) + ((2 * cVal U y + (c1 + c2 + 1) : ℕ) : ℕ∞) := by
      push_cast
      have : 2 * cVal U y + condCVal U x y + 1 + c2 ≤
          condCVal U x y + (2 * cVal U y + (c1 + c2 + 1)) := by omega
      exact_mod_cast this
    _               = condK U x y + ((2 * cVal U y + (c1 + c2 + 1) : ℕ) : ℕ∞) := by
      rw [h_eq_x]

/-- **Exercise 27.** `C([x, z] | [y, z]) ≤ C(x | y) + O(1)`. -/
theorem condK_pair_pair_le_condK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y z : BitString,
      condK U (pairCode x z) (pairCode y z) ≤ condK U x y + (k : ℕ∞) := by
  let D : Map := fun pr =>
    (U (pr.1, decodeFirst pr.2)).map fun x => pairCode x (decodeSecond pr.2)
  have hRun : Partrec (fun pr : BitString × BitString => U (pr.1, decodeFirst pr.2)) :=
    hU.1.comp (Computable.fst.pair (decodeFirst_computable.comp Computable.snd))
  have hOut : Computable (fun q : (BitString × BitString) × BitString =>
      pairCode q.2 (decodeSecond q.1.2)) :=
    (show Computable₂ (fun a b : BitString => pairCode a b) from pairCode_computable).comp
      Computable.snd
      (decodeSecond_computable.comp (Computable.snd.comp Computable.fst))
  have hD : isDecompressor D := Partrec.map hRun hOut
  obtain ⟨k, hk⟩ := hU.2 D hD
  refine ⟨k, fun x y z => ?_⟩
  have hsub : candidateLengths U x y ⊆ candidateLengths D (pairCode x z) (pairCode y z) := by
    rintro n ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    change pairCode x z ∈ D (p, pairCode y z)
    change pairCode x z ∈ (U (p, decodeFirst (pairCode y z))).map
      (fun u => pairCode u (decodeSecond (pairCode y z)))
    rw [decodeFirst_pairCode, decodeSecond_pairCode]
    exact Part.mem_map _ hp
  have hle : condK D (pairCode x z) (pairCode y z) ≤ condK U x y := sInf_le_sInf hsub
  calc
    condK U (pairCode x z) (pairCode y z)
        ≤ condK D (pairCode x z) (pairCode y z) + (k : ℕ∞) :=
      hk (pairCode x z) (pairCode y z)
    _ ≤ condK U x y + (k : ℕ∞) := by gcongr

/-- The minimal plain complexity of a program mapping `y` to `x`. -/
noncomputable def programComplexity (U : Map) (x y : BitString) : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ e : ℕ,
    Encodable.encode x ∈ (Denumerable.ofNat Code e).eval (Encodable.encode y) ∧
      plainKNat U e = v}

end Kolmogorov


