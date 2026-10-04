import KolmogorovMathlib.Complexity.PairComplexity.Overhead

/-!
# Logarithmic terms in the plain pair bound

`plainK_pair_le_add_logs` (SUV Exercise 21): `C(x, y) ≤ C(x) + log C(x) + C(y) + log C(y) +
O(1)` — the two programs are separated by writing the length of the first one
self-delimitingly.  `myPairCode`, `findS` and `extractFromS` are that framing and its parsing,
and the `decodeBits_append_*` lemmas say the padding is harmless.

`plainK_pair_le_two_mul` (Exercise 24) is the coarser bound `C(x, y) ≤ 2n + O(1)` for
`C(x), C(y) ≤ n`, by the decompressor `pairLevelMap` that splits its program in half and
unpads the two halves.
-/



namespace Kolmogorov
open Nat.Partrec (Code)

/-- **Exercise 21.** `C(x, y) ≤ C(x) + log C(x) + C(y) + log C(y) + O(1)`. -/
theorem plainK_pair_le_add_logs (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y +
        ((Nat.log 2 (cVal U x) + Nat.log 2 (cVal U y) + k : ℕ) : ℕ∞) := by
  have hD_decomp := symmLogsDecompressor_isDecompressor U hU.1
  obtain ⟨cD, hcD⟩ := hU.2 (symmLogsDecompressor U) hD_decomp
  use 4 + cD
  intro x y
  obtain ⟨c_plain, hc_plain⟩ := plainK_le_length U hU
  have hx_ne : plainK U x ≠ ⊤ := by
    have h_le := hc_plain x
    intro h_top
    rw [h_top] at h_le
    exact ENat.natCast_ne_top _ (le_top.antisymm h_le)
  have hy_ne : plainK U y ≠ ⊤ := by
    have h_le := hc_plain y
    intro h_top
    rw [h_top] at h_le
    exact ENat.natCast_ne_top _ (le_top.antisymm h_le)
  obtain ⟨p, hp_prod, hp_len⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hx_ne
  obtain ⟨q, hq_prod, hq_len⟩ := exists_program_of_KP_ne_top (M := U) (x := y) (y := []) hy_ne
  have hx_plainK : plainK U x = (p.length : ℕ∞) := hp_len.symm
  have hy_plainK : plainK U y = (q.length : ℕ∞) := hq_len.symm
  have hx_cVal : cVal U x = p.length := by
    unfold cVal
    rw [hx_plainK, ENat.toNat_natCast]
  have hy_cVal : cVal U y = q.length := by
    unfold cVal
    rw [hy_plainK, ENat.toNat_natCast]
  by_cases h_order : p.length ≤ q.length
  · let w := false :: pairCode (Nat.bits p.length) (p ++ q)
    have hw_prod : produces (symmLogsDecompressor U) w [] (pairCode x y) := by
      unfold produces
      dsimp [symmLogsDecompressor, w]
      rw [parsePair_encode]
      dsimp [evalPairCode]
      rw [Part.mem_bind_iff]
      refine ⟨x, hp_prod, ?_⟩
      rw [Part.mem_map_iff]
      exact ⟨y, hq_prod, rfl⟩
    have h_condK : condK (symmLogsDecompressor U) (pairCode x y) [] ≤ (w.length : ℕ∞) := by
      exact sInf_le ⟨w, hw_prod, rfl⟩
    have h_cPair_le : cPair U x y ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by
      unfold cPair
      calc plainK U (pairCode x y)
          ≤ condK (symmLogsDecompressor U) (pairCode x y) [] + (cD : ℕ∞) := hcD (pairCode x y) []
        _ ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by gcongr
    have hw_len : w.length = 2 * (Nat.bits p.length).length + 2 + p.length + q.length := by
      change (false :: pairCode (Nat.bits p.length) (p ++ q)).length = _
      rw [List.length_cons, length_pairCode, List.length_append]
      omega
    have h_bits_len := length_natBits_le_log p.length
    have hw_bound : w.length ≤
        p.length + q.length + Nat.log 2 (cVal U x) + Nat.log 2 (cVal U y) + 4 := by
      rw [hx_cVal, hy_cVal]
      have h_min : 2 * Nat.log 2 p.length ≤ Nat.log 2 p.length + Nat.log 2 q.length := by
        have := min_log_add_le p.length q.length
        rw [min_eq_left h_order] at this
        exact this
      omega
    have h_w_cast : (w.length : ℕ∞) + (cD : ℕ∞) ≤
        plainK U x + plainK U y +
          ((Nat.log 2 (cVal U x) + Nat.log 2 (cVal U y) + (4 + cD) : ℕ) : ℕ∞) := by
      rw [hx_plainK, hy_plainK]
      norm_cast
      omega
    exact le_trans h_cPair_le h_w_cast
  · push Not at h_order
    have h_order' : q.length ≤ p.length := h_order.le
    let w := true :: pairCode (Nat.bits q.length) (q ++ p)
    have hw_prod : produces (symmLogsDecompressor U) w [] (pairCode x y) := by
      unfold produces
      dsimp [symmLogsDecompressor, w]
      rw [parsePair_encode]
      dsimp [evalPairCode]
      rw [Part.mem_bind_iff]
      refine ⟨x, hp_prod, ?_⟩
      rw [Part.mem_map_iff]
      exact ⟨y, hq_prod, rfl⟩
    have h_condK : condK (symmLogsDecompressor U) (pairCode x y) [] ≤ (w.length : ℕ∞) := by
      exact sInf_le ⟨w, hw_prod, rfl⟩
    have h_cPair_le : cPair U x y ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by
      unfold cPair
      calc plainK U (pairCode x y)
          ≤ condK (symmLogsDecompressor U) (pairCode x y) [] + (cD : ℕ∞) := hcD (pairCode x y) []
        _ ≤ (w.length : ℕ∞) + (cD : ℕ∞) := by gcongr
    have hw_len : w.length = 2 * (Nat.bits q.length).length + 2 + p.length + q.length := by
      change (true :: pairCode (Nat.bits q.length) (q ++ p)).length = _
      rw [List.length_cons, length_pairCode, List.length_append]
      omega
    have h_bits_len := length_natBits_le_log q.length
    have hw_bound : w.length ≤
        p.length + q.length + Nat.log 2 (cVal U x) + Nat.log 2 (cVal U y) + 4 := by
      rw [hx_cVal, hy_cVal]
      have h_min : 2 * Nat.log 2 q.length ≤ Nat.log 2 p.length + Nat.log 2 q.length := by
        have := min_log_add_le p.length q.length
        rw [min_eq_right h_order'] at this
        exact this
      omega
    have h_w_cast : (w.length : ℕ∞) + (cD : ℕ∞) ≤
        plainK U x + plainK U y +
          ((Nat.log 2 (cVal U x) + Nat.log 2 (cVal U y) + (4 + cD) : ℕ) : ℕ∞) := by
      rw [hx_plainK, hy_plainK]
      norm_cast
      omega
    exact le_trans h_cPair_le h_w_cast

private def myPairCode (p : BitString × BitString) : BitString := pairCode p.1 p.2

private lemma myPairCode_comp : Computable myPairCode := pairCode_computable

private lemma decodeBits_append_false (l : List Bool) :
    decodeBits (l ++ [false]) = decodeBits l := by
  induction l with
  | nil => rfl
  | cons b tail ih => cases b <;> simp [decodeBits, ih]

/-- Appending trailing `false` bits does not change the natural number a bit list decodes to. -/
lemma decodeBits_append_replicate_false (bs : List Bool) (m : ℕ) :
    decodeBits (bs ++ List.replicate m false) = decodeBits bs := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, decodeBits_append_false, ih]

private lemma bits_length_le_bits_length_succ (S : ℕ) :
    (Nat.bits S).length ≤ (Nat.bits (S + 1)).length := by
  have h1 : (Nat.bits S).length = Nat.size S := Nat.size_eq_bits_len S
  have h2 : (Nat.bits (S + 1)).length = Nat.size (S + 1) := Nat.size_eq_bits_len (S + 1)
  rw [h1, h2]
  exact Nat.size_le_size (Nat.le_succ S)

private lemma f_strictMono : StrictMono (fun S => S + (Nat.bits S).length + 1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := bits_length_le_bits_length_succ n
  omega

private lemma findS_eq_some {N S : ℕ} (h : S + (Nat.bits S).length + 1 = N) :
    (List.range (N + 1)).find? (fun s => s + (Nat.bits s).length + 1 == N) = some S := by
  have h_mono := f_strictMono
  have h_lt : ∀ s < S, s + (Nat.bits s).length + 1 < N := by
    intro s hs
    have h_st := h_mono hs
    dsimp at h_st
    omega
  have h_not : ∀ s < S, (s + (Nat.bits s).length + 1 == N) = false := by
    intro s hs
    have := h_lt s hs
    simp; omega
  have h_eq : (S + (Nat.bits S).length + 1 == N) = true := by simp [h]
  have h_le : S ≤ N := by omega
  obtain ⟨l2, hl2⟩ : ∃ l2, List.range (N + 1) = List.range S ++ S :: l2 := by
    refine ⟨(List.range (N + 1)).drop (S + 1), ?_⟩
    have h1 : S + 1 ≤ N + 1 := by omega
    have h2 : (List.range (N + 1)).take (S + 1) = List.range S ++ [S] := by
      rw [List.take_range, min_eq_left h1, List.range_succ]
    have h3 := (List.take_append_drop (S + 1) (List.range (N + 1))).symm
    rw [h2] at h3
    rw [List.append_assoc] at h3
    exact h3
  rw [hl2, List.find?_append]
  have h_find_nil : (List.range S).find? (fun s => s + (Nat.bits s).length + 1 == N) = none := by
    rw [List.find?_eq_none]
    intro s hs
    have := h_not s (List.mem_range.mp hs)
    simp [this]
  rw [h_find_nil]
  simp [h_eq]

private def findS (N : ℕ) : Option ℕ :=
  (List.range (N + 1)).foldr
    (fun S acc => bif S + (Nat.bits S).length + 1 == N then some S else acc) none

private lemma primrec_findS : Primrec findS := by
  have h_range : Primrec (fun N : ℕ => List.range (N + 1)) :=
    Primrec.list_range.comp Primrec.succ
  have h_step : Primrec₂ (fun (N : ℕ) (p : ℕ × Option ℕ) =>
      bif p.1 + (Nat.bits p.1).length + 1 == N then some p.1 else p.2) := by
    have h_cond : Primrec₂ (fun (N : ℕ) (p : ℕ × Option ℕ) =>
        p.1 + (Nat.bits p.1).length + 1 == N) := by
      have h1 : Primrec₂ (fun (N : ℕ) (p : ℕ × Option ℕ) => p.1 + (Nat.bits p.1).length + 1) :=
        Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.list_length.comp (primrec_natBits.comp (Primrec.fst.comp Primrec.snd))))
      have h2 : Primrec₂ (fun (N : ℕ) (_p : ℕ × Option ℕ) => N) :=
        Primrec.fst
      exact Primrec.beq.comp h1 h2
    have h_then : Primrec₂ (fun (_N : ℕ) (p : ℕ × Option ℕ) => Option.some p.1) :=
      Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)
    have h_else : Primrec₂ (fun (_N : ℕ) (p : ℕ × Option ℕ) => p.2) :=
      Primrec.snd.comp Primrec.snd
    exact Primrec.cond h_cond h_then h_else
  exact Primrec.list_foldr h_range (Primrec.const (none : Option ℕ)) h_step.to₂

private def extractFromS (w : BitString) (S : ℕ) : Option (BitString × BitString) :=
  let k := (Nat.bits S).length + 1
  let hdr := w.take k
  let lx := decodeBits hdr
  bif lx > S then none else
  let rem := w.drop k
  let px := rem.take lx
  let qy := rem.drop lx
  some (px, qy)

private lemma primrec_extractFromS : Primrec₂ extractFromS := by
  have hk : Primrec (fun p : BitString × ℕ => (Nat.bits p.2).length + 1) :=
    Primrec.succ.comp (Primrec.list_length.comp (primrec_natBits.comp Primrec.snd))
  have h_take_raw : Primrec (fun p : BitString × ℕ => p.1.take p.2) :=
    Primrec.list_take.comp Primrec.snd Primrec.fst
  have h_drop_raw : Primrec (fun p : BitString × ℕ => p.1.drop p.2) :=
    Primrec.list_drop.comp Primrec.snd Primrec.fst
  have hhdr : Primrec (fun p : BitString × ℕ => p.1.take ((Nat.bits p.2).length + 1)) :=
    h_take_raw.comp (Primrec.fst.pair hk)
  have hlx : Primrec (fun p : BitString × ℕ => decodeBits (p.1.take ((Nat.bits p.2).length + 1))) :=
    primrec_decodeBits.comp hhdr
  have hcond : Primrec (fun p : BitString × ℕ =>
      decide (p.2 < decodeBits (p.1.take ((Nat.bits p.2).length + 1)))) :=
    (PrimrecPred.decide Primrec.nat_lt).comp (Primrec.snd.pair hlx)
  have hrem : Primrec (fun p : BitString × ℕ => p.1.drop ((Nat.bits p.2).length + 1)) :=
    h_drop_raw.comp (Primrec.fst.pair hk)
  have hpx : Primrec (fun p : BitString × ℕ =>
      (p.1.drop ((Nat.bits p.2).length + 1)).take
        (decodeBits (p.1.take ((Nat.bits p.2).length + 1)))) :=
    h_take_raw.comp (hrem.pair hlx)
  have hqy : Primrec (fun p : BitString × ℕ =>
      (p.1.drop ((Nat.bits p.2).length + 1)).drop
        (decodeBits (p.1.take ((Nat.bits p.2).length + 1)))) :=
    h_drop_raw.comp (hrem.pair hlx)
  have hthen : Primrec (fun _p : BitString × ℕ => (none : Option (BitString × BitString))) :=
    Primrec.const none
  have helse : Primrec (fun p : BitString × ℕ => Option.some (
      (p.1.drop ((Nat.bits p.2).length + 1)).take
        (decodeBits (p.1.take ((Nat.bits p.2).length + 1))),
      (p.1.drop ((Nat.bits p.2).length + 1)).drop
        (decodeBits (p.1.take ((Nat.bits p.2).length + 1))))) :=
    Primrec.option_some.comp (hpx.pair hqy)
  exact Primrec.cond hcond hthen helse

private def extractPrograms (w : BitString) : Option (BitString × BitString) :=
  (findS w.length).bind (fun S => extractFromS w S)

private lemma primrec_extractPrograms : Primrec extractPrograms := by
  have h_find : Primrec (fun w : BitString => findS w.length) :=
    primrec_findS.comp Primrec.list_length
  have h_ext : Primrec₂ (fun (w : BitString) (S : ℕ) => extractFromS w S) :=
    primrec_extractFromS
  exact Primrec.option_bind h_find h_ext

private lemma extractPrograms_spec (px qy : BitString) :
    let lx := px.length
    let ly := qy.length
    let S := lx + ly
    let k := (Nat.bits S).length + 1
    let hdr := Nat.bits lx ++ List.replicate (k - (Nat.bits lx).length) false
    let w := hdr ++ px ++ qy
    extractPrograms w = some (px, qy) := by
  intro lx ly S k
  set hdr : BitString := Nat.bits lx ++ List.replicate (k - (Nat.bits lx).length) false
  set w : BitString := hdr ++ px ++ qy
  have h_lx_le_S : lx ≤ S := Nat.le_add_right _ _
  have h_bits_lx_le : (Nat.bits lx).length ≤ (Nat.bits S).length := by
    have h1 : (Nat.bits lx).length = Nat.size lx := Nat.size_eq_bits_len _
    have h2 : (Nat.bits S).length = Nat.size S := Nat.size_eq_bits_len _
    rw [h1, h2]
    exact Nat.size_le_size h_lx_le_S
  have h_hdr_len : hdr.length = k := by
    dsimp [hdr, k]
    rw [List.length_append, List.length_replicate]
    omega
  have h_w_len : w.length = S + k := by
    dsimp [w, S, lx, ly]
    rw [List.length_append, List.length_append, h_hdr_len]
    omega
  have h_find : (List.range (w.length + 1)).find?
      (fun s => s + (Nat.bits s).length + 1 == w.length) = some S := by
    have h_w_eq : S + (Nat.bits S).length + 1 = w.length := by
      dsimp [k] at h_w_len
      omega
    exact findS_eq_some h_w_eq
  have h_foldr_findS : findS w.length =
      (List.range (w.length + 1)).find?
        (fun s => s + (Nat.bits s).length + 1 == w.length) := by
    unfold findS
    induction List.range (w.length + 1) with
    | nil => rfl
    | cons head tail ih =>
      simp at ih
      simp [ih]
      by_cases h : head + head.bits.length + 1 = w.length <;> simp [h]
  change (findS w.length).bind (fun S => extractFromS w S) = some (px, qy)
  rw [h_foldr_findS, h_find]
  unfold extractFromS
  dsimp only [Option.bind, k]
  have h_take : w.take ((Nat.bits S).length + 1) = hdr := by
    have h_k_eq : (Nat.bits S).length + 1 = hdr.length := h_hdr_len.symm
    dsimp [w]
    rw [h_k_eq, List.append_assoc, List.take_left]
  rw [h_take]
  dsimp only [hdr]
  rw [decodeBits_append_replicate_false, decodeBits_natBits]
  have h_not_gt : ¬ (lx > S) := by omega
  have h_drop : w.drop ((Nat.bits S).length + 1) = px ++ qy := by
    have h_k_eq : (Nat.bits S).length + 1 = hdr.length := h_hdr_len.symm
    dsimp [w]
    rw [h_k_eq, List.append_assoc, List.drop_left]
  rw [Bool.cond_eq_ite, ite_eq_right (by simp [h_not_gt]), h_drop]
  dsimp only [lx]
  rw [List.take_left, List.drop_left]

private def midMap (U : Map) (pq : BitString × BitString) : Part BitString :=
  (U (pq.1, [])).bind (fun x => (U (pq.2, [])).map (fun y => myPairCode (x, y)))

private lemma midMap_partrec (U : Map) (hU : isDecompressor U) : Partrec (midMap U) := by
  have h_eval1 : Partrec (fun pq : BitString × BitString => U (pq.1, [])) :=
    hU.comp (Computable.pair Computable.fst (Computable.const [])).partrec
  have h_eval2 : Partrec (fun p : (BitString × BitString) × BitString => U (p.1.2, [])) :=
    hU.comp (Computable.pair (Computable.snd.comp Computable.fst) (Computable.const [])).partrec
  have h_map : Computable (fun p : ((BitString × BitString) × BitString) × BitString =>
      myPairCode (p.1.2, p.2)) :=
    myPairCode_comp.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have h_inner : Partrec (fun p : (BitString × BitString) × BitString =>
      (U (p.1.2, [])).map (fun y => myPairCode (p.2, y))) :=
    Partrec.map h_eval2 h_map.partrec
  exact Partrec.bind h_eval1 h_inner

private def decompressor (U : Map) : Map := fun pr =>
  (↑(extractPrograms pr.1) : Part (BitString × BitString)).bind (midMap U)

private lemma decompressor_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (decompressor U) := by
  have h_ext : Partrec (fun pr : BitString × BitString =>
      (↑(extractPrograms pr.1) : Part (BitString × BitString))) :=
    Computable.ofOption (primrec_extractPrograms.to_comp.comp Computable.fst)
  have h_mid : Partrec (fun pr : (BitString × BitString) × (BitString × BitString) =>
      midMap U pr.2) :=
    (midMap_partrec U hU).comp Computable.snd.partrec
  exact Partrec.bind h_ext h_mid

/-- **Exercise 22.** `C(x, y) ≤ C(x) + C(y) + log (C(x) + C(y)) + O(1)`. -/
theorem plainK_pair_le_add_log_of_add (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + plainK U y +
        ((Nat.log 2 (cVal U x + cVal U y) + k : ℕ) : ℕ∞) := by
  obtain ⟨c_D, hc_D⟩ := hU.2 (decompressor U) (decompressor_isDecompressor U hU.1)
  use c_D + 2
  intro x y
  by_cases hx : plainK U x = ⊤
  · rw [hx, top_add]; exact le_top
  by_cases hy : plainK U y = ⊤
  · rw [hy, add_top, top_add]; exact le_top
  obtain ⟨px, hpx_prod, hpx_len⟩ := exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hx
  obtain ⟨qy, hqy_prod, hqy_len⟩ := exists_program_of_KP_ne_top (M := U) (x := y) (y := []) hy
  have hcVal_x : cVal U x = px.length := by
    dsimp [cVal, plainK, KP] at hpx_len ⊢
    rw [← hpx_len]
    rfl
  have hcVal_y : cVal U y = qy.length := by
    dsimp [cVal, plainK, KP] at hqy_len ⊢
    rw [← hqy_len]
    rfl
  set lx := px.length
  set ly := qy.length
  set S := lx + ly
  set k_hdr := (Nat.bits S).length + 1
  set hdr := Nat.bits lx ++ List.replicate (k_hdr - (Nat.bits lx).length) false
  set w := hdr ++ px ++ qy
  have h_ext_spec := extractPrograms_spec px qy
  have h_dec_mem : pairCode x y ∈ decompressor U (w, []) := by
    unfold decompressor
    rw [Part.mem_bind_iff]
    refine ⟨(px, qy), ?_, ?_⟩
    · rw [Part.mem_ofOption]
      exact h_ext_spec
    · unfold midMap myPairCode
      rw [Part.mem_bind_iff]
      refine ⟨x, hpx_prod, ?_⟩
      rw [Part.mem_map_iff]
      exact ⟨y, hqy_prod, rfl⟩
  have h_plainK_D : plainK (decompressor U) (pairCode x y) ≤ (w.length : ℕ∞) := by
    apply sInf_le
    exact ⟨w, h_dec_mem, rfl⟩
  have h_cPair_le := hc_D (pairCode x y) []
  dsimp [cPair] at h_cPair_le ⊢
  have h_bits_len : (Nat.bits S).length ≤ Nat.log 2 S + 1 := by
    have h1 : (Nat.bits S).length = Nat.size S := Nat.size_eq_bits_len S
    rw [h1, Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by decide) S
  have h_hdr_len_calc : hdr.length = (Nat.bits S).length + 1 := by
    dsimp [hdr, k_hdr]
    rw [List.length_append, List.length_replicate]
    have h_lx_le_S : lx ≤ S := Nat.le_add_right _ _
    have h_bits_lx_le : (Nat.bits lx).length ≤ (Nat.bits S).length := by
      have h1 : (Nat.bits lx).length = Nat.size lx := Nat.size_eq_bits_len _
      have h2 : (Nat.bits S).length = Nat.size S := Nat.size_eq_bits_len _
      rw [h1, h2]
      exact Nat.size_le_size h_lx_le_S
    omega
  have h_len : w.length = hdr.length + lx + ly := by
    change (hdr ++ px ++ qy).length = hdr.length + lx + ly
    rw [List.length_append, List.length_append]
  have h_w_len_calc : w.length = (Nat.bits S).length + 1 + lx + ly := by
    rw [h_len, h_hdr_len_calc]
  have h_w_len_bound : w.length ≤ lx + ly + Nat.log 2 S + 2 := by
    omega
  have h_cPair_bound : plainK (decompressor U) (pairCode x y) ≤
      (lx : ℕ∞) + (ly : ℕ∞) + ((Nat.log 2 S + 2 : ℕ) : ℕ∞) := by
    refine h_plainK_D.trans ?_
    push_cast
    have h_nat : w.length ≤ lx + ly + (Nat.log 2 S + 2) := h_w_len_bound
    exact_mod_cast h_nat
  have h_1 := add_le_add_left h_plainK_D (c_D : ℕ∞)
  have h_2 : (w.length : ℕ∞) + (c_D : ℕ∞) ≤
      (lx : ℕ∞) + (ly : ℕ∞) + ((Nat.log 2 S + (c_D + 2) : ℕ) : ℕ∞) := by
    push_cast
    have h_nat : w.length + c_D ≤ lx + ly + (Nat.log 2 S + (c_D + 2)) := by omega
    exact_mod_cast h_nat
  have h_cPair_bound_c_D := h_1.trans h_2
  have h_lx_eq : (lx : ℕ∞) = plainK U x := hpx_len
  have h_ly_eq : (ly : ℕ∞) = plainK U y := hqy_len
  refine h_cPair_le.trans (h_cPair_bound_c_D.trans ?_)
  rw [h_lx_eq, h_ly_eq, hcVal_x, hcVal_y]

/-- The code of the pair consisting of the output and the binary length of the program, used to
pair a string with its own complexity. -/
def pairSelfComplexityMap (p_x : (BitString × BitString) × BitString) : BitString :=
  pairCode p_x.2 (Nat.bits p_x.1.1.length)

/-- Decompressor which outputs the pair of `U`'s output and the length of the program it was
given, so that a shortest program for `x` also describes `⟨x, C(x)⟩`. -/
def pairSelfComplexityDecompressor (U : Map) : Map :=
  fun py => (U (py.1, [])).map (fun x => pairSelfComplexityMap (py, x))

private theorem pairSelfComplexityMap_computable : Computable pairSelfComplexityMap := by
  have hPairCode₂ : Computable₂ (fun (a b : BitString) => pairCode a b) :=
    pairCode_computable
  have h_snd : Computable (fun (p_x : (BitString × BitString) × BitString) => p_x.2) :=
    Computable.snd
  have h_bits : Computable (fun (p_x : (BitString × BitString) × BitString) =>
      Nat.bits p_x.1.1.length) :=
    natBits_computable.comp (Computable.list_length.comp (Computable.fst.comp Computable.fst))
  exact hPairCode₂.comp h_snd h_bits

private theorem pairSelfComplexityDecompressor_isDecompressor (U : Map)
    (hU : isOptimalConditional U) :
    isDecompressor (pairSelfComplexityDecompressor U) :=
  Partrec.map
    (Partrec.comp hU.1 (Computable.pair Computable.fst (Computable.const [])))
    pairSelfComplexityMap_computable

/-- **Exercise 23.** `C(x, C(x)) = C(x) + O(1)`. -/
theorem plainK_pair_self_plainK_eq (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x : BitString,
      cPair U x (Nat.bits (cVal U x)) ≤ plainK U x + (k : ℕ∞) ∧
        plainK U x ≤ cPair U x (Nat.bits (cVal U x)) + (k : ℕ∞) := by
  let D := pairSelfComplexityDecompressor U
  have hD := pairSelfComplexityDecompressor_isDecompressor U hU
  obtain ⟨c1, hc1⟩ := hU.2 D hD
  obtain ⟨c2, hc2⟩ := plainK_map_le U hU decodeFirst decodeFirst_computable
  refine ⟨c1 + c2, fun x => ⟨?_, ?_⟩⟩
  · by_cases htop : plainK U x = ⊤
    · rw [htop]; exact le_top
    · have hne : (candidateLengths U x []).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro he
        have : plainK U x = ⊤ := by change sInf (candidateLengths U x []) = ⊤; rw [he, sInf_empty]
        exact htop this
      obtain ⟨p, hp_prod, hp_len⟩ := csInf_mem hne
      have hp_val : p.length = cVal U x := by
        change (p.length : ℕ∞) = plainK U x at hp_len
        dsimp [cVal]
        rw [← hp_len, ENat.toNat_natCast]
      have hD_prod : pairCode x (Nat.bits (cVal U x)) ∈ D (p, []) := by
        change pairCode x (Nat.bits (cVal U x)) ∈
          (U (p, [])).map (fun x' => pairSelfComplexityMap ((p, []), x'))
        rw [Part.mem_map_iff]
        exact ⟨x, hp_prod, by dsimp [pairSelfComplexityMap]; rw [hp_val]⟩
      have h_cand : (p.length : ℕ∞) ∈
          candidateLengths D (pairCode x (Nat.bits (cVal U x))) [] := ⟨p, hD_prod, rfl⟩
      have h_le : condK D (pairCode x (Nat.bits (cVal U x))) [] ≤ plainK U x := by
        change sInf (candidateLengths D (pairCode x (Nat.bits (cVal U x))) []) ≤ plainK U x
        calc sInf (candidateLengths D (pairCode x (Nat.bits (cVal U x))) [])
          _ ≤ (p.length : ℕ∞) := sInf_le h_cand
          _ = plainK U x := hp_len
      have h_opt := hc1 (pairCode x (Nat.bits (cVal U x))) []
      dsimp [cPair]
      have h_trans : plainK U (pairCode x (Nat.bits (cVal U x))) ≤ plainK U x + (c1 : ℕ∞) :=
        le_trans h_opt (add_le_add_left h_le (c1 : ℕ∞))
      have hc12 : (c1 : ℕ∞) ≤ ((c1 + c2 : ℕ) : ℕ∞) := by
        rw [Nat.cast_add]
        exact le_add_right le_rfl
      calc plainK U (pairCode x (Nat.bits (cVal U x)))
        _ ≤ plainK U x + (c1 : ℕ∞) := h_trans
        _ ≤ plainK U x + ((c1 + c2 : ℕ) : ℕ∞) := add_le_add_right hc12 (plainK U x)
  · have h_map := hc2 (pairCode x (Nat.bits (cVal U x)))
    rw [decodeFirst_pairCode] at h_map
    dsimp [cPair]
    have hc21 : (c2 : ℕ∞) ≤ ((c1 + c2 : ℕ) : ℕ∞) := by
      rw [Nat.cast_add]
      exact le_add_left le_rfl
    calc plainK U x
      _ ≤ plainK U (pairCode x (Nat.bits (cVal U x))) + (c2 : ℕ∞) := h_map
      _ ≤ plainK U (pairCode x (Nat.bits (cVal U x))) + ((c1 + c2 : ℕ) : ℕ∞) :=
        add_le_add_right hc21 (plainK U (pairCode x (Nat.bits (cVal U x))))

/-- Remove the trailing block `1 0…0` added by `padString`, recovering the original string. -/
def unpadString (s : BitString) : BitString :=
  (s.reverse.drop (s.reverse.findIdx id + 1)).reverse

/-- Extend `p` to length `n + 1` by appending a single `true` followed by `false`s. -/
def padString (p : BitString) (n : ℕ) : BitString :=
  p ++ true :: List.replicate (n - p.length) false

/-- The first `true` in `0^m 1 l` is found at offset `m`, in the accumulator form of `findIdx`. -/
theorem findIdx_go_replicate_false_cons_true (m : ℕ) (l : BitString) (n : ℕ) :
    List.findIdx.go id (List.replicate m false ++ true :: l) n = m + n := by
  induction m generalizing n with
  | zero =>
    dsimp [List.findIdx.go]
    omega
  | succ m ih =>
    change List.findIdx.go id (false :: (List.replicate m false ++ true :: l)) n =
      m + 1 + n
    dsimp [List.findIdx.go]
    rw [ih (n + 1)]
    omega

/-- The index of the first `true` in `0^m 1 l` is `m`. -/
theorem findIdx_replicate_false_cons_true (m : ℕ) (l : BitString) :
    (List.replicate m false ++ true :: l).findIdx id = m := by
  change List.findIdx.go id (List.replicate m false ++ true :: l) 0 = m
  rw [findIdx_go_replicate_false_cons_true, add_zero]

/-- Dropping through the first `true` of `0^m 1 l` leaves `l`. -/
theorem drop_findIdx_replicate_false_cons_true (m : ℕ) (l : BitString) :
    (List.replicate m false ++ true :: l).drop
      ((List.replicate m false ++ true :: l).findIdx id + 1) = l := by
  rw [findIdx_replicate_false_cons_true]
  induction m with
  | zero => rfl
  | succ m ih =>
    change (false :: (List.replicate m false ++ true :: l)).drop (m + 1 + 1) = l
    dsimp [List.drop]
    exact ih

/-- Unpadding inverts padding: the padded string is stripped back to the original. -/
theorem unpadString_padString (p : BitString) (n : ℕ) (_hp : p.length ≤ n) :
    unpadString (padString p n) = p := by
  unfold unpadString padString
  have hrev : (p ++ true :: List.replicate (n - p.length) false).reverse =
      List.replicate (n - p.length) false ++ true :: p.reverse := by
    rw [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc]
    rfl
  rw [hrev, drop_findIdx_replicate_false_cons_true]
  exact List.reverse_reverse p

/-- Padding a string of length at most `n` yields a string of length `n + 1`. -/
theorem padString_length (p : BitString) (n : ℕ) (hp : p.length ≤ n) :
    (padString p n).length = n + 1 := by
  unfold padString
  simp [List.length_append, List.length_replicate]
  omega

/-- Unpadding a string is computable. -/
theorem unpadString_computable : Computable unpadString := by
  have hrev : Primrec (fun z : BitString => z.reverse) := Primrec.list_reverse
  have hidx : Primrec (fun z : BitString => z.findIdx id) :=
    Primrec.list_findIdx Primrec.id Primrec.snd
  have hidx_rev : Primrec (fun z : BitString => z.reverse.findIdx id) :=
    hidx.comp hrev
  have hdrop : Primrec (fun z : BitString =>
      z.reverse.drop (z.reverse.findIdx id + 1)) :=
    Primrec.list_drop.comp (Primrec.succ.comp hidx_rev) hrev
  have hunpad : Primrec (fun z : BitString =>
      (z.reverse.drop (z.reverse.findIdx id + 1)).reverse) :=
    Primrec.list_reverse.comp hdrop
  exact hunpad.to_comp

/-- The decompressor that splits its program in half, runs `U` on the two unpadded halves, and
returns the pair code of the two outputs. -/
def pairLevelMap (U : Map) : Map := fun pr =>
  (U (unpadString (pr.1.take (pr.1.length / 2)), [])).bind (fun x =>
    (U (unpadString (pr.1.drop (pr.1.length / 2)), [])).map (fun y => pairCode x y))

private theorem pairLevelMap_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (pairLevelMap U) := by
  have htake_comp : Computable (fun w : BitString => w.take (w.length / 2)) :=
    (Primrec.list_take.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))
      Primrec.id).to_comp
  have hdrop_comp : Computable (fun w : BitString => w.drop (w.length / 2)) :=
    (Primrec.list_drop.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))
      Primrec.id).to_comp
  have hf1 : Computable (fun pr : BitString × BitString =>
      unpadString (pr.1.take (pr.1.length / 2))) :=
    unpadString_computable.comp (htake_comp.comp Computable.fst)
  have hf2 : Computable (fun q : (BitString × BitString) × BitString =>
      unpadString (q.1.1.drop (q.1.1.length / 2))) :=
    unpadString_computable.comp (hdrop_comp.comp (Computable.fst.comp Computable.fst))
  have hPair : Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  have hRun1 : Partrec (fun pr : BitString × BitString =>
      U (unpadString (pr.1.take (pr.1.length / 2)), [])) :=
    Partrec.comp hU (Computable.pair hf1 (Computable.const []))
  have hRun2 : Partrec (fun q : (BitString × BitString) × BitString =>
      U (unpadString (q.1.1.drop (q.1.1.length / 2)), [])) :=
    Partrec.comp hU (Computable.pair hf2 (Computable.const []))
  have hMap : Partrec (fun q : (BitString × BitString) × BitString =>
      (U (unpadString (q.1.1.drop (q.1.1.length / 2)), [])).map
        (fun y => pairCode q.2 y)) :=
    Partrec.map hRun2 (hPair.comp (Computable.snd.comp Computable.fst) Computable.snd)
  -- the bind is assembled against its own displayed type: elaborating it
  -- against the unfolded body of `pairLevelMap` is what used to be slow.
  have hbind : Partrec (fun pr : BitString × BitString =>
      (U (unpadString (pr.1.take (pr.1.length / 2)), [])).bind fun x =>
        (U (unpadString (pr.1.drop (pr.1.length / 2)), [])).map fun y => pairCode x y) :=
    Partrec.bind hRun1 hMap
  exact hbind

/-- **Exercise 24.** `C(x), C(y) ≤ n` implies `C(x, y) ≤ 2 n + O(1)`. -/
theorem plainK_pair_le_two_mul (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y : BitString), plainK U x ≤ (n : ℕ∞) → plainK U y ≤ (n : ℕ∞) →
      cPair U x y ≤ ((2 * n + k : ℕ) : ℕ∞) := by
  let D := pairLevelMap U
  have hD : isDecompressor D := pairLevelMap_isDecompressor U hU.1
  obtain ⟨c, hc⟩ := hU.2 D hD
  refine ⟨c + 2, fun n x y hx hy => ?_⟩
  obtain ⟨p, hp_len, hp⟩ := (condK_le_iff U x [] n).mp hx
  have hple : p.length ≤ n := hp_len
  obtain ⟨q, hq_len, hq⟩ := (condK_le_iff U y [] n).mp hy
  have hqle : q.length ≤ n := hq_len
  set p' := padString p n
  set q' := padString q n
  set w := p' ++ q'
  have hp'len : p'.length = n + 1 := padString_length p n hple
  have hq'len : q'.length = n + 1 := padString_length q n hqle
  have hwlen : w.length = 2 * n + 2 := by
    dsimp [w]
    rw [List.length_append, hp'len, hq'len]
    omega
  have hwdiv : w.length / 2 = n + 1 := by
    rw [hwlen]
    omega
  have htake : w.take (w.length / 2) = p' := by
    rw [hwdiv]
    dsimp [w]
    rw [← hp'len]
    exact List.take_left
  have hdrop : w.drop (w.length / 2) = q' := by
    rw [hwdiv]
    dsimp [w]
    rw [← hp'len]
    exact List.drop_left
  have hunpad1 : unpadString (w.take (w.length / 2)) = p := by
    rw [htake]
    exact unpadString_padString p n hple
  have hunpad2 : unpadString (w.drop (w.length / 2)) = q := by
    rw [hdrop]
    exact unpadString_padString q n hqle
  have hDprod : produces D w [] (pairCode x y) := by
    change pairCode x y ∈ D (w, [])
    dsimp [D, pairLevelMap]
    rw [hunpad1, hunpad2]
    exact Part.mem_bind_iff.mpr ⟨x, hp, Part.mem_map (fun z => pairCode x z) hq⟩
  have hcond : condK D (pairCode x y) [] ≤ ((2 * n + 2 : ℕ) : ℕ∞) := by
    have hle := sInf_le (s := candidateLengths D (pairCode x y) []) ⟨w, hDprod, rfl⟩
    change _ ≤ (w.length : ℕ∞) at hle
    rw [hwlen] at hle
    exact hle
  have hpair : cPair U x y ≤ condK D (pairCode x y) [] + (c : ℕ∞) :=
    hc (pairCode x y) []
  calc cPair U x y ≤ condK D (pairCode x y) [] + (c : ℕ∞) := hpair
    _ ≤ ((2 * n + 2 : ℕ) : ℕ∞) + (c : ℕ∞) := by gcongr
    _ = ((2 * n + (c + 2) : ℕ) : ℕ∞) := by
      push_cast
      ring_nf

end Kolmogorov
