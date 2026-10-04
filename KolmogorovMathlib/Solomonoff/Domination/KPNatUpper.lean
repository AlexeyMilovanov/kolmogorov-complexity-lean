import KolmogorovMathlib.Prefix.UpperSemicomputableBound
import KolmogorovMathlib.MonotoneComplexity.SharedCoding

/-!
# Upper semicomputability of the prefix complexity of numerical indices

The weights `2^{-K(e)}` of the index mixture behind dominance must be lower semicomputable,
which comes down to the upper semicomputability of `e ↦ K(e)`
(`isUpperSemicomputableNat_KPNat_toNat`, SUV Theorem 62).  The approximation at stage `s`
dovetails the prefix machine for `s` steps over all programs of length at most the a priori
bound `2 |e| + c` and keeps the length of the shortest one that prints `e`; it is computable,
non-increasing in `s`, and stabilises at `K(e)`.
-/

namespace Kolmogorov

private def check_eval (U_code : Nat.Partrec.Code) (s : ℕ) (p x : BitString) : Bool :=
  match Nat.Partrec.Code.evaln s U_code (Encodable.encode (p, ([] : BitString))) with
  | some res => res == Encodable.encode x
  | none => false

private def KPNat_approx (U_code : Nat.Partrec.Code) (c_len : ℕ) (s e : ℕ) : ℕ :=
  let e_bs := natToBitString e
  let default_e := 2 * e_bs.length + c_len
  let p_list := boundedPrograms default_e
  let valid_p := p_list.filter (fun p => check_eval U_code s p e_bs)
  (valid_p.map List.length).foldl min default_e

/-- The dovetailed shortest-program bound is computable in the stage and the index. -/
private lemma KPNat_approx_computable (U_code : Nat.Partrec.Code) (c_len : ℕ) :
    Computable₂ (KPNat_approx U_code c_len) := by
  have hd_e : Primrec (fun p : ℕ × ℕ =>
      2 * (natToBitString p.2).length + c_len) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.list_length.comp (primrec_natToBitString.comp Primrec.snd)))
      (Primrec.const c_len)
  have hp : Primrec (fun p : ℕ × ℕ => boundedPrograms
      (2 * (natToBitString p.2).length + c_len)) :=
    primrec_boundedPrograms.comp hd_e
  have hc : Primrec₂ (fun (p : ℕ × ℕ) q =>
      check_eval U_code p.1 q (natToBitString p.2)) := by
    have he : Primrec (fun q : (ℕ × ℕ) × BitString =>
        Nat.Partrec.Code.evaln q.1.1 U_code (Encodable.encode (q.2, []))) :=
      Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const U_code))
        (Primrec.encode.comp
          (Primrec.pair Primrec.snd (Primrec.const ([] : BitString)))))
    have ho : Primrec (fun q : (ℕ × ℕ) × BitString =>
        some (Encodable.encode (natToBitString q.1.2))) :=
      Primrec.option_some.comp (Primrec.encode.comp
        (primrec_natToBitString.comp (Primrec.snd.comp Primrec.fst)))
    have hb : Primrec (fun q : (ℕ × ℕ) × BitString =>
        decide (Nat.Partrec.Code.evaln q.1.1 U_code (Encodable.encode (q.2, [])) =
          some (Encodable.encode (natToBitString q.1.2)))) :=
      Primrec.beq.comp he ho
    have hc' : Primrec (fun q : (ℕ × ℕ) × BitString =>
        check_eval U_code q.1.1 q.2 (natToBitString q.1.2)) :=
      hb.of_eq fun q => by
        dsimp [check_eval]
        have h_eq : ∀ o, decide (o = some (Encodable.encode (natToBitString q.1.2))) =
          match o with
          | some res => res == Encodable.encode (natToBitString q.1.2)
          | none => false := by
          intro o
          cases o with
          | none => rfl
          | some res => exact (Bool.beq_eq_decide_eq _ _).symm
        exact h_eq _
    exact hc'.to₂
  have hv := list_filter_primrec hp hc
  have hm := Primrec.list_map hv
    ((Primrec.list_length.comp Primrec.snd).to₂)
  have hf := Primrec.list_foldl hm hd_e
    ((Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact hf.to_comp.of_eq (fun _ => rfl)

/-- A program found to output `x` within `s` steps still does so within `s + 1` steps. -/
private lemma check_eval_succ {U_code : Nat.Partrec.Code} {s : ℕ} {p x : BitString}
    (hp : check_eval U_code s p x = true) : check_eval U_code (s + 1) p x = true := by
  change ((match Nat.Partrec.Code.evaln s U_code
    (Nat.pair (Encodable.encode p) 0) with
    | some res => res == Encodable.encode x
    | none => false) = true) at hp
  change ((match Nat.Partrec.Code.evaln (s + 1) U_code
    (Nat.pair (Encodable.encode p) 0) with
    | some res => res == Encodable.encode x
    | none => false) = true)
  cases h_eval : Nat.Partrec.Code.evaln s U_code (Nat.pair (Encodable.encode p) 0)
  · rw [h_eval] at hp
    exact Bool.noConfusion hp
  · rename_i res
    have hp' : (res == Encodable.encode x) = true := by
      simpa [h_eval] using hp
    have h_mem : res ∈ Nat.Partrec.Code.evaln s U_code
        (Nat.pair (Encodable.encode p) 0) := h_eval
    have h_mem_succ := Nat.Partrec.Code.evaln_mono (Nat.le_succ s) h_mem
    rw [show s + 1 = s.succ by omega, Option.mem_def.mp h_mem_succ]
    exact hp'

/-- Folding `min` over a list is monotone in the initial value. -/
private lemma foldl_min_mono (l : List ℕ) {c d : ℕ} (hcd : c ≤ d) :
    l.foldl min c ≤ l.foldl min d := by
  induction l generalizing c d with
  | nil => exact hcd
  | cons x xs ih => exact ih (min_le_min hcd le_rfl)

/-- Folding `min` over a longer list gives a smaller value. -/
private lemma foldl_min_le_of_sublist {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) (c : ℕ) :
    l₂.foldl min c ≤ l₁.foldl min c := by
  induction h generalizing c with
  | slnil => rfl
  | cons a _ ih => exact le_trans (ih (min c a)) (foldl_min_mono _ (min_le_left c a))
  | cons_cons a _ ih => exact ih (min c a)

/-- Folding `min` gives at most the initial value. -/
private lemma foldl_min_le_init (l : List ℕ) (c : ℕ) : l.foldl min c ≤ c := by
  induction l generalizing c with
  | nil => rfl
  | cons y ys ih => exact le_trans (ih (min c y)) (min_le_left c y)

/-- Folding `min` gives at most every element of the list. -/
private lemma foldl_min_le_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) (c : ℕ) :
    l.foldl min c ≤ x := by
  induction l generalizing c with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (foldl_min_le_init ys (min c x)) (min_le_right c x)
    · exact ih hmem (min c y)

/-- A common lower bound of the initial value and of every element bounds the folded `min`. -/
private lemma le_foldl_min {l : List ℕ} {b c : ℕ} (hc : b ≤ c) (h : ∀ x ∈ l, b ≤ x) :
    b ≤ l.foldl min c := by
  induction l generalizing c with
  | nil => exact hc
  | cons x xs ih =>
    exact ih (le_min hc (h x List.mem_cons_self)) fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- More programs are found at a later stage, so the shortest length found can only drop. -/
private lemma KPNat_approx_succ_le (U_code : Nat.Partrec.Code) (c_len s e : ℕ) :
    KPNat_approx U_code c_len (s + 1) e ≤ KPNat_approx U_code c_len s e := by
  dsimp [KPNat_approx]
  apply foldl_min_le_of_sublist
  apply List.Sublist.map
  generalize boundedPrograms (2 * (natToBitString e).length + c_len) = l
  induction l with
  | nil => simp
  | cons p ps ih =>
    cases hp : check_eval U_code s p (natToBitString e)
    · cases hq : check_eval U_code (s + 1) p (natToBitString e) <;> simp [hp, hq, ih]
    · simp [hp, check_eval_succ hp, ih]

/-- **Prefix complexity of a numerical index is upper semicomputable.** There is a computable,
pointwise non-increasing family of integer upper bounds for `(KPNat U e).toNat`, stabilising at
each `e`: dovetail the prefix machine over all programs and record the length of the shortest one
found so far. SUV Theorem 62 (upper semicomputability of `K`). -/
lemma isUpperSemicomputableNat_KPNat_toNat (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    IsUpperSemicomputableNat (fun e => (KPNat U e).toNat) := by
  obtain ⟨U_code, hU_code⟩ := Nat.Partrec.Code.exists_code.mp hU.isDecompressor
  obtain ⟨c_len, hc_len⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨KPNat_approx U_code c_len, KPNat_approx_computable U_code c_len,
    KPNat_approx_succ_le U_code c_len, fun e => ?_⟩
  change ∃ s₀, ∀ s, s₀ ≤ s → KPNat_approx U_code c_len s e =
    (KPPlain U (natToBitString e)).toNat
  dsimp [KPNat_approx]
  have h_fin := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc_len (natToBitString e))
  have h_default : (KPPlain U (natToBitString e)).toNat ≤
      2 * (natToBitString e).length + c_len := by
    have h_cast : ((KPPlain U (natToBitString e)).toNat : ENat) ≤
        2 * (natToBitString e).length + c_len :=
      (ENat.natCast_toNat h_fin).trans_le (hc_len (natToBitString e))
    exact_mod_cast h_cast
  obtain ⟨p, hp_len, hp_prod⟩ := (condK_le_iff U (natToBitString e) []
      (KPPlain U (natToBitString e)).toNat).mp (by
    rw [ENat.natCast_toNat h_fin]
    exact le_rfl)
  have h_len_le : p.length ≤ 2 * (natToBitString e).length + c_len :=
    le_trans hp_len h_default
  obtain ⟨s₀, hs₀⟩ :=
    (produces_iff_evaln U_code hU_code p (natToBitString e) []).mp hp_prod
  refine ⟨s₀, fun s hs => le_antisymm ?_ ?_⟩
  · -- the shortest program `p` has been found by stage `s₀`
    have h_mem_valid : p.length ∈
        ((boundedPrograms (2 * (natToBitString e).length + c_len)).filter
          (fun q => check_eval U_code s q (natToBitString e))).map List.length := by
      apply List.mem_map_of_mem
      rw [List.mem_filter]
      refine ⟨(mem_boundedPrograms_iff p
        (2 * (natToBitString e).length + c_len)).mpr h_len_le, ?_⟩
      dsimp [check_eval]
      have h_evaln_s := Nat.Partrec.Code.evaln_mono hs hs₀
      change Encodable.encode (natToBitString e) ∈ Nat.Partrec.Code.evaln s U_code
        (Nat.pair (Encodable.encode p) 0) at h_evaln_s
      rw [Option.mem_def.mp h_evaln_s]
      simp
    exact le_trans (foldl_min_le_of_mem h_mem_valid _) hp_len
  · -- every program found outputs `e`, so it is no shorter than the complexity
    refine le_foldl_min h_default fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨q, hq_mem, rfl⟩ := hx
    rw [List.mem_filter] at hq_mem
    have h_check := hq_mem.2
    change (match Nat.Partrec.Code.evaln s U_code
      (Encodable.encode (q, ([] : BitString))) with
      | some res => res == Encodable.encode (natToBitString e)
      | none => false) = true at h_check
    cases h_eval_q : Nat.Partrec.Code.evaln s U_code
        (Nat.pair (Encodable.encode q) 0)
    · simp [h_eval_q] at h_check
    · rename_i res
      have h_eq : res = Encodable.encode (natToBitString e) :=
        beq_iff_eq.mp (by simpa [h_eval_q] using h_check)
      rw [h_eq] at h_eval_q
      have h_prod := (produces_iff_evaln U_code hU_code q
        (natToBitString e) []).mpr ⟨s, h_eval_q⟩
      have h_cond_le := (condK_le_iff U (natToBitString e) [] q.length).mpr
        ⟨q, le_rfl, h_prod⟩
      have h_cast : ((KPPlain U (natToBitString e)).toNat : ENat) =
          KPPlain U (natToBitString e) := by
        rw [ENat.natCast_toNat h_fin]
      have h_plain : KPPlain U (natToBitString e) ≤ (q.length : ENat) := by
        simpa [KPPlain, KP, KP_eq_condK] using h_cond_le
      rw [← h_cast] at h_plain
      exact_mod_cast h_plain

end Kolmogorov
