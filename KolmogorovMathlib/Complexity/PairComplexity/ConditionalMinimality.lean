import KolmogorovMathlib.Complexity.PairComplexity.Basic

/-!
# The conditional pair bound, and pairs of minimal programs

`plainK_pair_le_add_two_log_add_condK` (SUV Theorem 20): `C(x, y) ≤ C(x) + 2 log C(x) +
C(y | x) + O(1)`.  Its proof runs a decompressor that first recovers `x` from a
self-delimiting program and then `y` from `x`; `t19_cand`, `t19_enum`, `t19_idx` and `t19_fn`
are the enumeration of the candidates it searches, made primitive recursive through
`evaln_arg`, `eval_step_prim` and `cand_prim`.

The module continues with the pair and triple bounds of SUV Exercises 16–24, ending with
`plainK_triple_le_add_log` (Exercise 16): `C(x, y, z) ≤ C(x) + C(y) + C(z) + O(log n)`, by the
three-stage `tripleDecompressor`.
-/

namespace Kolmogorov
open Nat.Partrec (Code)

private lemma nodup_findIdx_getElem {α : Type*} [DecidableEq α] {l : List α} (h : l.Nodup)
    (i : ℕ) (hi : i < l.length) :
    l.findIdx (fun q => decide (q = l[i])) = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a tail ih =>
    rw [List.nodup_cons] at h
    rcases h with ⟨ha_not, h_nodup⟩
    rw [List.findIdx_cons]
    cases i with
    | zero =>
      have : (decide (a = (a :: tail)[0]) : Bool) = true := by simp
      rw [this]
      rfl
    | succ i =>
      have hi_tail : i < tail.length := by simpa using hi
      have h_neq : (decide (a = (a :: tail)[i + 1]) : Bool) = false := by
        simp only [decide_eq_false_iff_not]
        intro h_eq
        have h_mem : (a :: tail)[i + 1] ∈ tail := List.getElem_mem hi_tail
        rw [← h_eq] at h_mem
        exact ha_not h_mem
      rw [h_neq]
      change (if false then 0 else List.findIdx (fun q => decide (q = tail[i])) tail + 1) = i + 1
      rw [if_neg (by decide)]
      congr 1
      exact ih h_nodup i hi_tail

private def t19_cand (c_code : Nat.Partrec.Code) (p y : BitString) (M : ℕ) : Option BitString :=
  let x_nat := M.unpair.1
  let s := M.unpair.2
  match (Encodable.decode x_nat : Option BitString) with
  | none => none
  | some x =>
    bif (Nat.Partrec.Code.evaln s c_code (Encodable.encode (x, y, p.length))).isSome then
      some x
    else
      none

private def t19_enum (c_code : Nat.Partrec.Code) (p y : BitString) (M : ℕ) : List BitString :=
  match M with
  | 0 => []
  | M + 1 =>
    let acc := t19_enum c_code p y M
    match t19_cand c_code p y M with
    | none => acc
    | some x => bif decide (x ∈ acc) then acc else acc ++ [x]

private def t19_idx (p : BitString) : ℕ :=
  (exactLengthPrograms p.length).findIdx (fun q => decide (q = p))

private def t19_fn (c_code : Nat.Partrec.Code) (p y : BitString) (M : ℕ) : Option BitString :=
  (t19_enum c_code p y M)[t19_idx p]?

private def evaln_arg (c_code : Nat.Partrec.Code)
    (pair : ((BitString × BitString) × ℕ) × BitString) : (ℕ × Nat.Partrec.Code) × ℕ :=
  (((pair.1).2.unpair.2, c_code), Encodable.encode (pair.2, pair.1.1.2, pair.1.1.1.length))

private theorem evaln_arg_prim (c_code : Nat.Partrec.Code) :
    Primrec (evaln_arg c_code) := by
  have h_s : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      (pair.1).2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))
  have h_c : Primrec (fun (_ : ((BitString × BitString) × ℕ) × BitString) => c_code) :=
    Primrec.const c_code
  have h_sc : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      ((pair.1).2.unpair.2, c_code)) :=
    Primrec.pair h_s h_c
  have h_p_len : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      pair.1.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have h_y : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      pair.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have h_x : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) => pair.2) :=
    Primrec.snd
  have h_tuple : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      Encodable.encode (pair.2, pair.1.1.2, pair.1.1.1.length)) :=
    Primrec.encode.comp (Primrec.pair h_x (Primrec.pair h_y h_p_len))
  exact Primrec.pair h_sc h_tuple

private theorem eval_step_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      (Nat.Partrec.Code.evaln (pair.1).2.unpair.2 c_code
        (Encodable.encode (pair.2, pair.1.1.2, pair.1.1.1.length))).isSome) := by
  have h_eval : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      Nat.Partrec.Code.evaln (pair.1).2.unpair.2 c_code
        (Encodable.encode (pair.2, pair.1.1.2, pair.1.1.1.length))) :=
    Nat.Partrec.Code.primrec_evaln.comp (evaln_arg_prim c_code)
  exact Primrec.option_isSome.comp h_eval

private theorem cand_body_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      bif (Nat.Partrec.Code.evaln (pair.1).2.unpair.2 c_code
        (Encodable.encode (pair.2, pair.1.1.2, pair.1.1.1.length))).isSome then
        some pair.2
      else
        none) := by
  have h_cond := eval_step_prim c_code
  have h_then : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) =>
      (some pair.2 : Option BitString)) :=
    Primrec.option_some.comp Primrec.snd
  have h_else : Primrec (fun (_ : ((BitString × BitString) × ℕ) × BitString) =>
      (none : Option BitString)) :=
    Primrec.const none
  exact Primrec.cond h_cond h_then h_else

private theorem cand_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (q : (BitString × BitString) × ℕ) => t19_cand c_code q.1.1 q.1.2 q.2) := by
  have h_decode : Primrec (fun (q : (BitString × BitString) × ℕ) =>
      (Encodable.decode q.2.unpair.1 : Option BitString)) :=
    Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have h_body : Primrec₂ (fun (q : (BitString × BitString) × ℕ) (x : BitString) =>
      bif (Nat.Partrec.Code.evaln q.2.unpair.2 c_code
        (Encodable.encode (x, q.1.2, q.1.1.length))).isSome then
        some x
      else
        none) :=
    (cand_body_prim c_code).to₂
  have h_cand := Primrec.option_bind h_decode h_body
  exact h_cand.of_eq (fun q => by
    dsimp [t19_cand]
    cases (Encodable.decode q.2.unpair.1 : Option BitString) <;> rfl)

private def append_if_not_mem (acc : List BitString) (x : BitString) : List BitString :=
  bif decide (x ∈ acc) then acc else acc ++ [x]

private theorem append_if_not_mem_prim :
    Primrec (fun (p : List BitString × BitString) => append_if_not_mem p.1 p.2) := by
  have h_mem : Primrec (fun (p : List BitString × BitString) => decide (p.2 ∈ p.1)) :=
    bitString_mem_primrec.comp Primrec.snd Primrec.fst
  have h_then : Primrec (fun (p : List BitString × BitString) => p.1) := Primrec.fst
  have h_else : Primrec (fun (p : List BitString × BitString) => p.1 ++ [p.2]) :=
    Primrec.list_append.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact Primrec.cond h_mem h_then h_else

private theorem step_cases_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (p : ((BitString × BitString) × ℕ) × (ℕ × List BitString)) =>
      (Option.casesOn (t19_cand c_code p.1.1.1 p.1.1.2 p.2.1) p.2.2 (fun x =>
        append_if_not_mem p.2.2 x) : List BitString)) := by
  have ho : Primrec (fun (p : ((BitString × BitString) × ℕ) × (ℕ × List BitString)) =>
      t19_cand c_code p.1.1.1 p.1.1.2 p.2.1) :=
    (cand_prim c_code).comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
                    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp Primrec.snd))
  have hf : Primrec (fun (p : ((BitString × BitString) × ℕ) × (ℕ × List BitString)) =>
      p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hg : Primrec₂
      (fun (p : ((BitString × BitString) × ℕ) × (ℕ × List BitString)) (x : BitString) =>
        append_if_not_mem p.2.2 x) :=
    (append_if_not_mem_prim.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
  exact Primrec.option_casesOn ho hf hg

private theorem enum_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (q : (BitString × BitString) × ℕ) => t19_enum c_code q.1.1 q.1.2 q.2) := by
  have h_rec := Primrec.nat_rec' Primrec.snd (Primrec.const []) (step_cases_prim c_code).to₂
  exact h_rec.of_eq (fun q => by
    induction q.2 with
    | zero => rfl
    | succ M ih =>
      dsimp [t19_enum]
      rw [← ih]
      cases t19_cand c_code q.1.1 q.1.2 M <;> rfl)

private theorem idx_prim :
    Primrec (fun (q : (BitString × BitString) × ℕ) => t19_idx q.1.1) := by
  have h_exact : Primrec (fun (q : (BitString × BitString) × ℕ) =>
      exactLengthPrograms q.1.1.length) :=
    primrec_exactLengthPrograms.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
  have h_eq : Primrec₂ (fun (q : (BitString × BitString) × ℕ) (r : BitString) =>
      decide (r = q.1.1)) := by
    have h_r : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) => pair.2) :=
      Primrec.snd
    have h_p : Primrec (fun (pair : ((BitString × BitString) × ℕ) × BitString) => pair.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    exact (PrimrecPred.decide (Primrec.eq.comp h_r h_p)).to₂
  exact Primrec.list_findIdx h_exact h_eq

private theorem getElem_prim (c_code : Nat.Partrec.Code) :
    Primrec (fun (q : (BitString × BitString) × ℕ) =>
      (t19_enum c_code q.1.1 q.1.2 q.2)[t19_idx q.1.1]?) :=
  Primrec.list_getElem?.comp (enum_prim c_code) idx_prim

private theorem getElem_computable (c_code : Nat.Partrec.Code) :
    Computable (fun (q : (BitString × BitString) × ℕ) =>
      (t19_enum c_code q.1.1 q.1.2 q.2)[t19_idx q.1.1]?) :=
  (getElem_prim c_code).to_comp

private noncomputable def t19_decompressor (c_code : Nat.Partrec.Code) : Map := fun pr =>
  (Nat.rfind (fun M => Part.some (t19_fn c_code pr.1 pr.2 M).isSome)).bind
    (fun M => Part.ofOption (t19_fn c_code pr.1 pr.2 M))

private theorem rfind_p_partrec (c_code : Nat.Partrec.Code) :
    Partrec (fun (p : (BitString × BitString) × ℕ) =>
      Part.some (t19_fn c_code p.1.1 p.1.2 p.2).isSome) := by
  have h_fn : Computable (fun (p : (BitString × BitString) × ℕ) =>
      (t19_fn c_code p.1.1 p.1.2 p.2).isSome) := by
    dsimp [t19_fn]
    exact Primrec.option_isSome.to_comp.comp (getElem_computable c_code)
  exact Partrec.some.comp h_fn

private theorem rfind_partrec (c_code : Nat.Partrec.Code) :
    Partrec (fun (pr : BitString × BitString) =>
      Nat.rfind (fun M => Part.some (t19_fn c_code pr.1 pr.2 M).isSome)) :=
  Partrec.rfind (rfind_p_partrec c_code).to₂

private theorem ofOpt_partrec (c_code : Nat.Partrec.Code) :
    Partrec (fun (p : (BitString × BitString) × ℕ) =>
      Part.ofOption (t19_fn c_code p.1.1 p.1.2 p.2)) :=
  Computable.ofOption (getElem_computable c_code)

private theorem t19_decompressor_isDecompressor (c_code : Nat.Partrec.Code) :
    isDecompressor (t19_decompressor c_code) :=
  Partrec.bind (rfind_partrec c_code) (ofOpt_partrec c_code).to₂

private lemma enum_mono (c_code : Nat.Partrec.Code) (p y : BitString) (M1 M2 : ℕ)
    (h : M1 ≤ M2) : ∃ rest, t19_enum c_code p y M2 = t19_enum c_code p y M1 ++ rest := by
  induction M2, h using Nat.le_induction with
  | base => refine ⟨[], by simp⟩
  | succ M2 h ih =>
    obtain ⟨rest, ih⟩ := ih
    change ∃ rest_succ, (match t19_cand c_code p y M2 with
      | none => t19_enum c_code p y M2
      | some x => bif decide (x ∈ t19_enum c_code p y M2) then t19_enum c_code p y M2
                  else t19_enum c_code p y M2 ++ [x]) =
      t19_enum c_code p y M1 ++ rest_succ
    rw [ih]
    rcases h_cand : t19_cand c_code p y M2 with _ | x
    · refine ⟨rest, rfl⟩
    · dsimp only
      by_cases h_mem : x ∈ t19_enum c_code p y M1 ++ rest
      · have h_dec : decide (x ∈ t19_enum c_code p y M1 ++ rest) = true :=
          decide_eq_true h_mem
        simp only [h_dec, cond_true]
        refine ⟨rest, rfl⟩
      · have h_dec : decide (x ∈ t19_enum c_code p y M1 ++ rest) = false :=
          decide_eq_false h_mem
        simp only [h_dec, cond_false]
        refine ⟨rest ++ [x], by rw [List.append_assoc]⟩

private lemma enum_nodup (c_code : Nat.Partrec.Code) (p y : BitString) (M : ℕ) :
    (t19_enum c_code p y M).Nodup := by
  induction M with
  | zero =>
    change ([] : List BitString).Nodup
    simp
  | succ M ih =>
    change (match t19_cand c_code p y M with
      | none => t19_enum c_code p y M
      | some x => bif decide (x ∈ t19_enum c_code p y M) then t19_enum c_code p y M
                  else t19_enum c_code p y M ++ [x]).Nodup
    rcases h_cand : t19_cand c_code p y M with _ | x
    · exact ih
    · dsimp only
      by_cases h_mem : x ∈ t19_enum c_code p y M
      · have h_dec : decide (x ∈ t19_enum c_code p y M) = true := decide_eq_true h_mem
        simp only [h_dec, cond_true]
        exact ih
      · have h_dec : decide (x ∈ t19_enum c_code p y M) = false := decide_eq_false h_mem
        simp only [h_dec, cond_false]
        rw [List.nodup_append]
        refine ⟨ih, List.nodup_singleton x, ?_⟩
        rintro z hz1 z2 hz2
        rw [List.mem_singleton] at hz2
        subst hz2
        rintro rfl
        exact h_mem hz1

/-- A candidate `z` produced by `t19_cand` at step `M` satisfies `k z y < |p|`. -/
private lemma t19_cand_sound (k : BitString → BitString → ℕ∞)
    (g : BitString × BitString × ℕ → Part Unit)
    (hg_dom : ∀ (p : BitString × BitString × ℕ), (g p).Dom ↔ k p.1 p.2.1 < (p.2.2 : ℕ∞))
    (c_code : Nat.Partrec.Code)
    (hc_code : c_code.eval = fun n => Part.bind (Part.ofOption (Encodable.decode n))
      (fun p => (g p).map Encodable.encode))
    (p y : BitString) (M : ℕ) (z : BitString) (hz : t19_cand c_code p y M = some z) :
    k z y < (p.length : ℕ∞) := by
  dsimp [t19_cand] at hz
  cases h_dec_z : Encodable.decode (α := BitString) M.unpair.1 with
  | none => rw [h_dec_z] at hz; contradiction
  | some z' =>
    rw [h_dec_z] at hz
    dsimp only at hz
    cases h_ev_z : (Nat.Partrec.Code.evaln M.unpair.2 c_code
      (Encodable.encode (z', y, p.length))).isSome with
    | false =>
      have h_cond_false : (Nat.Partrec.Code.evaln M.unpair.2 c_code
        (Nat.pair (Encodable.encode z')
          (Nat.pair (Encodable.encode y) p.length))).isSome = false := h_ev_z
      rw [h_cond_false] at hz
      contradiction
    | true =>
      have h_cond_true : (Nat.Partrec.Code.evaln M.unpair.2 c_code
        (Nat.pair (Encodable.encode z')
          (Nat.pair (Encodable.encode y) p.length))).isSome = true := h_ev_z
      rw [h_cond_true] at hz
      injection hz with h_eq_z
      subst h_eq_z
      obtain ⟨res, h_res⟩ := Option.isSome_iff_exists.mp h_ev_z
      have h_sound := Nat.Partrec.Code.evaln_sound h_res
      rw [hc_code] at h_sound
      dsimp only [Part.ofOption] at h_sound
      have h_dec_tuple : Encodable.decode (α := BitString × BitString × ℕ)
        (Encodable.encode (z', y, p.length)) = some (z', y, p.length) := Encodable.encodek _
      rw [h_dec_tuple] at h_sound
      dsimp only [Part.ofOption] at h_sound
      rw [Part.bind_some, Part.mem_map_iff] at h_sound
      obtain ⟨u, hu, _⟩ := h_sound
      have h_dom_in : (g (z', y, p.length)).Dom := Part.dom_iff_mem.mpr ⟨u, hu⟩
      exact (hg_dom (z', y, p.length)).mp h_dom_in

/-- Every string in `t19_enum c_code p y M` satisfies `k · y < |p|`. -/
private lemma t19_enum_sound (k : BitString → BitString → ℕ∞)
    (g : BitString × BitString × ℕ → Part Unit)
    (hg_dom : ∀ (p : BitString × BitString × ℕ), (g p).Dom ↔ k p.1 p.2.1 < (p.2.2 : ℕ∞))
    (c_code : Nat.Partrec.Code)
    (hc_code : c_code.eval = fun n => Part.bind (Part.ofOption (Encodable.decode n))
      (fun p => (g p).map Encodable.encode))
    (p y : BitString) (M : ℕ) (z : BitString) (hz : z ∈ t19_enum c_code p y M) :
    k z y < (p.length : ℕ∞) := by
  induction M with
  | zero =>
    change z ∈ ([] : List BitString) at hz
    simp at hz
  | succ M ih =>
    change z ∈ (match t19_cand c_code p y M with
      | none => t19_enum c_code p y M
      | some z' => bif decide (z' ∈ t19_enum c_code p y M) then t19_enum c_code p y M
                  else t19_enum c_code p y M ++ [z']) at hz
    rcases h_cand_M : t19_cand c_code p y M with _ | z'
    · rw [h_cand_M] at hz
      exact ih hz
    · rw [h_cand_M] at hz
      dsimp only at hz
      by_cases h_z_in : z' ∈ t19_enum c_code p y M
      · have h_dec : decide (z' ∈ t19_enum c_code p y M) = true := decide_eq_true h_z_in
        simp only [h_dec, cond_true] at hz
        exact ih hz
      · have h_dec : decide (z' ∈ t19_enum c_code p y M) = false := decide_eq_false h_z_in
        simp only [h_dec, cond_false] at hz
        rw [List.mem_append] at hz
        rcases hz with h1 | h2
        · exact ih h1
        · simp only [List.mem_singleton] at h2
          subst h2
          exact t19_cand_sound k g hg_dom c_code hc_code p y M z h_cand_M

/-- A candidate produced by `t19_cand` at step `M` belongs to `t19_enum` at step `M + 1`. -/
private lemma mem_t19_enum_succ_of_cand (c_code : Nat.Partrec.Code) (p y x : BitString) (M : ℕ)
    (h : t19_cand c_code p y M = some x) : x ∈ t19_enum c_code p y (M + 1) := by
  change x ∈ match t19_cand c_code p y M with
    | none => t19_enum c_code p y M
    | some z => bif decide (z ∈ t19_enum c_code p y M) then t19_enum c_code p y M
                else t19_enum c_code p y M ++ [z]
  rw [h]
  dsimp only
  by_cases h_in : x ∈ t19_enum c_code p y M
  · have h_dec : decide (x ∈ t19_enum c_code p y M) = true := decide_eq_true h_in
    simp only [h_dec, cond_true]
    exact h_in
  · have h_dec : decide (x ∈ t19_enum c_code p y M) = false := decide_eq_false h_in
    simp only [h_dec, cond_false]
    exact List.mem_append_right _ (by simp)

/-- `t19_cand` depends on the program `p` only through its length. -/
private lemma t19_cand_eq_of_length_eq (c_code : Nat.Partrec.Code) (p p' y : BitString) (M : ℕ)
    (h : p.length = p'.length) : t19_cand c_code p y M = t19_cand c_code p' y M := by
  dsimp [t19_cand]
  rw [h]

/-- `t19_enum` depends on the program `p` only through its length. -/
private lemma t19_enum_eq_of_length_eq (c_code : Nat.Partrec.Code) (p p' y : BitString) (M : ℕ)
    (h : p.length = p'.length) : t19_enum c_code p y M = t19_enum c_code p' y M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    change (match t19_cand c_code p y M with
      | none => t19_enum c_code p y M
      | some x => bif decide (x ∈ t19_enum c_code p y M) then t19_enum c_code p y M
                  else t19_enum c_code p y M ++ [x]) = _
    rw [t19_cand_eq_of_length_eq c_code p p' y M h, ih]
    rfl

/-- The complexity levels of `k` are small: for every condition `y` and every bound `n` the set
of strings of `k`-complexity below `n` is finite and has fewer than `2 ^ n` elements. -/
private def SmallComplexityLevels (k : BitString → BitString → ℕ∞) : Prop :=
  (∀ (y : BitString) (n : ℕ), {x : BitString | k x y < (n : ℕ∞)}.Finite) ∧
    ∀ (y : BitString) (n : ℕ), {x : BitString | k x y < (n : ℕ∞)}.ncard < 2 ^ n

/-- If every string enumerated by `t19_enum c_code p y M` has `k · y < n`, the enumeration has
fewer than `2 ^ n` entries, since the strings of `k`-complexity below `n` are fewer than `2 ^ n`. -/
private lemma t19_enum_length_lt (k : BitString → BitString → ℕ∞)
    (hlevels : SmallComplexityLevels k)
    (c_code : Nat.Partrec.Code) (p y : BitString) (M n : ℕ)
    (hsound : ∀ x_in ∈ t19_enum c_code p y M, k x_in y < (n : ℕ∞)) :
    (t19_enum c_code p y M).length < 2 ^ n := by
  obtain ⟨hfin, hcard⟩ := hlevels
  have h_sub : ∀ x_in ∈ t19_enum c_code p y M,
      x_in ∈ {z : BitString | k z y < (n : ℕ∞)} := hsound
  have h_nodup : (t19_enum c_code p y M).Nodup := enum_nodup c_code _ y M
  have h_card_le : (t19_enum c_code p y M).length ≤
      {z : BitString | k z y < (n : ℕ∞)}.ncard := by
    rw [Set.ncard_eq_toFinset_card _ (hfin y n)]
    have h_fin_sub : (t19_enum c_code p y M).toFinset ⊆ (hfin y n).toFinset := by
      intro x_in hx_in
      rw [List.mem_toFinset] at hx_in
      rw [Set.Finite.mem_toFinset]
      exact h_sub x_in hx_in
    have h1 := Finset.card_le_card h_fin_sub
    rw [List.toFinset_card_of_nodup h_nodup] at h1
    exact h1
  have h2 := hcard y n
  omega

/-- If `t19_fn c_code p y M_bound = some x` for some step `M_bound`, then `x` is an output of
`t19_decompressor c_code` on `(p, y)`. -/
private lemma t19_decompressor_mem (c_code : Nat.Partrec.Code) (p y x : BitString) (M_bound : ℕ)
    (h_fn : t19_fn c_code p y M_bound = some x) : x ∈ t19_decompressor c_code (p, y) := by
  have h_rfind_dom : (Nat.rfind (fun M => Part.some (t19_fn c_code p y M).isSome)).Dom := by
    rw [Nat.rfind_dom]
    refine ⟨M_bound, ?_, fun {m} _ => Part.some_dom _⟩
    rw [Part.mem_some_iff, h_fn]
    rfl
  set M_min := (Nat.rfind (fun M => Part.some (t19_fn c_code p y M).isSome)).get h_rfind_dom
  have hM_min_mem : M_min ∈ Nat.rfind (fun M => Part.some (t19_fn c_code p y M).isSome) :=
    Part.get_mem h_rfind_dom
  have hM_min_spec := Nat.mem_rfind.mp hM_min_mem
  have h_isSome : (t19_fn c_code p y M_min).isSome = true := by
    have h1 := hM_min_spec.1
    rw [Part.mem_some_iff] at h1
    exact h1.symm
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp h_isSome
  have hM_min_le : M_min ≤ M_bound := by
    by_contra! h_gt
    have h_lt_spec := hM_min_spec.2 (m := M_bound) h_gt
    rw [Part.mem_some_iff] at h_lt_spec
    rw [h_fn] at h_lt_spec
    contradiction
  have h_eq_x' : x' = x := by
    obtain ⟨rest_enum, h_enum_mono⟩ := enum_mono c_code p y M_min M_bound hM_min_le
    have h_fn_x_copy := h_fn
    have hx'_copy := hx'
    change (t19_enum c_code p y M_bound)[t19_idx p]? = some x at h_fn_x_copy
    change (t19_enum c_code p y M_min)[t19_idx p]? = some x' at hx'_copy
    rw [h_enum_mono] at h_fn_x_copy
    obtain ⟨h_lt_min, _⟩ := List.getElem?_eq_some_iff.mp hx'_copy
    have h_append_get : (t19_enum c_code p y M_min ++ rest_enum)[t19_idx p]? =
        (t19_enum c_code p y M_min)[t19_idx p]? :=
      List.getElem?_append_left h_lt_min
    rw [h_append_get] at h_fn_x_copy
    exact Option.some_injective _ (hx'_copy.symm.trans h_fn_x_copy)
  rw [← h_eq_x']
  change x' ∈ (Nat.rfind (fun M => Part.some (t19_fn c_code p y M).isSome)).bind
    (fun M => Part.ofOption (t19_fn c_code p y M))
  rw [Part.mem_bind_iff]
  refine ⟨M_min, hM_min_mem, ?_⟩
  rw [Part.mem_ofOption, hx']
  rfl

/-- **Theorem 19.** Conditional plain complexity is minimal, up to an additive
constant, among upper-semicomputable functions satisfying the counting bound in
every condition. -/
theorem condK_minimal_upperSemicomputable (U : Map) (hU : isOptimalConditional U)
    (k : BitString → BitString → ℕ∞) (hsemi : IsUpperSemicomputable₂ k)
    (hfin : ∀ (y : BitString) (n : ℕ), {x : BitString | k x y < (n : ℕ∞)}.Finite)
    (hcard : ∀ (y : BitString) (n : ℕ), {x : BitString | k x y < (n : ℕ∞)}.ncard < 2 ^ n) :
    ∃ c : ℕ, ∀ x y : BitString, condK U x y ≤ k x y + (c : ℕ∞) := by
  obtain ⟨g, hg_partrec, hg_dom⟩ := hsemi
  obtain ⟨c_code, hc_code⟩ := Nat.Partrec.Code.exists_code.mp hg_partrec
  have hD_decomp := t19_decompressor_isDecompressor c_code
  obtain ⟨cD, hcD⟩ := hU.2 (t19_decompressor c_code) hD_decomp
  refine ⟨cD + 1, fun x y => ?_⟩
  by_cases hk_top : k x y = ⊤
  · rw [hk_top, top_add]; exact le_top
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k x y = (n : ℕ∞) := by
    cases h : k x y
    · contradiction
    · exact ⟨_, rfl⟩
  rw [hn]
  have h_lt_n1 : k x y < ((n + 1 : ℕ) : ℕ∞) := by rw [hn]; exact_mod_cast Nat.lt_succ_self n
  have h_dom : (g (x, y, n + 1)).Dom := (hg_dom (x, y, n + 1)).mpr h_lt_n1
  have h_mem : (0 : ℕ) ∈ (g (x, y, n + 1)).map Encodable.encode := by
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp h_dom
    rw [Part.mem_map_iff]
    exact ⟨u, hu, rfl⟩
  have h_eval : (0 : ℕ) ∈ c_code.eval (Encodable.encode (x, y, n + 1)) := by
    rw [hc_code]
    dsimp only
    rw [Encodable.encodek]
    dsimp only [Part.ofOption]
    rw [Part.bind_some]
    exact h_mem
  obtain ⟨s0, hs0⟩ := Nat.Partrec.Code.evaln_complete.mp h_eval
  set x_nat := Encodable.encode x
  set M0 := Nat.pair x_nat s0
  have h_unpair1 : M0.unpair.1 = x_nat := by dsimp [M0]; rw [Nat.unpair_pair]
  have h_unpair2 : M0.unpair.2 = s0 := by dsimp [M0]; rw [Nat.unpair_pair]
  have h0_lt : 0 < (exactLengthPrograms (n + 1)).length := by
    rw [length_exactLengthPrograms (n + 1)]; positivity
  have h_cand_M0 : t19_cand c_code ((exactLengthPrograms (n + 1))[0]'h0_lt) y M0 = some x := by
    dsimp [t19_cand]
    rw [h_unpair1, h_unpair2]
    have h_dec : (Encodable.decode x_nat : Option BitString) = some x := Encodable.encodek x
    rw [h_dec]
    dsimp only
    have h0_get : (exactLengthPrograms (n + 1))[0]'h0_lt ∈ exactLengthPrograms (n + 1) :=
      List.getElem_mem h0_lt
    have h0_len : ((exactLengthPrograms (n + 1))[0]'h0_lt).length = n + 1 :=
      exactLengthPrograms_length_eq (n + 1) _ h0_get
    rw [h0_len]
    have ht_evaln :
        (Nat.Partrec.Code.evaln s0 c_code (Encodable.encode (x, y, n + 1))).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨0, hs0⟩
    change (bif (Nat.Partrec.Code.evaln s0 c_code
        (Encodable.encode (x, y, n + 1))).isSome then some x else none) = some x
    rw [ht_evaln]
    rfl
  set h0_str := (exactLengthPrograms (n + 1))[0]'h0_lt
  have h_x_in_enum : x ∈ t19_enum c_code h0_str y (M0 + 1) :=
    mem_t19_enum_succ_of_cand c_code h0_str y x M0 h_cand_M0
  have hc_eval : ∀ (x_in : BitString) (M : ℕ), x_in ∈ t19_enum c_code h0_str y M →
      k x_in y < (n + 1 : ℕ∞) := by
    intro x_in M h_in
    have h_len : h0_str.length = n + 1 :=
      exactLengthPrograms_length_eq (n + 1) _ (List.getElem_mem h0_lt)
    have h_bound := t19_enum_sound k g hg_dom c_code hc_code h0_str y M x_in h_in
    rwa [h_len] at h_bound
  have h0_len : h0_str.length = n + 1 :=
    exactLengthPrograms_length_eq (n + 1) _ (List.getElem_mem h0_lt)
  have h_len_lt := t19_enum_length_lt k ⟨hfin, hcard⟩ c_code h0_str y (M0 + 1) (n + 1)
    (hc_eval · (M0 + 1))
  have h_idx_lt : (t19_enum c_code h0_str y (M0 + 1)).findIdx (fun z => decide (z = x)) <
      (t19_enum c_code h0_str y (M0 + 1)).length := by
    rw [List.findIdx_lt_length]
    refine ⟨x, h_x_in_enum, ?_⟩
    simp
  have h_idx_bound : (t19_enum c_code h0_str y (M0 + 1)).findIdx (fun z => decide (z = x)) <
      2 ^ (n + 1) := lt_trans h_idx_lt h_len_lt
  have h_exact_lt : (t19_enum c_code h0_str y (M0 + 1)).findIdx (fun z => decide (z = x)) <
      (exactLengthPrograms (n + 1)).length := by rw [length_exactLengthPrograms]; exact h_idx_bound
  set idx_val := (t19_enum c_code h0_str y (M0 + 1)).findIdx (fun z => decide (z = x))
  have h_get_p : (exactLengthPrograms (n + 1))[idx_val]'h_exact_lt ∈
      exactLengthPrograms (n + 1) := List.getElem_mem h_exact_lt
  have h_p_len : ((exactLengthPrograms (n + 1))[idx_val]'h_exact_lt).length =
      n + 1 := exactLengthPrograms_length_eq (n + 1) _ h_get_p
  set p := (exactLengthPrograms (n + 1))[idx_val]'h_exact_lt
  have hp_len_eq : p.length = n + 1 := h_p_len
  have h_idx_p : t19_idx p = idx_val := by
    dsimp [t19_idx, p, idx_val]
    rw [hp_len_eq]
    have h_nodup_exact : (exactLengthPrograms (n + 1)).Nodup := exactLengthPrograms_nodup (n + 1)
    exact nodup_findIdx_getElem h_nodup_exact _ h_exact_lt
  have h_enum_eq : ∀ M, t19_enum c_code p y M = t19_enum c_code h0_str y M := fun M =>
    t19_enum_eq_of_length_eq c_code p h0_str y M (by rw [hp_len_eq, h0_len])
  have h_get_x : (t19_enum c_code p y (M0 + 1))[t19_idx p]? = some x := by
    rw [h_idx_p, h_enum_eq]
    have h_get_elem := List.findIdx_getElem (w := h_idx_lt)
      (p := fun z => decide (z = x)) (xs := t19_enum c_code h0_str y (M0 + 1))
    simp only [decide_eq_true_iff] at h_get_elem
    rw [List.getElem?_eq_getElem h_idx_lt, h_get_elem]
  have h_fn_x : t19_fn c_code p y (M0 + 1) = some x := h_get_x
  have h_dec_prod : x ∈ t19_decompressor c_code (p, y) :=
    t19_decompressor_mem c_code p y x (M0 + 1) h_fn_x
  have h_condK_D : condK (t19_decompressor c_code) x y ≤ (p.length : ℕ∞) := by
    rw [condK_le_iff]
    refine ⟨p, rfl.le, ?_⟩
    exact h_dec_prod
  have h_bound : condK (t19_decompressor c_code) x y ≤ ((n + 1 : ℕ) : ℕ∞) := by
    have h_copy := h_condK_D
    rwa [hp_len_eq] at h_copy
  have h1 := hcD x y
  have h2 : condK (t19_decompressor c_code) x y + (cD : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) + (cD : ℕ∞) := by
    gcongr
  have h3 : ((n + 1 : ℕ) : ℕ∞) + (cD : ℕ∞) = (n : ℕ∞) + ((cD + 1 : ℕ) : ℕ∞) := by
    norm_cast
    omega
  exact h1.trans (h2.trans_eq h3)

/-! ### Theorem 20: the conditional pair bound -/

/-- **Theorem 20.** `C(x, y) ≤ C(x) + 2 log C(x) + C(y | x) + O(1)`. -/
theorem plainK_pair_le_add_two_log_add_condK (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ x y : BitString,
      cPair U x y ≤ plainK U x + condK U y x + ((2 * Nat.log 2 (cVal U x) + k : ℕ) : ℕ∞) := by
  let splitLength : BitString → Nat := fun q => decodeBits (decodeFirst q)
  let joinedProg : BitString → BitString := fun q => decodeSecond q
  let firstProg : BitString → BitString := fun q => (joinedProg q).take (splitLength q)
  let secondProg : BitString → BitString := fun q => (joinedProg q).drop (splitLength q)
  let D : Map := fun pr =>
    (U (firstProg pr.1, [])).bind fun x =>
      (U (secondProg pr.1, x)).map fun y => pairCode x y
  have hSplitLength : Computable splitLength := decodeBits_computable.comp decodeFirst_computable
  have hJoinedProg : Computable joinedProg := decodeSecond_computable
  have hFirstProg : Computable firstProg := Primrec.list_take.to_comp.comp hJoinedProg hSplitLength
  have hSecondProg : Computable secondProg :=
    Primrec.list_drop.to_comp.comp hJoinedProg hSplitLength
  have hD : isDecompressor D := by
    have h1 : Partrec (fun pr : BitString × BitString => U (firstProg pr.1, [])) :=
      Partrec.comp hU.1 ((hFirstProg.comp Computable.fst).pair (Computable.const []))
    have h2 : Partrec (fun q : (BitString × BitString) × BitString =>
        U (secondProg q.1.1, q.2)) :=
      Partrec.comp hU.1
        ((hSecondProg.comp (Computable.fst.comp Computable.fst)).pair
          Computable.snd)
    have hPair : Computable
        (fun q : ((BitString × BitString) × BitString) × BitString =>
          pairCode q.1.2 q.2) :=
      (show Computable₂ (fun a b : BitString => pairCode a b) from
          pairCode_computable).comp
        (Computable.snd.comp Computable.fst) Computable.snd
    exact Partrec.bind h1 (Partrec.map h2 hPair)
  obtain ⟨cD, hcD⟩ := hU.2 D hD
  refine ⟨cD + 3, fun x y => ?_⟩
  by_cases hx : plainK U x = ⊤
  · rw [hx]
    simp
  by_cases hy : condK U y x = ⊤
  · rw [hy]
    simp
  have hx_fin : plainK U x ≠ ⊤ := hx
  have hy_fin : condK U y x ≠ ⊤ := hy
  set kx := cVal U x with hkx
  set kyx := (condK U y x).toNat with hkyx
  have hkx_eq : plainK U x = (kx : ℕ∞) := by rw [hkx]; exact (ENat.coe_toNat hx_fin).symm
  have hkyx_eq : condK U y x = (kyx : ℕ∞) := by rw [hkyx]; exact (ENat.coe_toNat hy_fin).symm
  have hkx_le : plainK U x ≤ (kx : ℕ∞) := hkx_eq.le
  have hy_le : condK U y x ≤ (kyx : ℕ∞) := hkyx_eq.le
  have hp_ex := (condK_le_iff U x [] kx).mp hkx_le
  rcases hp_ex with ⟨p, hpLen, hpProd⟩
  have hq_ex := (condK_le_iff U y x kyx).mp hy_le
  rcases hq_ex with ⟨q, hqLen, hqProd⟩
  dsimp [programLength] at hpLen hqLen
  set prog : BitString := pairCode (Nat.bits p.length) (p ++ q) with hProg
  have hFirstEval : firstProg prog = p := by
    dsimp [firstProg, joinedProg, splitLength]
    rw [hProg, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.take_left]
  have hSecondEval : secondProg prog = q := by
    dsimp [secondProg, joinedProg, splitLength]
    rw [hProg, decodeFirst_pairCode, decodeSecond_pairCode, decodeBits_natBits, List.drop_left]
  have hDProd : produces D prog [] (pairCode x y) := by
    change pairCode x y ∈ (U (firstProg prog, [])).bind fun x' =>
      (U (secondProg prog, x')).map fun y' => pairCode x' y'
    rw [hFirstEval, hSecondEval]
    exact Part.mem_bind_iff.mpr ⟨x, hpProd, Part.mem_map _ hqProd⟩
  have hProgMem : (prog.length : ℕ∞) ∈ candidateLengths D (pairCode x y) [] := ⟨prog, hDProd, rfl⟩
  have h1 : condK D (pairCode x y) [] ≤ (prog.length : ℕ∞) := sInf_le hProgMem
  have h2 : condK U (pairCode x y) [] ≤ condK D (pairCode x y) [] + (cD : ℕ∞) :=
    hcD (pairCode x y) []
  have hDBound : cPair U x y ≤ (prog.length : ℕ∞) + (cD : ℕ∞) := by
    calc cPair U x y ≤ condK D (pairCode x y) [] + (cD : ℕ∞) := h2
    _ ≤ (prog.length : ℕ∞) + (cD : ℕ∞) := by gcongr
  have hProgLength : prog.length = 2 * (Nat.bits p.length).length + 1 + p.length + q.length := by
    rw [hProg, length_pairCode, List.length_append]
    omega
  have hBits : (Nat.bits p.length).length ≤ Nat.log 2 kx + 1 := by
    have h1 : p.length ≤ kx := hpLen
    have h2 : (Nat.bits p.length).length ≤ (Nat.bits kx).length := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size h1
    have h3 : (Nat.bits kx).length ≤ Nat.log 2 kx + 1 := by
      rw [Nat.size_eq_bits_len]
      by_cases hkx0 : kx = 0
      · simp [hkx0]
      · have hlog : kx < 2 ^ (Nat.log 2 kx + 1) := Nat.lt_pow_succ_log_self (by decide) kx
        exact Nat.size_le.mpr hlog
    exact h2.trans h3
  have hProgLenLe : prog.length + cD ≤ kx + kyx + 2 * Nat.log 2 kx + (cD + 3) := by
    rw [hProgLength]
    omega
  calc cPair U x y ≤ (prog.length : ℕ∞) + (cD : ℕ∞) := hDBound
  _ = ((prog.length + cD : ℕ) : ℕ∞) := by push_cast; rfl
  _ ≤ ((kx + kyx + 2 * Nat.log 2 kx + (cD + 3) : ℕ) : ℕ∞) := by exact_mod_cast hProgLenLe
  _ = plainK U x + condK U y x + ((2 * Nat.log 2 (cVal U x) + (cD + 3) : ℕ) : ℕ∞) := by
    rw [hkx_eq, hkyx_eq, hkx]
    push_cast
    ring

/-! ### Exercises 16–24: bounds for pairs and triples -/

/-- Splits a program into three fields: two self-delimiting length prefixes tell where the
first and the second of the three subprograms end. -/
def decodeTriple (p : BitString) : BitString × BitString × BitString :=
  ((decodeSecond (decodeSecond p)).take (bitsToNat (decodeFirst p)),
   ((decodeSecond (decodeSecond p)).drop (bitsToNat (decodeFirst p))).take
     (bitsToNat (decodeFirst (decodeSecond p))),
   ((decodeSecond (decodeSecond p)).drop (bitsToNat (decodeFirst p))).drop
     (bitsToNat (decodeFirst (decodeSecond p))))

/-- Third stage of the triple decompressor: runs `U` on the third subprogram and returns the
code of the triple of the three outputs. -/
def tripleStep3 (U : Map) (q : ((BitString × BitString) × BitString) × BitString) :
    Part BitString :=
  (U ((decodeTriple q.1.1.1).2.2, [])).map (fun z => listCode [q.1.2, q.2, z])

/-- Second stage of the triple decompressor: runs `U` on the second subprogram and continues
with the third stage. -/
def tripleStep2 (U : Map) (q : (BitString × BitString) × BitString) : Part BitString :=
  (U ((decodeTriple q.1.1).2.1, [])).bind (fun y => tripleStep3 U (q, y))

/-- Decompressor for triples: the program consists of three subprograms for `x`, `y` and `z`,
laid out self-delimitingly, and the output is the code of `[x, y, z]`. -/
def tripleDecompressor (U : Map) (pw : BitString × BitString) : Part BitString :=
  (U ((decodeTriple pw.1).1, [])).bind (fun x => tripleStep2 U (pw, x))

/-- Splitting a program into its three fields is primitive recursive. -/
theorem decodeTriple_primrec : Primrec decodeTriple := by
  have hkx : Primrec (fun p : BitString => bitsToNat (decodeFirst p)) :=
    bitsToNat_primrec.comp CodedFiniteDistribution.decodeFirst_primrec
  have hr1 : Primrec (fun p : BitString => decodeSecond p) :=
    CodedFiniteDistribution.decodeSecond_primrec
  have hky : Primrec (fun p : BitString => bitsToNat (decodeFirst (decodeSecond p))) :=
    bitsToNat_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp hr1)
  have hrest : Primrec (fun p : BitString => decodeSecond (decodeSecond p)) :=
    CodedFiniteDistribution.decodeSecond_primrec.comp hr1
  have hpx : Primrec (fun p : BitString =>
      (decodeSecond (decodeSecond p)).take (bitsToNat (decodeFirst p))) :=
    Primrec.list_take.comp hrest hkx
  have hrest2 : Primrec (fun p : BitString =>
      (decodeSecond (decodeSecond p)).drop (bitsToNat (decodeFirst p))) :=
    Primrec.list_drop.comp hrest hkx
  have hpy : Primrec (fun p : BitString =>
      ((decodeSecond (decodeSecond p)).drop (bitsToNat (decodeFirst p))).take
        (bitsToNat (decodeFirst (decodeSecond p)))) :=
    Primrec.list_take.comp hrest2 hky
  have hpz : Primrec (fun p : BitString =>
      ((decodeSecond (decodeSecond p)).drop (bitsToNat (decodeFirst p))).drop
        (bitsToNat (decodeFirst (decodeSecond p)))) :=
    Primrec.list_drop.comp hrest2 hky
  exact hpx.pair (hpy.pair hpz)

attribute [irreducible] decodeTriple

/-- The first of the three outputs accumulated by the triple decompressor. -/
def tripleSel1 (q : (((BitString × BitString) × BitString) × BitString) × BitString) : BitString :=
  q.1.1.2

/-- The second of the three outputs accumulated by the triple decompressor. -/
def tripleSel2 (q : (((BitString × BitString) × BitString) × BitString) × BitString) : BitString :=
  q.1.2

/-- The third of the three outputs accumulated by the triple decompressor. -/
def tripleSel3 (q : (((BitString × BitString) × BitString) × BitString) × BitString) : BitString :=
  q.2

/-- The first accumulated output is a computable function of the state. -/
theorem tripleSel1_comp : Computable tripleSel1 :=
  Computable.snd.comp (Computable.fst.comp Computable.fst)

/-- The second accumulated output is a computable function of the state. -/
theorem tripleSel2_comp : Computable tripleSel2 :=
  Computable.snd.comp Computable.fst

/-- The third accumulated output is a computable function of the state. -/
theorem tripleSel3_comp : Computable tripleSel3 :=
  Computable.snd

/-- The list of the three accumulated outputs, which the triple decompressor encodes. -/
def tripleList (q : (((BitString × BitString) × BitString) × BitString) × BitString) :
    List BitString :=
  [tripleSel1 q, tripleSel2 q, tripleSel3 q]

/-- Forming the list of the three accumulated outputs is computable. -/
theorem tripleList_comp : Computable tripleList := by
  have hnil : Computable (fun _ : (((BitString × BitString) × BitString) × BitString) × BitString =>
      ([] : List BitString)) := Computable.const []
  have hc3 : Computable (fun q => [tripleSel3 q]) :=
    (show Computable₂ (fun (a : BitString) (b : List BitString) => a :: b) from
      Computable.list_cons).comp tripleSel3_comp hnil
  have hc2 : Computable (fun q => [tripleSel2 q, tripleSel3 q]) :=
    (show Computable₂ (fun (a : BitString) (b : List BitString) => a :: b) from
      Computable.list_cons).comp tripleSel2_comp hc3
  exact (show Computable₂ (fun (a : BitString) (b : List BitString) => a :: b) from
    Computable.list_cons).comp tripleSel1_comp hc2

/-- The argument on which the triple decompressor calls `U` first: the first subprogram with an
empty condition. -/
def tripleProj1 (pw : BitString × BitString) : BitString × BitString :=
  ((decodeTriple pw.1).1, [])

/-- The argument of the second call of `U`: the second subprogram with an empty condition. -/
def tripleProj2 (q : (BitString × BitString) × BitString) : BitString × BitString :=
  ((decodeTriple q.1.1).2.1, [])

/-- The argument of the third call of `U`: the third subprogram with an empty condition. -/
def tripleProj3 (q : ((BitString × BitString) × BitString) × BitString) : BitString × BitString :=
  ((decodeTriple q.1.1.1).2.2, [])

/-- The argument of the first call of `U` is computable in the program. -/
theorem tripleProj1_comp : Computable tripleProj1 :=
  (Computable.fst.comp (decodeTriple_primrec.to_comp.comp Computable.fst)).pair
    (Computable.const [])

/-- The argument of the second call of `U` is computable in the state. -/
theorem tripleProj2_comp : Computable tripleProj2 :=
  (Computable.fst.comp (Computable.snd.comp (decodeTriple_primrec.to_comp.comp
    (Computable.fst.comp Computable.fst)))).pair (Computable.const [])

/-- The argument of the third call of `U` is computable in the state. -/
theorem tripleProj3_comp : Computable tripleProj3 :=
  (Computable.snd.comp (Computable.snd.comp (decodeTriple_primrec.to_comp.comp
    (Computable.fst.comp (Computable.fst.comp Computable.fst))))).pair (Computable.const [])

/-- The triple decompressor is a decompressor whenever `U` is partial computable. -/
lemma tripleDecompressor_isDecompressor (U : Map) (hU : Partrec U) :
    isDecompressor (tripleDecompressor U) := by
  have hU1 : Partrec (fun pw : BitString × BitString => U (tripleProj1 pw)) :=
    Partrec.comp hU tripleProj1_comp
  have hU2 : Partrec (fun q : (BitString × BitString) × BitString => U (tripleProj2 q)) :=
    Partrec.comp hU tripleProj2_comp
  have hU3 : Partrec (fun q : ((BitString × BitString) × BitString) × BitString =>
      U (tripleProj3 q)) := Partrec.comp hU tripleProj3_comp
  have hlistCode : Computable (fun q : (((BitString × BitString) × BitString) × BitString) ×
      BitString => listCode (tripleList q)) :=
    listCode_computable.comp tripleList_comp
  have hStep3 : Partrec (fun q : ((BitString × BitString) × BitString) × BitString =>
      tripleStep3 U q) := Partrec.map hU3 hlistCode.to₂
  have hStep2 : Partrec (fun q : (BitString × BitString) × BitString =>
      tripleStep2 U q) := Partrec.bind hU2 hStep3.to₂
  have hStep1 : Partrec (fun pw : BitString × BitString =>
      tripleDecompressor U pw) := Partrec.bind hU1 hStep2.to₂
  exact hStep1

/-- **Exercise 16.** `C(x, y, z) ≤ C(x) + C(y) + C(z) + O(log n)` for strings of
length at most `n`. -/
theorem plainK_triple_le_add_log (U : Map) (hU : isOptimalConditional U) :
    ∃ k : ℕ, ∀ (n : ℕ) (x y z : BitString), x.length ≤ n → y.length ≤ n → z.length ≤ n →
      cTriple U x y z ≤ plainK U x + plainK U y + plainK U z + ((logSlack k n : ℕ) : ℕ∞) := by
  obtain ⟨cD, hcD⟩ := hU.2 (tripleDecompressor U) (tripleDecompressor_isDecompressor U hU.1)
  obtain ⟨cLen, hcLen⟩ := plainK_le_length U hU
  set Crem := 4 * (Nat.bits cLen).length + 6 + cD
  use 4 + Crem
  intro n x y z hx hy hz
  unfold cTriple
  by_cases hxTop : plainK U x = ⊤
  · rw [hxTop, top_add, top_add, top_add]
    exact le_top
  by_cases hyTop : plainK U y = ⊤
  · rw [hyTop, add_top, top_add, top_add]
    exact le_top
  by_cases hzTop : plainK U z = ⊤
  · rw [hzTop, add_top, top_add]
    exact le_top
  obtain ⟨px, hpx_prod, hpx_len⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := x) (y := []) hxTop
  obtain ⟨py, hpy_prod, hpy_len⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := y) (y := []) hyTop
  obtain ⟨pz, hpz_prod, hpz_len⟩ :=
    exists_program_of_KP_ne_top (M := U) (x := z) (y := []) hzTop
  set kx := px.length
  set ky := py.length
  set p := pairCode (Nat.bits kx) (pairCode (Nat.bits ky) (px ++ py ++ pz))
  have hp_dec1 : (decodeTriple p).1 = px := by
    unfold decodeTriple
    dsimp [p, kx, ky]
    rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode, decodeSecond_pairCode,
        List.append_assoc, List.take_left]
  have hp_dec2 : (decodeTriple p).2.1 = py := by
    unfold decodeTriple
    dsimp [p, kx, ky]
    rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode, decodeFirst_pairCode,
        bitsToNat_bits, decodeSecond_pairCode, List.append_assoc, List.drop_left, List.take_left]
  have hp_dec3 : (decodeTriple p).2.2 = pz := by
    unfold decodeTriple
    dsimp [p, kx, ky]
    rw [decodeFirst_pairCode, bitsToNat_bits, decodeSecond_pairCode, decodeFirst_pairCode,
        bitsToNat_bits, decodeSecond_pairCode, List.append_assoc, List.drop_left, List.drop_left]
  have hD_prod : listCode [x, y, z] ∈ tripleDecompressor U (p, []) := by
    dsimp [tripleDecompressor, tripleStep2, tripleStep3, tripleProj1, tripleProj2, tripleProj3,
           tripleList, tripleSel1, tripleSel2, tripleSel3]
    rw [hp_dec1, hp_dec2, hp_dec3]
    exact Part.mem_bind_iff.mpr ⟨x, hpx_prod, Part.mem_bind_iff.mpr
      ⟨y, hpy_prod, Part.mem_map (fun z => listCode [x, y, z]) hpz_prod⟩⟩
  have h_condK : condK (tripleDecompressor U) (listCode [x, y, z]) [] ≤ (p.length : ℕ∞) :=
    sInf_le ⟨p, hD_prod, rfl⟩
  have h_bound : plainK U (listCode [x, y, z]) ≤ (p.length : ℕ∞) + (cD : ℕ∞) := calc
    plainK U (listCode [x, y, z])
      ≤ condK (tripleDecompressor U) (listCode [x, y, z]) [] + (cD : ℕ∞) :=
      hcD (listCode [x, y, z]) []
    _ ≤ (p.length : ℕ∞) + (cD : ℕ∞) := by gcongr
  have hp_len : p.length = 2 * (Nat.bits kx).length + 2 * (Nat.bits ky).length + 2 +
      px.length + py.length + pz.length := by
    simp [p, length_pairCode]
    omega
  have hkx_le : kx ≤ n + cLen := by
    have h1 : (kx : ℕ∞) ≤ (n : ℕ∞) + (cLen : ℕ∞) := calc
      (kx : ℕ∞) = (px.length : ℕ∞) := rfl
      _ = plainK U x := hpx_len
      _ ≤ (x.length : ℕ∞) + (cLen : ℕ∞) := hcLen x
      _ ≤ (n : ℕ∞) + (cLen : ℕ∞) := by gcongr
    exact_mod_cast h1
  have hky_le : ky ≤ n + cLen := by
    have h1 : (ky : ℕ∞) ≤ (n : ℕ∞) + (cLen : ℕ∞) := calc
      (ky : ℕ∞) = (py.length : ℕ∞) := rfl
      _ = plainK U y := hpy_len
      _ ≤ (y.length : ℕ∞) + (cLen : ℕ∞) := hcLen y
      _ ≤ (n : ℕ∞) + (cLen : ℕ∞) := by gcongr
    exact_mod_cast h1
  have hkx_bits : (Nat.bits kx).length ≤ (Nat.bits n).length + (Nat.bits cLen).length + 1 :=
    (length_natBits_mono hkx_le).trans (length_natBits_add_le n cLen)
  have hky_bits : (Nat.bits ky).length ≤ (Nat.bits n).length + (Nat.bits cLen).length + 1 :=
    (length_natBits_mono hky_le).trans (length_natBits_add_le n cLen)
  have h_slack : 4 * (Nat.bits n).length + Crem ≤ logSlack (4 + Crem) n := by
    unfold logSlack
    set X := Crem * (Nat.bits n).length
    have hX : 0 ≤ X := Nat.zero_le _
    calc 4 * (Nat.bits n).length + Crem
        ≤ 4 * (Nat.bits n).length + X + 4 + Crem := by omega
      _ = (4 + Crem) * (Nat.bits n).length + (4 + Crem) := by ring
  have h_plen_bound : p.length + cD ≤
      px.length + py.length + pz.length + logSlack (4 + Crem) n := by
    dsimp [Crem] at h_slack ⊢
    omega
  calc plainK U (listCode [x, y, z])
      ≤ (p.length : ℕ∞) + (cD : ℕ∞) := h_bound
    _ = ((p.length + cD : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((px.length + py.length + pz.length + logSlack (4 + Crem) n : ℕ) : ℕ∞) := by
      exact_mod_cast h_plen_bound
    _ = (px.length : ℕ∞) + (py.length : ℕ∞) + (pz.length : ℕ∞) +
        ((logSlack (4 + Crem) n : ℕ) : ℕ∞) := by push_cast; ring
    _ = plainK U x + plainK U y + plainK U z +
        ((logSlack (4 + Crem) n : ℕ) : ℕ∞) := by
      rw [hpx_len, hpy_len, hpz_len]
      rfl

end Kolmogorov
