import KolmogorovMathlib.InformationLogic.NonTupleLemmas.ProbabilisticLemma
import KolmogorovMathlib.InformationLogic.NonTupleLemmas.QuadrupleConstruction

/-!
# Quadruple Gap

The complexity gap for quadruples of strings with almost equal complexity profiles
(Section 13.6 of Shen, Uspensky and Vereshchagin, *Kolmogorov complexity and algorithmic
randomness*).

For a triple `(a, b, e)` of `n`-bit words with `C(a, b, e) ≥ 3n − 1`, the xor quadruple
`(a, b, e, a ⊕ b ⊕ e)` has complexity profile `(n, 2n, 3n, 3n)` up to `O(log n)`.  Combining
this with the probabilistic construction of a quadruple with a large problem complexity, we get
two sequences of quadruples whose profiles differ by `O(log n)` but whose problem complexities
differ by at least `δn`.

## Main declarations

* `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: the profile of the xor quadruple
  of an incompressible triple.
* `exists_quadruples_profileClose_problemK_quad_gap`: Theorem 247, the gap between the
  problem complexities of two quadruple sequences with close profiles.
-/

namespace Kolmogorov
namespace InformationLogic
open ProblemCalculus

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: decode a
list code, append the xor of its first three entries and reorder the result along `idx`. -/
private def exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx
    (idx : List ℕ) (u : BitString) : BitString :=
  listCode (idx.map (fun i => (decodeListCode u ++
    [xorStr (xorStr ((decodeListCode u).getD 0 []) ((decodeListCode u).getD 1 []))
      ((decodeListCode u).getD 2 [])]).getD i []))

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: the
reordering map is computable, so it raises complexity by at most a constant. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le
    (D : Map) (hD : isOptimalConditional D) (idx : List ℕ) :
    ∃ c : ℕ, ∀ u : BitString,
      plainK D (exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx idx u) ≤
        plainK D u + (c : ℕ∞) := by
  have hL : Primrec decodeListCode := decodeListCode_primrec
  have hg : ∀ j : ℕ, Primrec (fun u : BitString => (decodeListCode u).getD j []) := fun j =>
    (Primrec.list_getD ([] : BitString)).comp hL (Primrec.const j)
  have hx : Primrec (fun u : BitString => xorStr (xorStr ((decodeListCode u).getD 0 [])
      ((decodeListCode u).getD 1 [])) ((decodeListCode u).getD 2 [])) :=
    xorStr_primrec.comp (xorStr_primrec.comp (hg 0) (hg 1)) (hg 2)
  have hF : Primrec (fun u : BitString => decodeListCode u ++
      [xorStr (xorStr ((decodeListCode u).getD 0 []) ((decodeListCode u).getD 1 []))
        ((decodeListCode u).getD 2 [])]) :=
    Primrec.list_concat.comp hL hx
  have hM : Primrec (fun u : BitString => idx.map (fun i => (decodeListCode u ++
      [xorStr (xorStr ((decodeListCode u).getD 0 []) ((decodeListCode u).getD 1 []))
        ((decodeListCode u).getD 2 [])]).getD i [])) :=
    Primrec.list_map (Primrec.const idx)
      ((Primrec.list_getD ([] : BitString)).comp (hF.comp Primrec.fst) Primrec.snd).to₂
  exact plainK_map_le D hD _ (listCode_primrec.comp hM).to_comp

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: appending
one string `w` to a list costs at most `|w| + O(log |w|)` bits of complexity. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_append
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (L : List BitString) (w : BitString),
      plainK D (listCode (L ++ [w])) ≤
        plainK D (listCode L) + ((w.length + logSlack k w.length : ℕ) : ℕ∞) := by
  let f : BitString → BitString := fun p =>
    listCode (decodeListCode (decodeSecond p) ++ [decodeFirst p])
  have hf : Computable f :=
    listCode_computable.comp (Computable.list_concat.comp
      (decodeListCode_computable.comp decodeSecond_computable) decodeFirst_computable)
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD f hf
  obtain ⟨k0, hk0⟩ := plainK_pair_le_add_two_log D hD
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  obtain ⟨C, hC⟩ := logSlack_linear_bound 2 1 c2
  refine ⟨C + (c1 + k0 + c2), fun L w => ?_⟩
  have hfw : f (pairCode w (listCode L)) = listCode (L ++ [w]) := by
    simp [f, decodeFirst_pairCode, decodeSecond_pairCode, decodeListCode_listCode]
  have hw : plainK D w ≤ ((w.length + c2 : ℕ) : ℕ∞) := by
    have := hc2 w; push_cast; exact this
  have hne : plainK D w ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hw
  have hcv : cVal D w ≤ w.length + c2 := by
    have h1 : plainK D w = (cVal D w : ℕ∞) := by
      unfold cVal; rw [ENat.natCast_toNat hne]
    rw [h1] at hw; exact_mod_cast hw
  have hlog : 2 * Nat.log 2 (cVal D w) ≤ logSlack C w.length := by
    have h1 : Nat.log 2 (cVal D w) ≤ (Nat.bits (1 * w.length + c2)).length := by
      rcases Nat.eq_zero_or_pos (cVal D w) with h0 | hpos
      · rw [h0]; simp
      · have h2 : 2 ^ Nat.log 2 (cVal D w) ≤ 1 * w.length + c2 := by
          have := Nat.pow_log_le_self 2 hpos.ne'
          omega
        have h3 : Nat.log 2 (cVal D w) < Nat.size (1 * w.length + c2) := Nat.lt_size.mpr h2
        rw [← Nat.size_eq_bits_len] at h3
        omega
    have h4 := hC w.length
    unfold logSlack at h4 ⊢
    omega
  have hnat : w.length + c2 + (logSlack C w.length + k0) + c1 ≤
      w.length + logSlack (C + (c1 + k0 + c2)) w.length := by
    have e1 := logSlack_add_constants C (c1 + k0 + c2) w.length
    have e2 : c1 + k0 + c2 ≤ logSlack (c1 + k0 + c2) w.length := by unfold logSlack; omega
    omega
  have hE : ((2 * Nat.log 2 (cVal D w) + k0 : ℕ) : ℕ∞) ≤
      ((logSlack C w.length + k0 : ℕ) : ℕ∞) := by
    exact_mod_cast (by omega : 2 * Nat.log 2 (cVal D w) + k0 ≤ logSlack C w.length + k0)
  calc plainK D (listCode (L ++ [w])) = plainK D (f (pairCode w (listCode L))) := by rw [hfw]
    _ ≤ plainK D (pairCode w (listCode L)) + (c1 : ℕ∞) := hc1 _
    _ ≤ (plainK D w + plainK D (listCode L) + ((2 * Nat.log 2 (cVal D w) + k0 : ℕ) : ℕ∞)) +
          (c1 : ℕ∞) := by gcongr; exact hk0 w (listCode L)
    _ ≤ (((w.length + c2 : ℕ) : ℕ∞) + plainK D (listCode L) +
          ((logSlack C w.length + k0 : ℕ) : ℕ∞)) + (c1 : ℕ∞) := by gcongr
    _ = plainK D (listCode L) +
          ((w.length + c2 + (logSlack C w.length + k0) + c1 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ plainK D (listCode L) +
          ((w.length + logSlack (C + (c1 + k0 + c2)) w.length : ℕ) : ℕ∞) := by
        gcongr

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: appending
a list `M` of `n`-bit strings costs at most `|M| (n + O(log n))` bits of complexity. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_appendList
    (D : Map) (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (L M : List BitString), (∀ x ∈ M, x.length = n) →
      plainK D (listCode (L ++ M)) ≤
        plainK D (listCode L) + ((M.length * (n + logSlack k n) : ℕ) : ℕ∞) := by
  obtain ⟨k, hk⟩ := exists_quadruples_profileClose_problemK_quad_gap_profile_v_append D hD
  refine ⟨k, fun n L M hM => ?_⟩
  induction M using List.reverseRecOn with
  | nil => simp
  | append_singleton M w ih =>
    have hM' : ∀ x ∈ M, x.length = n := fun x hx => hM x (List.mem_append_left _ hx)
    have hw : w.length = n := hM w (by simp)
    calc plainK D (listCode (L ++ (M ++ [w]))) = plainK D (listCode ((L ++ M) ++ [w])) := by
          rw [List.append_assoc]
      _ ≤ plainK D (listCode (L ++ M)) + ((w.length + logSlack k w.length : ℕ) : ℕ∞) := hk _ _
      _ ≤ (plainK D (listCode L) + ((M.length * (n + logSlack k n) : ℕ) : ℕ∞)) +
            ((n + logSlack k n : ℕ) : ℕ∞) := by
          rw [hw]; gcongr; exact ih hM'
      _ = plainK D (listCode L) + (((M ++ [w]).length * (n + logSlack k n) : ℕ) : ℕ∞) := by
          rw [List.length_append, List.length_singleton]; push_cast; ring

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: the
arithmetic of one case. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_arith
    (X : ℕ∞) (n s ls LS c1 c2 : ℕ) (hs : s ≤ 3) (hK : 3 * ls + c1 + c2 + 1 ≤ LS)
    (hup : X ≤ ((c1 + s * (n + ls) : ℕ) : ℕ∞))
    (hlow : ((3 * n - 1 : ℕ) : ℕ∞) ≤ X + (((3 - s) * (n + ls) + c2 : ℕ) : ℕ∞)) :
    X ≤ ((s * n : ℕ) : ℕ∞) + (LS : ℕ∞) ∧ ((s * n : ℕ) : ℕ∞) ≤ X + (LS : ℕ∞) := by
  induction X using ENat.recTopCoe with
  | top => exact absurd (lt_of_lt_of_le (ENat.natCast_lt_top _) hup) (lt_irrefl _)
  | coe x =>
    have hup' : x ≤ c1 + s * (n + ls) := by exact_mod_cast hup
    have hlow' : 3 * n - 1 ≤ x + ((3 - s) * (n + ls) + c2) := by exact_mod_cast hlow
    constructor
    · have : x ≤ s * n + LS := by interval_cases s <;> omega
      exact_mod_cast this
    · have : s * n ≤ x + LS := by interval_cases s <;> omega
      exact_mod_cast this

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: one case
of at most three strings `L`, completed by the strings `M` to a triple from which `abe` is
recovered by `reidx idx`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch
    (D : Map) (k c0 cR LS n : ℕ) (L M : List BitString) (idx : List ℕ) (abe : BitString)
    (happ : ∀ (L M : List BitString), (∀ x ∈ M, x.length = n) →
      plainK D (listCode (L ++ M)) ≤
        plainK D (listCode L) + ((M.length * (n + logSlack k n) : ℕ) : ℕ∞))
    (hc0 : plainK D (listCode []) ≤ (c0 : ℕ∞))
    (hR : ∀ u, plainK D
      (exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx idx u) ≤
        plainK D u + (cR : ℕ∞))
    (hL : ∀ x ∈ L, x.length = n) (hM : ∀ x ∈ M, x.length = n)
    (hLM : L.length + M.length = 3)
    (heq : exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx idx
      (listCode (L ++ M)) = abe)
    (hrand : ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D abe)
    (hK : 3 * logSlack k n + c0 + cR + 1 ≤ LS) :
    plainK D (listCode L) ≤ ((L.length * n : ℕ) : ℕ∞) + (LS : ℕ∞) ∧
      ((L.length * n : ℕ) : ℕ∞) ≤ plainK D (listCode L) + (LS : ℕ∞) := by
  have hup : plainK D (listCode L) ≤ ((c0 + L.length * (n + logSlack k n) : ℕ) : ℕ∞) := by
    have h := happ [] L hL
    simp only [List.nil_append] at h
    calc plainK D (listCode L) ≤
          plainK D (listCode []) + ((L.length * (n + logSlack k n) : ℕ) : ℕ∞) := h
      _ ≤ (c0 : ℕ∞) + ((L.length * (n + logSlack k n) : ℕ) : ℕ∞) := by gcongr
      _ = _ := by push_cast; ring
  have hlow : ((3 * n - 1 : ℕ) : ℕ∞) ≤
      plainK D (listCode L) + (((3 - L.length) * (n + logSlack k n) + cR : ℕ) : ℕ∞) := by
    have hMl : M.length = 3 - L.length := by omega
    calc ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D abe := hrand
      _ = plainK D (exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx idx
            (listCode (L ++ M))) := by rw [heq]
      _ ≤ plainK D (listCode (L ++ M)) + (cR : ℕ∞) := hR _
      _ ≤ (plainK D (listCode L) + ((M.length * (n + logSlack k n) : ℕ) : ℕ∞)) + (cR : ℕ∞) :=
          by gcongr; exact happ L M hM
      _ = _ := by rw [hMl]; push_cast; ring
  exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_arith _ n L.length
    (logSlack k n) LS c0 cR (by omega) hK hup hlow

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: a
bitwise criterion for `(x ⊕ y) ⊕ z = w`. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq
    (n : ℕ) (x y z w : BitString) (hx : x.length = n) (hw : w.length = n)
    (h : ∀ i < n,
      w.getD i false = xor (xor (x.getD i false) (y.getD i false)) (z.getD i false)) :
    xorStr (xorStr x y) z = w := by
  refine List.ext_getElem (by simp [hx, hw]) (fun i h1 h2 => ?_)
  have hi : i < n := by rw [← hw]; exact h2
  have hix : i < x.length := by omega
  have hixy : i < (xorStr x y).length := by simp; omega
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2,
    getD_xorStr _ _ _ hixy, getD_xorStr _ _ _ hix, h i hi]

/-- Auxiliary for `exists_quadruples_profileClose_problemK_quad_gap_profile_v`: the
reordering map on a list code. -/
private lemma exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode
    (idx : List ℕ) (l : List BitString) :
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx idx (listCode l) =
      listCode (idx.map (fun i => (l ++ [xorStr (xorStr (l.getD 0 []) (l.getD 1 []))
        (l.getD 2 [])]).getD i [])) := by
  simp only [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx,
    decodeListCode_listCode]

/-- Step 3 of the proof of `exists_quadruples_profileClose_problemK_quad_gap`:
the complexity profile of the xor quadruple `ū = (a, b, e, a ⊕ b ⊕ e)` for `n`-bit words with
`C(a, b, e) ≥ 3n − 1` is also `(n, 2n, 3n, 3n)`: every sub-tuple `S` has complexity
`min(|S|, 3) · n` up to `O(log n)`, with `k` independent of `n, a, b, e`.
Book's proof: upper bounds from lengths and from `d` being computable from `a, b, e`; lower
bounds from `C(a, b, e) ≥ 3n − 1` and symmetry of information: any three of `a, b, e, d`
determine the fourth, and the remaining strings of a sub-tuple `S` of at most `3` elements
are determined, up to `O(1)`, by `3 − |S|` words of length `n`, so
`C(S) ≥ C(a, b, e) − (3 − |S|) n − O(log n)`. -/
theorem exists_quadruples_profileClose_problemK_quad_gap_profile_v (D : Map)
    (hD : isOptimalConditional D) :
    ∃ k : ℕ, ∀ (n : ℕ) (a b e : BitString), a.length = n → b.length = n → e.length = n →
      ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e]) →
      ∀ S : Finset (Fin 4), S.Nonempty →
        plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) ≤
            ((min S.card 3 * n : ℕ) : ℕ∞) + (logSlack k n : ℕ∞) ∧
          ((min S.card 3 * n : ℕ) : ℕ∞) ≤
            plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) +
              (logSlack k n : ℕ∞) := by
  obtain ⟨k, happ⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_appendList D hD
  obtain ⟨c0, hc0⟩ := plainK_le_length D hD
  have hc0' : plainK D (listCode []) ≤ (c0 : ℕ∞) := by simpa using hc0 (listCode [])
  obtain ⟨r1, hr1⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 1, 2]
  obtain ⟨r2, hr2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [1, 0, 2]
  obtain ⟨r3, hr3⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [1, 2, 0]
  obtain ⟨r4, hr4⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [1, 2, 3]
  obtain ⟨r5, hr5⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 2, 1]
  obtain ⟨r6, hr6⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 2, 3]
  obtain ⟨r7, hr7⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [2, 0, 1]
  obtain ⟨r8, hr8⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [2, 0, 3]
  obtain ⟨r9, hr9⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [2, 3, 0]
  obtain ⟨r10, hr10⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 1, 3]
  obtain ⟨r11, hr11⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 3, 1]
  obtain ⟨r12, hr12⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [3, 0, 1]
  obtain ⟨r13, hr13⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_le D hD [0, 1, 2, 3]
  refine ⟨3 * k + (c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1),
    fun n a b e ha hb he hrand S hS => ?_⟩
  have hK : 3 * logSlack k n +
      (c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1) ≤
      logSlack (3 * k +
        (c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1)) n := by
    rw [logSlack_add_constants]
    have h1 : logSlack (3 * k) n = 3 * logSlack k n := by unfold logSlack; ring
    have h2 : c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1 ≤
        logSlack
          (c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1) n := by
      unfold logSlack; omega
    omega
  generalize logSlack (3 * k +
    (c0 + (r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13) + 1)) n = LS
    at hK ⊢
  have hd : (xorStr (xorStr a b) e).length = n := by simp [ha]
  have hdbit : ∀ i < n, (xorStr (xorStr a b) e).getD i false =
      xor (xor (a.getD i false) (b.getD i false)) (e.getD i false) := by
    intro i hi
    rw [getD_xorStr _ _ _ (by simp; omega), getD_xorStr _ _ _ (by omega)]
  generalize hdd : xorStr (xorStr a b) e = d at hd hdbit ⊢
  have x4 : xorStr (xorStr d a) b = e :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n d a b e hd he
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x7 : xorStr (xorStr a d) b = e :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n a d b e ha he
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x9 : xorStr (xorStr b d) a = e :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n b d a e hb he
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x10 : xorStr (xorStr e d) a = b :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n e d a b he hb
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x12 : xorStr (xorStr a b) d = e :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n a b d e ha he
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x13 : xorStr (xorStr a e) d = b :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n a e d b ha hb
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have x14 : xorStr (xorStr b e) d = a :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_v_xor_eq n b e d a hb ha
      (fun i hi => by
        rw [hdbit i hi]
        cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> rfl)
  have happn := happ n
  by_cases h0 : (0 : Fin 4) ∈ S <;> by_cases h1 : (1 : Fin 4) ∈ S <;>
    by_cases h2 : (2 : Fin 4) ∈ S <;> by_cases h3 : (3 : Fin 4) ∈ S
  · -- `S = {0, 1, 2, 3}`
    obtain rfl : S = {0, 1, 2, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    change plainK D (listCode [a, b, e, d]) ≤ ((3 * n : ℕ) : ℕ∞) + (LS : ℕ∞) ∧
      ((3 * n : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e, d]) + (LS : ℕ∞)
    have hup : plainK D (listCode [a, b, e, d]) ≤
        (((c0 + r13) + 3 * (n + logSlack k n) : ℕ) : ℕ∞) := by
      have e1 : listCode [a, b, e, d] =
          exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx [0, 1, 2, 3]
            (listCode [a, b, e]) := by
        rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
        simp [hdd]
      have h1 := happn [] [a, b, e] (by simp [ha, hb, he])
      simp only [List.nil_append] at h1
      calc plainK D (listCode [a, b, e, d])
          = plainK D (exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx
              [0, 1, 2, 3] (listCode [a, b, e])) := by rw [← e1]
        _ ≤ plainK D (listCode [a, b, e]) + (r13 : ℕ∞) := hr13 _
        _ ≤ (plainK D (listCode []) + (([a, b, e].length * (n + logSlack k n) : ℕ) : ℕ∞)) +
              (r13 : ℕ∞) := by gcongr
        _ ≤ ((c0 : ℕ∞) + (([a, b, e].length * (n + logSlack k n) : ℕ) : ℕ∞)) + (r13 : ℕ∞) := by
              gcongr
        _ = _ := by simp only [List.length_cons, List.length_nil]; push_cast; ring
    have hlow : ((3 * n - 1 : ℕ) : ℕ∞) ≤
        plainK D (listCode [a, b, e, d]) + (((3 - 3) * (n + logSlack k n) + r1 : ℕ) : ℕ∞) := by
      have e2 : exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx [0, 1, 2]
          (listCode [a, b, e, d]) = listCode [a, b, e] := by
        rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
        simp
      calc ((3 * n - 1 : ℕ) : ℕ∞) ≤ plainK D (listCode [a, b, e]) := hrand
        _ = plainK D (exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx
              [0, 1, 2] (listCode [a, b, e, d])) := by rw [e2]
        _ ≤ plainK D (listCode [a, b, e, d]) + (r1 : ℕ∞) := hr1 _
        _ = _ := by simp
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_arith _ n 3
      (logSlack k n) LS (c0 + r13) r1 (by norm_num) (by omega) hup hlow
  · -- `S = {0, 1, 2}`
    obtain rfl : S = {0, 1, 2} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r1 LS n
      [a, b, e] [] [0, 1, 2] (listCode [a, b, e]) happn hc0' hr1 (by simp [ha, hb, he])
      (by simp) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {0, 1, 3}`
    obtain rfl : S = {0, 1, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r10 LS n
      [a, b, d] [] [0, 1, 3] (listCode [a, b, e]) happn hc0' hr10 (by simp [ha, hb, hd])
      (by simp) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x12])
      hrand (by omega)
  · -- `S = {0, 1}`
    obtain rfl : S = {0, 1} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r1 LS n
      [a, b] [e] [0, 1, 2] (listCode [a, b, e]) happn hc0' hr1 (by simp [ha, hb])
      (by simp [he]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {0, 2, 3}`
    obtain rfl : S = {0, 2, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r11 LS n
      [a, e, d] [] [0, 3, 1] (listCode [a, b, e]) happn hc0' hr11 (by simp [ha, he, hd])
      (by simp) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x13])
      hrand (by omega)
  · -- `S = {0, 2}`
    obtain rfl : S = {0, 2} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r5 LS n
      [a, e] [b] [0, 2, 1] (listCode [a, b, e]) happn hc0' hr5 (by simp [ha, he])
      (by simp [hb]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {0, 3}`
    obtain rfl : S = {0, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r6 LS n
      [a, d] [b] [0, 2, 3] (listCode [a, b, e]) happn hc0' hr6 (by simp [ha, hd])
      (by simp [hb]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x7])
      hrand (by omega)
  · -- `S = {0}`
    obtain rfl : S = {0} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r1 LS n
      [a] [b, e] [0, 1, 2] (listCode [a, b, e]) happn hc0' hr1 (by simp [ha])
      (by simp [hb, he]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {1, 2, 3}`
    obtain rfl : S = {1, 2, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r12 LS n
      [b, e, d] [] [3, 0, 1] (listCode [a, b, e]) happn hc0' hr12 (by simp [hb, he, hd])
      (by simp) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x14])
      hrand (by omega)
  · -- `S = {1, 2}`
    obtain rfl : S = {1, 2} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r7 LS n
      [b, e] [a] [2, 0, 1] (listCode [a, b, e]) happn hc0' hr7 (by simp [hb, he])
      (by simp [ha]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {1, 3}`
    obtain rfl : S = {1, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r8 LS n
      [b, d] [a] [2, 0, 3] (listCode [a, b, e]) happn hc0' hr8 (by simp [hb, hd])
      (by simp [ha]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x9])
      hrand (by omega)
  · -- `S = {1}`
    obtain rfl : S = {1} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r2 LS n
      [b] [a, e] [1, 0, 2] (listCode [a, b, e]) happn hc0' hr2 (by simp [hb])
      (by simp [ha, he]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {2, 3}`
    obtain rfl : S = {2, 3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r9 LS n
      [e, d] [a] [2, 3, 0] (listCode [a, b, e]) happn hc0' hr9 (by simp [he, hd])
      (by simp [ha]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x10])
      hrand (by omega)
  · -- `S = {2}`
    obtain rfl : S = {2} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r3 LS n
      [e] [a, b] [1, 2, 0] (listCode [a, b, e]) happn hc0' hr3 (by simp [he])
      (by simp [ha, hb]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp)
      hrand (by omega)
  · -- `S = {3}`
    obtain rfl : S = {3} := by ext i; fin_cases i <;> simp [h0, h1, h2, h3]
    exact exists_quadruples_profileClose_problemK_quad_gap_profile_v_branch D k c0 r4 LS n
      [d] [a, b] [1, 2, 3] (listCode [a, b, e]) happn hc0' hr4 (by simp [hd])
      (by simp [ha, hb]) rfl
      (by rw [exists_quadruples_profileClose_problemK_quad_gap_profile_v_reidx_listCode]
          simp [x4])
      hrand (by omega)
  · -- `S = ∅`, excluded by `hS`
    exfalso
    obtain ⟨i, hi⟩ := hS
    fin_cases i
    · exact h0 hi
    · exact h1 hi
    · exact h2 hi
    · exact h3 hi

/-- Step 4 of the proof of `exists_quadruples_profileClose_problemK_quad_gap`:
the xor quadruple `ū = (a, b, e, a ⊕ b ⊕ e)` of `n`-bit words has a cheap solution:
`C((a → e) ∧ (b → d)) ≤ n + O(1)`, the constant independent of `n, a, b, e`.
Book's proof: put `w = a ⊕ e` (an `n`-bit word); `x ↦ x ⊕ w` maps `a` to `e` and `b` to
`b ⊕ a ⊕ e = d`; let `α` be the Gödel translation `t(w)` of the partial computable language
`V (s, x) = x ⊕ s`, so `[α](x) = x ⊕ w`; the pair `[α, α]` is a solution computable from `w`
(`C(w) ≤ n + O(1)`), hence of complexity `≤ n + O(1)`. -/
private theorem exists_quadruples_profileClose_problemK_quad_gap_step4_upper (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ c : ℕ, ∀ (n : ℕ) (a b e : BitString), a.length = n → b.length = n → e.length = n →
      problemK D (quadProblem P ![a, b, e, xorStr (xorStr a b) e]) ≤ (n : ℕ∞) + (c : ℕ∞) := by
  obtain ⟨hpair, -, -, -, -, -, hG⟩ := hP
  let V : Map := fun sx => Part.some (xorStr sx.2 sx.1)
  have hV : Partrec V :=
    Computable.partrec (xorStr_primrec.to_comp.comp Computable.snd Computable.fst)
  obtain ⟨t, ht, hts⟩ := hG V hV
  let f : BitString → BitString := fun w => P.pair (t w) (t w)
  have hf : Computable f := hpair.comp ht ht
  obtain ⟨c1, hc1⟩ := plainK_map_le D hD f hf
  obtain ⟨c2, hc2⟩ := plainK_le_length D hD
  refine ⟨c1 + c2, fun n a b e ha hb he => ?_⟩
  set w := xorStr a e with hw
  have hwlen : w.length = n := by rw [hw, length_xorStr, ha]
  have hxor : xorStr b w = xorStr (xorStr a b) e := by
    refine List.ext_getElem (by simp [ha, hb]) (fun i h1 h2 => ?_)
    have hi : i < b.length := by simpa using h1
    have hia : i < a.length := by omega
    have hie : i < e.length := by omega
    have hiw : i < w.length := by omega
    have hiab : i < (xorStr a b).length := by simp; omega
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2,
      getD_xorStr _ _ _ hi, hw, getD_xorStr _ _ _ hia,
      getD_xorStr _ _ _ hiab, getD_xorStr _ _ _ hia]
    cases a.getD i false <;> cases b.getD i false <;> cases e.getD i false <;> simp
  have h1 : t w ∈ P.imp {a} {e} := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨e, Set.mem_singleton _, ?_⟩
    rw [hts]
    change e ∈ Part.some (xorStr x w)
    rw [hw, xorStr_xorStr_left x e (by rw [ha, he])]
    exact Part.mem_some _
  have h2 : t w ∈ P.imp {b} {xorStr (xorStr a b) e} := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨xorStr (xorStr a b) e, Set.mem_singleton _, ?_⟩
    rw [hts]
    change _ ∈ Part.some (xorStr x w)
    rw [hx, hxor]
    exact Part.mem_some _
  have hz : f w ∈ quadProblem P ![a, b, e, xorStr (xorStr a b) e] :=
    Set.mem_image2_of_mem h1 h2
  calc problemK D (quadProblem P ![a, b, e, xorStr (xorStr a b) e])
      ≤ plainK D (f w) := problemK_le_of_mem D hz
    _ ≤ plainK D w + (c1 : ℕ∞) := hc1 w
    _ ≤ ((w.length : ℕ∞) + c2) + (c1 : ℕ∞) := by
        gcongr
        exact hc2 w
    _ = (n : ℕ∞) + ((c1 + c2 : ℕ) : ℕ∞) := by
        rw [hwlen]; push_cast; ring

/-- SUV Theorem 247 (Section 13.6, printed p. 418).  For some `δ > 0` there are two sequences
of quadruples `ũₙ = (ãₙ, b̃ₙ, c̃ₙ, d̃ₙ)` and `ūₙ = (āₙ, b̄ₙ, c̄ₙ, d̄ₙ)` of strings of lengths `O(n)`
such that `C((ãₙ → c̃ₙ) ∧ (b̃ₙ → d̃ₙ))` exceeds `C((āₙ → c̄ₙ) ∧ (b̄ₙ → d̄ₙ))` by at least `δn`,
while the complexities of the strings, all their pairs, triples and the quadruples differ by
`O(log n)`.  We write `δ = 1/m` (`m * C(ū) + n ≤ m * C(ũ)` in `ℕ∞`) and require the gap for
`n ≥ N` only (equivalent: redefine the sequences below `N`).
Book's proofs.  Geometric: in the affine 3-space over the field with `2ⁿ` elements, `ã`, `b̃` a
random pair of intersecting lines, `c̃` their common point, `d̃` their plane; the incidence lemma
`incidence_pairs_card_sq_le` (at most `O(2^{5.5n})` pairs of lines served by a pair of
functions) gives `C(ũ) ≥ 1.5n`, while `ā = uvws`, `b̄ = pqrs`, `c̄ = ups`, `d̄ = vqs` (seven
random `n`-bit pieces) has the same profile and `C(ū) ≈ n` (use `p ⊕ v`).
Probabilistic: a function `Q` of complexity `log n + O(1)` found by exhaustive search (Chernoff
bound; `exists_computable_family_problemK_quad_ge`), `(ã, b̃, c̃)` a triple of complexity
`≥ 3n − 1` among the more than half of good triples, `d̃ = Q(ã, b̃, c̃)`, so
`C(ũ) ≥ 2n − O(log n)`; the profile (`n`, `2n`, `3n`, `3n`) follows from the three bounds of
the lemma and the upper bounds of Problem 342 by symmetry of information.  Against it
`(ā, b̄, c̄)` a random `3n`-bit string cut in three, `d̄ = ā ⊕ b̄ ⊕ c̄`, `C(ū) ≤ n + O(1)` (use
`ā ⊕ c̄`). -/
theorem exists_quadruples_profileClose_problemK_quad_gap (D : Map)
    (hD : isOptimalConditional D) (P : ProblemCalculus) (hP : P.Admissible) :
    ∃ (m c N : ℕ) (u v : ℕ → Fin 4 → BitString), 0 < m ∧
      (∀ n i, (u n i).length ≤ c * (n + 1) ∧ (v n i).length ≤ c * (n + 1)) ∧
      (∀ n, TupleProfileClose D (logSlack c n) (u n) (v n)) ∧
      ∀ n ≥ N, (m : ℕ∞) * problemK D (quadProblem P (v n)) + (n : ℕ∞) ≤
        (m : ℕ∞) * problemK D (quadProblem P (u n)) := by
  obtain ⟨Q, cQ, N, hQ, hN⟩ := exists_computable_family_problemK_quad_ge D hD P hP
  obtain ⟨k2, h2⟩ :=
    exists_quadruples_profileClose_problemK_quad_gap_profile_u D hD P hP Q hQ cQ
  obtain ⟨k3, h3⟩ := exists_quadruples_profileClose_problemK_quad_gap_profile_v D hD
  obtain ⟨c4, h4⟩ := exists_quadruples_profileClose_problemK_quad_gap_step4_upper D hD P hP
  obtain ⟨N', hN'⟩ := exists_bits_linear_domination 1 (2 * cQ) (2 * c4 + 2 * cQ)
  have key : ∀ n : ℕ, ∃ uv : (Fin 4 → BitString) × (Fin 4 → BitString),
      (∀ i, (uv.1 i).length ≤ (k2 + k3 + 1) * (n + 1) ∧
        (uv.2 i).length ≤ (k2 + k3 + 1) * (n + 1)) ∧
      TupleProfileClose D (logSlack (k2 + k3 + 1) n) uv.1 uv.2 ∧
      (max N N' ≤ n → (2 : ℕ∞) * problemK D (quadProblem P uv.2) + (n : ℕ∞) ≤
        (2 : ℕ∞) * problemK D (quadProblem P uv.1)) := by
    intro n
    by_cases hn : max N N' ≤ n
    · have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
      obtain ⟨hlen, hcard⟩ := hN n hnN
      obtain ⟨⟨a, b, e⟩, ht, hrand⟩ :=
        exists_quadruples_profileClose_problemK_quad_gap_count D n
          {t : BitString × BitString × BitString |
            t.1.length = n ∧ t.2.1.length = n ∧ t.2.2.length = n ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.1, t.2.1, t.2.2,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞) ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.2, t.1, t.2.1,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞) ∧
            ((2 * n : ℕ) : ℕ∞) ≤ problemK D (quadProblem P ![t.2.1, t.2.2, t.1,
              Q n t.1 t.2.1 t.2.2]) + (logSlack cQ n : ℕ∞)}
          (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩) hcard
      obtain ⟨ha, hb, he, hl1, hl2, hl3⟩ := ht
      have hQlen := hlen a b e ha hb he
      have hxlen : (xorStr (xorStr a b) e).length = n := by simp [ha]
      have hs : (logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞) ≤
          (logSlack (k2 + k3 + 1) n : ℕ∞) := by
        have h1 := logSlack_add_constants k2 k3 n
        have h2 := logSlack_mono_left (c := k2 + k3) (c' := k2 + k3 + 1) (by omega) n
        exact_mod_cast (by omega : logSlack k2 n + logSlack k3 n ≤ logSlack (k2 + k3 + 1) n)
      refine ⟨(![a, b, e, Q n a b e], ![a, b, e, xorStr (xorStr a b) e]), ?_, ?_, ?_⟩
      · intro i
        have hnc : n ≤ (k2 + k3 + 1) * (n + 1) := by nlinarith
        fin_cases i <;> simp [ha, hb, he, hQlen, hxlen, hnc]
      · intro S hS
        obtain ⟨u1, u2⟩ := h2 n a b e ha hb he hQlen hrand hl1 hl2 hl3 S hS
        obtain ⟨v1, v2⟩ := h3 n a b e ha hb he hrand S hS
        constructor
        · calc _ ≤ _ := u1
            _ ≤ (plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) +
                (logSlack k3 n : ℕ∞)) + (logSlack k2 n : ℕ∞) := by gcongr
            _ = plainK D (subtupleCode ![a, b, e, xorStr (xorStr a b) e] S) +
                ((logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞)) := by ring
            _ ≤ _ := by gcongr
        · calc _ ≤ _ := v1
            _ ≤ (plainK D (subtupleCode ![a, b, e, Q n a b e] S) +
                (logSlack k2 n : ℕ∞)) + (logSlack k3 n : ℕ∞) := by gcongr
            _ = plainK D (subtupleCode ![a, b, e, Q n a b e] S) +
                ((logSlack k2 n : ℕ∞) + (logSlack k3 n : ℕ∞)) := by ring
            _ ≤ _ := by gcongr
      · intro _
        have hup := h4 n a b e ha hb he
        generalize problemK D (quadProblem P ![a, b, e, xorStr (xorStr a b) e]) = Kv at *
        generalize problemK D (quadProblem P ![a, b, e, Q n a b e]) = Ku at *
        have hdom := hN' n hnN'
        induction Ku using ENat.recTopCoe with
        | top => simp
        | coe x =>
          induction Kv using ENat.recTopCoe with
          | top => exact absurd hup (by simp)
          | coe y =>
            have hup' : y ≤ n + c4 := by exact_mod_cast hup
            have hl1' : 2 * n ≤ x + logSlack cQ n := by exact_mod_cast hl1
            unfold logSlack at hl1' hdom
            have hmul : 2 * cQ * (Nat.bits n).length = 2 * (cQ * (Nat.bits n).length) := by ring
            have : (2 : ℕ∞) * (y : ℕ∞) + (n : ℕ∞) ≤ (2 : ℕ∞) * (x : ℕ∞) := by
              exact_mod_cast (by omega : 2 * y + n ≤ 2 * x)
            exact this
    · refine ⟨(fun _ => [], fun _ => []), ?_, ?_, fun h => absurd h hn⟩
      · intro i; simp
      · intro S _
        exact ⟨le_self_add, le_self_add⟩
  choose uv huv using key
  exact ⟨2, k2 + k3 + 1, max N N', fun n => (uv n).1, fun n => (uv n).2, by norm_num,
    fun n => (huv n).1, fun n => (huv n).2.1, fun n hn => (huv n).2.2 hn⟩

end InformationLogic
end Kolmogorov
