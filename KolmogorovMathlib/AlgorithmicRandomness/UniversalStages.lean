import KolmogorovMathlib.AlgorithmicRandomness.StageComputable
import Mathlib.Computability.PartrecCode
import KolmogorovMathlib.Foundation.PrimrecExtras

/-!
# A universal family of monotone dyadic stage tables

Every lower semicomputable function on Cantor space is the monotone limit of a
computable family of dyadic basic functions (Theorem 40).  Such a family is a
table `A : ℕ → BitString → ℕ`, and the tables in question are exactly the total
computable ones — a class that cannot be enumerated directly.

`patchTable e s x` simulates the `e`-th partial recursive function for `s`
steps and *patches* the result into a table which is monotone by construction:
`2 * patchTable e s x ≤ patchTable e (s + 1) x`.  The patched family is
computable in `(e, s, x)`, is dominated by any monotone table that `e` codes,
and its supremum recovers the corresponding function.
-/

namespace Kolmogorov

open MeasureTheory ENNReal Nat.Partrec

/-- The value computed by the code `e` on the input `(j, x)` within `b` steps;
`0` if the computation has not converged in time. -/
def rawTable (e b j : ℕ) (x : BitString) : ℕ :=
  (Code.evaln b (Denumerable.ofNat Code e) (Nat.pair j (Encodable.encode x))).getD 0

/-- The raw table entries increase with the bound on the search. -/
lemma rawTable_mono {e b b' j : ℕ} (x : BitString) (h : b ≤ b') :
    rawTable e b j x ≤ rawTable e b' j x := by
  unfold rawTable
  cases hb : Code.evaln b (Denumerable.ofNat Code e) (Nat.pair j (Encodable.encode x)) with
  | none => simp
  | some v =>
      have hmem : v ∈ Code.evaln b' (Denumerable.ofNat Code e)
          (Nat.pair j (Encodable.encode x)) := Code.evaln_mono h (by rw [hb]; rfl)
      have hb' : Code.evaln b' (Denumerable.ofNat Code e)
          (Nat.pair j (Encodable.encode x)) = some v := hmem
      rw [hb']

/-- The patched loop: after `j` steps it has produced a value which is at least
twice the value after `j - 1` steps. -/
def patchLoop (e b : ℕ) (x : BitString) : ℕ → ℕ
  | 0 => rawTable e b 0 []
  | j + 1 => max (2 * patchLoop e b x j) (rawTable e b (j + 1) (x.take (j + 1)))

/-- The patching loop is the recursion on the stage that starts from the raw table at stage
zero. -/
lemma patchLoop_eq_natRec (e b : ℕ) (x : BitString) (s : ℕ) :
    patchLoop e b x s = Nat.rec (motive := fun _ => ℕ) (rawTable e b 0 [])
      (fun j IH => max (2 * IH) (rawTable e b (j + 1) (x.take (j + 1)))) s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [patchLoop, ih]

/-- The `e`-th patched stage table at stage `s`. -/
def patchTable (e s : ℕ) (x : BitString) : ℕ := patchLoop e s x s

/-- The patched table entries increase with the bound on the search. -/
lemma patchLoop_mono_bound {e b b' : ℕ} (x : BitString) (h : b ≤ b') :
    ∀ j, patchLoop e b x j ≤ patchLoop e b' x j := by
  intro j
  induction j with
  | zero => exact rawTable_mono _ h
  | succ j ih =>
      exact max_le_max (Nat.mul_le_mul_left 2 ih) (rawTable_mono _ h)

/-- The patched table at stage `j` reads at most the first `j` bits of its string argument. -/
lemma patchLoop_take {e b : ℕ} (x : BitString) {m : ℕ} :
    ∀ j, j ≤ m → patchLoop e b (x.take m) j = patchLoop e b x j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hjm : j ≤ m := Nat.le_of_succ_le hj
      have htake : (x.take m).take (j + 1) = x.take (j + 1) := by
        rw [List.take_take]
        congr 1
        omega
      rw [patchLoop, patchLoop, ih hjm, htake]

/-- The patched table at stage `s` reads at most the first `s` bits of its string argument. -/
lemma patchTable_take (e s : ℕ) (x : BitString) {m : ℕ} (h : s ≤ m) :
    patchTable e s (x.take m) = patchTable e s x :=
  patchLoop_take x s h

/-- The patched table at least doubles from one stage to the next, so the dyadic values it
denotes are non-decreasing. -/
lemma two_mul_patchTable_le (e s : ℕ) (x : BitString) :
    2 * patchTable e s x ≤ patchTable e (s + 1) x := by
  have h1 : patchLoop e s x s ≤ patchLoop e (s + 1) x s :=
    patchLoop_mono_bound x (Nat.le_succ s) s
  have h2 : 2 * patchLoop e (s + 1) x s ≤ patchLoop e (s + 1) x (s + 1) := by
    rw [patchLoop]
    exact le_max_left _ _
  calc 2 * patchTable e s x = 2 * patchLoop e s x s := rfl
    _ ≤ 2 * patchLoop e (s + 1) x s := Nat.mul_le_mul_left 2 h1
    _ ≤ patchLoop e (s + 1) x (s + 1) := h2

/-- The patched table dominates the raw table entry of the same stage. -/
lemma patchLoop_ge_step {e b : ℕ} (x : BitString) (j : ℕ) :
    rawTable e b j (x.take j) ≤ patchLoop e b x j := by
  cases j with
  | zero => simp [patchLoop, List.take_zero]
  | succ j => exact le_max_right _ _

/-- Advancing the stage by `k` multiplies the patched table by at least `2^k`. -/
lemma patchLoop_growth {e b : ℕ} (x : BitString) {j : ℕ} :
    ∀ k, 2 ^ k * patchLoop e b x j ≤ patchLoop e b x (j + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : 2 * patchLoop e b x (j + k) ≤ patchLoop e b x (j + k + 1) := by
        rw [patchLoop]
        exact le_max_left _ _
      calc 2 ^ (k + 1) * patchLoop e b x j = 2 * (2 ^ k * patchLoop e b x j) := by ring
        _ ≤ 2 * patchLoop e b x (j + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ patchLoop e b x (j + k + 1) := hstep
        _ = patchLoop e b x (j + (k + 1)) := by rw [Nat.add_assoc]

/-! ## Codes -/

/-- Every computable table is coded: the simulated values are either `0`
(divergence within the step bound) or the true values, and every single value is
eventually produced. -/
lemma exists_code_rawTable {A : ℕ → BitString → ℕ} (hA : Computable₂ A) :
    ∃ e : ℕ, (∀ b j x, rawTable e b j x = 0 ∨ rawTable e b j x = A j x) ∧
      (∀ j x, ∃ b, rawTable e b j x = A j x) := by
  classical
  set G : ℕ → ℕ := fun n =>
    A (Nat.unpair n).1 ((Encodable.decode (α := BitString) (Nat.unpair n).2).getD []) with hG
  have hGcomp : Computable G := by
    have hfst : Computable (fun n : ℕ => (Nat.unpair n).1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp
    have hsnd : Computable (fun n : ℕ =>
        (Encodable.decode (α := BitString) (Nat.unpair n).2).getD []) :=
      Computable.option_getD
        (Computable.decode.comp (Primrec.snd.comp Primrec.unpair).to_comp)
        (Computable.const [])
    exact hA.comp hfst hsnd
  have hpart : Nat.Partrec (fun x => Part.some (G x)) :=
    Partrec.nat_iff.mp (Computable.partrec hGcomp)
  obtain ⟨c₀, hc₀⟩ := Code.exists_code.mp hpart
  refine ⟨Encodable.encode c₀, ?_, ?_⟩
  · intro b j x
    have hofNat : Denumerable.ofNat Code (Encodable.encode c₀) = c₀ :=
      Denumerable.ofNat_encode c₀
    unfold rawTable
    rw [hofNat]
    cases hev : Code.evaln b c₀ (Nat.pair j (Encodable.encode x)) with
    | none => left; simp
    | some v =>
        right
        have hmem : v ∈ Code.eval c₀ (Nat.pair j (Encodable.encode x)) :=
          Code.evaln_sound (by rw [hev]; rfl)
        rw [hc₀] at hmem
        have hveq : v = G (Nat.pair j (Encodable.encode x)) := by
          simpa [eq_comm] using hmem
        simp only [Option.getD_some, hveq, hG, Nat.unpair_pair, Encodable.encodek,
          Option.getD_some]
  · intro j x
    have hofNat : Denumerable.ofNat Code (Encodable.encode c₀) = c₀ :=
      Denumerable.ofNat_encode c₀
    have hmem : G (Nat.pair j (Encodable.encode x))
        ∈ Code.eval c₀ (Nat.pair j (Encodable.encode x)) := by
      rw [hc₀]
      simp
    obtain ⟨b, hb⟩ := Code.evaln_complete.mp hmem
    refine ⟨b, ?_⟩
    have hb' : Code.evaln b c₀ (Nat.pair j (Encodable.encode x))
        = some (G (Nat.pair j (Encodable.encode x))) := hb
    unfold rawTable
    rw [hofNat, hb']
    simp [hG, Nat.unpair_pair]

/-! ## Domination and the supremum property -/

variable {A : ℕ → BitString → ℕ} {e : ℕ}

/-- The patched table never exceeds a monotone table that the code produces. -/
lemma patchLoop_le_of_code
    (hzero : ∀ b j x, rawTable e b j x = 0 ∨ rawTable e b j x = A j x)
    (hmono : ∀ s (w : CantorSeq),
      2 * A s (cantorPrefix w s) ≤ A (s + 1) (cantorPrefix w (s + 1)))
    (b : ℕ) (w : CantorSeq) (m : ℕ) :
    ∀ j, j ≤ m → patchLoop e b (cantorPrefix w m) j ≤ A j (cantorPrefix w j) := by
  intro j
  induction j with
  | zero =>
      intro _
      have : cantorPrefix w 0 = ([] : BitString) := by simp [cantorPrefix]
      rw [patchLoop, this]
      rcases hzero b 0 ([] : BitString) with h | h <;> rw [h]
      · exact Nat.zero_le _
  | succ j ih =>
      intro hj
      have hjm : j ≤ m := Nat.le_of_succ_le hj
      have htake : (cantorPrefix w m).take (j + 1) = cantorPrefix w (j + 1) :=
        cantorPrefix_take w (j + 1) m hj
      rw [patchLoop, htake]
      refine max_le ?_ ?_
      · exact le_trans (Nat.mul_le_mul_left 2 (ih hjm)) (hmono j w)
      · rcases hzero b (j + 1) (cantorPrefix w (j + 1)) with h | h <;> rw [h]
        · exact Nat.zero_le _

/-- If every raw entry is either zero or the corresponding value of `A`, and `A` at least doubles
along a sequence, then the patched table is dominated by `A`. -/
lemma patchTable_le_of_code
    (hzero : ∀ b j x, rawTable e b j x = 0 ∨ rawTable e b j x = A j x)
    (hmono : ∀ s (w : CantorSeq),
      2 * A s (cantorPrefix w s) ≤ A (s + 1) (cantorPrefix w (s + 1)))
    (s : ℕ) (w : CantorSeq) :
    patchTable e s (cantorPrefix w s) ≤ A s (cantorPrefix w s) :=
  patchLoop_le_of_code hzero hmono s w s s le_rfl

/-- Each value of a coded table is reached by the patched family. -/
lemma exists_bound_patchTable
    (hconv : ∀ j x, ∃ b, rawTable e b j x = A j x) (s : ℕ) (w : CantorSeq) :
    ∃ b, s ≤ b ∧ 2 ^ (b - s) * A s (cantorPrefix w s) ≤ patchTable e b (cantorPrefix w b) := by
  obtain ⟨b₀, hb₀⟩ := hconv s (cantorPrefix w s)
  refine ⟨max b₀ s, le_max_right _ _, ?_⟩
  set b := max b₀ s with hb
  have hraw : A s (cantorPrefix w s) ≤ rawTable e b s (cantorPrefix w s) := by
    rw [← hb₀]
    exact rawTable_mono _ (le_max_left _ _)
  have hstep : rawTable e b s ((cantorPrefix w b).take s) ≤ patchLoop e b (cantorPrefix w b) s :=
    patchLoop_ge_step _ s
  have htake : (cantorPrefix w b).take s = cantorPrefix w s :=
    cantorPrefix_take w s b (le_max_right _ _)
  rw [htake] at hstep
  have hbase : A s (cantorPrefix w s) ≤ patchLoop e b (cantorPrefix w b) s :=
    le_trans hraw hstep
  have hgrow : 2 ^ (b - s) * patchLoop e b (cantorPrefix w b) s
      ≤ patchLoop e b (cantorPrefix w b) (s + (b - s)) :=
    patchLoop_growth _ (b - s)
  have hsb : s + (b - s) = b := by omega
  rw [hsb] at hgrow
  exact le_trans (Nat.mul_le_mul_left _ hbase) hgrow

/-! ## Computability of the patched family -/

/-- The raw table is computable in all of its arguments. -/
lemma computable_rawTable {α : Type} [Primcodable α] {E B J : α → ℕ} {X : α → BitString}
    (hE : Computable E) (hB : Computable B) (hJ : Computable J) (hX : Computable X) :
    Computable (fun z => rawTable (E z) (B z) (J z) (X z)) := by
  have hcode : Computable (fun z => Denumerable.ofNat Code (E z)) :=
    ((Primrec.ofNat Code).to_comp).comp hE
  have hinput : Computable (fun z => Nat.pair (J z) (Encodable.encode (X z))) :=
    Computable₂.comp (Primrec₂.natPair.to_comp) hJ (Primrec.encode.to_comp.comp hX)
  have hev : Computable (fun z =>
      Code.evaln (B z) (Denumerable.ofNat Code (E z)) (Nat.pair (J z) (Encodable.encode (X z)))) :=
    Code.primrec_evaln.to_comp.comp ((hB.pair hcode).pair hinput)
  exact Computable.option_getD hev (Computable.const 0)

/-- The patching loop is computable in the index, the bound, the string and the stage. -/
lemma computable_patchLoop :
    Computable (fun q : (ℕ × ℕ × BitString) × ℕ => patchLoop q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hbase : Computable (fun z : ℕ × ℕ × BitString => rawTable z.1 z.2.1 0 []) :=
    computable_rawTable Computable.fst (Computable.fst.comp Computable.snd)
      (Computable.const 0) (Computable.const [])
  have hraw : Computable (fun q : (ℕ × ℕ × BitString) × (ℕ × ℕ) =>
      rawTable q.1.1 q.1.2.1 (q.2.1 + 1) (q.1.2.2.take (q.2.1 + 1))) := by
    refine computable_rawTable (Computable.fst.comp Computable.fst)
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.succ.comp (Computable.fst.comp Computable.snd)) ?_
    have htake₂ : Computable₂ (fun (n : ℕ) (l : BitString) => l.take n) :=
      Primrec₂.to_comp (Primrec.list_take.comp Primrec.snd Primrec.fst).to₂
    exact Computable₂.comp htake₂
      (Computable.succ.comp (Computable.fst.comp Computable.snd))
      (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hstep : Computable₂ (fun (z : ℕ × ℕ × BitString) (q : ℕ × ℕ) =>
      max (2 * q.2) (rawTable z.1 z.2.1 (q.1 + 1) (z.2.2.take (q.1 + 1)))) := by
    have hdouble : Computable (fun q : (ℕ × ℕ × BitString) × (ℕ × ℕ) => 2 * q.2.2) :=
      Computable₂.comp (Primrec.nat_mul.to_comp) (Computable.const 2)
        (Computable.snd.comp Computable.snd)
    exact Computable₂.comp (Primrec.nat_max.to_comp) hdouble hraw
  have hbase' : Computable (fun q : (ℕ × ℕ × BitString) × ℕ =>
      rawTable q.1.1 q.1.2.1 0 []) := hbase.comp Computable.fst
  have hstep' : Computable₂ (fun (q : (ℕ × ℕ × BitString) × ℕ) (r : ℕ × ℕ) =>
      max (2 * r.2) (rawTable q.1.1 q.1.2.1 (r.1 + 1) (q.1.2.2.take (r.1 + 1)))) :=
    Computable₂.comp
      (f := fun (z : ℕ × ℕ × BitString) (r : ℕ × ℕ) =>
        max (2 * r.2) (rawTable z.1 z.2.1 (r.1 + 1) (z.2.2.take (r.1 + 1))))
      hstep (Computable.fst.comp Computable.fst) Computable.snd
  exact (Computable.nat_rec Computable.snd hbase' hstep').of_eq fun q =>
    (patchLoop_eq_natRec q.1.1 q.1.2.1 q.1.2.2 q.2).symm

/-- The patched table is computable in the index, the stage and the string. -/
lemma computable_patchTable :
    Computable (fun p : ℕ × ℕ × BitString => patchTable p.1 p.2.1 p.2.2) := by
  have := computable_patchLoop.comp
    (Computable.pair (Computable.pair Computable.fst
      (Computable.pair (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)))
      (Computable.fst.comp Computable.snd))
  exact this

end Kolmogorov
