import KolmogorovMathlib.Core.Basic

/-!
# Cantor space and its finite prefixes

`CantorSeq = ℕ → Bool` is the space of infinite binary sequences.  `cantorPrefix w n` is the
bitstring of its first `n` bits, `IsCantorPrefix x w` says `x` is an initial segment of `w`,
and `prependCantor x rest` puts a finite string in front of a sequence.

The lemmas are the ones every later argument uses without comment: a prefix has the expected
length and entries (`cantorPrefix_length`, `cantorPrefix_getElem`), initial segments are
exactly the prefixes of matching length (`isCantorPrefix_iff_cantorPrefix_eq`), prefixes of
one sequence are nested (`cantorPrefix_mono`), and prepending interacts with all of these as
expected (`prependCantor_append`, `cantorPrefix_prepend`).

This is the base of `AlgorithmicRandomness`; the measure-theoretic structure of the space is
in `Cylinders`.
-/

open Kolmogorov

/-- Cantor space: infinite binary sequences, i.e. functions `ℕ → Bool`. -/
abbrev CantorSeq := ℕ → Bool

/-- The finite bit string formed by the first `n` bits of the sequence `w`. -/
def cantorPrefix (w : CantorSeq) (n : ℕ) : BitString :=
  List.ofFn (fun i : Fin n => w i)

/-- The finite bit string `x` is an initial segment of the infinite sequence `w`. -/
def IsCantorPrefix (x : BitString) (w : CantorSeq) : Prop :=
  ∀ i, (h : i < x.length) → w i = x[i]

/-- The sequence obtained by putting the bits of `x` first and continuing with `rest`. -/
def prependCantor (x : BitString) (rest : CantorSeq) : CantorSeq :=
  fun i => if h : i < x.length then x[i] else rest (i - x.length)

/-- The length-`n` prefix of a sequence has length `n`. -/
@[simp] lemma cantorPrefix_length (w : CantorSeq) (n : ℕ) :
    (cantorPrefix w n).length = n := by
  simp [cantorPrefix]

/-- The `i`-th entry of the prefix of `w` is the `i`-th bit of `w`. -/
@[simp] lemma cantorPrefix_getElem (w : CantorSeq) (n : ℕ) (i : ℕ)
    (h : i < (cantorPrefix w n).length) :
    (cantorPrefix w n)[i] = w i := by
  have hi : i < n := by simpa [cantorPrefix] using h
  simp [cantorPrefix]

/-- A string is an initial segment of a sequence exactly when it equals the prefix of matching
length. -/
lemma isCantorPrefix_iff_cantorPrefix_eq (x : BitString) (w : CantorSeq) :
    IsCantorPrefix x w ↔ cantorPrefix w x.length = x := by
  constructor
  · intro h
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have h3 : i < x.length := by simpa using h1
      simp only [cantorPrefix_getElem]
      exact h i h3
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simp [cantorPrefix, List.getElem?_ofFn] at this
    simpa [List.getElem?_eq_getElem hi, hi] using this

/-- Truncating a longer prefix of a sequence yields the shorter prefix. -/
lemma cantorPrefix_take (w : CantorSeq) (m n : ℕ) (h : m ≤ n) :
    (cantorPrefix w n).take m = cantorPrefix w m := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [cantorPrefix_length] at h2
    have h3 : i < n := by omega
    simp [cantorPrefix]

/-- Prefixes of a sequence are nested: the shorter one is a prefix of the longer one. -/
theorem cantorPrefix_mono (w : CantorSeq) {m n : ℕ} (h : m ≤ n) :
    cantorPrefix w m <+: cantorPrefix w n := by
  rw [← cantorPrefix_take w m n h]
  exact List.take_prefix m (cantorPrefix w n)

/-- The string `x` is an initial segment of any sequence obtained by prepending `x`. -/
lemma isCantorPrefix_prepend (x : BitString) (rest : CantorSeq) :
    IsCantorPrefix x (prependCantor x rest) := by
  intro i hi
  simp [prependCantor, hi]

/-- Prepending the empty string does nothing. -/
@[simp] lemma prependCantor_nil (rest : CantorSeq) : prependCantor [] rest = rest := by
  funext i
  simp [prependCantor]

/-- Prepending a concatenation is prepending the two strings in turn. -/
lemma prependCantor_append (x y : BitString) (rest : CantorSeq) :
    prependCantor (x ++ y) rest = prependCantor x (prependCantor y rest) := by
  funext i
  by_cases hx : i < x.length
  · have hxy : i < (x ++ y).length := by simp only [List.length_append]; omega
    simp only [prependCantor, dif_pos hx, dif_pos hxy, List.getElem_append_left hx]
  · by_cases hxy : i < (x ++ y).length
    · have hy : i - x.length < y.length := by
        simp only [List.length_append] at hxy; omega
      simp only [prependCantor, dif_neg hx, dif_pos hxy, dif_pos hy]
      exact List.getElem_append_right (by omega)
    · have hy : ¬ i - x.length < y.length := by
        simp only [List.length_append] at hxy; omega
      simp only [prependCantor, dif_neg hx, dif_neg hxy, dif_neg hy]
      congr 1
      simp only [List.length_append]
      omega

/-- The initial segment of length `|x|` of a sequence beginning with `x` is `x`. -/
lemma cantorPrefix_prepend (x : BitString) (rest : CantorSeq) :
    cantorPrefix (prependCantor x rest) x.length = x := by
  rw [← isCantorPrefix_iff_cantorPrefix_eq]
  exact isCantorPrefix_prepend x rest
