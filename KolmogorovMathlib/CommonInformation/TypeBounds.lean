import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Finset.Sort
import KolmogorovMathlib.CommonInformation.FixedHistogram

/-!
# Method-of-types arithmetic core (SUV Chapter 11, §11.4)

This file develops the exact natural-number "method of types" facts that
Exercise 316 (conditional-independence non-extractability) needs, with **no**
real entropy function, no Stirling estimate, and no Chapter 7 API.

Writing `typeProb f = ∏ i, (f i / n) ^ (f i)` informally, the key facts are:

* `multinomial_mul_typeProb_le_one`  — `M(f) · ∏ f_i^{f_i} ≤ n^n`, i.e. a type
  has probability at most one (one summand of the multinomial expansion of
  `n^n`).
* `one_le_pow_mul_multinomial_mul_typeProb` — `n^n ≤ (n+1)^{|s|} · (M(f) · ∏
  f_i^{f_i})`, i.e. a type maximises its own probability up to the polynomial
  number of types.
* `typeProb_product_form` — for a product-form joint histogram, the type
  probability factors.
* `multinomial_marginals_le_of_product_form` — the resulting `O(log N)` type
  defect `M(gA)·M(gB) ≤ (n+1)^{|A||B|}·M(g)`.
* `multinomial_fiber_factorization` — the exact fibre factorisation of a joint
  multinomial coefficient, turning a conditional-independence link into a
  per-fibre product-form statement.

All complexity/probability statements are in exact cross-multiplied
natural-number form; probabilities never appear as rationals.

The per-coordinate arithmetic root is `f! · f^k ≤ k! · f^f`
(`factorial_mul_pow_le_factorial_mul_pow_self`): the function `m ↦ m!/f^m`
attains its minimum at `m = f`.
-/

namespace Kolmogorov

open Finset Nat

/-! ### Per-coordinate root inequality -/

/-- The per-coordinate root: `f! · f^k ≤ k! · f^f`.  Equivalently `g(f) ≤ g(k)`
for `g(m) = m!/f^m`, whose minimum is at `m = f`. -/
theorem factorial_mul_pow_le_factorial_mul_pow_self (f k : ℕ) :
    f.factorial * f ^ k ≤ k.factorial * f ^ f := by
  rcases le_total k f with hkf | hfk
  · -- `k ≤ f`: downward induction on `d = f - k`.
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkf
    clear hkf
    induction d generalizing k with
    | zero => simp
    | succ d ih =>
      rw [show k + (d + 1) = k + 1 + d from by ring]
      have hmpos : 0 < k + 1 + d := by omega
      have IH := ih (k + 1)
      -- IH : (k+1+d)! * (k+1+d)^(k+1) ≤ (k+1)! * (k+1+d)^(k+1+d)
      have hstep :
          (k + 1 + d) * ((k + 1 + d)! * (k + 1 + d) ^ k) ≤
            (k + 1 + d) * (k ! * (k + 1 + d) ^ (k + 1 + d)) := by
        calc (k + 1 + d) * ((k + 1 + d)! * (k + 1 + d) ^ k)
            = (k + 1 + d)! * (k + 1 + d) ^ (k + 1) := by ring
          _ ≤ (k + 1)! * (k + 1 + d) ^ (k + 1 + d) := IH
          _ = (k + 1) * (k ! * (k + 1 + d) ^ (k + 1 + d)) := by
              rw [Nat.factorial_succ]; ring
          _ ≤ (k + 1 + d) * (k ! * (k + 1 + d) ^ (k + 1 + d)) :=
              Nat.mul_le_mul_right _ (by omega)
      exact Nat.le_of_mul_le_mul_left hstep hmpos
  · -- `f ≤ k`: forward induction on `k` from `f`.
    induction k, hfk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
      calc f.factorial * f ^ (k + 1)
          = (f.factorial * f ^ k) * f := by ring
        _ ≤ (k.factorial * f ^ f) * f := by gcongr
        _ ≤ (k.factorial * f ^ f) * (k + 1) := by gcongr; omega
        _ = (k + 1).factorial * f ^ f := by rw [Nat.factorial_succ]; ring

/-! ### Counting the number of types -/

/-- There are at most `(n+1)^{|s|}` histograms on `s` with total `n`. -/
theorem card_piAntidiag_le {α : Type*} [DecidableEq α] (s : Finset α) (n : ℕ) :
    (s.piAntidiag n).card ≤ (n + 1) ^ s.card := by
  classical
  have htarget :
      (Fintype.piFinset (fun (_ : s) => Finset.range (n + 1))).card = (n + 1) ^ s.card := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const]
  rw [← htarget]
  apply Finset.card_le_card_of_injOn (fun f => fun (i : s) => f i.val)
  · intro f hf
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    rw [Finset.mem_coe, Finset.mem_piAntidiag] at hf
    obtain ⟨hfsum, -⟩ := hf
    have hfsum' : (∑ j ∈ s, f j) = n := hfsum
    have hle : f i.val ≤ ∑ j ∈ s, f j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) i.2
    change f i.val < n + 1
    omega
  · intro f hf g hg hfg
    rw [Finset.mem_coe, Finset.mem_piAntidiag] at hf hg
    funext a
    by_cases ha : a ∈ s
    · have := congr_fun hfg ⟨a, ha⟩
      simpa using this
    · have hf0 : f a = 0 := by by_contra h; exact ha (hf.2 a h)
      have hg0 : g a = 0 := by by_contra h; exact ha (hg.2 a h)
      rw [hf0, hg0]

/-! ### A type maximises its own probability -/

/-- For two histograms `f, k` of the same total, `M(k)·∏ f_i^{k_i} ≤ M(f)·∏
f_i^{f_i}`: the type `f` maximises the (cross-multiplied) probability of `k`. -/
theorem multinomial_mul_pow_le_multinomial_mul_pow_self {α : Type*} [DecidableEq α] (s : Finset α)
    (n : ℕ) (f k : α → ℕ) (hf : f ∈ s.piAntidiag n) (hk : k ∈ s.piAntidiag n) :
    Nat.multinomial s k * ∏ i ∈ s, (f i) ^ (k i) ≤
      Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i) := by
  have hfsum : ∑ i ∈ s, f i = n := (Finset.mem_piAntidiag.mp hf).1
  have hksum : ∑ i ∈ s, k i = n := (Finset.mem_piAntidiag.mp hk).1
  have specf : (∏ i ∈ s, (f i)!) * Nat.multinomial s f = (∑ i ∈ s, f i)! :=
    Nat.multinomial_spec s f
  have speck : (∏ i ∈ s, (k i)!) * Nat.multinomial s k = (∑ i ∈ s, k i)! :=
    Nat.multinomial_spec s k
  rw [hfsum] at specf
  rw [hksum] at speck
  have hCpos : 0 < (∏ i ∈ s, (k i)!) * (∏ i ∈ s, (f i)!) :=
    Nat.mul_pos (Finset.prod_pos fun i _ => Nat.factorial_pos _)
      (Finset.prod_pos fun i _ => Nat.factorial_pos _)
  have coordwise :
      ∏ i ∈ s, ((f i) ^ (k i) * (f i)!) ≤ ∏ i ∈ s, ((f i) ^ (f i) * (k i)!) := by
    apply Finset.prod_le_prod'
    intro i _
    calc (f i) ^ (k i) * (f i)! = (f i)! * (f i) ^ (k i) := by ring
      _ ≤ (k i)! * (f i) ^ (f i) := factorial_mul_pow_le_factorial_mul_pow_self (f i) (k i)
      _ = (f i) ^ (f i) * (k i)! := by ring
  refine Nat.le_of_mul_le_mul_right ?_ hCpos
  calc (Nat.multinomial s k * ∏ i ∈ s, (f i) ^ (k i)) *
          ((∏ i ∈ s, (k i)!) * (∏ i ∈ s, (f i)!))
      = ((∏ i ∈ s, (k i)!) * Nat.multinomial s k) *
          ((∏ i ∈ s, (f i) ^ (k i)) * (∏ i ∈ s, (f i)!)) := by ring
    _ = n ! * ∏ i ∈ s, ((f i) ^ (k i) * (f i)!) := by rw [speck, ← Finset.prod_mul_distrib]
    _ ≤ n ! * ∏ i ∈ s, ((f i) ^ (f i) * (k i)!) := by gcongr
    _ = ((∏ i ∈ s, (f i)!) * Nat.multinomial s f) *
          ((∏ i ∈ s, (f i) ^ (f i)) * (∏ i ∈ s, (k i)!)) := by
        rw [specf, Finset.prod_mul_distrib]
    _ = (Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i)) *
          ((∏ i ∈ s, (k i)!) * (∏ i ∈ s, (f i)!)) := by ring

/-! ### A type has probability at most one, and at least `1/#types` -/

/-- `M(f) · ∏ f_i^{f_i} ≤ n^n`: one summand of the multinomial expansion of `n^n`. -/
theorem multinomial_mul_typeProb_le_one {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (n : ℕ) (hf : f ∈ s.piAntidiag n) :
    Nat.multinomial s f * (∏ i ∈ s, (f i) ^ (f i)) ≤ n ^ n := by
  have hsum : ∑ i ∈ s, f i = n := (Finset.mem_piAntidiag.mp hf).1
  have key := Finset.sum_pow_eq_sum_piAntidiag s f n
  simp only [Nat.cast_id] at key
  have hle := Finset.single_le_sum
    (f := fun k => Nat.multinomial s k * ∏ i ∈ s, f i ^ (k i))
    (fun k _ => Nat.zero_le _) hf
  rw [← key, hsum] at hle
  exact hle

/-- `n^n ≤ (n+1)^{|s|} · (M(f) · ∏ f_i^{f_i})`: a type maximises its own
probability, and there are at most `(n+1)^{|s|}` types. -/
theorem one_le_pow_mul_multinomial_mul_typeProb {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) (n : ℕ) (hf : f ∈ s.piAntidiag n) :
    n ^ n ≤ (n + 1) ^ s.card * (Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i)) := by
  have hsum : ∑ i ∈ s, f i = n := (Finset.mem_piAntidiag.mp hf).1
  have key := Finset.sum_pow_eq_sum_piAntidiag s f n
  simp only [Nat.cast_id] at key
  rw [hsum] at key
  rw [key]
  have hbound :
      ∑ k ∈ s.piAntidiag n, Nat.multinomial s k * ∏ i ∈ s, f i ^ (k i)
        ≤ (s.piAntidiag n).card • (Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i)) := by
    apply Finset.sum_le_card_nsmul
    intro k hk
    exact multinomial_mul_pow_le_multinomial_mul_pow_self s n f k hf hk
  rw [smul_eq_mul] at hbound
  calc ∑ k ∈ s.piAntidiag n, Nat.multinomial s k * ∏ i ∈ s, f i ^ (k i)
      ≤ (s.piAntidiag n).card * (Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i)) := hbound
    _ ≤ (n + 1) ^ s.card * (Nat.multinomial s f * ∏ i ∈ s, (f i) ^ (f i)) := by
        apply Nat.mul_le_mul_right
        exact card_piAntidiag_le s n

/-! ### The product-form type probability factors -/

/-- For a product-form joint histogram (`n · g(a,b) = gA a · gB b`) whose
marginals are `gA, gB` and whose total is `n`, the type probability factors:
`n^n · ∏ g_ab^{g_ab} = (∏ gA_a^{gA_a})·(∏ gB_b^{gB_b})`.

The marginal (`h_gA`, `h_gB`) and total (`h_sum`) hypotheses are mathematically
necessary: without them the identity is false (e.g. `A=B={*}`, `n=1`, `g=6`,
`gA=2`, `gB=3` satisfies `n·g = gA·gB` but `1·6⁶ ≠ 2²·3³`). -/
theorem typeProb_product_form {A B : Type*} [Fintype A] [Fintype B] (g : A × B → ℕ)
    (gA : A → ℕ) (gB : B → ℕ) (n : ℕ)
    (h_gA : ∀ a, gA a = ∑ b, g (a, b))
    (h_gB : ∀ b, gB b = ∑ a, g (a, b))
    (h_sum : ∑ ab, g ab = n)
    (hg : ∀ a b, n * g (a, b) = gA a * gB b) :
    n ^ n * ∏ ab ∈ univ, (g ab) ^ (g ab) =
      (∏ a ∈ univ, (gA a) ^ (gA a)) * (∏ b ∈ univ, (gB b) ^ (gB b)) := by
  have hpt : ∀ ab : A × B,
      n ^ (g ab) * (g ab) ^ (g ab) = (gA ab.1) ^ (g ab) * (gB ab.2) ^ (g ab) := by
    rintro ⟨a, b⟩
    rw [← mul_pow, ← mul_pow, hg a b]
  have hA : (∏ ab : A × B, (gA ab.1) ^ (g ab)) = ∏ a, (gA a) ^ (gA a) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, ← h_gA a]
  have hB : (∏ ab : A × B, (gB ab.2) ^ (g ab)) = ∏ b, (gB b) ^ (gB b) := by
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, ← h_gB b]
  calc n ^ n * ∏ ab, (g ab) ^ (g ab)
      = (∏ ab : A × B, n ^ (g ab)) * ∏ ab, (g ab) ^ (g ab) := by
        rw [Finset.prod_pow_eq_pow_sum, h_sum]
    _ = ∏ ab : A × B, (n ^ (g ab) * (g ab) ^ (g ab)) := by rw [Finset.prod_mul_distrib]
    _ = ∏ ab : A × B, ((gA ab.1) ^ (g ab) * (gB ab.2) ^ (g ab)) :=
        Finset.prod_congr rfl (fun ab _ => hpt ab)
    _ = (∏ ab : A × B, (gA ab.1) ^ (g ab)) * ∏ ab : A × B, (gB ab.2) ^ (g ab) := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ a, (gA a) ^ (gA a)) * ∏ b, (gB b) ^ (gB b) := by rw [hA, hB]

/-! ### The type defect for marginals -/

/-- The `O(log N)` type defect: for a product-form joint histogram with
marginals `gA, gB`, total `n > 0`,
`M(gA)·M(gB) ≤ (n+1)^{|A||B|}·M(g)`.

The product-form and marginal hypotheses force the total of `g` to be either
`0` or `n`.  The zero-total branch is handled explicitly below, so callers do
not have to provide a redundant normalization hypothesis. -/
theorem multinomial_marginals_le_of_product_form {A B : Type*} [Fintype A] [Fintype B]
    (g : A × B → ℕ) (gA : A → ℕ) (gB : B → ℕ) (n : ℕ)
    (h_n : n > 0)
    (h_gA : ∀ a, gA a = ∑ b, g (a, b))
    (h_gB : ∀ b, gB b = ∑ a, g (a, b))
    (hg : ∀ a b, n * g (a, b) = gA a * gB b) :
    Nat.multinomial univ gA * Nat.multinomial univ gB ≤
      (n + 1) ^ (Fintype.card A * Fintype.card B) * Nat.multinomial univ g := by
  classical
  let total := ∑ ab : A × B, g ab
  have hsumA_total : ∑ a, gA a = total := by
    dsimp only [total]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun a _ => h_gA a)
  have hsumB_total : ∑ b, gB b = total := by
    dsimp only [total]
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl (fun b _ => h_gB b)
  have htotal_product : n * total = total * total := by
    calc
      n * total = ∑ ab : A × B, n * g ab := by
        dsimp only [total]
        rw [Finset.mul_sum]
      _ = ∑ ab : A × B, gA ab.1 * gB ab.2 := by
        refine Finset.sum_congr rfl fun ab _ => ?_
        exact hg ab.1 ab.2
      _ = (∑ a, gA a) * (∑ b, gB b) := by
        rw [Fintype.sum_prod_type]
        calc
          ∑ a, ∑ b, gA a * gB b =
              ∑ a, gA a * (∑ b, gB b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
          _ = (∑ a, gA a) * (∑ b, gB b) := by rw [Finset.sum_mul]
      _ = total * total := by rw [hsumA_total, hsumB_total]
  by_cases htotal_zero : total = 0
  · have hg_zero : g = 0 := by
      funext ab
      exact Finset.sum_eq_zero_iff.mp htotal_zero ab (Finset.mem_univ ab)
    have hgA_zero : gA = 0 := by
      funext a
      rw [h_gA a]
      simp [hg_zero]
    have hgB_zero : gB = 0 := by
      funext b
      rw [h_gB b]
      simp [hg_zero]
    rw [hg_zero, hgA_zero, hgB_zero]
    simp only [Nat.multinomial, Pi.zero_apply, Finset.sum_const_zero, Nat.factorial_zero,
      Finset.prod_const_one, Nat.div_one, one_mul]
    rw [mul_one]
    exact Nat.one_le_pow (Fintype.card A * Fintype.card B) (n + 1) (by omega)
  have htotal_pos : 0 < total := Nat.pos_of_ne_zero htotal_zero
  have htotal_eq_n : total = n := by
    symm
    exact Nat.eq_of_mul_eq_mul_right htotal_pos htotal_product
  have h_sum : ∑ ab : A × B, g ab = n := by
    change total = n
    exact htotal_eq_n
  have hsumA : ∑ a, gA a = n := hsumA_total.trans htotal_eq_n
  have hsumB : ∑ b, gB b = n := hsumB_total.trans htotal_eq_n
  -- Type memberships.
  have hgA_mem : gA ∈ (univ : Finset A).piAntidiag n :=
    Finset.mem_piAntidiag.mpr ⟨hsumA, fun i _ => Finset.mem_univ i⟩
  have hgB_mem : gB ∈ (univ : Finset B).piAntidiag n :=
    Finset.mem_piAntidiag.mpr ⟨hsumB, fun i _ => Finset.mem_univ i⟩
  have hg_mem : g ∈ (univ : Finset (A × B)).piAntidiag n :=
    Finset.mem_piAntidiag.mpr ⟨h_sum, fun i _ => Finset.mem_univ i⟩
  -- The three type bounds and the product-form factorisation.
  have hA4 := multinomial_mul_typeProb_le_one (univ : Finset A) gA n hgA_mem
  have hB4 := multinomial_mul_typeProb_le_one (univ : Finset B) gB n hgB_mem
  have h5 := one_le_pow_mul_multinomial_mul_typeProb (univ : Finset (A × B)) g n hg_mem
  rw [Finset.card_univ, Fintype.card_prod] at h5
  have h6 := typeProb_product_form g gA gB n h_gA h_gB h_sum hg
  set MA := Nat.multinomial univ gA with hMA
  set MB := Nat.multinomial univ gB with hMB
  set Mg := Nat.multinomial univ g with hMg
  set PA := ∏ a, (gA a) ^ (gA a) with hPA
  set PB := ∏ b, (gB b) ^ (gB b) with hPB
  set Pg := ∏ ab, (g ab) ^ (g ab) with hPg_def
  have hnn : 0 < n ^ n := pow_pos h_n n
  have hPg : 0 < Pg := by
    rw [hPg_def]
    exact Finset.prod_pos fun ab _ =>
      Nat.pos_of_ne_zero (fun h => by rw [Nat.pow_eq_zero] at h; exact h.2 h.1)
  -- Multiply the two "probability ≤ 1" bounds and factor with the product form.
  have key1 : (MA * MB * Pg) * n ^ n ≤ n ^ n * n ^ n := by
    have e : (MA * PA) * (MB * PB) = (MA * MB * Pg) * n ^ n := by
      rw [show (MA * PA) * (MB * PB) = (MA * MB) * (PA * PB) by ring, ← h6]; ring
    rw [← e]
    exact Nat.mul_le_mul hA4 hB4
  have key2 : MA * MB * Pg ≤ n ^ n := Nat.le_of_mul_le_mul_right key1 hnn
  have key3 :
      (MA * MB) * Pg ≤ ((n + 1) ^ (Fintype.card A * Fintype.card B) * Mg) * Pg := by
    calc (MA * MB) * Pg
        = MA * MB * Pg := by ring
      _ ≤ n ^ n := key2
      _ ≤ (n + 1) ^ (Fintype.card A * Fintype.card B) * (Mg * Pg) := h5
      _ = ((n + 1) ^ (Fintype.card A * Fintype.card B) * Mg) * Pg := by ring
  exact Nat.le_of_mul_le_mul_right key3 hPg

/-! ### Fibre factorisation of the multinomial coefficient -/

/-- Exact fibre factorisation: `M(f) = M(f_W) · ∏_w M(f_{·|w})` where `f_W w = ∑_a
f(a,w)` and `f_{·|w} a = f(a,w)`.  This turns a conditional-independence link
into a per-fibre product-form statement. -/
theorem multinomial_fiber_factorization {A W : Type*} [Fintype A] [Fintype W]
    (f : A × W → ℕ) :
    Nat.multinomial univ f =
      Nat.multinomial univ (fun w => ∑ a, f (a, w)) *
      ∏ w ∈ univ, Nat.multinomial univ (fun a => f (a, w)) := by
  have hP : 0 < ∏ x : A × W, (f x)! := Finset.prod_pos fun x _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_left hP ?_
  rw [Nat.multinomial_spec univ f]
  symm
  calc (∏ x : A × W, (f x)!) *
          (Nat.multinomial univ (fun w => ∑ a, f (a, w)) *
            ∏ w, Nat.multinomial univ (fun a => f (a, w)))
      = (∏ w, ∏ a, (f (a, w))!) *
          (Nat.multinomial univ (fun w => ∑ a, f (a, w)) *
            ∏ w, Nat.multinomial univ (fun a => f (a, w))) := by
        rw [Fintype.prod_prod_type_right]
    _ = Nat.multinomial univ (fun w => ∑ a, f (a, w)) *
          ((∏ w, ∏ a, (f (a, w))!) * ∏ w, Nat.multinomial univ (fun a => f (a, w))) := by
        ring
    _ = Nat.multinomial univ (fun w => ∑ a, f (a, w)) *
          ∏ w, ((∏ a, (f (a, w))!) * Nat.multinomial univ (fun a => f (a, w))) := by
        rw [← Finset.prod_mul_distrib]
    _ = Nat.multinomial univ (fun w => ∑ a, f (a, w)) * ∏ w, (∑ a, f (a, w))! := by
        refine congrArg _ (Finset.prod_congr rfl (fun w _ => ?_))
        exact Nat.multinomial_spec univ (fun a => f (a, w))
    _ = (∏ w, (∑ a, f (a, w))!) * Nat.multinomial univ (fun w => ∑ a, f (a, w)) := by ring
    _ = (∑ w, ∑ a, f (a, w))! := Nat.multinomial_spec univ (fun w => ∑ a, f (a, w))
    _ = (∑ x : A × W, f x)! := by rw [Fintype.sum_prod_type_right]

end Kolmogorov
