import KolmogorovMathlib.CommonInformation.ChainFibre

/-!
# Fibre incompressibility of a maximal sample along an arbitrary projection

The one-coordinate lower profile of `ChainSample.lean`
(`chain_single_projection_plainK_lower_at`) uses an exact product splitting of
the chain alphabet at the chosen coordinate.  That splitting is only available
for projections whose fibres all have the same size, which fails for the
two- and three-coordinate projections (e.g. `v ↦ (v i, v i)`).

This file replaces the exact splitting by an *injective* labelling
`v ↦ (π v, ι v)` of the alphabet inside a product `Fin m × Fin n`, where `ι` is
any numbering of the alphabet.  The resulting histogram is the original one
extended by zeros, so all counting quantities (multinomial, parameter table)
are unchanged, while the product shape required by
`condK_fixedHistogramWord_given_projection_le_add_params` is available for an
arbitrary projection `π`.

The main result `maximalSample_projection_typeLog_le` is the abstract
fibre-incompressibility statement: for a maximal-complexity word `W` realising
a histogram `g`, the type-log of the pushforward histogram `π_* g` is at most
the plain complexity of any string `proj W` from which the projected word is
computable, up to a logarithmic term.
-/

namespace Kolmogorov

open Finset

/-! ### Extension by zero along an injection -/

/-- A finite sum of a function supported on the range of an injection is the
sum of its pullback. -/
theorem sum_eq_sum_comp_of_zero_off_range {A B : Type*} [Fintype A] [Fintype B]
    (psi : A → B) (hpsi : Function.Injective psi) (F : B → ℕ)
    (h0 : ∀ b : B, (∀ a : A, psi a ≠ b) → F b = 0) :
    ∑ b, F b = ∑ a, F (psi a) := by
  classical
  have hsubset : ∑ b ∈ Finset.univ.image psi, F b = ∑ b, F b := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro b _ hb
    refine h0 b (fun a ha => ?_)
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
  rw [← hsubset]
  exact Finset.sum_image (fun x _ y _ h => hpsi h)

/-- A finite product of a function equal to `1` off the range of an injection
is the product of its pullback. -/
theorem prod_eq_prod_comp_of_one_off_range {A B : Type*} [Fintype A] [Fintype B]
    (psi : A → B) (hpsi : Function.Injective psi) (F : B → ℕ)
    (h1 : ∀ b : B, (∀ a : A, psi a ≠ b) → F b = 1) :
    ∏ b, F b = ∏ a, F (psi a) := by
  classical
  have hsubset : ∏ b ∈ Finset.univ.image psi, F b = ∏ b, F b := by
    refine Finset.prod_subset (Finset.subset_univ _) ?_
    intro b _ hb
    refine h1 b (fun a ha => ?_)
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
  rw [← hsubset]
  exact Finset.prod_image (fun x _ y _ h => hpsi h)

/-- Extending a histogram by zeros along an injective relabelling leaves the
multinomial coefficient unchanged. -/
theorem multinomial_eq_of_zero_off_range {A B : Type*} [Fintype A] [Fintype B]
    (psi : A → B) (hpsi : Function.Injective psi)
    (g : A → ℕ) (F : B → ℕ) (hF : ∀ a, F (psi a) = g a)
    (h0 : ∀ b : B, (∀ a : A, psi a ≠ b) → F b = 0) :
    Nat.multinomial univ F = Nat.multinomial univ g := by
  classical
  unfold Nat.multinomial
  have hsum : ∑ b, F b = ∑ a, g a := by
    rw [sum_eq_sum_comp_of_zero_off_range psi hpsi F h0]
    exact Finset.sum_congr rfl (fun a _ => hF a)
  have hprod : ∏ b, Nat.factorial (F b) = ∏ a, Nat.factorial (g a) := by
    rw [prod_eq_prod_comp_of_one_off_range psi hpsi (fun b => Nat.factorial (F b))
      (fun b hb => by simp [h0 b hb])]
    exact Finset.prod_congr rfl (fun a _ => congrArg Nat.factorial (hF a))
  rw [hsum, hprod]

/-! ### The abstract fibre-incompressibility bound -/

/-- **Fibre incompressibility of a maximal sample.**

Let `W` be a word over a finite alphabet `A` realising the histogram `g` of
total mass `N`, whose coded form `finiteWordCode W` is of maximal plain
complexity within its type (`histogramTypeLog g ≤ kW + 1`).  Let `π : A → Fin m`
be any projection and `proj W` any string from which the projected word
`W.map π` is computable (hypothesis `h₁`) and which is itself computable from
the full coded word (hypothesis `h₂`).  Then the type-log of the pushforward
histogram is at most the plain complexity of `proj W`, up to a logarithmic
term with a constant that does not depend on `N`, `g` or `W`.

The linear bound `kW ≤ c₃ * N + c₃ * Nat.size (N + 1) + c₃` on the complexity of
the coded full word is only used to control the logarithmic term of the
complexity chain rule. -/
theorem maximalSample_projection_typeLog_le
    (V : Map) (hV : isOptimalConditional V)
    {A : Type*} [Fintype A] [DecidableEq A] [FiniteLetterCode A]
    (m : ℕ) (pi : A → Fin m) (proj : List A → BitString) (c₁ c₂ c₃ : ℕ)
    (h₁ : ∀ (W : List A) (z : BitString),
      condK V z (proj W) ≤ condK V z (finiteWordCode (W.map pi)) + (c₁ : ENat))
    (h₂ : ∀ W : List A,
      plainK V (pairCode (proj W) (finiteWordCode W)) ≤
        plainK V (finiteWordCode W) + (c₂ : ENat))
    :
    ∃ C : ℕ, ∀ (N : ℕ) (g : A → ℕ) (W : List A) (kW : ℕ),
      (∀ v, W.count v = g v) → (∑ v, g v = N) →
      HasPlainComplexityValue V (finiteWordCode W) kW →
      (histogramTypeLog g : ENat) ≤ (kW : ENat) + 1 →
      kW ≤ c₃ * N + c₃ * Nat.size (N + 1) + c₃ →
      (histogramTypeLog
          (fun a : Fin m => ∑ v ∈ Finset.univ.filter (fun v => pi v = a), g v) : ENat) ≤
        plainK V (proj W) + (logSlack C (N + 1) : ENat) := by
  classical
  obtain ⟨cProj, hProj⟩ := condK_fixedHistogramWord_given_projection_le_add_params V hV
  set n := Fintype.card A with hn
  set eA : A ≃ Fin n := Fintype.equivFin A with heA
  set psi : A → Fin m × Fin n := fun v => (pi v, eA v) with hpsi
  have hpsiInj : Function.Injective psi := by
    intro a b hab
    exact eA.injective (congrArg Prod.snd hab)
  have hcodeInj : Function.Injective
      (fun v : A => FiniteLetterCode.encode (psi v)) := by
    intro a b hab
    exact hpsiInj (FiniteLetterCode.injective hab)
  obtain ⟨cOut, hOut⟩ := condK_numericWord_recode_le V hV
    (fun v : A => FiniteLetterCode.encode (psi v))
    (FiniteLetterCode.encode : A → ℕ) hcodeInj
  obtain ⟨cChain, hChain⟩ := pairPlainK_chain_upper_values V hV
  obtain ⟨cRight, hRight⟩ := pairPlainK_right_le V hV
  set gamma := 3 * c₃ + c₂ + 1 with hgamma
  set C := 2 * n + cChain +
    (2 * Nat.size m + 2 * Nat.size n + m * n + cProj + cOut + c₁ + cRight + 2 +
      cChain * Nat.size gamma + cChain) with hC
  refine ⟨C, ?_⟩
  intro N g W kW hcounts hsumg hvalue hmaximal hkW_up'
  set x := proj W with hx
  set y := finiteWordCode W with hy
  set w : List (Fin m × Fin n) := W.map psi with hw
  set f : Fin m × Fin n → ℕ := fun ab => w.count ab with hf
  have hwcount : ∀ ab, w.count ab = f ab := fun _ => rfl
  have hfpsi : ∀ v, f (psi v) = g v := by
    intro v
    have h := List.count_map_of_injective W psi hpsiInj v
    change w.count (psi v) = g v
    rw [hw, h, hcounts v]
  have hf0 : ∀ ab, (∀ v, psi v ≠ ab) → f ab = 0 := by
    intro ab hab
    change w.count ab = 0
    refine List.count_eq_zero.mpr ?_
    intro hmem
    rw [hw, List.mem_map] at hmem
    obtain ⟨v, _, hv⟩ := hmem
    exact hab v hv
  set hist : Fin m → ℕ :=
    fun a => ∑ v ∈ Finset.univ.filter (fun v => pi v = a), g v with hhist
  have hmarg : ∀ a, ∑ b, f (a, b) = hist a := by
    intro a
    have hre : ∑ b : Fin n, f (a, b) = ∑ v : A, f (a, eA v) :=
      (Equiv.sum_comp eA (fun b => f (a, b))).symm
    have hfil : hist a = ∑ v : A, if pi v = a then g v else 0 := by
      rw [hhist]
      simp only [Finset.sum_filter]
    rw [hre, hfil]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : pi v = a
    · have : (a, eA v) = psi v := by rw [hpsi, ← hv]
      rw [this, hfpsi v]
      simp [hv]
    · have hzero : f (a, eA v) = 0 := by
        refine hf0 _ (fun v' hv' => ?_)
        have h1 : eA v' = eA v := congrArg Prod.snd hv'
        have h2 : v' = v := eA.injective h1
        subst h2
        exact hv (congrArg Prod.fst hv')
      rw [hzero]
      simp [hv]
  have hmultf : Nat.multinomial univ f = Nat.multinomial univ g :=
    multinomial_eq_of_zero_off_range psi hpsiInj g f hfpsi hf0
  have hsplit : Nat.multinomial univ g =
      Nat.multinomial univ hist *
        ∏ a, Nat.multinomial univ (fun b => f (a, b)) := by
    rw [← hmultf, multinomial_fiber_factorization_left f]
    exact congrArg (fun t => t * ∏ a, Nat.multinomial univ (fun b => f (a, b)))
      (congrArg (Nat.multinomial univ) (funext hmarg))
  -- counting parameters
  set SP := Nat.size (∏ a, Nat.multinomial univ (fun b => f (a, b))) with hSP
  set PARAM := 2 * Nat.size m + 2 * Nat.size n +
    2 * (∑ ab, Nat.size (f ab)) + m * n + cProj with hPARAM
  set S := Nat.size (N + 1) with hS
  have hgle : ∀ v, g v ≤ N := by
    intro v
    calc g v ≤ ∑ u, g u := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      _ = N := hsumg
  have hsumsize : ∑ ab, Nat.size (f ab) ≤ n * Nat.size N := by
    have hzero : ∀ ab, (∀ v, psi v ≠ ab) → Nat.size (f ab) = 0 := by
      intro ab hab
      rw [hf0 ab hab]
      simp
    calc ∑ ab, Nat.size (f ab) = ∑ v, Nat.size (f (psi v)) :=
          sum_eq_sum_comp_of_zero_off_range psi hpsiInj _ hzero
      _ = ∑ v, Nat.size (g v) := Finset.sum_congr rfl (fun v _ => by rw [hfpsi v])
      _ ≤ ∑ _v : A, Nat.size N :=
          Finset.sum_le_sum (fun v _ => Nat.size_le_size (hgle v))
      _ = n * Nat.size N := by rw [hn]; simp
  -- complexity chain
  have hfst : w.map Prod.fst = W.map pi := by
    rw [hw, List.map_map]
    rfl
  have hww : finiteWordCode w =
      numericWordCode (W.map (fun v => FiniteLetterCode.encode (psi v))) := by
    rw [hw]
    unfold finiteWordCode numericWordCode
    rw [List.map_map]
    rfl
  have hyy : y = numericWordCode (W.map (FiniteLetterCode.encode : A → ℕ)) := rfl
  have h1 := hProj m n f w hwcount
  have h2 := hOut W (finiteWordCode (w.map Prod.fst))
  rw [← hww, ← hyy] at h2
  have hcondy : condK V y x ≤ ((SP + PARAM + cOut + c₁ : ℕ) : ENat) := by
    calc condK V y x ≤ condK V y (finiteWordCode (W.map pi)) + (c₁ : ENat) := h₁ W y
      _ = condK V y (finiteWordCode (w.map Prod.fst)) + (c₁ : ENat) := by rw [hfst]
      _ ≤ (condK V (finiteWordCode w) (finiteWordCode (w.map Prod.fst)) +
            (cOut : ENat)) + (c₁ : ENat) := by gcongr
      _ ≤ (((SP + PARAM : ℕ) : ENat) + (cOut : ENat)) + (c₁ : ENat) := by
            gcongr
            refine le_trans h1 (le_of_eq ?_)
            norm_cast
            rw [hPARAM, hSP]
            ring
      _ = ((SP + PARAM + cOut + c₁ : ℕ) : ENat) := by push_cast; ring
  obtain ⟨kx, hkx⟩ := exists_plainComplexityValue V hV x
  obtain ⟨kyx, hkyx⟩ := exists_plainConditionalComplexityValue V hV y x
  obtain ⟨kxy, hkxy⟩ := exists_plainComplexityValue V hV (pairCode x y)
  have hkyx_le : kyx ≤ SP + PARAM + cOut + c₁ := by
    have hcast : (kyx : ENat) ≤ ((SP + PARAM + cOut + c₁ : ℕ) : ENat) := by
      rw [← hkyx]; exact hcondy
    exact_mod_cast hcast
  have hchain : kxy ≤ kx + kyx + logSlack cChain (kxy + 1) :=
    hChain x y kx kyx kxy hkx hkyx hkxy
  have hkW_le : kW ≤ kxy + cRight := by
    have h := hRight x y
    rw [hvalue, pairPlainK, hkxy] at h
    exact_mod_cast h
  have hkxy_le : kxy ≤ kW + c₂ := by
    have h := h₂ W
    rw [← hx, ← hy, hkxy, hvalue] at h
    exact_mod_cast h
  have hkW_up : kW ≤ c₃ * N + c₃ * S + c₃ := by
    rw [hS]
    exact hkW_up'
  have hmax : Nat.size (Nat.multinomial univ g) ≤ kW + 1 := by
    unfold histogramTypeLog at hmaximal
    exact_mod_cast hmaximal
  have hbinpos : 1 ≤ Nat.multinomial univ hist := Nat.multinomial_pos _ _
  have hprodpos : 1 ≤ ∏ a, Nat.multinomial univ (fun b => f (a, b)) :=
    Finset.prod_pos (fun a _ => Nat.multinomial_pos _ _)
  have hsizes : Nat.size (Nat.multinomial univ hist) + SP ≤
      Nat.size (Nat.multinomial univ hist *
        ∏ a, Nat.multinomial univ (fun b => f (a, b))) + 1 :=
    size_add_size_le_size_mul_succ hbinpos hprodpos
  rw [← hsplit] at hsizes
  have hkey : Nat.size (Nat.multinomial univ hist) + SP ≤ kW + 2 := by omega
  -- the logarithmic slack of the chain rule
  have hkxy1 : kxy + 1 ≤ gamma * (N + 1) := by
    have hSN : S ≤ N + 1 := by
      rw [hS]
      exact size_le_self (N + 1)
    have hexp : gamma * (N + 1) = 3 * c₃ * (N + 1) + (c₂ + 1) * (N + 1) := by
      rw [hgamma]; ring
    have h1' : c₃ * N ≤ c₃ * (N + 1) := Nat.mul_le_mul_left _ (Nat.le_succ N)
    have h2' : c₃ * S ≤ c₃ * (N + 1) := Nat.mul_le_mul_left _ hSN
    have h3' : c₃ ≤ c₃ * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h4' : c₂ + 1 ≤ (c₂ + 1) * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h5' : 3 * c₃ * (N + 1) = 3 * (c₃ * (N + 1)) := by ring
    omega
  have hlogb : logSlack cChain (kxy + 1) ≤ cChain * (Nat.size gamma + S) + cChain := by
    have hsize1 : Nat.size (kxy + 1) ≤ Nat.size gamma + S := by
      calc Nat.size (kxy + 1) ≤ Nat.size (gamma * (N + 1)) := Nat.size_le_size hkxy1
        _ ≤ Nat.size gamma + Nat.size (N + 1) := size_mul_le _ _
        _ = Nat.size gamma + S := by rw [hS]
    unfold logSlack
    rw [Nat.size_eq_bits_len]
    have := Nat.mul_le_mul_left cChain hsize1
    omega
  have hsizeN : Nat.size N ≤ S := by
    rw [hS]
    exact Nat.size_le_size (Nat.le_succ N)
  have hPARAMb : PARAM ≤ 2 * n * S +
      (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) := by
    have h1' : 2 * (∑ ab, Nat.size (f ab)) ≤ 2 * n * S := by
      calc 2 * (∑ ab, Nat.size (f ab)) ≤ 2 * (n * Nat.size N) := by omega
        _ ≤ 2 * n * S := by
            rw [mul_assoc]
            exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n hsizeN)
    rw [hPARAM]
    omega
  have hgoalNat : Nat.size (Nat.multinomial univ hist) ≤ kx + logSlack C (N + 1) := by
    have hlog : logSlack C (N + 1) = C * S + C := by
      unfold logSlack
      rw [hS, Nat.size_eq_bits_len]
    have hCbig : 2 * n * S + (2 * Nat.size m + 2 * Nat.size n + m * n + cProj) +
        cOut + c₁ + (cChain * (Nat.size gamma + S) + cChain) + cRight + 2 ≤ C * S + C := by
      have hA : (2 * n + cChain) * S ≤ C * S :=
        Nat.mul_le_mul_right _ (by rw [hC]; omega)
      have hB : 2 * Nat.size m + 2 * Nat.size n + m * n + cProj + cOut + c₁ +
          cRight + 2 + cChain * Nat.size gamma + cChain ≤ C := by
        rw [hC]; omega
      have hdist : (2 * n + cChain) * S = 2 * n * S + cChain * S := by ring
      have hdist2 : cChain * (Nat.size gamma + S) =
          cChain * Nat.size gamma + cChain * S := by ring
      omega
    rw [hlog]
    omega
  rw [hkx]
  have : (histogramTypeLog hist : ENat) ≤ ((kx + logSlack C (N + 1) : ℕ) : ENat) := by
    unfold histogramTypeLog
    exact_mod_cast hgoalNat
  calc (histogramTypeLog hist : ENat) ≤ ((kx + logSlack C (N + 1) : ℕ) : ENat) := this
    _ = (kx : ENat) + (logSlack C (N + 1) : ENat) := by push_cast; ring

end Kolmogorov
