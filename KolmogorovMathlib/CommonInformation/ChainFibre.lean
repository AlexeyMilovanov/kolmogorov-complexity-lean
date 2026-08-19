import KolmogorovMathlib.CommonInformation.ChainHistogram
import KolmogorovMathlib.CommonInformation.FixedHistogramRank
import KolmogorovMathlib.CommonInformation.FixedHistogramProjectionParams
import KolmogorovMathlib.CommonInformation.PlainCoding
import KolmogorovMathlib.CommonInformation.PlainSymmetry
import KolmogorovMathlib.CommonInformation.Splitting
import KolmogorovMathlib.CommonInformation.TypeBounds

/-!
# Alphabet recoding tools for chain fibre arguments

The fibre (conditional) counting bound
`condK_fixedHistogramWord_given_projection_le_add_params` is stated for words
over an executable product alphabet `Fin m × Fin n`, while the chain sample of
SUV Exercise 316 lives over `Fin (2*k+2) → Bool` and its coordinate projections
are *raw bit strings*.  This file supplies the missing glue:

* `exists_natTable` — a finite alphabet recoding is a fixed lookup table;
* `recodeWordCode`, `bitProjWord` — computable letter-wise recodings of the
  numeric word code, together with their evaluation lemmas;
* `condK_numericWord_recode_le`, `condK_numericWord_cond_recode_le`,
  `condK_boolWord_cond_le`, `plainK_pairCode_boolProj_le` — the resulting
  `O(1)` complexity transfers;
* `multinomial_le_pow_card_fin`, `size_add_size_le_size_mul_succ`,
  `multinomial_fiber_factorization_left` — the counting arithmetic used to turn
  a fibre factorisation into a two-sided binary-size statement.
-/

namespace Kolmogorov

open Finset

/-! ### Counting arithmetic -/

/-- The number of words of a given length over `Fin m`. -/
theorem length_allWords (m n : ℕ) : (allWords m n).length = m ^ n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    rw [allWords, List.length_flatMap]
    simp [ih, pow_succ, Nat.mul_comm]

/-- A multinomial coefficient counts words, hence is at most the alphabet size
raised to the word length. -/
theorem multinomial_le_pow_card_fin {m : ℕ} (f : Fin m → ℕ) :
    Nat.multinomial univ f ≤ m ^ (∑ i, f i) := by
  rw [← length_fixedHistogramWords f, ← length_allWords m (∑ i, f i)]
  exact List.length_filter_le _ _

/-- Binary sizes are subadditive under multiplication up to one bit. -/
theorem size_add_size_le_size_mul_succ {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.size a + Nat.size b ≤ Nat.size (a * b) + 1 := by
  have hsa : 0 < Nat.size a := Nat.size_pos.mpr ha
  have hsb : 0 < Nat.size b := Nat.size_pos.mpr hb
  have h1 : 2 ^ (Nat.size a - 1) ≤ a := Nat.lt_size.mp (by omega)
  have h2 : 2 ^ (Nat.size b - 1) ≤ b := Nat.lt_size.mp (by omega)
  have h3 : 2 ^ (Nat.size a - 1 + (Nat.size b - 1)) ≤ a * b := by
    rw [pow_add]; exact Nat.mul_le_mul h1 h2
  have h4 : Nat.size a - 1 + (Nat.size b - 1) < Nat.size (a * b) :=
    Nat.lt_size.mpr h3
  omega

/-- The binary size of a natural number is at most the number itself. -/
theorem size_le_self (n : ℕ) : Nat.size n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    by_contra hcon
    push Not at hcon
    have hpow : 2 ^ n ≤ 2 ^ (Nat.size n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by
      have : 0 < Nat.size n := Nat.size_pos.mpr hn
      omega)
    have h3 : n < 2 ^ n := Nat.lt_two_pow_self
    omega

/-- Binary size is subadditive under multiplication. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h1 : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have h2 : b < 2 ^ Nat.size b := Nat.lt_size_self b
  have hlt : a * b < 2 ^ (Nat.size a + Nat.size b) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
  exact Nat.size_le.mpr hlt

/-- Multinomial coefficients are invariant under reindexing by an equivalence. -/
theorem multinomial_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℕ) :
    Nat.multinomial Finset.univ (f ∘ e) = Nat.multinomial Finset.univ f := by
  have hsum : ∑ x : A, (f ∘ e) x = ∑ y : B, f y := Equiv.sum_comp e f
  have hprod : ∏ x : A, Nat.factorial ((f ∘ e) x) =
      ∏ y : B, Nat.factorial (f y) :=
    Equiv.prod_comp e (fun y => Nat.factorial (f y))
  unfold Nat.multinomial
  rw [hsum, hprod]

/-- The lower power associated with the binary size of `x` is at most `x`. -/
theorem size_pred_pow_le {x : ℕ} (hx : 2 ≤ x) : 2 ^ (Nat.size x - 1) ≤ x := by
  have h1 : ¬ (x < 2 ^ (Nat.size x - 1)) := by
    intro h2
    have h3 : Nat.size x ≤ Nat.size x - 1 := Nat.size_le.mpr h2
    have h4 : 2 ≤ Nat.size x := by
      have : 0 < x := by omega
      have h5 := Nat.size_pos.mpr this
      have : ¬ (x < 2 ^ 1) := by intro h; omega
      have h6 := mt Nat.size_le.mp this
      omega
    omega
  exact Nat.le_of_not_lt h1

/-- Fibre factorisation of the multinomial coefficient along the *first*
coordinate. -/
theorem multinomial_fiber_factorization_left {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℕ) :
    Nat.multinomial univ f =
      Nat.multinomial univ (fun a => ∑ b, f (a, b)) *
      ∏ a ∈ univ, Nat.multinomial univ (fun b => f (a, b)) := by
  have h := multinomial_fiber_factorization (fun p : B × A => f (p.2, p.1))
  have he : Nat.multinomial univ (fun p : B × A => f (p.2, p.1)) =
      Nat.multinomial univ f := by
    have := multinomial_comp_equiv (Equiv.prodComm B A) f
    exact this
  rw [he] at h
  simpa using h

/-- **Method-of-types entropy bound.**  A multinomial coefficient times the
product of its own entries raised to themselves is at most the total mass raised
to itself.  This is the single term `k = g` of the multinomial theorem evaluated
at `f = g`. -/
theorem multinomial_mul_prod_pow_self_le {α : Type*} [Fintype α]
    (g : α → ℕ) :
    Nat.multinomial Finset.univ g * ∏ i, g i ^ g i ≤ (∑ i, g i) ^ (∑ i, g i) := by
  classical
  set n := ∑ i, g i with hn
  have hmem : g ∈ Finset.piAntidiag (Finset.univ : Finset α) n := by
    simp [Finset.mem_piAntidiag, ← hn]
  have hthm := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset α)
    (fun i => g i) n
  rw [← hn] at hthm
  calc Nat.multinomial Finset.univ g * ∏ i, g i ^ g i
      ≤ ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
          Nat.multinomial Finset.univ k * ∏ i, g i ^ k i :=
        Finset.single_le_sum
          (f := fun k => Nat.multinomial Finset.univ k * ∏ i, g i ^ k i)
          (fun _ _ => Nat.zero_le _) hmem
    _ = n ^ n := hthm.symm

/-- Multiplying by a power of two shifts the binary size. -/
theorem size_mul_two_pow {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    Nat.size (m * 2 ^ n) = Nat.size m + n := by
  rw [← Nat.shiftLeft_eq, Nat.size_shiftLeft hm]

/-! ### Finite recoding tables -/

/-- Any recoding of a finite alphabet is realised by a fixed lookup table. -/
theorem exists_natTable {A : Type*} [Finite A] (c1 c2 : A → ℕ)
    (h1 : Function.Injective c1) :
    ∃ tab : List ℕ, ∀ a : A, tab.getD (c1 a) 0 = c2 a := by
  classical
  cases nonempty_fintype A with | intro instA =>
  set g : ℕ → ℕ := fun i => if h : ∃ a : A, c1 a = i then c2 h.choose else 0 with hg
  set M := (Finset.univ.sup (fun a : A => c1 a)) + 1 with hM
  refine ⟨(List.range M).map g, fun a => ?_⟩
  have hsup := Finset.le_sup (f := fun a : A => c1 a) (Finset.mem_univ a)
  have hlt : c1 a < M := by omega
  have hlen : ((List.range M).map g).length = M := by simp
  rw [List.getD_eq_getElem _ _ (by omega)]
  have hgi : ((List.range M).map g)[c1 a] =
      g ((List.range M)[c1 a]'(by simpa using hlt)) := by simp
  rw [hgi]
  have hr : (List.range M)[c1 a]'(by simpa using hlt) = c1 a := by simp
  rw [hr, hg]
  have hex : ∃ b : A, c1 b = c1 a := ⟨a, rfl⟩
  simp only [dif_pos hex]
  exact congrArg c2 (h1 hex.choose_spec)

/-! ### Computable letter-wise recodings -/

/-- The numeric word carried by a `numericWordCode` string. -/
noncomputable def decodeNatWord (z : BitString) : List ℕ :=
  ((Encodable.decode (bitsToNat z) : Option (List ℕ))).getD []

theorem decodeNatWord_primrec : Primrec decodeNatWord := by
  unfold decodeNatWord
  exact Primrec.option_getD.comp (Primrec.decode.comp bitsToNat_primrec)
    (Primrec.const [])

@[simp]
theorem decodeNatWord_numericWordCode (l : List ℕ) :
    decodeNatWord (numericWordCode l) = l := by
  unfold decodeNatWord numericWordCode
  rw [bitsToNat_bits, Encodable.encodek]
  rfl

/-- Letter-wise recoding of a numeric word code through a lookup table. -/
noncomputable def recodeWordCode (tab : List ℕ) (z : BitString) : BitString :=
  numericWordCode ((decodeNatWord z).map (fun x => tab.getD x 0))

theorem recodeWordCode_computable (tab : List ℕ) : Computable (recodeWordCode tab) := by
  unfold recodeWordCode
  have h4 : Primrec (fun x : ℕ => tab.getD x 0) :=
    (Primrec.list_getD 0).comp (Primrec.const tab) Primrec.id
  exact (numericWordCode_primrec.comp
    (Primrec.list_map decodeNatWord_primrec ((h4.comp Primrec.snd).to₂))).to_comp

theorem recodeWordCode_numericWordCode (tab : List ℕ) (l : List ℕ) :
    recodeWordCode tab (numericWordCode l) =
      numericWordCode (l.map fun x => tab.getD x 0) := by
  unfold recodeWordCode
  rw [decodeNatWord_numericWordCode]

/-- Letter-wise binary projection of a numeric word code through a lookup
table. -/
noncomputable def bitProjWord (tab : List ℕ) (z : BitString) : BitString :=
  (decodeNatWord z).map (fun x => tab.getD x 0 == 1)

theorem bitProjWord_computable (tab : List ℕ) : Computable (bitProjWord tab) := by
  unfold bitProjWord
  have h4 : Primrec (fun x : ℕ => tab.getD x 0 == 1) := by
    have h : PrimrecPred (fun x : ℕ => tab.getD x 0 = 1) :=
      Primrec.eq.comp ((Primrec.list_getD 0).comp (Primrec.const tab) Primrec.id)
        (Primrec.const 1)
    obtain ⟨_, h'⟩ := h
    exact h'.of_eq (fun x => by apply Bool.eq_iff_iff.mpr; simp [beq_iff_eq])
  exact (Primrec.list_map decodeNatWord_primrec ((h4.comp Primrec.snd).to₂)).to_comp

theorem bitProjWord_numericWordCode (tab : List ℕ) (l : List ℕ) :
    bitProjWord tab (numericWordCode l) = l.map (fun x => tab.getD x 0 == 1) := by
  unfold bitProjWord
  rw [decodeNatWord_numericWordCode]

/-- The two bit projections obtained by table lookup from one numeric word
code, packaged with the chapter's canonical pair code. -/
noncomputable def pairBitProjWords (tab₁ tab₂ : List ℕ) (z : BitString) : BitString :=
  pairCode (bitProjWord tab₁ z) (bitProjWord tab₂ z)

theorem pairBitProjWords_computable (tab₁ tab₂ : List ℕ) :
    Computable (pairBitProjWords tab₁ tab₂) := by
  unfold pairBitProjWords
  have hpair : Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  exact hpair.comp (bitProjWord_computable tab₁) (bitProjWord_computable tab₂)

/-- Three bit projections obtained from one numeric word code, using the nested
pair convention of `chainTripleAt`. -/
noncomputable def tripleBitProjWords (tab₁ tab₂ tab₃ : List ℕ)
    (z : BitString) : BitString :=
  pairCode (pairBitProjWords tab₁ tab₂ z) (bitProjWord tab₃ z)

theorem tripleBitProjWords_computable (tab₁ tab₂ tab₃ : List ℕ) :
    Computable (tripleBitProjWords tab₁ tab₂ tab₃) := by
  unfold tripleBitProjWords
  have hpair : Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  exact hpair.comp (pairBitProjWords_computable tab₁ tab₂)
    (bitProjWord_computable tab₃)

/-- The bit word obtained from a numeric word code by a table lookup, paired
with the code itself. -/
noncomputable def pairSelfBitProj (tab : List ℕ) (z : BitString) : BitString :=
  pairCode (bitProjWord tab z) z

theorem pairSelfBitProj_computable (tab : List ℕ) :
    Computable (pairSelfBitProj tab) := by
  unfold pairSelfBitProj
  have hpair : Computable₂ (fun x y : BitString => pairCode x y) := pairCode_computable
  exact hpair.comp (bitProjWord_computable tab) Computable.id

/-! ### Complexity transfers -/

/-- Replacing the *condition* by something computable from it can only help. -/
theorem condK_cond_map_le (V : Map) (hV : isOptimalConditional V)
    (s : BitString → BitString) (hs : Computable s) :
    ∃ c : ℕ, ∀ x y : BitString, condK V x y ≤ condK V x (s y) + (c : ENat) := by
  let D : Map := fun pr => V (pr.1, s pr.2)
  have hD : isDecompressor D :=
    hV.1.comp (Computable.pair Computable.fst (hs.comp Computable.snd))
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun x y => ?_⟩
  refine le_trans (hc x y) ?_
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, hp, rfl⟩

/-- Recoding the alphabet of the described word costs `O(1)`. -/
theorem condK_numericWord_recode_le (V : Map) (hV : isOptimalConditional V)
    {A : Type*} [Finite A] (c1 c2 : A → ℕ) (h1 : Function.Injective c1) :
    ∃ c : ℕ, ∀ (w : List A) (y : BitString),
      condK V (numericWordCode (w.map c2)) y ≤
        condK V (numericWordCode (w.map c1)) y + (c : ENat) := by
  obtain ⟨tab, htab⟩ := exists_natTable c1 c2 h1
  obtain ⟨c, hc⟩ := condKMapLe V hV (recodeWordCode tab) (recodeWordCode_computable tab)
  refine ⟨c, fun w y => ?_⟩
  have hval : recodeWordCode tab (numericWordCode (w.map c1)) =
      numericWordCode (w.map c2) := by
    rw [recodeWordCode_numericWordCode, List.map_map]
    congr 1
    exact List.map_congr_left (fun a _ => htab a)
  have := hc (numericWordCode (w.map c1)) y
  rwa [hval] at this

/-- Recoding the alphabet of the *condition* word costs `O(1)`. -/
theorem condK_numericWord_cond_recode_le (V : Map) (hV : isOptimalConditional V)
    {A : Type*} [Finite A] (c1 c2 : A → ℕ) (h1 : Function.Injective c1) :
    ∃ c : ℕ, ∀ (w : List A) (x : BitString),
      condK V x (numericWordCode (w.map c1)) ≤
        condK V x (numericWordCode (w.map c2)) + (c : ENat) := by
  obtain ⟨tab, htab⟩ := exists_natTable c1 c2 h1
  obtain ⟨c, hc⟩ := condK_cond_map_le V hV (recodeWordCode tab)
    (recodeWordCode_computable tab)
  refine ⟨c, fun w x => ?_⟩
  have hval : recodeWordCode tab (numericWordCode (w.map c1)) =
      numericWordCode (w.map c2) := by
    rw [recodeWordCode_numericWordCode, List.map_map]
    congr 1
    exact List.map_congr_left (fun a _ => htab a)
  have := hc x (numericWordCode (w.map c1))
  rwa [hval] at this

/-- Conditioning on a raw bit word is at least as strong as conditioning on its
numeric word code. -/
theorem condK_boolWord_cond_le (V : Map) (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x z : BitString),
      condK V z x ≤
        condK V z (numericWordCode (x.map (fun b => if b then 1 else 0))) +
          (c : ENat) := by
  have hs : Computable (fun x : BitString =>
      numericWordCode (x.map (fun b => if b then (1 : ℕ) else 0))) := by
    have hb : Primrec (fun b : Bool => if b then (1 : ℕ) else 0) :=
      Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)
    exact (numericWordCode_primrec.comp
      (Primrec.list_map Primrec.id ((hb.comp Primrec.snd).to₂))).to_comp
  obtain ⟨c, hc⟩ := condK_cond_map_le V hV _ hs
  exact ⟨c, fun x z => hc z x⟩

/-- Pairing a numeric word code with one of its letter-wise binary projections
costs `O(1)`. -/
theorem plainK_pairCode_boolProj_le (V : Map) (hV : isOptimalConditional V)
    {A : Type*} [Finite A] (c1 : A → ℕ) (h1 : Function.Injective c1)
    (g : A → Bool) :
    ∃ c : ℕ, ∀ w : List A,
      plainK V (pairCode (w.map g) (numericWordCode (w.map c1))) ≤
        plainK V (numericWordCode (w.map c1)) + (c : ENat) := by
  obtain ⟨tab, htab⟩ := exists_natTable c1 (fun a => if g a then 1 else 0) h1
  obtain ⟨c, hc⟩ := plainKMapLe V hV (pairSelfBitProj tab)
    (pairSelfBitProj_computable tab)
  refine ⟨c, fun w => ?_⟩
  have hval : pairSelfBitProj tab (numericWordCode (w.map c1)) =
      pairCode (w.map g) (numericWordCode (w.map c1)) := by
    unfold pairSelfBitProj
    congr 1
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab a]
    cases g a <;> simp
  have := hc (numericWordCode (w.map c1))
  rwa [hval] at this

/-- Recoding one aligned finite-alphabet word as the canonical pair of two
letter-wise bit projections costs only a uniform constant. -/
theorem plainK_pairCode_two_boolProjections_le (V : Map)
    (hV : isOptimalConditional V) {A : Type*} [Finite A]
    (c₁ : A → ℕ) (hc₁ : Function.Injective c₁) (g₁ g₂ : A → Bool) :
    ∃ c : ℕ, ∀ w : List A,
      plainK V (pairCode (w.map g₁) (w.map g₂)) ≤
        plainK V (numericWordCode (w.map c₁)) + (c : ENat) := by
  obtain ⟨tab₁, htab₁⟩ :=
    exists_natTable c₁ (fun a => if g₁ a then 1 else 0) hc₁
  obtain ⟨tab₂, htab₂⟩ :=
    exists_natTable c₁ (fun a => if g₂ a then 1 else 0) hc₁
  obtain ⟨c, hc⟩ := plainKMapLe V hV (pairBitProjWords tab₁ tab₂)
    (pairBitProjWords_computable tab₁ tab₂)
  refine ⟨c, fun w => ?_⟩
  have hproj₁ : bitProjWord tab₁ (numericWordCode (w.map c₁)) = w.map g₁ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₁ a]
    cases g₁ a <;> simp
  have hproj₂ : bitProjWord tab₂ (numericWordCode (w.map c₁)) = w.map g₂ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₂ a]
    cases g₂ a <;> simp
  have hval : pairBitProjWords tab₁ tab₂ (numericWordCode (w.map c₁)) =
      pairCode (w.map g₁) (w.map g₂) := by
    rw [pairBitProjWords, hproj₁, hproj₂]
  simpa only [hval] using hc (numericWordCode (w.map c₁))

/-- Recoding one aligned finite-alphabet word as the canonical nested pair of
three letter-wise bit projections costs only a uniform constant. -/
theorem plainK_pairCode_three_boolProjections_le (V : Map)
    (hV : isOptimalConditional V) {A : Type*} [Finite A]
    (c₁ : A → ℕ) (hc₁ : Function.Injective c₁) (g₁ g₂ g₃ : A → Bool) :
    ∃ c : ℕ, ∀ w : List A,
      plainK V (pairCode (pairCode (w.map g₁) (w.map g₂)) (w.map g₃)) ≤
        plainK V (numericWordCode (w.map c₁)) + (c : ENat) := by
  obtain ⟨tab₁, htab₁⟩ :=
    exists_natTable c₁ (fun a => if g₁ a then 1 else 0) hc₁
  obtain ⟨tab₂, htab₂⟩ :=
    exists_natTable c₁ (fun a => if g₂ a then 1 else 0) hc₁
  obtain ⟨tab₃, htab₃⟩ :=
    exists_natTable c₁ (fun a => if g₃ a then 1 else 0) hc₁
  obtain ⟨c, hc⟩ := plainKMapLe V hV (tripleBitProjWords tab₁ tab₂ tab₃)
    (tripleBitProjWords_computable tab₁ tab₂ tab₃)
  refine ⟨c, fun w => ?_⟩
  have hproj₁ : bitProjWord tab₁ (numericWordCode (w.map c₁)) = w.map g₁ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₁ a]
    cases g₁ a <;> simp
  have hproj₂ : bitProjWord tab₂ (numericWordCode (w.map c₁)) = w.map g₂ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₂ a]
    cases g₂ a <;> simp
  have hproj₃ : bitProjWord tab₃ (numericWordCode (w.map c₁)) = w.map g₃ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₃ a]
    cases g₃ a <;> simp
  have hval : tripleBitProjWords tab₁ tab₂ tab₃
      (numericWordCode (w.map c₁)) =
        pairCode (pairCode (w.map g₁) (w.map g₂)) (w.map g₃) := by
    rw [tripleBitProjWords, pairBitProjWords, hproj₁, hproj₂, hproj₃]
  simpa only [hval] using hc (numericWordCode (w.map c₁))

/-! ### Merging the bit words of a pair code -/

/-- The numeric word whose letters merge, position by position, the two bit
words carried by a pair code. -/
noncomputable def mergeTwoBitWordsCode (z : BitString) : BitString :=
  numericWordCode ((List.range (decodeFirst z).length).map (fun t =>
    2 * (if (decodeFirst z).getD t false then 1 else 0) +
      (if (decodeSecond z).getD t false then 1 else 0)))

/-- The numeric word whose letters merge, position by position, the three bit
words carried by a nested pair code. -/
noncomputable def mergeThreeBitWordsCode (z : BitString) : BitString :=
  numericWordCode ((List.range (decodeFirst (decodeFirst z)).length).map (fun t =>
    4 * (if (decodeFirst (decodeFirst z)).getD t false then 1 else 0) +
      2 * (if (decodeSecond (decodeFirst z)).getD t false then 1 else 0) +
      (if (decodeSecond z).getD t false then 1 else 0)))

private theorem primrec_boolBit :
    Primrec (fun b : Bool => if b then (1 : ℕ) else 0) :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true))
    (Primrec.const 1) (Primrec.const 0)

theorem mergeTwoBitWordsCode_computable : Computable mergeTwoBitWordsCode := by
  have hrange : Primrec (fun z : BitString => List.range (decodeFirst z).length) :=
    Primrec.list_range.comp (Primrec.list_length.comp decodeFirst_primrec')
  have hu : Primrec (fun p : BitString × ℕ => (decodeFirst p.1).getD p.2 false) :=
    (Primrec.list_getD false).comp (decodeFirst_primrec'.comp Primrec.fst) Primrec.snd
  have hv : Primrec (fun p : BitString × ℕ => (decodeSecond p.1).getD p.2 false) :=
    (Primrec.list_getD false).comp (decodeSecond_primrec'.comp Primrec.fst) Primrec.snd
  have hbody : Primrec (fun p : BitString × ℕ =>
      2 * (if (decodeFirst p.1).getD p.2 false then 1 else 0) +
        (if (decodeSecond p.1).getD p.2 false then 1 else 0)) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (primrec_boolBit.comp hu))
      (primrec_boolBit.comp hv)
  exact (numericWordCode_primrec.comp (Primrec.list_map hrange hbody.to₂)).to_comp

theorem mergeThreeBitWordsCode_computable : Computable mergeThreeBitWordsCode := by
  have hff : Primrec (fun z : BitString => decodeFirst (decodeFirst z)) :=
    decodeFirst_primrec'.comp decodeFirst_primrec'
  have hsf : Primrec (fun z : BitString => decodeSecond (decodeFirst z)) :=
    decodeSecond_primrec'.comp decodeFirst_primrec'
  have hrange : Primrec
      (fun z : BitString => List.range (decodeFirst (decodeFirst z)).length) :=
    Primrec.list_range.comp (Primrec.list_length.comp hff)
  have hu : Primrec (fun p : BitString × ℕ =>
      (decodeFirst (decodeFirst p.1)).getD p.2 false) :=
    (Primrec.list_getD false).comp (hff.comp Primrec.fst) Primrec.snd
  have hv : Primrec (fun p : BitString × ℕ =>
      (decodeSecond (decodeFirst p.1)).getD p.2 false) :=
    (Primrec.list_getD false).comp (hsf.comp Primrec.fst) Primrec.snd
  have hw : Primrec (fun p : BitString × ℕ => (decodeSecond p.1).getD p.2 false) :=
    (Primrec.list_getD false).comp (decodeSecond_primrec'.comp Primrec.fst) Primrec.snd
  have hbody : Primrec (fun p : BitString × ℕ =>
      4 * (if (decodeFirst (decodeFirst p.1)).getD p.2 false then 1 else 0) +
        2 * (if (decodeSecond (decodeFirst p.1)).getD p.2 false then 1 else 0) +
        (if (decodeSecond p.1).getD p.2 false then 1 else 0)) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (primrec_boolBit.comp hu))
        (Primrec.nat_mul.comp (Primrec.const 2) (primrec_boolBit.comp hv)))
      (primrec_boolBit.comp hw)
  exact (numericWordCode_primrec.comp (Primrec.list_map hrange hbody.to₂)).to_comp

/-- Reading two aligned projections of a word position by position. -/
theorem range_map_getD_two {A : Type*} (W : List A) (g₁ g₂ : A → Bool)
    (F : Bool → Bool → ℕ) :
    (List.range W.length).map (fun t =>
        F ((W.map g₁).getD t false) ((W.map g₂).getD t false)) =
      W.map (fun a => F (g₁ a) (g₂ a)) := by
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range] at *
    rw [List.getD_eq_getElem _ _ (by simpa using h2),
      List.getD_eq_getElem _ _ (by simpa using h2)]
    simp

/-- Reading three aligned projections of a word position by position. -/
theorem range_map_getD_three {A : Type*} (W : List A) (g₁ g₂ g₃ : A → Bool)
    (F : Bool → Bool → Bool → ℕ) :
    (List.range W.length).map (fun t =>
        F ((W.map g₁).getD t false) ((W.map g₂).getD t false)
          ((W.map g₃).getD t false)) =
      W.map (fun a => F (g₁ a) (g₂ a) (g₃ a)) := by
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range] at *
    rw [List.getD_eq_getElem _ _ (by simpa using h2),
      List.getD_eq_getElem _ _ (by simpa using h2),
      List.getD_eq_getElem _ _ (by simpa using h2)]
    simp

theorem mergeTwoBitWordsCode_pairCode {A : Type*} (W : List A) (g₁ g₂ : A → Bool) :
    mergeTwoBitWordsCode (pairCode (W.map g₁) (W.map g₂)) =
      numericWordCode (W.map (fun v =>
        2 * (if g₁ v then 1 else 0) + (if g₂ v then 1 else 0))) := by
  unfold mergeTwoBitWordsCode
  rw [decodeFirst_pairCode, decodeSecond_pairCode, List.length_map]
  rw [range_map_getD_two W g₁ g₂
    (fun a b => 2 * (if a then 1 else 0) + (if b then 1 else 0))]

theorem mergeThreeBitWordsCode_pairCode {A : Type*} (W : List A)
    (g₁ g₂ g₃ : A → Bool) :
    mergeThreeBitWordsCode
        (pairCode (pairCode (W.map g₁) (W.map g₂)) (W.map g₃)) =
      numericWordCode (W.map (fun v =>
        4 * (if g₁ v then 1 else 0) + 2 * (if g₂ v then 1 else 0) +
          (if g₃ v then 1 else 0))) := by
  unfold mergeThreeBitWordsCode
  rw [decodeFirst_pairCode, decodeSecond_pairCode, decodeFirst_pairCode,
    decodeSecond_pairCode, List.length_map]
  rw [range_map_getD_three W g₁ g₂ g₃
    (fun a b c => 4 * (if a then 1 else 0) + 2 * (if b then 1 else 0) +
      (if c then 1 else 0))]

/-- Conditioning on the canonical pair of two aligned bit projections is at
least as strong as conditioning on any numeric recoding of the aligned
two-letter word, up to a uniform constant. -/
theorem condK_cond_pairCode_two_boolWords_le (V : Map) (hV : isOptimalConditional V)
    {A : Type*} (g₁ g₂ : A → Bool) (d : Bool × Bool → ℕ) :
    ∃ c : ℕ, ∀ (W : List A) (z : BitString),
      condK V z (pairCode (W.map g₁) (W.map g₂)) ≤
        condK V z (numericWordCode (W.map (fun v => d (g₁ v, g₂ v)))) +
          (c : ENat) := by
  obtain ⟨cMerge, hMerge⟩ :=
    condK_cond_map_le V hV mergeTwoBitWordsCode mergeTwoBitWordsCode_computable
  have hinj : Function.Injective
      (fun p : Bool × Bool => 2 * (if p.1 then 1 else 0) + (if p.2 then 1 else 0)) := by
    decide
  obtain ⟨cRe, hRe⟩ := condK_numericWord_cond_recode_le V hV
    (fun p : Bool × Bool => 2 * (if p.1 then 1 else 0) + (if p.2 then 1 else 0))
    d hinj
  refine ⟨cMerge + cRe, fun W z => ?_⟩
  have hmap₁ : (W.map (fun v => (g₁ v, g₂ v))).map
      (fun p : Bool × Bool => 2 * (if p.1 then 1 else 0) + (if p.2 then 1 else 0)) =
      W.map (fun v => 2 * (if g₁ v then 1 else 0) + (if g₂ v then 1 else 0)) := by
    rw [List.map_map]
    rfl
  have hmap₂ : (W.map (fun v => (g₁ v, g₂ v))).map d =
      W.map (fun v => d (g₁ v, g₂ v)) := by
    rw [List.map_map]
    rfl
  have h1 := hMerge z (pairCode (W.map g₁) (W.map g₂))
  rw [mergeTwoBitWordsCode_pairCode W g₁ g₂] at h1
  have h2 := hRe (W.map (fun v => (g₁ v, g₂ v))) z
  rw [hmap₁, hmap₂] at h2
  calc condK V z (pairCode (W.map g₁) (W.map g₂))
      ≤ condK V z (numericWordCode
          (W.map (fun v => 2 * (if g₁ v then 1 else 0) + (if g₂ v then 1 else 0)))) +
            (cMerge : ENat) := h1
    _ ≤ (condK V z (numericWordCode (W.map (fun v => d (g₁ v, g₂ v)))) + (cRe : ENat)) +
          (cMerge : ENat) := by gcongr
    _ = condK V z (numericWordCode (W.map (fun v => d (g₁ v, g₂ v)))) +
          ((cMerge + cRe : ℕ) : ENat) := by push_cast; ring

/-- Conditioning on the canonical nested pair of three aligned bit projections
is at least as strong as conditioning on any numeric recoding of the aligned
three-letter word, up to a uniform constant. -/
theorem condK_cond_pairCode_three_boolWords_le (V : Map)
    (hV : isOptimalConditional V) {A : Type*} (g₁ g₂ g₃ : A → Bool)
    (d : (Bool × Bool) × Bool → ℕ) :
    ∃ c : ℕ, ∀ (W : List A) (z : BitString),
      condK V z (pairCode (pairCode (W.map g₁) (W.map g₂)) (W.map g₃)) ≤
        condK V z (numericWordCode (W.map (fun v => d ((g₁ v, g₂ v), g₃ v)))) +
          (c : ENat) := by
  obtain ⟨cMerge, hMerge⟩ :=
    condK_cond_map_le V hV mergeThreeBitWordsCode mergeThreeBitWordsCode_computable
  have hinj : Function.Injective
      (fun p : (Bool × Bool) × Bool =>
        4 * (if p.1.1 then 1 else 0) + 2 * (if p.1.2 then 1 else 0) +
          (if p.2 then 1 else 0)) := by
    decide
  obtain ⟨cRe, hRe⟩ := condK_numericWord_cond_recode_le V hV
    (fun p : (Bool × Bool) × Bool =>
      4 * (if p.1.1 then 1 else 0) + 2 * (if p.1.2 then 1 else 0) +
        (if p.2 then 1 else 0))
    d hinj
  refine ⟨cMerge + cRe, fun W z => ?_⟩
  have hmap₁ : (W.map (fun v => ((g₁ v, g₂ v), g₃ v))).map
      (fun p : (Bool × Bool) × Bool =>
        4 * (if p.1.1 then 1 else 0) + 2 * (if p.1.2 then 1 else 0) +
          (if p.2 then 1 else 0)) =
      W.map (fun v => 4 * (if g₁ v then 1 else 0) + 2 * (if g₂ v then 1 else 0) +
        (if g₃ v then 1 else 0)) := by
    rw [List.map_map]
    rfl
  have hmap₂ : (W.map (fun v => ((g₁ v, g₂ v), g₃ v))).map d =
      W.map (fun v => d ((g₁ v, g₂ v), g₃ v)) := by
    rw [List.map_map]
    rfl
  have h1 := hMerge z (pairCode (pairCode (W.map g₁) (W.map g₂)) (W.map g₃))
  rw [mergeThreeBitWordsCode_pairCode W g₁ g₂ g₃] at h1
  have h2 := hRe (W.map (fun v => ((g₁ v, g₂ v), g₃ v))) z
  rw [hmap₁, hmap₂] at h2
  calc condK V z (pairCode (pairCode (W.map g₁) (W.map g₂)) (W.map g₃))
      ≤ condK V z (numericWordCode
          (W.map (fun v => 4 * (if g₁ v then 1 else 0) +
            2 * (if g₂ v then 1 else 0) + (if g₃ v then 1 else 0)))) +
            (cMerge : ENat) := h1
    _ ≤ (condK V z (numericWordCode (W.map (fun v => d ((g₁ v, g₂ v), g₃ v)))) +
          (cRe : ENat)) + (cMerge : ENat) := by gcongr
    _ = condK V z (numericWordCode (W.map (fun v => d ((g₁ v, g₂ v), g₃ v)))) +
          ((cMerge + cRe : ℕ) : ENat) := by push_cast; ring

/-- Pairing a numeric word code with anything computable from it costs `O(1)`. -/
theorem plainK_pairCode_map_self_le (V : Map) (hV : isOptimalConditional V)
    (s : BitString → BitString) (hs : Computable s) :
    ∃ c : ℕ, ∀ z : BitString,
      plainK V (pairCode (s z) z) ≤ plainK V z + (c : ENat) := by
  have hpair : Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  obtain ⟨c, hc⟩ := plainKMapLe V hV (fun z => pairCode (s z) z)
    (hpair.comp hs Computable.id)
  exact ⟨c, fun z => hc z⟩

/-- Pairing a numeric word code with the canonical pair of two of its
letter-wise bit projections costs `O(1)`. -/
theorem plainK_pairCode_two_boolProjections_self_le (V : Map)
    (hV : isOptimalConditional V) {A : Type*} [Finite A]
    (c₁ : A → ℕ) (hc₁ : Function.Injective c₁) (g₁ g₂ : A → Bool) :
    ∃ c : ℕ, ∀ w : List A,
      plainK V (pairCode (pairCode (w.map g₁) (w.map g₂))
          (numericWordCode (w.map c₁))) ≤
        plainK V (numericWordCode (w.map c₁)) + (c : ENat) := by
  obtain ⟨tab₁, htab₁⟩ :=
    exists_natTable c₁ (fun a => if g₁ a then 1 else 0) hc₁
  obtain ⟨tab₂, htab₂⟩ :=
    exists_natTable c₁ (fun a => if g₂ a then 1 else 0) hc₁
  obtain ⟨c, hc⟩ := plainK_pairCode_map_self_le V hV (pairBitProjWords tab₁ tab₂)
    (pairBitProjWords_computable tab₁ tab₂)
  refine ⟨c, fun w => ?_⟩
  have hproj₁ : bitProjWord tab₁ (numericWordCode (w.map c₁)) = w.map g₁ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₁ a]
    cases g₁ a <;> simp
  have hproj₂ : bitProjWord tab₂ (numericWordCode (w.map c₁)) = w.map g₂ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₂ a]
    cases g₂ a <;> simp
  have hval : pairBitProjWords tab₁ tab₂ (numericWordCode (w.map c₁)) =
      pairCode (w.map g₁) (w.map g₂) := by
    rw [pairBitProjWords, hproj₁, hproj₂]
  simpa only [hval] using hc (numericWordCode (w.map c₁))

/-- Pairing a numeric word code with the canonical nested pair of three of its
letter-wise bit projections costs `O(1)`. -/
theorem plainK_pairCode_three_boolProjections_self_le (V : Map)
    (hV : isOptimalConditional V) {A : Type*} [Finite A]
    (c₁ : A → ℕ) (hc₁ : Function.Injective c₁) (g₁ g₂ g₃ : A → Bool) :
    ∃ c : ℕ, ∀ w : List A,
      plainK V (pairCode (pairCode (pairCode (w.map g₁) (w.map g₂)) (w.map g₃))
          (numericWordCode (w.map c₁))) ≤
        plainK V (numericWordCode (w.map c₁)) + (c : ENat) := by
  obtain ⟨tab₁, htab₁⟩ :=
    exists_natTable c₁ (fun a => if g₁ a then 1 else 0) hc₁
  obtain ⟨tab₂, htab₂⟩ :=
    exists_natTable c₁ (fun a => if g₂ a then 1 else 0) hc₁
  obtain ⟨tab₃, htab₃⟩ :=
    exists_natTable c₁ (fun a => if g₃ a then 1 else 0) hc₁
  obtain ⟨c, hc⟩ := plainK_pairCode_map_self_le V hV
    (tripleBitProjWords tab₁ tab₂ tab₃)
    (tripleBitProjWords_computable tab₁ tab₂ tab₃)
  refine ⟨c, fun w => ?_⟩
  have hproj₁ : bitProjWord tab₁ (numericWordCode (w.map c₁)) = w.map g₁ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₁ a]
    cases g₁ a <;> simp
  have hproj₂ : bitProjWord tab₂ (numericWordCode (w.map c₁)) = w.map g₂ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₂ a]
    cases g₂ a <;> simp
  have hproj₃ : bitProjWord tab₃ (numericWordCode (w.map c₁)) = w.map g₃ := by
    rw [bitProjWord_numericWordCode, List.map_map]
    refine List.map_congr_left (fun a _ => ?_)
    simp only [Function.comp_apply, htab₃ a]
    cases g₃ a <;> simp
  have hval : tripleBitProjWords tab₁ tab₂ tab₃ (numericWordCode (w.map c₁)) =
      pairCode (pairCode (w.map g₁) (w.map g₂)) (w.map g₃) := by
    rw [tripleBitProjWords, pairBitProjWords, hproj₁, hproj₂, hproj₃]
  simpa only [hval] using hc (numericWordCode (w.map c₁))

end Kolmogorov
