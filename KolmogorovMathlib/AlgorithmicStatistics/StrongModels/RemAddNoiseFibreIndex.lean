import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.AddNoiseFibres

/-!
# Conditional indexing inside a noise fibre

This file supplies the conditional small-fibre indexing bridge required by the
reverse direction of VS40 `rem:add-noise`.

Three ingredients are proved:

* `condK_element_via_model_condition` generalizes `condK_element_via_model` from
  a finite-set condition to an arbitrary conditioning string: an element of a
  finite set `D` costs `C(D | z) + log #D + O(log C(D | z))` bits given `z`.
* `finiteSetSndFiber_condK_le`: the set of second coordinates of the fibre of a
  finite pair model `B` over a first coordinate `x` is computable from `x` and
  a code for `B`, hence costs `C(B | [A]) + O(1)` bits given `⟨x, [A]⟩`.
* `condK_noise_via_pair_fibre` combines the two: the noise string `y` itself
  costs `C(B | [A]) + log #(fibre of B over x) + O(log N)` bits given
  `⟨x, [A]⟩`, whenever `C(B | [A]) ≤ N`.
-/

namespace Kolmogorov

open Kolmogorov.CodedFiniteDistribution

/-! ### Indexing an element of a finite model under an arbitrary condition -/

/-- Conditional two-stage coding through a finite set, with an arbitrary
conditioning string.  If the code of `D` costs at most `a` bits given `z`, then
an element of `D` costs `a` plus its exact ceiling-log ordinal and the
self-delimiting header for the first program. -/
theorem condK_element_via_model_condition
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (D : Finset BitString) (hD : D.Nonempty)
        (x z : BitString) (a : Nat),
      x ∈ D →
      condK V (codedUniformOn D hD).code z ≤ (a : ENat) →
      condK V x z ≤
        ((a + finiteSetLogCard D +
          2 * (Nat.bits a).length + c : Nat) : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (reductionModelElementDecompressor V)
    (reductionModelElementDecompressor_partrec V hV.1)
  refine ⟨cSim + 1, ?_⟩
  intro D hD x z a hxD hcond
  obtain ⟨q, hqLen, hqProd⟩ :=
    (condKLeIff V (codedUniformOn D hD).code z a).mp hcond
  change q.length ≤ a at hqLen
  set s := finiteSetLogCard D with hs
  set idx := (canonicalFinsetList D).findIdx (· == x) with hidx
  set r := chunkAddress idx s with hr
  have hidxCard : idx < D.card := by
    rw [hidx, ← length_canonicalFinsetList, List.findIdx_lt_length]
    exact ⟨x, mem_canonicalFinsetList.mpr hxD, by simp⟩
  have hidxPow : idx < 2 ^ s :=
    hidxCard.trans_le (finiteSetLogCard_spec D)
  have hrLen : r.length = s := chunkAddress_length idx s hidxPow
  have hrProd : produces reductionSetIndexDecompressor r
      (codedUniformOn D hD).code x :=
    reductionSetIndexDecompressor_produces D hD x hxD
  have hprod := reductionModelElementDecompressor_produces hqProd hrProd
  have hqBits : (Nat.bits q.length).length ≤ (Nat.bits a).length :=
    length_natBits_mono hqLen
  calc
    condK V x z
      ≤ condK (reductionModelElementDecompressor V) x z + (cSim : ENat) :=
        hSim _ _
    _ ≤ ((totalProgramPairCode q r).length : ENat) + (cSim : ENat) := by
      gcongr
      exact sInf_le ⟨totalProgramPairCode q r, hprod, rfl⟩
    _ = ((q.length + r.length +
          2 * (Nat.bits q.length).length + 1 + cSim : Nat) : ENat) := by
      rw [length_totalProgramPairCode]
      norm_cast
    _ ≤ ((a + s + 2 * (Nat.bits a).length + (cSim + 1) : Nat) : ENat) := by
      exact_mod_cast (show q.length + r.length +
        2 * (Nat.bits q.length).length + 1 + cSim ≤
          a + s + 2 * (Nat.bits a).length + (cSim + 1) by
        rw [hrLen]
        omega)

/-! ### The second-coordinate fibre of a finite pair model -/

/-- The set of second coordinates occurring in the fibre of `B` over `x`. -/
def finiteSetSndFiber (B : Finset BitString) (x : BitString) :
    Finset BitString :=
  (finiteSetFstFiber B x).image decodeSecond

theorem finiteSetFstFiber_mem
    {B : Finset BitString} {x y : BitString} (hxy : pairCode x y ∈ B) :
    pairCode x y ∈ finiteSetFstFiber B x := by
  rw [finiteSetFstFiber, Finset.mem_filter]
  exact ⟨hxy, decodeFirst_pairCode x y⟩

theorem finiteSetSndFiber_mem
    {B : Finset BitString} {x y : BitString} (hxy : pairCode x y ∈ B) :
    y ∈ finiteSetSndFiber B x := by
  rw [finiteSetSndFiber, Finset.mem_image]
  exact ⟨pairCode x y, finiteSetFstFiber_mem hxy, decodeSecond_pairCode x y⟩

theorem finiteSetSndFiber_nonempty
    {B : Finset BitString} {x y : BitString} (hxy : pairCode x y ∈ B) :
    (finiteSetSndFiber B x).Nonempty :=
  ⟨y, finiteSetSndFiber_mem hxy⟩

theorem finiteSetSndFiber_card_le (B : Finset BitString) (x : BitString) :
    (finiteSetSndFiber B x).card ≤ (finiteSetFstFiber B x).card :=
  Finset.card_image_le

/-- The second-coordinate fibre is no larger than the fibre itself. -/
theorem finiteSetSndFiber_logCard_le (B : Finset BitString) (x : BitString) :
    finiteSetLogCard (finiteSetSndFiber B x) ≤
      finiteSetLogCard (finiteSetFstFiber B x) :=
  finiteSetLogCard_mono (finiteSetSndFiber_card_le B x)

/-! ### Computing the fibre from a finite-set code and a first coordinate -/

/-- Decode a canonical finite-set code, keep the points whose first coordinate
is `x`, and canonically encode the finite set of their second coordinates. -/
noncomputable def finiteSetSndFiberCode (w x : BitString) : BitString :=
  canonicalImageCodeOfList
    ((canonicalPointListOfCode w).filterMap
      (fun z => if decodeFirst z = x then some (decodeSecond z) else none))

theorem finiteSetSndFiberCode_computable :
    Computable₂ finiteSetSndFiberCode := by
  have hlist : Primrec (fun p : BitString × BitString =>
      canonicalPointListOfCode p.1) :=
    canonicalPointListOfCode_primrec.comp Primrec.fst
  have hsel : Primrec₂ (fun (p : BitString × BitString) (z : BitString) =>
      if decodeFirst z = p.2 then some (decodeSecond z) else none) := by
    refine Primrec.ite ?_ ?_ ?_
    · exact Primrec.eq.comp (decodeFirst_primrec.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    · exact Primrec.option_some.comp (decodeSecond_primrec.comp Primrec.snd)
    · exact Primrec.const none
  exact ((canonicalImageCodeOfList_primrec.comp
    (Primrec.listFilterMap hlist hsel)).to_comp).to₂

private theorem finiteSetSndFiber_list_toFinset
    (B : Finset BitString) (x : BitString) :
    ((canonicalFinsetList B).filterMap
        (fun z => if decodeFirst z = x then some (decodeSecond z)
          else none)).toFinset =
      finiteSetSndFiber B x := by
  ext v
  simp only [List.mem_toFinset, List.mem_filterMap, finiteSetSndFiber,
    finiteSetFstFiber, Finset.mem_image, Finset.mem_filter,
    mem_canonicalFinsetList]
  constructor
  · rintro ⟨z, hz, hfz⟩
    by_cases hzx : decodeFirst z = x
    · rw [if_pos hzx] at hfz
      exact ⟨z, ⟨hz, hzx⟩, by simpa using hfz⟩
    · rw [if_neg hzx] at hfz
      exact absurd hfz (by simp)
  · rintro ⟨z, ⟨hz, hzx⟩, hv⟩
    exact ⟨z, hz, by rw [if_pos hzx, hv]⟩

theorem finiteSetSndFiberCode_codedUniformOn
    (B : Finset BitString) (hB : B.Nonempty) (x : BitString)
    (hY : (finiteSetSndFiber B x).Nonempty) :
    finiteSetSndFiberCode (codedUniformOn B hB).code x =
      (codedUniformOn (finiteSetSndFiber B x) hY).code := by
  set L := (canonicalFinsetList B).filterMap
    (fun z => if decodeFirst z = x then some (decodeSecond z) else none)
    with hL
  have hLfinset : L.toFinset = finiteSetSndFiber B x :=
    finiteSetSndFiber_list_toFinset B x
  have hLne : L.toFinset.Nonempty := by rw [hLfinset]; exact hY
  unfold finiteSetSndFiberCode
  rw [canonicalPointListOfCode_codedUniformOn]
  change canonicalImageCodeOfList L = _
  rw [canonicalImageCodeOfList_eq_codedUniformOn L hLne]
  exact codedUniformOn_code_congr hLne hY hLfinset

/-! ### The conditional cost of the fibre -/

/-- Decompressor that reads a first coordinate and an auxiliary condition from
its conditional input, runs `V` on the auxiliary condition to obtain a
finite-set code, and returns the code of the corresponding fibre. -/
noncomputable def finiteSetSndFiberCondDecompressor (V : Map) : Map :=
  fun input =>
    (V (input.1, decodeSecond input.2)).map
      (fun Bcode => finiteSetSndFiberCode Bcode (decodeFirst input.2))

theorem finiteSetSndFiberCondDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (finiteSetSndFiberCondDecompressor V) := by
  unfold finiteSetSndFiberCondDecompressor
  refine Partrec.map ?_ ?_
  · exact Partrec.comp hV
      (Computable.pair Computable.fst
        (decodeSecond_computable.comp Computable.snd))
  · exact finiteSetSndFiberCode_computable.comp Computable.snd
      (decodeFirst_computable.comp (Computable.snd.comp Computable.fst))

theorem finiteSetSndFiberCondDecompressor_produces
    {V : Map} {p cond Bcode x : BitString}
    (h : produces V p cond Bcode) :
    produces (finiteSetSndFiberCondDecompressor V) p (pairCode x cond)
      (finiteSetSndFiberCode Bcode x) := by
  unfold produces finiteSetSndFiberCondDecompressor
  simp only [decodeSecond_pairCode, decodeFirst_pairCode]
  exact (Part.mem_map_iff _).2 ⟨Bcode, h, rfl⟩

/-- **Conditional cost of the noise fibre.**  If the model `B` costs at most
`q` bits given `[A]`, then the second-coordinate fibre of `B` over `x` costs at
most `q + O(1)` bits given the pair `⟨x, [A]⟩`. -/
theorem finiteSetSndFiber_condK_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty)
        (A : Finset BitString) (hA : A.Nonempty)
        (x y : BitString) (q : Nat)
        (hY : (finiteSetSndFiber B x).Nonempty),
      pairCode x y ∈ B →
      condK V (codedUniformOn B hB).code
        (codedUniformOn A hA).code ≤ (q : ENat) →
      condK V (codedUniformOn (finiteSetSndFiber B x) hY).code
        (pairCode x (codedUniformOn A hA).code) ≤ ((q + c : Nat) : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (finiteSetSndFiberCondDecompressor V)
    (finiteSetSndFiberCondDecompressor_partrec V hV.1)
  refine ⟨cSim, fun B hB A hA x y q hY _hpair hq => ?_⟩
  obtain ⟨p, hpLen, hpProd⟩ :=
    (condKLeIff V (codedUniformOn B hB).code (codedUniformOn A hA).code q).mp hq
  change p.length ≤ q at hpLen
  have hprod := finiteSetSndFiberCondDecompressor_produces (x := x) hpProd
  rw [finiteSetSndFiberCode_codedUniformOn B hB x hY] at hprod
  calc
    condK V (codedUniformOn (finiteSetSndFiber B x) hY).code
        (pairCode x (codedUniformOn A hA).code)
      ≤ condK (finiteSetSndFiberCondDecompressor V)
          (codedUniformOn (finiteSetSndFiber B x) hY).code
          (pairCode x (codedUniformOn A hA).code) + (cSim : ENat) := hSim _ _
    _ ≤ ((p.length : ENat)) + (cSim : ENat) := by
        gcongr
        exact sInf_le ⟨p, hprod, rfl⟩
    _ ≤ ((q + cSim : Nat) : ENat) := by
        exact_mod_cast (show p.length + cSim ≤ q + cSim by omega)

/-! ### Indexing the noise string inside its fibre -/

/-- **Conditional small-fibre indexing bridge.**  If the model `B` containing
`pairCode x y` costs at most `q ≤ N` bits given `[A]`, then the noise string
`y` costs at most `q + log #(fibre of B over x) + O(log N)` bits given the pair
`⟨x, [A]⟩`. -/
theorem condK_noise_via_pair_fibre
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B : Finset BitString) (hB : B.Nonempty)
        (A : Finset BitString) (hA : A.Nonempty)
        (x y : BitString) (q N : Nat),
      pairCode x y ∈ B →
      condK V (codedUniformOn B hB).code
        (codedUniformOn A hA).code ≤ (q : ENat) →
      q ≤ N →
      condK V y (pairCode x (codedUniformOn A hA).code) ≤
        ((q + finiteSetLogCard (finiteSetFstFiber B x) +
          logSlack c N : Nat) : ENat) := by
  obtain ⟨cElem, hElem⟩ := condK_element_via_model_condition V hV
  obtain ⟨cFib, hFib⟩ := finiteSetSndFiber_condK_le V hV
  obtain ⟨cLin, hLin⟩ := logSlack_linear_bound 2 1 cFib
  refine ⟨cLin + (cFib + cElem), ?_⟩
  intro B hB A hA x y q N hpair hq hqN
  have hY : (finiteSetSndFiber B x).Nonempty := finiteSetSndFiber_nonempty hpair
  have hyY : y ∈ finiteSetSndFiber B x := finiteSetSndFiber_mem hpair
  have hcode := hFib B hB A hA x y q hY hpair hq
  have hmain := hElem (finiteSetSndFiber B x) hY y
    (pairCode x (codedUniformOn A hA).code) (q + cFib) hyY hcode
  refine hmain.trans ?_
  have hlog : finiteSetLogCard (finiteSetSndFiber B x) ≤
      finiteSetLogCard (finiteSetFstFiber B x) :=
    finiteSetSndFiber_logCard_le B x
  have hbits : 2 * (Nat.bits (q + cFib)).length + 2 ≤ logSlack cLin N := by
    have hmono : logSlack 2 (q + cFib) ≤ logSlack 2 (1 * N + cFib) :=
      logSlack_mono_right 2 (by omega)
    have hls : logSlack 2 (q + cFib) = 2 * (Nat.bits (q + cFib)).length + 2 :=
      rfl
    have := hLin N
    omega
  have habsorb : logSlack cLin N + (cFib + cElem) ≤
      logSlack (cLin + (cFib + cElem)) N :=
    logSlack_add_const_le cLin (cFib + cElem) N
  have harith :
      q + cFib + finiteSetLogCard (finiteSetSndFiber B x) +
          2 * (Nat.bits (q + cFib)).length + cElem ≤
        q + finiteSetLogCard (finiteSetFstFiber B x) +
          logSlack (cLin + (cFib + cElem)) N := by
    omega
  exact_mod_cast harith

/-! ### Conditional two-stage coding with a threaded context -/

/-- Sequential composition of two programs that keeps the original condition
available to the second stage: the first program produces an intermediate
string `w` from the condition `z`, the second program produces the target from
the pair `⟨z, w⟩`. -/
noncomputable def condPairContextComposeDecompressor (V : Map) : Map :=
  fun pr =>
    (V (decodeTotalProgramPairFirst pr.1, pr.2)).bind fun w =>
      V (decodeTotalProgramPairSecond pr.1, pairCode pr.2 w)

theorem condPairContextComposeDecompressor_partrec
    {V : Map} (hV : isDecompressor V) :
    isDecompressor (condPairContextComposeDecompressor V) := by
  have hfirst : Partrec (fun input : BitString × BitString =>
      V (decodeTotalProgramPairFirst input.1, input.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairFirst_computable.comp Computable.fst)
        Computable.snd)
  have hpairCode : Computable₂ (fun (u v : BitString) => pairCode u v) :=
    pairCode_computable
  have hctx : Computable
      (fun input : (BitString × BitString) × BitString =>
        pairCode input.1.2 input.2) :=
    hpairCode.comp (Computable.snd.comp Computable.fst) Computable.snd
  have hsecond : Partrec
      (fun input : (BitString × BitString) × BitString =>
        V (decodeTotalProgramPairSecond input.1.1,
          pairCode input.1.2 input.2)) :=
    Partrec.comp hV
      (Computable.pair
        (decodeTotalProgramPairSecond_computable.comp
          (Computable.fst.comp Computable.fst))
        hctx)
  exact Partrec.bind hfirst hsecond

theorem condPairContextComposeDecompressor_produces
    {V : Map} {p q z w x : BitString}
    (hp : produces V p z w)
    (hq : produces V q (pairCode z w) x) :
    produces (condPairContextComposeDecompressor V)
      (totalProgramPairCode p q) z x := by
  unfold produces condPairContextComposeDecompressor
  rw [decodeTotalProgramPairFirst_pair, Part.mem_bind_iff]
  exact ⟨w, hp, by simpa using hq⟩

/-- **Conditional two-stage coding with a threaded context.**  Describing `w`
from `z` and then `x` from the pair `⟨z, w⟩` describes `x` from `z`, at the cost
of a self-delimiting header for the first program. -/
theorem condK_two_stage_pair_context
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (x z w : BitString) (a b : Nat),
      condK V w z ≤ (a : ENat) →
      condK V x (pairCode z w) ≤ (b : ENat) →
      condK V x z ≤ ((a + b + 2 * (Nat.bits a).length + c : Nat) : ENat) := by
  obtain ⟨cSim, hSim⟩ := hV.2 (condPairContextComposeDecompressor V)
    (condPairContextComposeDecompressor_partrec hV.1)
  refine ⟨cSim + 1, ?_⟩
  intro x z w a b hw hx
  obtain ⟨p, hpLen, hpProd⟩ := (condKLeIff V w z a).mp hw
  obtain ⟨q, hqLen, hqProd⟩ := (condKLeIff V x (pairCode z w) b).mp hx
  change p.length ≤ a at hpLen
  change q.length ≤ b at hqLen
  have hprod := condPairContextComposeDecompressor_produces hpProd hqProd
  have hpBits : (Nat.bits p.length).length ≤ (Nat.bits a).length :=
    length_natBits_mono hpLen
  calc
    condK V x z
      ≤ condK (condPairContextComposeDecompressor V) x z + (cSim : ENat) :=
        hSim _ _
    _ ≤ ((totalProgramPairCode p q).length : ENat) + (cSim : ENat) := by
        gcongr
        exact sInf_le ⟨totalProgramPairCode p q, hprod, rfl⟩
    _ = ((p.length + q.length +
          2 * (Nat.bits p.length).length + 1 + cSim : Nat) : ENat) := by
        rw [length_totalProgramPairCode]
        norm_cast
    _ ≤ ((a + b + 2 * (Nat.bits a).length + (cSim + 1) : Nat) : ENat) := by
        exact_mod_cast (show p.length + q.length +
          2 * (Nat.bits p.length).length + 1 + cSim ≤
            a + b + 2 * (Nat.bits a).length + (cSim + 1) by omega)

/-! ### The noise fibre of a conditionally random pair is large -/

/-- **Lower bound on the noise fibre.**  If `y` is conditionally `epsilon`-random
given `x`, the pair `⟨x, y⟩` lies in `B`, the auxiliary model `A` costs at most
`g` bits given `x`, and `B` costs at most `q` bits given `[A]`, then the fibre
of `B` over `x` has logarithmic cardinality at least
`|y| - epsilon - g - q - O(log N)`. -/
theorem finiteSetFstFiber_logCard_lower_of_random
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B A : Finset BitString) (hB : B.Nonempty) (hA : A.Nonempty)
        (x y : BitString) (epsilon g q N : Nat),
      pairCode x y ∈ B →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V (codedUniformOn A hA).code x ≤ (g : ENat) →
      condK V (codedUniformOn B hB).code
        (codedUniformOn A hA).code ≤ (q : ENat) →
      q ≤ N →
      g ≤ N →
      y.length ≤ epsilon + g + q +
        finiteSetLogCard (finiteSetFstFiber B x) + logSlack c N := by
  obtain ⟨cFib, hFib⟩ := condK_noise_via_pair_fibre V hV
  obtain ⟨cTwo, hTwo⟩ := condK_two_stage_pair_context V hV
  refine ⟨2 + cFib + cTwo, ?_⟩
  intro B A hB hA x y epsilon g q N hpair hrandom hg hq hqN hgN
  set F := finiteSetLogCard (finiteSetFstFiber B x) with hF
  have hfib := hFib B hB A hA x y q N hpair hq hqN
  have hstage := hTwo y x (codedUniformOn A hA).code g
    (q + F + logSlack cFib N) hg hfib
  have hy : (y.length : ENat) ≤
      ((g + (q + F + logSlack cFib N) + 2 * (Nat.bits g).length + cTwo :
        Nat) : ENat) + (epsilon : ENat) :=
    hrandom.trans (by gcongr)
  have hyNat : y.length ≤
      g + (q + F + logSlack cFib N) + 2 * (Nat.bits g).length + cTwo +
        epsilon := by
    exact_mod_cast hy
  have hbits : 2 * (Nat.bits g).length + 2 ≤ logSlack 2 N := by
    have hmono : logSlack 2 g ≤ logSlack 2 N := logSlack_mono_right 2 hgN
    have hls : logSlack 2 g = 2 * (Nat.bits g).length + 2 := rfl
    omega
  have hsum : logSlack 2 N + logSlack cFib N + cTwo ≤
      logSlack (2 + cFib + cTwo) N := by
    rw [logSlack_add_const]
    exact logSlack_add_const_le (2 + cFib) cTwo N
  omega

/-- **Heavy-fibre model of the first coordinate.**  From an ordinary plain
`(i, j)`-model `B` of `pairCode x y`, an auxiliary model `A` with
`C([A] | x) ≤ g` and `C([B] | [A]) ≤ q`, and conditional `epsilon`-randomness of
`y` given `x`, the heavy first-coordinate truncation of `B` is an ordinary plain
model of `x` with complexity `i + O(log N)` and log-size
`j - |y| + epsilon + g + q + O(log N)`. -/
theorem inPlainDescriptionProfile_of_heavy_fibre
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ (B A : Finset BitString) (hB : B.Nonempty) (hA : A.Nonempty)
        (x y : BitString) (epsilon g q N i j : Nat),
      pairCode x y ∈ B →
      plainSetComplexity V B hB ≤ (i : ENat) →
      B.card ≤ 2 ^ j →
      (y.length : ENat) ≤ condK V y x + (epsilon : ENat) →
      condK V (codedUniformOn A hA).code x ≤ (g : ENat) →
      condK V (codedUniformOn B hB).code
        (codedUniformOn A hA).code ≤ (q : ENat) →
      q ≤ N →
      g ≤ N →
      j ≤ N →
      InPlainDescriptionProfile V x (i + logSlack c N)
        (j - y.length + epsilon + g + q + logSlack c N + 1) := by
  obtain ⟨cLow, hLow⟩ := finiteSetFstFiber_logCard_lower_of_random V hV
  obtain ⟨cHeavy, hHeavy⟩ :=
    finiteSetFstHeavyTruncation_plainSetComplexity_le V hV
  refine ⟨cLow + cHeavy, ?_⟩
  intro B A hB hA x y epsilon g q N i j hpair hi hj hrandom hg hq hqN hgN hjN
  set F := finiteSetLogCard (finiteSetFstFiber B x) with hF
  set H := finiteSetFstHeavyTruncation B F with hH
  have hxH : x ∈ H := finiteSetFstHeavyTruncation_mem hpair (le_of_eq hF.symm)
  have hHne : H.Nonempty := ⟨x, hxH⟩
  have hlogB : finiteSetLogCard B ≤ j := (finiteSetLogCard_le_iff B j).mpr hj
  have hFj : F ≤ j := by
    refine le_trans ?_ hlogB
    refine finiteSetLogCard_mono ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hlower := hLow B A hB hA x y epsilon g q N hpair hrandom hg hq hqN hgN
  refine ⟨H, hHne, hxH, ?_, ?_⟩
  · have hcomp : plainSetComplexity V H hHne ≤
        plainSetComplexity V B hB + (logSlack cHeavy F : ENat) :=
        hHeavy B hB F hHne
    have hslack : logSlack cHeavy F ≤ logSlack (cLow + cHeavy) N := by
      refine le_trans (logSlack_mono_right cHeavy (show F ≤ N by omega)) ?_
      exact logSlack_mono_left (c := cHeavy) (c' := cLow + cHeavy)
        (by omega) N
    calc
      plainSetComplexity V H hHne
          ≤ plainSetComplexity V B hB + (logSlack cHeavy F : ENat) := hcomp
      _ ≤ (i : ENat) + (logSlack (cLow + cHeavy) N : ENat) :=
          add_le_add hi (by exact_mod_cast hslack)
      _ = ((i + logSlack (cLow + cHeavy) N : Nat) : ENat) := by norm_cast
  · refine (finiteSetLogCard_le_iff H _).mp ?_
    have hcard : finiteSetLogCard H ≤ finiteSetLogCard B - F + 1 :=
      finiteSetFstHeavyTruncation_logCard_le B F
    have hslackLow : logSlack cLow N ≤ logSlack (cLow + cHeavy) N :=
      logSlack_mono_left (c := cLow) (c' := cLow + cHeavy) (by omega) N
    omega

end Kolmogorov
