import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.Basic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.Prefix.Properties

/-!
# Parameter-charge helpers for the strong-models section

Two small book-keeping lemmas used when charging visible parameters against a
logarithmic slack budget:

* `KPPlain_natCode_le_logSlack` repackages `KPPlain_natCode_le_log` so that the
  cost of a natural-number parameter is expressed directly as a `logSlack`
  budget;
* `logSlack_three_add_le` is the three-summand version of `logSlack_add_le`.
* `KP_partrec_two_parameter_supply` charges a partial-recursive reconstruction
  that really consumes two advice strings by the sum of their prefix
  complexities.
* `KP_le_length_of_computable_width` charges a raw string verbatim when the
  context computably determines its length;
* `KP_partrec_two_parameters_fixed_suffix` combines the two: a reconstruction
  from two advice strings together with a suffix whose width is computed from
  them costs the two prefix complexities plus the bare suffix length, with no
  extra logarithmic magnitude term.
-/

namespace Kolmogorov

/-- The prefix complexity of the code of a natural number `d` is bounded by a
`logSlack` budget in `d`, up to an additive constant. -/
theorem KPPlain_natCode_le_logSlack
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ d : ℕ,
      KPPlain U (natCode d) ≤
        ((logSlack c d + c : ℕ) : ENat) := by
  obtain ⟨c0, hc0⟩ := KPPlain_natCode_le_log U hU
  refine ⟨c0 + 2, fun d => ?_⟩
  refine le_trans (hc0 d) ?_
  have hnat : 2 * (Nat.bits d).length + c0 ≤ logSlack (c0 + 2) d + (c0 + 2) := by
    unfold logSlack
    nlinarith [Nat.zero_le ((Nat.bits d).length), Nat.zero_le c0]
  calc
    2 * ((Nat.bits d).length : ENat) + (c0 : ENat)
        = ((2 * (Nat.bits d).length + c0 : ℕ) : ENat) := by push_cast; ring
    _ ≤ ((logSlack (c0 + 2) d + (c0 + 2) : ℕ) : ENat) := by
        exact_mod_cast hnat

/-- Subadditivity of `logSlack` for three summands. -/
theorem logSlack_three_add_le (c kx delta d : ℕ) :
    logSlack c (kx + delta + d) ≤
      logSlack c kx + logSlack c delta + logSlack c d :=
  le_trans (logSlack_add_le c (kx + delta) d)
    (Nat.add_le_add_right (logSlack_add_le c kx delta) _)

/-- A partial-recursive reconstruction that consumes two explicit advice
strings can be supplied by shortest prefix programs for those strings.  This
is the decoder-side parameter-charge lemma: unlike pair-code subadditivity by
itself, the hypothesis records the reconstruction that actually uses the two
pieces of advice. -/
theorem KP_partrec_two_parameter_supply
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString → BitString →. BitString)
    (hf : Partrec (fun p : BitString × BitString =>
      f p.2 (decodeFirst p.1) (decodeSecond p.1))) :
    ∃ c : ℕ, ∀ (y a b w : BitString), w ∈ f y a b →
      KP U w y ≤ KPPlain U a + KPPlain U b + (c : ENat) := by
  let g : BitString → BitString →. BitString := fun y z =>
    f y (decodeFirst z) (decodeSecond z)
  have hg : Partrec (fun p : BitString × BitString => g p.2 p.1) := by
    simpa [g] using hf
  obtain ⟨cMap, hMap⟩ := KP_partrec_cond_first_map_le U hU g hg
  obtain ⟨cCond, hCond⟩ := KP_le_KPPlain U hU
  obtain ⟨cPair, hPair⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  refine ⟨cMap + cCond + cPair, fun y a b w hw => ?_⟩
  have hw' : w ∈ g y (pairCode a b) := by
    simpa [g, decodeFirst_pairCode, decodeSecond_pairCode] using hw
  calc
    KP U w y ≤ KP U (pairCode a b) y + (cMap : ENat) :=
      hMap (pairCode a b) w y hw'
    _ ≤ (KPPlain U (pairCode a b) + (cCond : ENat)) + (cMap : ENat) := by
      gcongr
      exact hCond (pairCode a b) y
    _ ≤ (KPPlain U a + KPPlain U b + (cPair : ENat)) +
          (cCond : ENat) + (cMap : ENat) := by
      gcongr
      exact hPair a b
    _ = KPPlain U a + KPPlain U b +
          ((cMap + cCond + cPair : ℕ) : ENat) := by
      push_cast
      abel

/-! ### A fixed-width raw suffix in a context that determines its width -/

/-- Option-valued conditional decompressor accepting exactly those programs whose
length is the width computed from the context, returning the program literally. -/
def exactWidthContextDecompressorOpt (width : BitString → ℕ)
    (pr : BitString × BitString) : Option BitString :=
  bif (pr.1.length == width pr.2) then some pr.1 else none

/-- Conditional decompressor accepting exactly those programs whose length is the
width computed from the context.  For each fixed context all halting programs
have the same length, so the domain is prefix-free. -/
def exactWidthContextDecompressor (width : BitString → ℕ) : Map := fun pr =>
  Part.ofOption (exactWidthContextDecompressorOpt width pr)

lemma exactWidthContextDecompressor_computable {width : BitString → ℕ}
    (hwidth : Computable width) :
    isDecompressor (exactWidthContextDecompressor width) := by
  have h_opt : Computable (exactWidthContextDecompressorOpt width) := by
    have h_len : Computable (fun pr : BitString × BitString => pr.1.length) :=
      Computable.list_length.comp Computable.fst
    have h_w : Computable (fun pr : BitString × BitString => width pr.2) :=
      hwidth.comp Computable.snd
    have h_beq : Computable (fun pr : BitString × BitString =>
        (pr.1.length == width pr.2)) :=
      (Primrec.beq.comp Primrec.fst Primrec.snd).to_comp.comp (h_len.pair h_w)
    have h_none : Computable (fun (_ : BitString × BitString) => (none : Option BitString)) :=
      Computable.const (α := BitString × BitString) (σ := Option BitString) none
    exact (Computable.cond h_beq (Computable.option_some.comp Computable.fst) h_none).of_eq
      (fun pr => by
        unfold exactWidthContextDecompressorOpt
        cases h : (pr.1.length == width pr.2) <;> rfl)
  exact Computable.ofOption h_opt

lemma exactWidthContextDecompressor_isPrefixMachine (width : BitString → ℕ) :
    IsPrefixMachine (exactWidthContextDecompressor width) := by
  intro y p hp q hq hpre
  have hp' : exactWidthContextDecompressorOpt width (p, y) ≠ none := by
    intro h
    change (Part.ofOption (exactWidthContextDecompressorOpt width (p, y))).Dom at hp
    rw [h] at hp
    exact hp
  have hq' : exactWidthContextDecompressorOpt width (q, y) ≠ none := by
    intro h
    change (Part.ofOption (exactWidthContextDecompressorOpt width (q, y))).Dom at hq
    rw [h] at hq
    exact hq
  unfold exactWidthContextDecompressorOpt at hp' hq'
  cases hp_eq : (p.length == width y) <;> rw [hp_eq] at hp'
  · contradiction
  cases hq_eq : (q.length == width y) <;> rw [hq_eq] at hq'
  · contradiction
  have hplen : p.length = width y := beq_iff_eq.mp hp_eq
  have hqlen : q.length = width y := beq_iff_eq.mp hq_eq
  exact hpre.eq_of_length (by rw [hplen, hqlen])

lemma exactWidthContextDecompressor_produces {width : BitString → ℕ}
    (z y : BitString) (h : z.length = width y) :
    produces (exactWidthContextDecompressor width) z y z := by
  unfold produces exactWidthContextDecompressor exactWidthContextDecompressorOpt
  rw [beq_iff_eq.mpr h]
  exact ⟨trivial, rfl⟩

/-- **Fixed-width raw suffix bound.**  If the context `y` computably determines
the length of `z`, then `z` itself can be handed to a prefix machine verbatim:
`KP U z y ≤ |z| + O(1)`, with no logarithmic length overhead. -/
theorem KP_le_length_of_computable_width
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (width : BitString → ℕ) (hwidth : Computable width) :
    ∃ c : ℕ, ∀ z y : BitString, z.length = width y →
      KP U z y ≤ (z.length : ENat) + (c : ENat) := by
  have hM : IsPrefixDecompressor (exactWidthContextDecompressor width) :=
    ⟨exactWidthContextDecompressor_computable hwidth,
      exactWidthContextDecompressor_isPrefixMachine width⟩
  obtain ⟨c, hc⟩ := hU.invariance hM
  refine ⟨c, fun z y hz => ?_⟩
  have hprod := exactWidthContextDecompressor_produces (width := width) z y hz
  calc
    KP U z y ≤ KP (exactWidthContextDecompressor width) z y + (c : ENat) := hc z y
    _ ≤ (z.length : ENat) + (c : ENat) := by
        gcongr
        exact KP_le_programLength_of_produces hprod

/-- **Two parameters plus a fixed-width suffix.**  A partial-recursive
reconstruction that consumes two advice strings `a`, `b` and a further string
`z` whose exact width is computed from `a` and `b` is charged by
`KPPlain a + KPPlain b + |z| + O(1)`: because the width of `z` is recovered from
the decoded parameters, the raw suffix `z` costs only its own length, with no
extra `O(log |z|)` magnitude term. -/
theorem KP_partrec_two_parameters_fixed_suffix
    (U : Map) (hU : IsOptimalPrefixConditional U)
    (width : BitString → BitString → ℕ)
    (hwidth : Computable fun p : BitString × BitString => width p.1 p.2)
    (f : BitString → BitString → BitString → BitString →. BitString)
    (hf : Partrec (fun p : BitString × BitString =>
      f p.2 (decodeFirst (decodeFirst p.1)) (decodeSecond (decodeFirst p.1))
        (decodeSecond p.1))) :
    ∃ c : ℕ, ∀ (y a b z w : BitString), z.length = width a b → w ∈ f y a b z →
      KP U w y ≤ KPPlain U a + KPPlain U b + (z.length : ENat) + (c : ENat) := by
  -- The reconstruction, packed as a partial map of a single string argument.
  let g : BitString → BitString →. BitString := fun y q =>
    f y (decodeFirst (decodeFirst q)) (decodeSecond (decodeFirst q)) (decodeSecond q)
  have hg : Partrec (fun p : BitString × BitString => g p.2 p.1) := by
    simpa [g] using hf
  obtain ⟨cMap, hMap⟩ := KP_partrec_cond_first_map_le U hU g hg
  obtain ⟨cCond, hCond⟩ := KP_le_KPPlain U hU
  obtain ⟨cChain, hChain⟩ := KPPlain_le_KPPlain_add_KP U hU
  obtain ⟨cPairPlain, hPairPlain⟩ := KPPair_le_KPPlain_add_KPPlain U hU
  -- Building `pairCode v z` from the context `v` and the data `z`.
  obtain ⟨cBuild, hBuild⟩ :=
    KP_partrec_cond_first_map_le U hU
      (fun v z => (Part.some (pairCode v z) : Part BitString))
      (by
        have hswap : Computable (fun p : BitString × BitString => (p.2, p.1)) :=
          Computable.pair Computable.snd Computable.fst
        have hbuild : Computable (fun p : BitString × BitString => pairCode p.2 p.1) :=
          Computable.comp (g := fun p : BitString × BitString => (p.2, p.1))
            pairCode_computable hswap
        exact hbuild.partrec)
  -- The width of the suffix, read off from the context.
  have hsplit : Computable (fun v : BitString => (decodeFirst v, decodeSecond v)) :=
    Computable.pair decodeFirst_computable decodeSecond_computable
  obtain ⟨cWidth, hWidth⟩ :=
    KP_le_length_of_computable_width U hU
      (fun v => width (decodeFirst v) (decodeSecond v))
      (Computable.comp (g := fun v : BitString => (decodeFirst v, decodeSecond v)) hwidth hsplit)
  refine ⟨cMap + cCond + cChain + cPairPlain + cBuild + cWidth, ?_⟩
  intro y a b z w hz hw
  set v : BitString := pairCode a b with hv
  set P : BitString := pairCode v z with hP
  have hdec1 : decodeFirst P = v := by rw [hP, decodeFirst_pairCode]
  have hdec2 : decodeSecond P = z := by rw [hP, decodeSecond_pairCode]
  have hwP : w ∈ g y P := by
    simp only [g, hdec1, hdec2, hv, decodeFirst_pairCode, decodeSecond_pairCode]
    exact hw
  have hzv : z.length = width (decodeFirst v) (decodeSecond v) := by
    rw [hv, decodeFirst_pairCode, decodeSecond_pairCode]; exact hz
  have hstep1 : KP U w y ≤ KP U P y + (cMap : ENat) := hMap P w y hwP
  have hstep2 : KP U P y ≤ KPPlain U P + (cCond : ENat) := hCond P y
  have hstep3 : KPPlain U P ≤ KPPlain U v + KP U P v + (cChain : ENat) := hChain P v
  have hstep4 : KP U P v ≤ KP U z v + (cBuild : ENat) :=
    hBuild z P v (by simp [hP])
  have hstep5 : KP U z v ≤ (z.length : ENat) + (cWidth : ENat) := hWidth z v hzv
  have hstep6 : KPPlain U v ≤ KPPlain U a + KPPlain U b + (cPairPlain : ENat) := by
    have := hPairPlain a b
    simpa [hv, KPPair, KPPlain] using this
  calc
    KP U w y ≤ KP U P y + (cMap : ENat) := hstep1
    _ ≤ (KPPlain U P + (cCond : ENat)) + (cMap : ENat) := by gcongr
    _ ≤ ((KPPlain U v + KP U P v + (cChain : ENat)) + (cCond : ENat)) + (cMap : ENat) := by
        gcongr
    _ ≤ (((KPPlain U a + KPPlain U b + (cPairPlain : ENat))
            + (KP U z v + (cBuild : ENat)) + (cChain : ENat))
          + (cCond : ENat)) + (cMap : ENat) := by
        gcongr
    _ ≤ (((KPPlain U a + KPPlain U b + (cPairPlain : ENat))
            + (((z.length : ENat) + (cWidth : ENat)) + (cBuild : ENat)) + (cChain : ENat))
          + (cCond : ENat)) + (cMap : ENat) := by
        gcongr
    _ = KPPlain U a + KPPlain U b + (z.length : ENat)
          + ((cMap + cCond + cChain + cPairPlain + cBuild + cWidth : ℕ) : ENat) := by
        push_cast
        abel

end Kolmogorov
