import KolmogorovMathlib.AlgorithmicStatistics.StrongModels.TotalComplexity

/-!
# Elementary Total-Map Bounds

Basic stability properties of total conditional complexity.  The additive
constants below depend only on the fixed machines and computable output map,
and precede every varying string.
-/

namespace Kolmogorov

/-- A decompressor that ignores its program and returns the context. -/
def contextReturnDecompressor : Map :=
  fun pair => Part.some pair.2

/-- The machine that returns its condition unchanged is a decompressor. -/
lemma contextReturnDecompressor_partrec :
    isDecompressor contextReturnDecompressor :=
  Computable.partrec Computable.snd

/-- The empty program halts on every condition under the condition-returning machine. -/
lemma contextReturnDecompressor_empty_total :
    IsTotalProgram contextReturnDecompressor [] := by
  intro y
  trivial

/-- On the empty program the condition-returning machine outputs its condition. -/
lemma contextReturnDecompressor_empty_produces (x : BitString) :
    produces contextReturnDecompressor [] x x := by
  exact ⟨trivial, rfl⟩

/-- Postcompose the output of a decompressor with a total function. -/
def totalOutputMapDecompressor
    (T : Map) (f : BitString → BitString) : Map :=
  fun pair => (T pair).map f

/-- Post-composing a decompressor with a computable map on outputs again gives a decompressor. -/
lemma totalOutputMapDecompressor_partrec
    (T : Map) (hT : isDecompressor T)
    (f : BitString → BitString) (hf : Computable f) :
    isDecompressor (totalOutputMapDecompressor T f) :=
  Partrec.map hT (Computable.comp hf Computable.snd)

/-- A program total for `T` stays total after post-composing `T` with a map on outputs. -/
lemma IsTotalProgram.outputMap
    {T : Map} {p : BitString}
    (hp : IsTotalProgram T p)
    (f : BitString → BitString) :
    IsTotalProgram (totalOutputMapDecompressor T f) p := by
  intro y
  exact hp y

/-- Applying `f` to outputs can only shorten descriptions: the total conditional complexity of
`f x` under the post-composed machine is at most that of `x` under `T`. -/
lemma totalCondK_outputMap_le
    (T : Map) (f : BitString → BitString)
    (x y : BitString) :
    totalCondK (totalOutputMapDecompressor T f) (f x) y ≤
      totalCondK T x y := by
  apply sInf_le_sInf
  rintro _ ⟨p, hp_total, hp_prod, rfl⟩
  refine ⟨p, hp_total.outputMap f, ?_, rfl⟩
  change f x ∈ Part.map f (T (p, y))
  exact (Part.mem_map_iff _).2 ⟨x, hp_prod, rfl⟩

/-- Precompose the context input of a decompressor with a total function. -/
def totalContextMapDecompressor
    (T : Map) (f : BitString → BitString) : Map :=
  fun pr => T (pr.1, f pr.2)

/-- Pre-composing a decompressor with a computable map on conditions again gives a decompressor. -/
lemma totalContextMapDecompressor_partrec
    (T : Map) (hT : isDecompressor T)
    (f : BitString → BitString) (hf : Computable f) :
    isDecompressor (totalContextMapDecompressor T f) := by
  have : Computable (fun pr : BitString × BitString => (pr.1, f pr.2)) :=
    Computable.pair Computable.fst (hf.comp Computable.snd)
  change Partrec (fun pr : BitString × BitString => T (pr.1, f pr.2))
  exact Partrec.comp hT this

/-- A program total for `T` stays total after pre-composing `T` with a map on conditions. -/
lemma IsTotalProgram.contextMap
    {T : Map} {p : BitString}
    (hp : IsTotalProgram T p)
    (f : BitString → BitString) :
    IsTotalProgram (totalContextMapDecompressor T f) p := by
  intro y
  change (T (p, f y)).Dom
  exact hp (f y)

/-- The total conditional complexity of `x` given `y` under the machine that first applies `f` to
its condition is at most the complexity of `x` given `f y` under `T`. -/
lemma totalCondK_contextMap_le
    (T : Map) (f : BitString → BitString)
    (x y : BitString) :
    totalCondK (totalContextMapDecompressor T f) x y ≤
      totalCondK T x (f y) := by
  apply sInf_le_sInf
  rintro _ ⟨p, hp_total, hp_prod, rfl⟩
  refine ⟨p, ?_, ?_, rfl⟩
  · exact hp_total.contextMap f
  · change x ∈ T (p, f y)
    exact hp_prod

/-- Regard an ordinary plain program as a total conditional program by running
it at the empty context and ignoring the displayed condition. -/
def plainProgramTotalDecompressor (V : Map) : Map :=
  fun pr => V (pr.1, [])

/-- The machine that runs a plain program on the empty condition is a decompressor. -/
lemma plainProgramTotalDecompressor_partrec
    (V : Map) (hV : isDecompressor V) :
    isDecompressor (plainProgramTotalDecompressor V) := by
  unfold plainProgramTotalDecompressor
  exact Partrec.comp hV
    (Computable.pair Computable.fst (Computable.const []))

/-- A plain program that halts on the empty condition is a total program of the associated machine.
A plain program that halts on the empty condition is a total program of the associated machine. -/
lemma plainProgramTotalDecompressor_program_total
    {V : Map} {p x : BitString}
    (hp : produces V p [] x) :
    IsTotalProgram (plainProgramTotalDecompressor V) p := by
  intro y
  change (V (p, [])).Dom
  exact Part.dom_iff_mem.mpr ⟨x, hp⟩

/-- Total conditional complexity under the machine built from `V` never exceeds the plain complexity
under `V`, for any condition. -/
lemma totalCondK_plainProgramTotal_le
    (V : Map) (x y : BitString) :
    totalCondK (plainProgramTotalDecompressor V) x y ≤
      plainK V x := by
  apply sInf_le_sInf
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, plainProgramTotalDecompressor_program_total hp, hp, rfl⟩

/-- Total conditional complexity is bounded by ordinary plain complexity, up
to a constant depending only on the two fixed machines. -/
theorem totalCondK_le_plainK
    (V T : Map) (hV : isDecompressor V)
    (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x y,
      totalCondK T x y ≤ plainK V x + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (plainProgramTotalDecompressor V)
      (plainProgramTotalDecompressor_partrec V hV)
  refine ⟨c, fun x y => ?_⟩
  calc
    totalCondK T x y
        ≤ totalCondK (plainProgramTotalDecompressor V) x y +
            (c : ENat) := hc x y
    _ ≤ plainK V x + (c : ENat) := by
      gcongr
      exact totalCondK_plainProgramTotal_le V x y

/-- A computable change of condition increases total conditional complexity by
at most a uniform additive constant. -/
theorem totalCondK_condition_map_le
    (T : Map) (hT : IsOptimalTotalConditional T)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : Nat, ∀ x y,
      totalCondK T x y ≤ totalCondK T x (f y) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (totalContextMapDecompressor T f)
      (totalContextMapDecompressor_partrec T hT.1 f hf)
  refine ⟨c, fun x y => ?_⟩
  calc
    totalCondK T x y
        ≤ totalCondK (totalContextMapDecompressor T f) x y + (c : ENat) := hc x y
    _ ≤ totalCondK T x (f y) + (c : ENat) := by
      gcongr
      exact totalCondK_contextMap_le T f x y

/-- Total conditional complexity of a string given itself is uniformly bounded. -/
theorem totalCondK_self_le_const
    (T : Map) (hT : IsOptimalTotalConditional T) :
    ∃ c : Nat, ∀ x,
      totalCondK T x x ≤ (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 contextReturnDecompressor contextReturnDecompressor_partrec
  refine ⟨c, fun x => ?_⟩
  calc
    totalCondK T x x
        ≤ totalCondK contextReturnDecompressor x x + (c : ENat) := hc x x
    _ ≤ (0 : ENat) + (c : ENat) := by
      gcongr
      exact totalCondK_le_programLength
        contextReturnDecompressor_empty_total
        (contextReturnDecompressor_empty_produces x)
    _ = (c : ENat) := zero_add _

/-- A computable output map increases total conditional complexity by at most
a uniform additive constant. -/
theorem totalCondK_map_le
    (T : Map) (hT : IsOptimalTotalConditional T)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : Nat, ∀ x y,
      totalCondK T (f x) y ≤
        totalCondK T x y + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    hT.2 (totalOutputMapDecompressor T f)
      (totalOutputMapDecompressor_partrec T hT.1 f hf)
  refine ⟨c, fun x y => ?_⟩
  calc
    totalCondK T (f x) y
        ≤ totalCondK (totalOutputMapDecompressor T f) (f x) y +
            (c : ENat) := hc (f x) y
    _ ≤ totalCondK T x y + (c : ENat) := by
      gcongr
      exact totalCondK_outputMap_le T f x y

/-- A computable image of the context has uniformly bounded total conditional
complexity relative to that context. -/
theorem totalCondK_map_self_le_const
    (T : Map) (hT : IsOptimalTotalConditional T)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : Nat, ∀ x,
      totalCondK T (f x) x ≤ (c : ENat) := by
  obtain ⟨c_map, h_map⟩ := totalCondK_map_le T hT f hf
  obtain ⟨c_self, h_self⟩ := totalCondK_self_le_const T hT
  refine ⟨c_map + c_self, fun x => ?_⟩
  calc
    totalCondK T (f x) x
        ≤ totalCondK T x x + (c_map : ENat) := h_map x x
    _ ≤ (c_self : ENat) + (c_map : ENat) := by
      gcongr
      exact h_self x
    _ = ((c_self + c_map : Nat) : ENat) := by rw [Nat.cast_add]
    _ = ((c_map + c_self : Nat) : ENat) := by rw [Nat.add_comm]

end Kolmogorov
