import KolmogorovMathlib.CommonInformation.Definitions

namespace Kolmogorov

theorem HasPlainComplexityValue.exists_program
    {V : Map} {x : BitString} {k : Nat}
    (h : HasPlainComplexityValue V x k) :
    ∃ p : BitString, produces V p [] x ∧ p.length = k := by
  have hfinite : KP V x [] ≠ ⊤ := by
    change plainK V x ≠ ⊤
    rw [h]
    exact ENat.natCast_ne_top k
  obtain ⟨p, hp, hlen⟩ :=
    exists_program_of_KP_ne_top (M := V) (x := x) (y := []) hfinite
  refine ⟨p, hp, ?_⟩
  have hlen' : (p.length : ENat) = (k : ENat) := by
    rw [hlen]
    exact h
  exact_mod_cast hlen'

theorem HasPlainConditionalComplexityValue.exists_program
    {V : Map} {x y : BitString} {k : Nat}
    (h : HasPlainConditionalComplexityValue V x y k) :
    ∃ p : BitString, produces V p y x ∧ p.length = k := by
  have hfinite : KP V x y ≠ ⊤ := by
    change condK V x y ≠ ⊤
    rw [h]
    exact ENat.natCast_ne_top k
  obtain ⟨p, hp, hlen⟩ :=
    exists_program_of_KP_ne_top (M := V) (x := x) (y := y) hfinite
  refine ⟨p, hp, ?_⟩
  have hlen' : (p.length : ENat) = (k : ENat) := by
    rw [hlen]
    exact h
  exact_mod_cast hlen'

theorem exists_plainComplexityValue
    (V : Map) (hV : isOptimalConditional V) (x : BitString) :
    ∃ k : Nat, HasPlainComplexityValue V x k := by
  obtain ⟨c, hc⟩ := plainKLeLength V hV
  have hfinite : plainK V x ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hc x)
    rw [← Nat.cast_add]
    exact ENat.natCast_ne_top _
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact ⟨k, hk.symm⟩

theorem exists_plainConditionalComplexityValue
    (V : Map) (hV : isOptimalConditional V) (x y : BitString) :
    ∃ k : Nat, HasPlainConditionalComplexityValue V x y k := by
  obtain ⟨cPlain, hPlain⟩ := plainKLeLength V hV
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  have hbound :
      condK V x y ≤ ((x.length + cPlain + cCond : Nat) : ENat) := by
    calc
      condK V x y ≤ plainK V x + (cCond : ENat) := hCond x y
      _ ≤ ((x.length : Nat) : ENat) + (cPlain : ENat) + (cCond : ENat) := by
        gcongr
        exact hPlain x
      _ = ((x.length + cPlain + cCond : Nat) : ENat) := by push_cast; rfl
  have hfinite : condK V x y ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hbound
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact ⟨k, hk.symm⟩

theorem condK_output_given_plainProgram_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ p x : BitString,
      produces V p [] x → condK V x p ≤ (c : ENat) := by
  let D : Map := fun pr => V (pr.2, [])
  have hD : isDecompressor D :=
    Partrec.comp hV.1 (Computable.pair Computable.snd (Computable.const []))
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p x hp => ?_⟩
  calc
    condK V x p ≤ condK D x p + (c : ENat) := hc x p
    _ ≤ (0 : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨[], hp, rfl⟩
    _ = (c : ENat) := zero_add _

theorem plainK_output_le_plainK_program
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ p x : BitString,
      produces V p [] x →
      plainK V x ≤ plainK V p + (c : ENat) := by
  let D : Map := fun pr =>
    (V (pr.1, [])).bind (fun p => V (p, []))
  have hFirst : Partrec (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV.1 (Computable.pair Computable.fst (Computable.const []))
  have hSecond :
      Partrec (fun q : (BitString × BitString) × BitString => V (q.2, [])) :=
    Partrec.comp hV.1 (Computable.pair Computable.snd (Computable.const []))
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p x hp => ?_⟩
  obtain ⟨kp, hkp⟩ := exists_plainComplexityValue V hV p
  obtain ⟨q, hq, hqLen⟩ := hkp.exists_program
  have hDprod : produces D q [] x := by
    exact Part.mem_bind_iff.mpr ⟨p, hq, hp⟩
  calc
    plainK V x ≤ plainK D x + (c : ENat) := hc x []
    _ ≤ (q.length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨q, hDprod, rfl⟩
    _ = plainK V p + (c : ENat) := by rw [hqLen, hkp]

theorem pairPlainK_output_program_le_plainK_program
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ p x : BitString,
      produces V p [] x →
      pairPlainK V x p ≤ plainK V p + (c : ENat) := by
  let f : BitString →. BitString := fun p =>
    (V (p, [])).map fun x => pairCode x p
  have hRun : Partrec (fun p : BitString => V (p, [])) :=
    Partrec.comp hV.1 (Computable.pair Computable.id (Computable.const []))
  have hPair₂ : Computable₂ (fun x y : BitString => pairCode x y) :=
    pairCode_computable
  have hPair :
      Computable (fun q : BitString × BitString => pairCode q.2 q.1) :=
    hPair₂.comp Computable.snd Computable.fst
  have hf : Partrec f := Partrec.map hRun hPair
  let D : Map := fun pr => (V (pr.1, [])).bind f
  have hFirst : Partrec (fun pr : BitString × BitString => V (pr.1, [])) :=
    Partrec.comp hV.1 (Computable.pair Computable.fst (Computable.const []))
  have hSecond :
      Partrec (fun q : (BitString × BitString) × BitString => f q.2) :=
    Partrec.comp hf Computable.snd
  have hD : isDecompressor D := Partrec.bind hFirst hSecond
  obtain ⟨c, hc⟩ := hV.2 D hD
  refine ⟨c, fun p x hp => ?_⟩
  obtain ⟨kp, hkp⟩ := exists_plainComplexityValue V hV p
  obtain ⟨q, hq, hqLen⟩ := hkp.exists_program
  have hDprod : produces D q [] (pairCode x p) := by
    exact Part.mem_bind_iff.mpr
      ⟨p, hq, Part.mem_map (fun z => pairCode z p) hp⟩
  calc
    pairPlainK V x p ≤ plainK D (pairCode x p) + (c : ENat) := hc (pairCode x p) []
    _ ≤ (q.length : ENat) + (c : ENat) := by
      gcongr
      exact sInf_le ⟨q, hDprod, rfl⟩
    _ = plainK V p + (c : ENat) := by rw [hqLen, hkp]

theorem pairPlainK_left_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString,
      plainK V x ≤ pairPlainK V x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe V hV decodeFirst decodeFirst_computable
  refine ⟨c, fun x y => ?_⟩
  simpa [pairPlainK, decodeFirst_pairCode] using hc (pairCode x y)

theorem pairPlainK_right_le
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString,
      plainK V y ≤ pairPlainK V x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe V hV decodeSecond decodeSecond_computable
  refine ⟨c, fun x y => ?_⟩
  simpa [pairPlainK, decodeSecond_pairCode] using hc (pairCode x y)

theorem condK_right_le_pairPlainK
    (V : Map) (hV : isOptimalConditional V) :
    ∃ c : Nat, ∀ x y : BitString,
      condK V y x ≤ pairPlainK V x y + (c : ENat) := by
  obtain ⟨cCond, hCond⟩ := condKLePlainK V hV
  obtain ⟨cPair, hPair⟩ := pairPlainK_right_le V hV
  refine ⟨cCond + cPair, fun x y => ?_⟩
  calc
    condK V y x ≤ plainK V y + (cCond : ENat) := hCond y x
    _ ≤ (pairPlainK V x y + (cPair : ENat)) + (cCond : ENat) := by
      gcongr
      exact hPair x y
    _ = pairPlainK V x y + ((cCond + cPair : Nat) : ENat) := by
      rw [Nat.cast_add]
      ac_rfl

end Kolmogorov
